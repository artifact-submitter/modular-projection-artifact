#!/usr/bin/env python3
"""Small, deliberately strict parsers for the repository's Lean source style.

This is not a general Lean parser.  It recognizes the canonical import,
namespace, section, and explicit declaration commands used by CertifiedJL.
Unsupported public-declaration syntax is rejected instead of being silently
omitted from an evidence manifest.
"""

from __future__ import annotations

from dataclasses import dataclass
import re


class LeanSourceError(ValueError):
    """The source is outside the syntax understood by this evidence parser."""


def strip_lean_comments(source: str, owner: str) -> str:
    """Erase nested Lean comments while preserving newlines and strings."""

    output: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    escaped = False
    while index < len(source):
        pair = source[index:index + 2]
        character = source[index]
        if block_depth:
            if pair == "/-":
                output.extend((" ", " "))
                block_depth += 1
                index += 2
            elif pair == "-/":
                output.extend((" ", " "))
                block_depth -= 1
                index += 2
            else:
                output.append("\n" if character == "\n" else " ")
                index += 1
            continue
        if in_string:
            output.append(character)
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                in_string = False
            index += 1
            continue
        if pair == "/-":
            output.extend((" ", " "))
            block_depth = 1
            index += 2
        elif pair == "--":
            output.extend((" ", " "))
            index += 2
            while index < len(source) and source[index] != "\n":
                output.append(" ")
                index += 1
        else:
            output.append(character)
            if character == '"':
                in_string = True
            index += 1
    if block_depth:
        raise LeanSourceError(f"unclosed block comment in {owner}")
    if in_string:
        raise LeanSourceError(f"unclosed string in {owner}")
    return "".join(output)


def strip_lean_attributes(source: str, owner: str) -> str:
    """Erase balanced ``@[...]`` commands, including multiline attributes."""

    output: list[str] = []
    index = 0
    attribute_depth = 0
    in_string = False
    escaped = False
    while index < len(source):
        pair = source[index:index + 2]
        character = source[index]
        if not attribute_depth and pair == "@[":
            output.extend((" ", " "))
            attribute_depth = 1
            index += 2
            continue
        if attribute_depth:
            output.append("\n" if character == "\n" else " ")
            if in_string:
                if escaped:
                    escaped = False
                elif character == "\\":
                    escaped = True
                elif character == '"':
                    in_string = False
            elif character == '"':
                in_string = True
            elif character == "[":
                attribute_depth += 1
            elif character == "]":
                attribute_depth -= 1
            index += 1
            continue
        output.append(character)
        index += 1
    if attribute_depth:
        raise LeanSourceError(f"unclosed attribute in {owner}")
    return "".join(output)


def imports_in_source(source: str, owner: str) -> tuple[str, ...]:
    """Return canonical one-module-per-command imports."""

    normalized = strip_lean_comments(source, owner)
    imports: list[str] = []
    for line_number, line in enumerate(normalized.splitlines(), start=1):
        if re.match(r"^\s*(?:public\s+)?import\b", line) is None:
            continue
        match = re.fullmatch(
            r"\s*(?:public\s+)?import\s+"
            r"([A-Za-z0-9_]+(?:\.[A-Za-z0-9_]+)*)\s*",
            line,
        )
        if match is None:
            raise LeanSourceError(
                f"noncanonical import in {owner}:{line_number}: {line.strip()}"
            )
        imports.append(match.group(1))
    return tuple(imports)


@dataclass(frozen=True)
class _Scope:
    kind: str
    label: str | None
    namespace_components: tuple[str, ...] = ()


_MODIFIERS = (
    r"(?P<modifiers>"
    r"(?:(?:private|protected|noncomputable|nonrec|local|public|unsafe)\s+)*)"
)
_ORDINARY_KIND = (
    r"(?:structure|inductive|class|opaque|def|abbrev|theorem|lemma|"
    r"axiom|constant)"
)
_INSTANCE_KIND = (
    r"(?:scoped\s+)?instance"
    r"(?:\s*\(\s*priority\s*:=\s*[^)]*\))?"
)
_DECLARATION_PATTERN = re.compile(
    r"^\s*" + _MODIFIERS
    + rf"(?:{_ORDINARY_KIND}|{_INSTANCE_KIND})\s+"
    + r"(?P<name>[A-Za-z0-9_]+(?:\.[A-Za-z0-9_]+)*)\b"
)
_ANONYMOUS_INSTANCE_PATTERN = re.compile(
    r"^\s*" + _MODIFIERS + _INSTANCE_KIND + r"\s*:"
)
_DECLARATION_START_PATTERN = re.compile(
    r"^\s*" + _MODIFIERS
    + rf"(?:{_ORDINARY_KIND}|(?:scoped\s+)?instance)\b"
)


def _namespace_components(scopes: list[_Scope]) -> list[str]:
    return [
        component
        for scope in scopes
        if scope.kind == "namespace"
        for component in scope.namespace_components
    ]


def qualified_declarations(source: str, owner: str) -> set[str]:
    """Collect explicit non-private declarations with their Lean namespaces.

    Named and anonymous ``section`` scopes are tracked separately from
    namespaces.  This matters for files that close a named section with
    ``end Foo`` before closing their surrounding namespace.
    """

    source = strip_lean_attributes(strip_lean_comments(source, owner), owner)
    scopes: list[_Scope] = []
    declarations: set[str] = set()
    namespace_pattern = re.compile(
        r"^\s*namespace\s+([A-Za-z0-9_.]+)\s*$"
    )
    section_pattern = re.compile(
        r"^\s*section(?:\s+([A-Za-z0-9_.]+))?\s*$"
    )
    end_pattern = re.compile(r"^\s*end(?:\s+([A-Za-z0-9_.]+))?\s*$")
    lines = source.splitlines()
    line_index = 0
    while line_index < len(lines):
        line = lines[line_index]
        if match := namespace_pattern.match(line):
            name = match.group(1)
            scopes.append(
                _Scope("namespace", name, tuple(name.split(".")))
            )
            line_index += 1
            continue
        if match := section_pattern.match(line):
            scopes.append(_Scope("section", match.group(1)))
            line_index += 1
            continue
        if match := end_pattern.match(line):
            if not scopes:
                raise LeanSourceError(
                    f"unbalanced scope end in {owner}:{line_index + 1}: {line}"
                )
            scope = scopes.pop()
            closing_name = match.group(1)
            if closing_name is not None:
                acceptable = {scope.label}
                if scope.namespace_components:
                    acceptable.add(scope.namespace_components[-1])
                    acceptable.add(".".join(scope.namespace_components))
                if closing_name not in acceptable:
                    raise LeanSourceError(
                        f"scope end {closing_name!r} closes "
                        f"{scope.label!r} in {owner}:{line_index + 1}"
                    )
            line_index += 1
            continue

        start_match = _DECLARATION_START_PATTERN.match(line)
        if start_match is None:
            line_index += 1
            continue
        start_modifiers = start_match.group("modifiers").split()
        if "private" in start_modifiers or "local" in start_modifiers:
            line_index += 1
            continue

        header = line
        end_index = line_index
        named_match = _DECLARATION_PATTERN.match(header)
        anonymous_match = _ANONYMOUS_INSTANCE_PATTERN.match(header)
        while (
            named_match is None
            and anonymous_match is None
            and end_index + 1 < len(lines)
            and end_index - line_index < 12
        ):
            end_index += 1
            header += " " + lines[end_index].strip()
            named_match = _DECLARATION_PATTERN.match(header)
            anonymous_match = _ANONYMOUS_INSTANCE_PATTERN.match(header)

        if anonymous_match is not None:
            raise LeanSourceError(
                f"anonymous public instance in {owner}:{line_index + 1}"
            )
        if named_match is None:
            raise LeanSourceError(
                f"unsupported public declaration in "
                f"{owner}:{line_index + 1}: {header}"
            )
        namespace = _namespace_components(scopes)
        if not namespace:
            raise LeanSourceError(
                f"public declaration outside namespace in "
                f"{owner}:{line_index + 1}: {line}"
            )
        declaration = ".".join([*namespace, named_match.group("name")])
        if declaration in declarations:
            raise LeanSourceError(
                f"duplicate explicit declaration {declaration} in {owner}"
            )
        declarations.add(declaration)
        line_index = end_index + 1

    if scopes:
        rendered = [(scope.kind, scope.label) for scope in scopes]
        raise LeanSourceError(f"unclosed scopes in {owner}: {rendered}")
    return declarations
