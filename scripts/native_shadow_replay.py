#!/usr/bin/env python3
"""Build certificate roots in an isolated native-decide shadow tree.

Production sources are never edited.  The selected replay roots and their
repository import closure define the only files in which ``decide +kernel``
may be replaced by ``native_decide``.  A deterministic manifest authenticates
the source tree, catalog selection, closure, and every replacement.
"""

from __future__ import annotations

import argparse
from collections import deque
from dataclasses import asdict, dataclass
import hashlib
import json
import os
import platform
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import time
import tomllib

from lean_source import imports_in_source
from compute_replay_digest import compute_identity, validate_identity_document


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CATALOG = ROOT / "evidence" / "certificates" / "replay-families.toml"
DOCUMENT_DOMAINS = {
    "source-inputs": b"CertifiedJL native replay source inputs v2\0",
    "manifest": b"CertifiedJL native shadow replay manifest v2\0",
    "provenance": b"CertifiedJL native shadow replay provenance v2\0",
    "audit": b"CertifiedJL native replay independent audit v2\0",
    "receipt": b"CertifiedJL native replay success receipt v2\0",
}
DOCUMENT_HASH_FIELDS = {
    "source-inputs": "source_inputs_sha256",
    "manifest": "manifest_sha256",
    "provenance": "provenance_sha256",
    "audit": "audit_sha256",
    "receipt": "receipt_sha256",
}
TREE_DOMAIN = b"CertifiedJL native shadow replay tree v2"
BUILD_INPUT_DOMAIN = b"CertifiedJL native shadow replay build inputs v2\0"
KERNEL_DECIDE = re.compile(r"\bdecide\s*\+kernel\b")
MODULE = re.compile(r"[A-Za-z0-9_]+(?:\.[A-Za-z0-9_]+)*\Z")
AUDIT_TARGETS_PER_BLOCK = 256


class NativeReplayError(RuntimeError):
    """The requested native replay is not safely reproducible."""


@dataclass(frozen=True)
class Replacement:
    line: int
    column: int
    start: int
    stop: int
    original: str
    declaration: str
    declaration_kind: str
    declaration_type_source_sha256: str
    category: str
    proof_start: int
    proof_stop: int
    replacement: str = "native_decide"


@dataclass(frozen=True)
class TransformedFile:
    module: str
    path: str
    source_sha256: str
    shadow_sha256: str
    replacements: tuple[Replacement, ...]


@dataclass(frozen=True)
class ProofSpan:
    declaration: str
    declaration_kind: str
    declaration_start: int
    proof_start: int
    proof_stop: int
    type_source_sha256: str
    is_private: bool
    is_whole_replay: bool


@dataclass(frozen=True)
class ExcludedSite:
    line: int
    column: int
    start: int
    stop: int
    original: str
    declaration: str
    reason: str


def sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def read_utf8_exact(path: Path) -> str:
    return path.read_bytes().decode("utf-8")


def write_utf8_exact(path: Path, source: str) -> None:
    path.write_bytes(source.encode("utf-8"))


def module_source(root: Path, module: str) -> Path:
    return root / (module.replace(".", "/") + ".lean")


def module_name(root: Path, source: Path) -> str:
    return ".".join(source.relative_to(root).with_suffix("").parts)


def _masked_code(source: str, owner: str) -> str:
    """Mask comments and strings while preserving code offsets and newlines."""

    output: list[str] = []
    index = 0
    block_depth = 0
    line_comment = False
    in_string = False
    escaped = False
    while index < len(source):
        pair = source[index:index + 2]
        character = source[index]
        if line_comment:
            if character == "\n":
                line_comment = False
                output.append("\n")
            else:
                output.append(" ")
            index += 1
            continue
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
            output.append("\n" if character == "\n" else " ")
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                in_string = False
            index += 1
            continue
        if pair == "--":
            output.extend((" ", " "))
            line_comment = True
            index += 2
        elif pair == "/-":
            output.extend((" ", " "))
            block_depth = 1
            index += 2
        elif character == '"':
            output.append(" ")
            in_string = True
            index += 1
        else:
            output.append(character)
            index += 1
    if block_depth:
        raise NativeReplayError(f"unclosed block comment in {owner}")
    if in_string:
        raise NativeReplayError(f"unclosed string in {owner}")
    return "".join(output)


def _proof_spans(source: str, owner: str) -> tuple[ProofSpan, ...]:
    """Recognize public theorem/lemma tactic proofs in repository source style."""

    masked = _masked_code(source, owner)
    lines = masked.splitlines(keepends=True)
    offsets: list[int] = []
    offset = 0
    for line in lines:
        offsets.append(offset)
        offset += len(line)

    scope_stack: list[tuple[str, str, tuple[str, ...]]] = []
    starts: list[tuple[int, str, str, bool]] = []
    namespace_re = re.compile(r"^namespace\s+([A-Za-z0-9_.]+)\s*$")
    section_re = re.compile(r"^section(?:\s+([A-Za-z0-9_.]+))?\s*$")
    end_re = re.compile(r"^end(?:\s+([A-Za-z0-9_.]+))?\s*$")
    declaration_re = re.compile(
        r"^(?P<mods>(?:(?:private|protected|noncomputable|nonrec|public)\s+)*)"
        r"(?P<kind>theorem|lemma)\s+"
        r"(?P<name>[A-Za-z0-9_]+(?:\.[A-Za-z0-9_]+)*)\b"
    )
    top_command_re = re.compile(
        r"^(?:@\[|namespace\b|section\b|end\b|open\b|variable\b|"
        r"include\b|omit\b|attribute\b|set_option\b|"
        r"(?:(?:private|protected|noncomputable|nonrec|local|public|unsafe)\s+)*"
        r"(?:theorem|lemma|def|abbrev|opaque|instance|structure|inductive|class|"
        r"axiom|constant|example)\b|#)"
    )
    command_offsets: list[int] = []
    for line_index, line_with_newline in enumerate(lines):
        line = line_with_newline.rstrip("\r\n")
        if line and not line[0].isspace() and top_command_re.match(line):
            command_offsets.append(offsets[line_index])
        if match := namespace_re.fullmatch(line):
            name = match.group(1)
            scope_stack.append(("namespace", name, tuple(name.split("."))))
            continue
        if match := section_re.fullmatch(line):
            scope_stack.append(("section", match.group(1) or "", ()))
            continue
        if end_re.fullmatch(line):
            if not scope_stack:
                raise NativeReplayError(f"unbalanced scope end in {owner}:{line_index + 1}")
            scope_stack.pop()
            continue
        match = declaration_re.match(line)
        if match is None:
            continue
        namespaces = [
            component
            for kind, _label, components in scope_stack
            if kind == "namespace"
            for component in components
        ]
        if not namespaces:
            raise NativeReplayError(
                f"replay declaration outside namespace in {owner}:{line_index + 1}"
            )
        name = ".".join([*namespaces, match.group("name")])
        private = "private" in match.group("mods").split()
        starts.append((offsets[line_index], match.group("kind"), name, private))

    spans: list[ProofSpan] = []
    for declaration_start, kind, name, private in starts:
        next_commands = [value for value in command_offsets if value > declaration_start]
        declaration_stop = min(next_commands, default=len(source))
        declaration_source = masked[declaration_start:declaration_stop]
        proof_match = re.search(r":=\s*by\b", declaration_source)
        if proof_match is None:
            continue
        proof_start = declaration_start + proof_match.start()
        type_source = source[declaration_start:proof_start]
        proof_source = masked[proof_start:declaration_stop]
        whole_replay = re.fullmatch(
            r":=\s*by\s*"
            r"(?:set_option\s+[A-Za-z0-9_.]+\s+[^\n]+\s+in\s*)*"
            r"decide\s*\+kernel\s*",
            proof_source,
        ) is not None
        spans.append(
            ProofSpan(
                declaration=name,
                declaration_kind=kind,
                declaration_start=declaration_start,
                proof_start=proof_start,
                proof_stop=declaration_stop,
                type_source_sha256=sha256(type_source.encode("utf-8")),
                is_private=private,
                is_whole_replay=whole_replay,
            )
        )
    return tuple(spans)


def classify_replay_sites(
    source: str, owner: str
) -> tuple[tuple[Replacement, ...], tuple[ExcludedSite, ...]]:
    masked = _masked_code(source, owner)
    matches = list(KERNEL_DECIDE.finditer(masked))
    if not matches:
        return (), ()
    spans = _proof_spans(source, owner)
    replacements_list: list[Replacement] = []
    excluded: list[ExcludedSite] = []
    for match in matches:
        owners = [
            span for span in spans if span.proof_start <= match.start() < span.proof_stop
        ]
        if len(owners) != 1:
            raise NativeReplayError(
                f"{owner}:{source.count(chr(10), 0, match.start()) + 1}: "
                "kernel replay site is not owned by one public theorem/lemma proof span"
            )
        proof = owners[0]
        if proof.is_private:
            excluded.append(
                ExcludedSite(
                    line=source.count("\n", 0, match.start()) + 1,
                    column=match.start() - source.rfind("\n", 0, match.start()),
                    start=match.start(),
                    stop=match.end(),
                    original=source[match.start():match.end()],
                    declaration=proof.declaration,
                    reason="private-declaration",
                )
            )
            continue
        replacements_list.append(
            Replacement(
                line=source.count("\n", 0, match.start()) + 1,
                column=match.start() - source.rfind("\n", 0, match.start()),
                start=match.start(),
                stop=match.end(),
                original=source[match.start():match.end()],
                declaration=proof.declaration,
                declaration_kind=proof.declaration_kind,
                declaration_type_source_sha256=proof.type_source_sha256,
                category=(
                    "whole-declaration"
                    if proof.is_whole_replay
                    else "composite-proof"
                ),
                proof_start=proof.proof_start,
                proof_stop=proof.proof_stop,
            )
        )
    return tuple(replacements_list), tuple(excluded)


def transform_source(source: str, owner: str) -> tuple[str, tuple[Replacement, ...]]:
    replacements, _excluded = classify_replay_sites(source, owner)
    transformed = source
    for replacement in reversed(replacements):
        transformed = (
            transformed[:replacement.start]
            + replacement.replacement
            + transformed[replacement.stop:]
        )
    expected = source
    for replacement in reversed(replacements):
        expected = (
            expected[:replacement.start]
            + replacement.replacement
            + expected[replacement.stop:]
        )
    if transformed != expected:
        raise NativeReplayError(f"non-replay bytes changed in {owner}")
    return transformed, replacements


def import_graph(
    root: Path, paths: tuple[Path, ...] | None = None
) -> dict[str, tuple[str, ...]]:
    graph: dict[str, tuple[str, ...]] = {}
    sources = tracked_files(root) if paths is None else paths
    for source in sorted(path for path in sources if path.suffix == ".lean"):
        relative = source.relative_to(root)
        module = module_name(root, source)
        graph[module] = imports_in_source(
            read_utf8_exact(source), relative.as_posix()
        )
    return graph


def import_closure(
    graph: dict[str, tuple[str, ...]], roots: tuple[str, ...]
) -> tuple[str, ...]:
    missing = sorted(root for root in roots if root not in graph)
    if missing:
        raise NativeReplayError(f"replay roots have no repository source: {missing}")
    reached: set[str] = set()
    pending = deque(roots)
    while pending:
        module = pending.popleft()
        if module in reached or module not in graph:
            continue
        reached.add(module)
        pending.extend(graph[module])
    return tuple(sorted(reached))


def validate_production_closure(closure: tuple[str, ...]) -> None:
    fast_modules = [
        module
        for module in closure
        if module == "CertifiedJLFast" or module.startswith("CertifiedJLFast.")
    ]
    if fast_modules:
        raise NativeReplayError(
            f"native production closure reaches fast-assumption modules: {fast_modules}"
        )


def replay_build_roots(
    roots: tuple[str, ...], attesting: bool
) -> tuple[tuple[str, ...], tuple[str, ...]]:
    assembly_roots = ("CertifiedJL",) if attesting else ()
    return tuple(sorted(set(roots) | set(assembly_roots))), assembly_roots


def validate_selection_options(
    direct_roots: tuple[str, ...],
    family_ids: tuple[str, ...],
    all_catalog_families: bool,
) -> None:
    if all_catalog_families and family_ids:
        raise NativeReplayError(
            "do not combine --all-catalog-families with --family-id"
        )
    if direct_roots and (family_ids or all_catalog_families):
        raise NativeReplayError("do not mix direct replay roots with catalog selection")


def validate_attesting_catalog(catalog: Path) -> None:
    """Require proof-record attestations to use the repository's canonical catalog."""
    if catalog.resolve() != DEFAULT_CATALOG.resolve():
        raise NativeReplayError(
            "attesting replay must use evidence/certificates/replay-families.toml"
        )


def roots_from_catalog(
    catalog: Path, family_ids: tuple[str, ...], all_families: bool = False
) -> tuple[tuple[str, ...], tuple[str, ...], tuple[str, ...]]:
    with catalog.open("rb") as stream:
        document = tomllib.load(stream)
    if document.get("schema_version") != 1:
        raise NativeReplayError("unsupported replay-family catalog schema")
    entries = document.get("family", [])
    by_id = {entry.get("id"): entry for entry in entries}
    if len(by_id) != len(entries):
        raise NativeReplayError("certificate catalog has duplicate or missing IDs")
    selected_ids = tuple(sorted(by_id)) if all_families else family_ids
    if not selected_ids:
        raise NativeReplayError("select --family-id, --all-catalog-families, or --root")
    unknown = sorted(set(selected_ids) - set(by_id))
    if unknown:
        raise NativeReplayError(f"unknown certificate family IDs: {unknown}")
    roots: set[str] = set()
    certificate_ids: set[str] = set()
    for family_id in selected_ids:
        record = by_id[family_id]
        certificate_ids.update(record.get("certificate_ids", []))
        for module in record.get("replay_roots", []):
            if MODULE.fullmatch(module) is None:
                raise NativeReplayError(
                    f"{family_id}: invalid replay root: {module!r}"
                )
            roots.add(module)
    return tuple(selected_ids), tuple(sorted(certificate_ids)), tuple(sorted(roots))


def git_output(root: Path, *args: str) -> bytes:
    result = subprocess.run(
        ["git", *args], cwd=root, check=True, stdout=subprocess.PIPE
    )
    return result.stdout


def git_status(root: Path) -> bytes:
    return git_output(root, "status", "--porcelain=v1", "--untracked-files=all")


def tracked_files(root: Path) -> tuple[Path, ...]:
    payload = git_output(root, "ls-files", "-z")
    return tuple(root / os.fsdecode(name) for name in payload.split(b"\0") if name)


def tree_digest(root: Path, paths: tuple[Path, ...]) -> str:
    digest = hashlib.sha256()
    digest.update(TREE_DOMAIN + b"\0")
    for path in paths:
        relative = path.relative_to(root).as_posix().encode("utf-8")
        if path.is_symlink():
            payload = b"120000\0" + os.fsencode(os.readlink(path))
        else:
            mode = b"100755\0" if path.stat().st_mode & 0o111 else b"100644\0"
            payload = mode + path.read_bytes()
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        digest.update(len(payload).to_bytes(8, "big"))
        digest.update(payload)
    return digest.hexdigest()


def copy_tracked_tree(root: Path, shadow: Path, paths: tuple[Path, ...]) -> str:
    for source in paths:
        relative = source.relative_to(root)
        target = shadow / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        if source.is_symlink():
            target.symlink_to(os.readlink(source))
        else:
            shutil.copy2(source, target)
    packages = root / ".lake" / "packages"
    if not packages.is_dir():
        raise NativeReplayError("exact .lake/packages dependency cache is missing")
    shadow_packages = shadow / ".lake" / "packages"
    shadow_packages.mkdir(parents=True)
    for package in packages.iterdir():
        target = shadow_packages / package.name
        target.symlink_to(package.resolve(), target_is_directory=True)
    return tree_digest(shadow, tuple(shadow / path.relative_to(root) for path in paths))


def verified_dependencies(root: Path) -> tuple[dict[str, object], ...]:
    manifest_path = root / "lake-manifest.json"
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise NativeReplayError(f"cannot read lake-manifest.json: {error}") from error
    entries = manifest.get("packages")
    if not isinstance(entries, list):
        raise NativeReplayError("lake manifest has no package list")
    packages = root / ".lake" / "packages"
    if not packages.is_dir():
        raise NativeReplayError("exact .lake/packages dependency cache is missing")
    expected_names = [entry.get("name") for entry in entries]
    if any(not isinstance(name, str) or not name for name in expected_names):
        raise NativeReplayError("lake manifest contains an invalid package name")
    if len(expected_names) != len(set(expected_names)):
        raise NativeReplayError("lake manifest contains duplicate package names")
    actual_names = sorted(path.name for path in packages.iterdir())
    if actual_names != sorted(expected_names):
        raise NativeReplayError(
            "live .lake/packages entries differ from lake-manifest.json"
        )
    result: list[dict[str, object]] = []
    for entry in entries:
        name = str(entry["name"])
        if entry.get("type") != "git":
            raise NativeReplayError(
                f"unsupported non-git dependency {name}: {entry.get('type')!r}"
            )
        if entry.get("subDir") is not None:
            raise NativeReplayError(
                f"unsupported git dependency subdirectory for {name}"
            )
        expected_revision = entry.get("rev")
        if not isinstance(expected_revision, str) or not re.fullmatch(
            r"[0-9a-f]{40}", expected_revision
        ):
            raise NativeReplayError(f"invalid expected git revision for {name}")
        package = (packages / name).resolve()
        if not package.is_dir() or not (package / ".git").exists():
            raise NativeReplayError(f"dependency {name} is not a live git checkout")
        expected_url = entry.get("url")
        if not isinstance(expected_url, str) or not expected_url:
            raise NativeReplayError(f"invalid expected git URL for {name}")
        actual_revision = git_output(package, "rev-parse", "HEAD").decode().strip()
        actual_url = git_output(package, "remote", "get-url", "origin").decode().strip()
        status = git_status(package)
        if actual_revision != expected_revision:
            raise NativeReplayError(
                f"dependency {name} revision differs from lake-manifest.json"
            )
        if status:
            raise NativeReplayError(f"dependency {name} checkout is not clean")
        if actual_url != expected_url:
            raise NativeReplayError(
                f"dependency {name} origin differs from lake-manifest.json"
            )
        result.append(
            {
                "name": name,
                "type": "git",
                "expected_url": expected_url,
                "actual_url": actual_url,
                "expected_revision": expected_revision,
                "actual_revision": actual_revision,
                "status_sha256": sha256(status),
            }
        )
    return tuple(sorted(result, key=lambda record: str(record["name"])))


def transform_closure(
    source_root: Path, shadow_root: Path, closure: tuple[str, ...]
) -> tuple[tuple[TransformedFile, ...], tuple[dict[str, object], ...]]:
    transformed_files: list[TransformedFile] = []
    excluded_sites: list[dict[str, object]] = []
    for module in closure:
        source_path = module_source(source_root, module)
        if not source_path.is_file():
            continue
        source = read_utf8_exact(source_path)
        replacements, excluded = classify_replay_sites(source, module)
        transformed = source
        for replacement in reversed(replacements):
            transformed = (
                transformed[:replacement.start]
                + replacement.replacement
                + transformed[replacement.stop:]
            )
        excluded_sites.extend(
            {
                "module": module,
                "path": source_path.relative_to(source_root).as_posix(),
                **asdict(site),
            }
            for site in excluded
        )
        if not replacements:
            continue
        shadow_path = module_source(shadow_root, module)
        write_utf8_exact(shadow_path, transformed)
        transformed_files.append(
            TransformedFile(
                module=module,
                path=source_path.relative_to(source_root).as_posix(),
                source_sha256=sha256(source.encode("utf-8")),
                shadow_sha256=sha256(transformed.encode("utf-8")),
                replacements=replacements,
            )
        )
    return tuple(transformed_files), tuple(excluded_sites)


def _canonical_manifest(payload: dict[str, object]) -> bytes:
    return json.dumps(
        payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("utf-8")


def seal_document(payload: dict[str, object], kind: str) -> dict[str, object]:
    if kind not in DOCUMENT_DOMAINS:
        raise NativeReplayError(f"unknown native replay document kind: {kind}")
    result = dict(payload)
    hash_field = DOCUMENT_HASH_FIELDS[kind]
    result.pop(hash_field, None)
    result["document_kind"] = kind
    result[hash_field] = sha256(DOCUMENT_DOMAINS[kind] + _canonical_manifest(result))
    return result


def verify_document(document: dict[str, object], kind: str) -> None:
    if document.get("document_kind") != kind:
        raise NativeReplayError(f"native replay document is not a {kind} document")
    hash_field = DOCUMENT_HASH_FIELDS[kind]
    claimed = document.get(hash_field)
    if not isinstance(claimed, str):
        raise NativeReplayError(f"native {kind} document is not sealed")
    unsigned = dict(document)
    unsigned.pop(hash_field)
    expected = sha256(DOCUMENT_DOMAINS[kind] + _canonical_manifest(unsigned))
    if claimed != expected:
        raise NativeReplayError(f"native {kind} document digest mismatch")


def seal_manifest(payload: dict[str, object]) -> dict[str, object]:
    """Compatibility name for the schema-v2 manifest sealer."""
    return seal_document(payload, "manifest")


def verify_manifest(manifest: dict[str, object]) -> None:
    verify_document(manifest, "manifest")
    for record in manifest.get("transformed_files", []):
        if not record.get("replacements"):
            raise NativeReplayError("manifest contains an unchanged transformed file")


def write_manifest(path: Path, manifest: dict[str, object]) -> None:
    verify_manifest(manifest)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")


def write_document(path: Path, document: dict[str, object], kind: str) -> None:
    verify_document(document, kind)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(document, indent=2, sort_keys=True) + "\n")


def write_document_exclusive(
    path: Path, document: dict[str, object], kind: str
) -> None:
    verify_document(document, kind)
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        with path.open("x", encoding="utf-8") as stream:
            stream.write(json.dumps(document, indent=2, sort_keys=True) + "\n")
    except FileExistsError as error:
        raise NativeReplayError(f"refusing to replace existing {path}") from error


def read_document(path: Path, kind: str) -> dict[str, object]:
    try:
        document = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise NativeReplayError(f"cannot read {path}: {error}") from error
    if not isinstance(document, dict):
        raise NativeReplayError(f"expected a JSON object in {path}")
    verify_document(document, kind)
    return document


def execution_environment(argv: list[str], cwd: Path = ROOT) -> dict[str, object]:
    lean = subprocess.run(
        ["lean", "--version"], check=True, text=True,
        cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    ).stdout.strip()
    lake = subprocess.run(
        ["lake", "--version"], check=True, text=True,
        cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    ).stdout.strip()
    env_names = (
        "LEAN_NUM_THREADS", "LAKE_ARTIFACT_CACHE", "LAKE_NO_CACHE",
        "CERTIFIEDJL_NATIVE_BUILD_DIR", "CERTIFIEDJL_NATIVE_SHADOW_DIR",
        "LEAN_PATH", "LEAN_SRC_PATH", "LEAN_OPTS",
    )
    ci_names = ("GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT", "GITHUB_SHA", "GITHUB_REPOSITORY")
    return {
        "argv": argv,
        "lean_version": lean,
        "lake_version": lake,
        "os": platform.system(),
        "os_release": platform.release(),
        "architecture": platform.machine(),
        "python_version": platform.python_version(),
        "environment": {name: os.environ.get(name) for name in env_names},
        "github": {name: os.environ.get(name) for name in ci_names},
    }


def validate_execution_environment(record: object, label: str) -> None:
    if not isinstance(record, dict):
        raise NativeReplayError(f"{label} has no execution environment")
    if (
        not isinstance(record.get("argv"), list)
        or not all(isinstance(value, str) for value in record["argv"])
        or not record["argv"]
        or not isinstance(record.get("lean_version"), str)
        or not record["lean_version"]
        or not isinstance(record.get("lake_version"), str)
        or not record["lake_version"]
        or not isinstance(record.get("os"), str)
        or not isinstance(record.get("os_release"), str)
        or not isinstance(record.get("architecture"), str)
        or not isinstance(record.get("python_version"), str)
    ):
        raise NativeReplayError(f"{label} execution environment is incomplete")
    environment = record.get("environment")
    expected_names = {
        "LEAN_NUM_THREADS", "LAKE_ARTIFACT_CACHE", "LAKE_NO_CACHE",
        "CERTIFIEDJL_NATIVE_BUILD_DIR", "CERTIFIEDJL_NATIVE_SHADOW_DIR",
        "LEAN_PATH", "LEAN_SRC_PATH", "LEAN_OPTS",
    }
    if (
        not isinstance(environment, dict)
        or set(environment) != expected_names
        or not all(value is None or isinstance(value, str) for value in environment.values())
    ):
        raise NativeReplayError(f"{label} relevant environment is incomplete")
    github = record.get("github")
    expected_ci_names = {
        "GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT", "GITHUB_SHA", "GITHUB_REPOSITORY"
    }
    if (
        not isinstance(github, dict)
        or set(github) != expected_ci_names
        or not all(value is None or isinstance(value, str) for value in github.values())
    ):
        raise NativeReplayError(f"{label} GitHub execution identity is incomplete")


def validate_execution_against_current(
    record: object, label: str, expected_script: str
) -> None:
    validate_execution_environment(record, label)
    assert isinstance(record, dict)
    observed = execution_environment([expected_script])
    for field in (
        "lean_version", "lake_version", "os", "os_release", "architecture",
        "python_version", "environment", "github",
    ):
        if record.get(field) != observed.get(field):
            raise NativeReplayError(f"{label} execution identity differs at {field}")
    argv = record["argv"]
    if not any(Path(value).name == expected_script for value in argv):
        raise NativeReplayError(f"{label} argv does not name {expected_script}")


def validate_github_source_commit(
    record: object, source_commit: object, label: str
) -> None:
    validate_execution_environment(record, label)
    assert isinstance(record, dict)
    github_sha = record["github"].get("GITHUB_SHA")
    if github_sha is not None and github_sha != source_commit:
        raise NativeReplayError(f"{label} GITHUB_SHA differs from the source commit")


def build_input_identity(
    shadow: Path,
    closure: tuple[str, ...],
    build_roots: tuple[str, ...],
    dependencies: tuple[dict[str, object], ...],
) -> dict[str, object]:
    modules: list[dict[str, str]] = []
    for module in closure:
        path = module_source(shadow, module)
        if path.is_file():
            modules.append({
                "module": module,
                "path": path.relative_to(shadow).as_posix(),
                "sha256": sha256(path.read_bytes()),
            })
    configuration = []
    for relative in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        path = shadow / relative
        configuration.append({"path": relative, "sha256": sha256(path.read_bytes())})
    payload: dict[str, object] = {
        "schema_version": 2,
        "build_roots": list(build_roots),
        "build_command": ["lake", "build", *build_roots],
        "axiom_audit_command": ["lake", "env", "lean", "CertifiedJLNativeReplayAudit.lean"],
        "closure_modules": list(closure),
        "module_inputs": modules,
        "configuration_inputs": configuration,
        "dependencies": list(dependencies),
        "transformation": "owned decide +kernel sites to native_decide, v2",
    }
    return {
        **payload,
        "digest": sha256(BUILD_INPUT_DOMAIN + _canonical_manifest(payload)),
    }


def build_manifest(
    *,
    root: Path,
    catalog: Path | None,
    family_ids: tuple[str, ...],
    certificate_ids: tuple[str, ...],
    roots: tuple[str, ...],
    build_roots: tuple[str, ...],
    assembly_roots: tuple[str, ...],
    validation_scope: str,
    closure: tuple[str, ...],
    transformed: tuple[TransformedFile, ...],
    excluded_sites: tuple[dict[str, object], ...],
    source_tree_sha256: str,
    shadow_tree_sha256_before_transform: str,
    shadow_tree_sha256_after_transform: str,
    dependencies: tuple[dict[str, object], ...],
    source_status: bytes,
    source_inputs: dict[str, object],
    build_inputs: dict[str, object],
    execution: dict[str, object],
    incremental_cache: dict[str, object],
) -> dict[str, object]:
    payload: dict[str, object] = {
        "schema_version": 2,
        "mode": "native-shadow-replay",
        "attests_execution": False,
        "source_inputs_sha256": source_inputs["source_inputs_sha256"],
        "source_commit": git_output(root, "rev-parse", "HEAD").decode().strip(),
        "source_clean": not source_status,
        "source_status_sha256": sha256(source_status),
        "source_tree_sha256": source_tree_sha256,
        "shadow_tree_sha256_before_transform": shadow_tree_sha256_before_transform,
        "shadow_tree_sha256_after_transform": shadow_tree_sha256_after_transform,
        "catalog": None if catalog is None else catalog.relative_to(root).as_posix(),
        "catalog_sha256": None if catalog is None else sha256(catalog.read_bytes()),
        "family_ids": list(family_ids),
        "certificate_ids": list(certificate_ids),
        "roots": list(roots),
        "build_roots": list(build_roots),
        "build_command": ["lake", "build", *build_roots],
        "axiom_audit_command": [
            "lake", "env", "lean", "CertifiedJLNativeReplayAudit.lean"
        ],
        "assembly_roots": list(assembly_roots),
        "validation_scope": validation_scope,
        "closure_modules": list(closure),
        "fast_module_count": 0,
        "fast_module_policy": "production native closure excludes CertifiedJLFast",
        "dependencies": list(dependencies),
        "build_inputs": build_inputs,
        "execution": execution,
        "incremental_cache": incremental_cache,
        "transformed_files": [asdict(record) for record in transformed],
        "replacement_count": sum(len(record.replacements) for record in transformed),
        "excluded_replay_sites": list(excluded_sites),
        "excluded_replay_site_count": len(excluded_sites),
        "native_axiom_policy": "all direct native_decide axioms are safe and theorem-owned; whole declarations produce one exact theorem-proposition axiom, while composite proofs record every generated subgoal axiom",
        "production_sources_modified": False,
    }
    return seal_manifest(payload)


def transformed_declarations(
    transformed: tuple[TransformedFile, ...]
) -> tuple[dict[str, object], ...]:
    declarations: dict[str, dict[str, object]] = {}
    for record in transformed:
        for replacement in record.replacements:
            prior = declarations.setdefault(
                replacement.declaration,
                {
                    "declaration": replacement.declaration,
                    "type_source_sha256": replacement.declaration_type_source_sha256,
                    "category": replacement.category,
                    "transformed_site_count": 0,
                },
            )
            if (
                prior["type_source_sha256"]
                != replacement.declaration_type_source_sha256
                or prior["category"] != replacement.category
            ):
                raise NativeReplayError(
                    f"inconsistent declaration census for {replacement.declaration}"
                )
            prior["transformed_site_count"] = int(prior["transformed_site_count"]) + 1
    return tuple(declarations[name] for name in sorted(declarations))


def render_axiom_audit(
    roots: tuple[str, ...], declarations: tuple[dict[str, object], ...]
) -> str:
    imports = "\n".join(f"import {root}" for root in roots)
    header = f'''{imports}
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command
'''
    blocks: list[str] = []
    for start in range(0, len(declarations), AUDIT_TARGETS_PER_BLOCK):
        shard = declarations[start:start + AUDIT_TARGETS_PER_BLOCK]
        targets = ",\n    ".join(
            f"(``{record['declaration']}, \"{record['type_source_sha256']}\", "
            f"{record['transformed_site_count']}, \"{record['category']}\")"
            for record in shard
        )
        blocks.append(f'''

run_cmd do
  let targets : List (Name × String × Nat × String) := [
    {targets}
  ]
  for (target, sourceTypeSHA256, transformedSiteCount, category) in targets do
    let env ← getEnv
    let some info := env.find? target
      | throwError "missing transformed declaration {{target}}"
    match info with
    | .thmInfo _ => pure ()
    | _ => throwError "transformed declaration is not a theorem: {{target}}"
    let axioms := (← Lean.collectAxioms target).qsort
      (fun left right => left.toString < right.toString)
    let standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    let nativeAxioms := axioms.filter fun name => !standardAxioms.contains name
    let ownedPrefix := target.toString ++ "._native.native_decide.ax_"
    let directAxioms := nativeAxioms.filter fun name =>
      name.toString.startsWith ownedPrefix
    if category == "whole-declaration" then
      unless transformedSiteCount == 1 && directAxioms.size == 1 do
        throwError "whole-declaration replay did not produce exactly one direct native axiom for {{target}}"
    else if category == "composite-proof" then
      unless 0 < directAxioms.size do
        throwError "composite replay produced no direct native axioms for {{target}}"
    else
      throwError "unknown native transformation category for {{target}}: {{category}}"
    for axiomName in nativeAxioms do
      logInfo m!"CERTIFIEDJL_NATIVE_DEPENDENCY|{{target}}|{{axiomName}}"
    for axiomName in directAxioms do
      let some axiomInfo := env.find? axiomName
        | throwError "missing generated native axiom {{axiomName}}"
      let .axiomInfo axiomValue := axiomInfo
        | throwError "generated native dependency is not an axiom: {{axiomName}}"
      unless axiomValue.isUnsafe == false do
        throwError "generated native axiom is unsafe: {{axiomName}}"
      let .app (.app (.app (.const eqName _) boolType) decided) rhs := axiomValue.type
        | throwError "generated native axiom is not a Boolean equality: {{axiomName}}"
      unless eqName == ``Eq && boolType.isConstOf ``Bool && rhs.isConstOf ``Bool.true do
        throwError "generated native axiom has the wrong Boolean equality shape: {{axiomName}}"
      let .app (.app (.const decideName _) proposition) _instance := decided
        | throwError "generated native axiom left side is not decide: {{axiomName}}"
      unless decideName == ``decide do
        throwError "generated native axiom left side uses the wrong decision function: {{axiomName}}"
      if category == "whole-declaration" then
        unless proposition == info.type do
          throwError "whole-declaration native axiom does not decide theorem type: {{axiomName}}"
      logInfo m!"CERTIFIEDJL_NATIVE_CENSUS|{{target}}|{{category}}|{{transformedSiteCount}}|{{directAxioms.size}}|{{hash info.type}}|{{sourceTypeSHA256}}|{{axiomName}}|{{hash axiomValue.type}}|{{hash proposition}}"
''')
    return header + "".join(blocks)


def run_axiom_audit(
    shadow: Path,
    roots: tuple[str, ...],
    declarations: tuple[dict[str, object], ...],
    output_path: Path,
) -> tuple[int, float, str, tuple[dict[str, object], ...]]:
    audit_source = shadow / "CertifiedJLNativeReplayAudit.lean"
    audit_source.write_text(render_axiom_audit(roots, declarations), encoding="utf-8")
    command = ["lake", "env", "lean", audit_source.name]
    started = time.monotonic()
    result = subprocess.run(
        command,
        cwd=shadow,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    elapsed = time.monotonic() - started
    output_path.write_text(result.stdout, encoding="utf-8")
    sys.stdout.write(result.stdout)
    census: list[dict[str, object]] = []
    dependency_census: dict[str, list[str]] = {}
    if result.returncode == 0:
        expected = {record["declaration"]: record for record in declarations}
        for line in result.stdout.splitlines():
            dependency_marker = "CERTIFIEDJL_NATIVE_DEPENDENCY|"
            if dependency_marker in line:
                payload = line[line.index(dependency_marker):].split("|")
                if len(payload) != 3:
                    raise NativeReplayError(
                        f"malformed native dependency line: {line}"
                    )
                _tag, declaration, axiom_name = payload
                if declaration not in expected:
                    raise NativeReplayError(
                        f"dependency census reported an unowned declaration: {declaration}"
                    )
                dependency_census.setdefault(declaration, []).append(axiom_name)
                continue
            marker = "CERTIFIEDJL_NATIVE_CENSUS|"
            if marker not in line:
                continue
            payload = line[line.index(marker):].split("|")
            if len(payload) != 10:
                raise NativeReplayError(f"malformed native census line: {line}")
            (
                _tag,
                declaration,
                category,
                transformed_site_count,
                direct_axiom_count,
                type_hash,
                source_type_sha256,
                axiom_name,
                axiom_type_hash,
                proposition_hash,
            ) = payload
            if declaration not in expected:
                raise NativeReplayError(
                    f"axiom census reported an unowned declaration: {declaration}"
                )
            if source_type_sha256 != expected[declaration]["type_source_sha256"]:
                raise NativeReplayError(
                    f"axiom census type-source mismatch for {declaration}"
                )
            owned_prefix = declaration + "._native.native_decide.ax_"
            if (
                category != expected[declaration]["category"]
                or transformed_site_count
                != str(expected[declaration]["transformed_site_count"])
                or not direct_axiom_count.isdigit()
                or not type_hash.isdigit()
                or not axiom_type_hash.isdigit()
                or not proposition_hash.isdigit()
                or not axiom_name.startswith(owned_prefix)
            ):
                raise NativeReplayError(
                    f"unexpected exact census payload for {declaration}: "
                    f"type={type_hash}, axiom={axiom_name}, "
                    f"axiom_type={axiom_type_hash}"
                )
            census.append(
                {
                    "declaration": declaration,
                    "category": category,
                    "transformed_site_count": int(transformed_site_count),
                    "direct_axiom_count": int(direct_axiom_count),
                    "native_type_hash": type_hash,
                    "type_source_sha256": source_type_sha256,
                    "axiom": axiom_name,
                    "axiom_type_hash": axiom_type_hash,
                    "native_proposition_hash": proposition_hash,
                }
            )
        for declaration, record in expected.items():
            owned = [item for item in census if item["declaration"] == declaration]
            category = record["category"]
            source_sites = int(record["transformed_site_count"])
            if (
                (category == "whole-declaration" and len(owned) != 1)
                or (
                    category == "composite-proof"
                    and not owned
                )
                or category not in {"whole-declaration", "composite-proof"}
                or any(item["direct_axiom_count"] != len(owned) for item in owned)
            ):
                raise NativeReplayError(
                    f"native census count mismatch for {declaration}: "
                    f"source_sites={source_sites}, direct_axioms={len(owned)}"
                )
        known_axioms = {str(item["axiom"]) for item in census}
        if set(dependency_census) != set(expected):
            raise NativeReplayError("native dependency census is incomplete")
        for declaration, dependencies in dependency_census.items():
            if dependencies != sorted(set(dependencies)):
                raise NativeReplayError(
                    f"native dependency census is not unique and deterministic for {declaration}"
                )
            if not set(dependencies) <= known_axioms:
                raise NativeReplayError(
                    f"native dependency census contains an unregistered axiom for {declaration}"
                )
        for item in census:
            item["collect_axioms"] = dependency_census[str(item["declaration"])]
    return (
        result.returncode,
        elapsed,
        sha256(result.stdout.encode("utf-8")),
        tuple(sorted(census, key=lambda record: str(record["declaration"]))),
    )


def write_provenance(
    path: Path,
    *,
    manifest: dict[str, object],
    declarations: tuple[dict[str, object], ...],
    build_status: int,
    build_elapsed: float,
    audit_status: int,
    audit_elapsed: float,
    audit_output_sha256: str,
    axiom_census: tuple[dict[str, object], ...],
    execution: dict[str, object],
) -> dict[str, object]:
    payload: dict[str, object] = {
        "schema_version": 2,
        "mode": "native-shadow-replay-provenance",
        "attests_execution": True,
        "source_inputs_sha256": manifest["source_inputs_sha256"],
        "transformation_manifest_sha256": manifest["manifest_sha256"],
        "source_commit": manifest["source_commit"],
        "roots": manifest["roots"],
        "build_roots": manifest["build_roots"],
        "build_command": manifest["build_command"],
        "axiom_audit_command": manifest["axiom_audit_command"],
        "assembly_roots": manifest["assembly_roots"],
        "validation_scope": manifest["validation_scope"],
        "dependencies": manifest["dependencies"],
        "declarations": list(declarations),
        "collect_axioms_policy": "exact safe theorem-owned direct-axiom census; one theorem-proposition axiom for whole declarations and a nonempty independent subgoal census for composite proofs",
        "build_status": build_status,
        "build_elapsed_seconds": round(build_elapsed, 3),
        "axiom_audit_status": audit_status,
        "axiom_audit_elapsed_seconds": round(audit_elapsed, 3),
        "axiom_audit_output_sha256": audit_output_sha256,
        "axiom_census": list(axiom_census),
        "execution": execution,
        "build_inputs_digest": manifest["build_inputs"]["digest"],
        "incremental_cache": manifest["incremental_cache"],
    }
    sealed = seal_document(payload, "provenance")
    write_document(path, sealed, "provenance")
    return sealed


def run_build(shadow: Path, build_roots: tuple[str, ...]) -> tuple[int, float]:
    command = ["lake", "build", *build_roots]
    print("native shadow:", shadow)
    print("native command:", shlex.join(command))
    started = time.monotonic()
    result = subprocess.run(command, cwd=shadow)
    return result.returncode, time.monotonic() - started


def current_source_inputs() -> dict[str, object]:
    identity = compute_identity(mode="native")
    try:
        validate_identity_document(identity)
    except ValueError as error:
        raise NativeReplayError(f"invalid native source-input identity: {error}") from error
    return seal_document(identity, "source-inputs")


def validate_source_inputs_against_checkout(document: dict[str, object]) -> None:
    verify_document(document, "source-inputs")
    try:
        validate_identity_document(document)
    except ValueError as error:
        raise NativeReplayError(f"invalid native source-input identity: {error}") from error
    current = compute_identity(mode="native")
    for key, value in current.items():
        if document.get(key) != value:
            raise NativeReplayError(
                f"native source-input identity differs from checkout at {key}"
            )


def validate_completed_document_chain(
    *,
    source_inputs: dict[str, object],
    manifest: dict[str, object],
    provenance: dict[str, object],
    audit: dict[str, object],
    census_sha256: str,
    receipt: dict[str, object] | None = None,
) -> None:
    try:
        validate_identity_document(source_inputs)
    except ValueError as error:
        raise NativeReplayError(f"source-input identity is invalid: {error}") from error
    if source_inputs.get("mode") != "native":
        raise NativeReplayError("native replay source-input identity has the wrong mode")
    for label, document in (("manifest", manifest), ("provenance", provenance),
                            ("audit", audit)):
        validate_github_source_commit(document.get("execution"),
                                      source_inputs.get("source_commit"), label)
    if receipt is not None:
        validate_github_source_commit(receipt.get("execution"),
                                      source_inputs.get("source_commit"), "receipt")
    identities = (
        (manifest, 2, "native-shadow-replay"),
        (provenance, 2, "native-shadow-replay-provenance"),
        (audit, 2, "native-shadow-replay-independent-audit"),
    )
    if any(document.get("schema_version") != schema or document.get("mode") != mode
           for document, schema, mode in identities):
        raise NativeReplayError("completed native documents have unsupported schema or mode")
    if (
        manifest.get("attests_execution") is not False
        or provenance.get("attests_execution") is not True
        or provenance.get("build_status") != 0
        or provenance.get("axiom_audit_status") != 0
        or audit.get("success") is not True
        or audit.get("attests_execution") is not True
        or manifest.get("source_inputs_sha256") != source_inputs.get("source_inputs_sha256")
        or provenance.get("source_inputs_sha256") != source_inputs.get("source_inputs_sha256")
        or provenance.get("transformation_manifest_sha256") != manifest.get("manifest_sha256")
        or audit.get("source_inputs_sha256") != source_inputs.get("source_inputs_sha256")
        or audit.get("manifest_sha256") != manifest.get("manifest_sha256")
        or audit.get("provenance_sha256") != provenance.get("provenance_sha256")
        or audit.get("axiom_census_sha256") != census_sha256
        or audit.get("build_inputs_digest") != manifest.get("build_inputs", {}).get("digest")
        or manifest.get("source_commit") != source_inputs.get("source_commit")
        or provenance.get("source_commit") != source_inputs.get("source_commit")
        or audit.get("source_commit") != source_inputs.get("source_commit")
        or audit.get("validation_digest") != source_inputs.get("validation_digest")
        or provenance.get("validation_scope") != manifest.get("validation_scope")
        or audit.get("validation_scope") != manifest.get("validation_scope")
        or provenance.get("incremental_cache") != manifest.get("incremental_cache")
        or audit.get("attests_full_production_replay")
        is not (manifest.get("validation_scope") == "attesting")
    ):
        raise NativeReplayError("completed native replay documents do not cross-bind")
    if receipt is not None and (
        receipt.get("schema_version") != 2
        or receipt.get("mode") != "native-shadow-replay-receipt"
        or receipt.get("success") is not True
        or receipt.get("attests_execution") is not True
        or receipt.get("source_inputs_sha256") != source_inputs.get("source_inputs_sha256")
        or receipt.get("manifest_sha256") != manifest.get("manifest_sha256")
        or receipt.get("provenance_sha256") != provenance.get("provenance_sha256")
        or receipt.get("audit_sha256") != audit.get("audit_sha256")
        or receipt.get("axiom_census_sha256") != census_sha256
        or receipt.get("build_inputs_digest") != manifest.get("build_inputs", {}).get("digest")
        or receipt.get("source_commit") != source_inputs.get("source_commit")
        or receipt.get("validation_digest") != source_inputs.get("validation_digest")
        or receipt.get("validation_scope") != manifest.get("validation_scope")
        or receipt.get("incremental_cache") != manifest.get("incremental_cache")
        or receipt.get("attests_full_production_replay")
        is not (manifest.get("validation_scope") == "attesting")
    ):
        raise NativeReplayError("native replay receipt does not bind completed evidence")


def _verify_prior_completed_runtime(
    prior: Path, expected_build_inputs: dict[str, object]
) -> dict[str, object]:
    source_inputs = read_document(prior / "native-replay-source-inputs.json", "source-inputs")
    try:
        validate_identity_document(source_inputs)
    except ValueError as error:
        raise NativeReplayError(f"prior source-input identity is invalid: {error}") from error
    manifest = read_document(prior / "native-replay-manifest.json", "manifest")
    provenance = read_document(prior / "native-replay-provenance.json", "provenance")
    audit = read_document(prior / "native-replay-audit.json", "audit")
    receipt = read_document(prior / "native-replay-receipt.json", "receipt")
    census_path = prior / "native-replay-axiom-census.txt"
    if not census_path.is_file():
        raise NativeReplayError("prior completed runtime has no axiom census")
    validate_completed_document_chain(
        source_inputs=source_inputs,
        manifest=manifest,
        provenance=provenance,
        audit=audit,
        census_sha256=sha256(census_path.read_bytes()),
        receipt=receipt,
    )
    prior_build_inputs = manifest.get("build_inputs")
    if (
        not isinstance(prior_build_inputs, dict)
        or prior_build_inputs.get("digest") != expected_build_inputs.get("digest")
        or prior_build_inputs != expected_build_inputs
    ):
        raise NativeReplayError("prior native build inputs differ from current transformed closure")
    prior_shadow = prior / "shadow-tree"
    for record in prior_build_inputs.get("module_inputs", []):
        path = prior_shadow / str(record["path"])
        if not path.is_file() or sha256(path.read_bytes()) != record.get("sha256"):
            raise NativeReplayError(f"prior cached module input differs: {record.get('path')}")
    for record in prior_build_inputs.get("configuration_inputs", []):
        path = prior_shadow / str(record["path"])
        if not path.is_file() or sha256(path.read_bytes()) != record.get("sha256"):
            raise NativeReplayError(f"prior cached build configuration differs: {record.get('path')}")
    build = prior_shadow / ".lake" / "build"
    if build.is_symlink() or not build.is_dir():
        raise NativeReplayError("prior completed runtime has no native build cache")
    linked = next((path for path in build.rglob("*") if path.is_symlink()), None)
    if linked is not None:
        raise NativeReplayError(
            f"prior native build cache contains a symlink: {linked.relative_to(build)}"
        )
    return receipt


def seed_incremental_cache(
    prior: Path, shadow: Path, expected_build_inputs: dict[str, object]
) -> dict[str, object]:
    receipt = _verify_prior_completed_runtime(prior.resolve(), expected_build_inputs)
    source = prior.resolve() / "shadow-tree" / ".lake" / "build"
    target = shadow / ".lake" / "build"
    if target.exists() or target.is_symlink():
        raise NativeReplayError("new native shadow already contains a project build cache")
    source_resolved = source.resolve()
    target_resolved = target.resolve()
    if (
        source_resolved == target_resolved
        or source_resolved in target_resolved.parents
        or target_resolved in source_resolved.parents
    ):
        raise NativeReplayError("incremental cache source and target overlap")
    copy_strategy = "independent-copy"
    command: list[str] | None = None
    if platform.system() == "Darwin":
        command = ["cp", "-cR", str(source), str(target)]
        copy_strategy = "apfs-copy-on-write"
    elif platform.system() == "Linux":
        command = ["cp", "-a", "--reflink=auto", str(source), str(target)]
        copy_strategy = "reflink-or-independent-copy"
    if command is not None:
        result = subprocess.run(
            command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True
        )
        if result.returncode != 0:
            shutil.rmtree(target, ignore_errors=True)
            shutil.copytree(source, target, copy_function=shutil.copy2, symlinks=True)
            copy_strategy = "independent-copy-fallback"
    else:
        shutil.copytree(source, target, copy_function=shutil.copy2, symlinks=True)
    if target.is_symlink() or not target.is_dir():
        raise NativeReplayError("incremental project-cache copy did not produce a build tree")
    linked = next((path for path in target.rglob("*") if path.is_symlink()), None)
    if linked is not None:
        raise NativeReplayError("incremental project-cache copy retained a symlink")
    return {
        "used": True,
        "trust": "incremental-input-only; fresh lake build and independent audit required",
        "prior_receipt_sha256": receipt["receipt_sha256"],
        "prior_build_inputs_digest": expected_build_inputs["digest"],
        "copy_strategy": copy_strategy,
    }


def finalize_receipt(runtime: Path) -> Path:
    runtime = runtime.resolve()
    receipt_path = runtime / "native-replay-receipt.json"
    if receipt_path.exists() or receipt_path.is_symlink():
        raise NativeReplayError("native replay receipt already exists")
    source_inputs = read_document(runtime / "native-replay-source-inputs.json", "source-inputs")
    validate_source_inputs_against_checkout(source_inputs)
    manifest = read_document(runtime / "native-replay-manifest.json", "manifest")
    provenance = read_document(runtime / "native-replay-provenance.json", "provenance")
    audit = read_document(runtime / "native-replay-audit.json", "audit")
    census_path = runtime / "native-replay-axiom-census.txt"
    census_sha256 = sha256(census_path.read_bytes())
    validate_execution_against_current(
        audit.get("execution"), "audit", "audit_native_replay.py"
    )
    validate_github_source_commit(
        audit.get("execution"), source_inputs.get("source_commit"), "audit"
    )
    shadow = runtime / "shadow-tree"
    paths = tracked_files(ROOT)
    dependencies = verified_dependencies(ROOT)
    source_packages = ROOT / ".lake" / "packages"
    shadow_packages = shadow / ".lake" / "packages"
    dependency_links_ok = shadow_packages.is_dir() and (
        sorted(path.name for path in shadow_packages.iterdir())
        == sorted(str(record["name"]) for record in dependencies)
    )
    for record in dependencies:
        name = str(record["name"])
        link = shadow_packages / name
        dependency_links_ok = dependency_links_ok and link.is_symlink()
        if link.is_symlink():
            dependency_links_ok = dependency_links_ok and (
                link.resolve() == (source_packages / name).resolve()
            )
    shadow_paths = tuple(shadow / path.relative_to(ROOT) for path in paths)
    build_roots = tuple(map(str, manifest.get("build_roots", [])))
    closure = tuple(map(str, manifest.get("closure_modules", [])))
    final_build_inputs = build_input_identity(shadow, closure, build_roots, dependencies)
    validate_completed_document_chain(
        source_inputs=source_inputs,
        manifest=manifest,
        provenance=provenance,
        audit=audit,
        census_sha256=census_sha256,
    )
    if (
        manifest.get("source_tree_sha256") != tree_digest(ROOT, paths)
        or manifest.get("shadow_tree_sha256_after_transform") != tree_digest(shadow, shadow_paths)
        or manifest.get("dependencies") != list(dependencies)
        or not dependency_links_ok
        or manifest.get("build_inputs") != final_build_inputs
        or audit.get("build_inputs_digest") != final_build_inputs.get("digest")
    ):
        raise NativeReplayError("successful native replay evidence does not cross-bind")
    payload: dict[str, object] = {
        "schema_version": 2,
        "mode": "native-shadow-replay-receipt",
        "validation_scope": manifest["validation_scope"],
        "attests_full_production_replay": manifest["validation_scope"] == "attesting",
        "attests_execution": True,
        "success": True,
        "source_inputs_sha256": source_inputs["source_inputs_sha256"],
        "manifest_sha256": manifest["manifest_sha256"],
        "provenance_sha256": provenance["provenance_sha256"],
        "audit_sha256": audit["audit_sha256"],
        "axiom_census_sha256": census_sha256,
        "source_commit": source_inputs["source_commit"],
        "validation_digest": source_inputs["validation_digest"],
        "build_inputs_digest": manifest["build_inputs"]["digest"],
        "incremental_cache": manifest["incremental_cache"],
        "execution": execution_environment([sys.executable, *sys.argv]),
        "self_hash_is_signature": False,
    }
    receipt = seal_document(payload, "receipt")
    write_document_exclusive(receipt_path, receipt, "receipt")
    return receipt_path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--catalog", type=Path, default=DEFAULT_CATALOG)
    parser.add_argument("--family-id", action="append", default=[])
    parser.add_argument("--all-catalog-families", action="store_true")
    parser.add_argument("--root", action="append", default=[])
    parser.add_argument(
        "--allow-dirty", action="store_true",
        help="legacy flag retained for CLI compatibility; schema-v2 runs remain clean-only",
    )
    parser.add_argument("--plan-only", action="store_true")
    parser.add_argument("--runtime-dir", type=Path)
    parser.add_argument(
        "--reuse-from", type=Path,
        help="seed a fresh run from a completed schema-v2 runtime with identical build inputs",
    )
    parser.add_argument("--finalize-receipt", action="store_true", help=argparse.SUPPRESS)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.finalize_receipt:
        if args.reuse_from or args.plan_only or args.root or args.family_id or args.all_catalog_families:
            raise NativeReplayError("receipt finalization does not accept replay selection options")
        configured = args.runtime_dir or (
            Path(value) if (value := os.environ.get("CERTIFIEDJL_NATIVE_BUILD_DIR")) else None
        )
        if configured is None:
            raise NativeReplayError("receipt finalization requires --runtime-dir")
        print(f"native replay receipt written: {finalize_receipt(configured)}")
        return
    root = ROOT.resolve()
    catalog = args.catalog.resolve() if args.catalog else None
    direct_roots = tuple(args.root)
    for module in direct_roots:
        if MODULE.fullmatch(module) is None:
            raise NativeReplayError(f"invalid direct replay root: {module!r}")
    validate_selection_options(
        direct_roots, tuple(args.family_id), args.all_catalog_families
    )
    family_ids: tuple[str, ...] = ()
    certificate_ids: tuple[str, ...] = ()
    catalog_roots: tuple[str, ...] = ()
    select_all = args.all_catalog_families or (not args.family_id and not direct_roots)
    if args.family_id or select_all:
        if catalog is None or not catalog.is_file():
            raise NativeReplayError("selected catalog does not exist")
        if select_all:
            validate_attesting_catalog(catalog)
        family_ids, certificate_ids, catalog_roots = roots_from_catalog(
            catalog, tuple(args.family_id), select_all
        )
    roots = tuple(sorted(set(direct_roots) | set(catalog_roots)))
    if not roots:
        raise NativeReplayError("no replay roots selected")
    build_roots, assembly_roots = replay_build_roots(roots, select_all)
    validation_scope = "attesting" if select_all else "diagnostic-partial"

    status_before = git_status(root)
    if status_before:
        raise NativeReplayError("schema-v2 native replay requires a clean source worktree")
    source_inputs = current_source_inputs()
    paths = tracked_files(root)
    source_tree_sha256 = tree_digest(root, paths)
    dependencies = verified_dependencies(root)
    graph = import_graph(root, paths)
    closure = import_closure(graph, build_roots)
    validate_production_closure(closure)

    configured_runtime = (
        args.runtime_dir
        or (Path(value) if (value := os.environ.get("CERTIFIEDJL_NATIVE_BUILD_DIR")) else None)
        or (Path(value) if (value := os.environ.get("CERTIFIEDJL_NATIVE_SHADOW_DIR")) else None)
    )
    runtime = (
        configured_runtime.resolve()
        if configured_runtime
        else Path(tempfile.mkdtemp(prefix="certifiedjl-native-replay-")).resolve()
    )
    if runtime == root or root in runtime.parents:
        raise NativeReplayError("native runtime directory must be outside the source checkout")
    if runtime.exists() and any(runtime.iterdir()):
        raise NativeReplayError(f"native runtime directory is not empty: {runtime}")
    runtime.mkdir(parents=True, exist_ok=True)
    shadow_base = Path(os.environ.get("CERTIFIEDJL_NATIVE_SHADOW_DIR", runtime)).resolve()
    if shadow_base == root or root in shadow_base.parents:
        raise NativeReplayError("native shadow directory must be outside the source checkout")
    if shadow_base != runtime:
        raise NativeReplayError(
            "CERTIFIEDJL_NATIVE_BUILD_DIR and CERTIFIEDJL_NATIVE_SHADOW_DIR "
            "must resolve to the same isolated runtime"
        )
    shadow_base.mkdir(parents=True, exist_ok=True)
    shadow = shadow_base / "shadow-tree"
    if shadow.exists():
        raise NativeReplayError(f"native shadow tree already exists: {shadow}")
    shadow.mkdir(parents=True)
    manifest_path = runtime / "native-replay-manifest.json"
    provenance_path = runtime / "native-replay-provenance.json"
    audit_output_path = runtime / "native-replay-axiom-census.txt"
    source_inputs_path = runtime / "native-replay-source-inputs.json"
    try:
        write_document(source_inputs_path, source_inputs, "source-inputs")
        copied_digest = copy_tracked_tree(root, shadow, paths)
        if copied_digest != source_tree_sha256:
            raise NativeReplayError("shadow copy differs before transformation")
        transformed, excluded_sites = transform_closure(root, shadow, closure)
        if not transformed:
            raise NativeReplayError("selected closure has no kernel replay sites")
        shadow_paths = tuple(shadow / path.relative_to(root) for path in paths)
        transformed_tree_digest = tree_digest(shadow, shadow_paths)
        build_inputs = build_input_identity(shadow, closure, build_roots, dependencies)
        incremental_cache: dict[str, object] = {
            "used": False,
            "trust": "no incremental project cache supplied",
            "prior_receipt_sha256": None,
            "prior_build_inputs_digest": None,
            "copy_strategy": None,
        }
        if args.reuse_from:
            if args.plan_only:
                raise NativeReplayError("--reuse-from cannot be combined with --plan-only")
            incremental_cache = seed_incremental_cache(
                args.reuse_from.resolve(), shadow, build_inputs
            )
        execution = execution_environment([sys.executable, *sys.argv])
        manifest = build_manifest(
            root=root,
            catalog=catalog if family_ids else None,
            family_ids=family_ids,
            certificate_ids=certificate_ids,
            roots=roots,
            build_roots=build_roots,
            assembly_roots=assembly_roots,
            validation_scope=validation_scope,
            closure=closure,
            transformed=transformed,
            excluded_sites=excluded_sites,
            source_tree_sha256=source_tree_sha256,
            shadow_tree_sha256_before_transform=copied_digest,
            shadow_tree_sha256_after_transform=transformed_tree_digest,
            dependencies=dependencies,
            source_status=status_before,
            source_inputs=source_inputs,
            build_inputs=build_inputs,
            execution=execution,
            incremental_cache=incremental_cache,
        )
        declarations = transformed_declarations(transformed)
        manifest = seal_manifest(
            {
                **{key: value for key, value in manifest.items() if key != "manifest_sha256"},
                "transformed_declarations": list(declarations),
            }
        )
        write_manifest(manifest_path, manifest)
        print(
            f"native plan: {len(build_roots)} build roots, "
            f"{len(closure)} repository modules, "
            f"{len(transformed)} transformed files, "
            f"{manifest['replacement_count']} native sites, "
            f"{manifest['excluded_replay_site_count']} preserved private sites"
        )
        if args.plan_only:
            status_after = git_status(root)
            if (
                status_after != status_before
                or tree_digest(root, paths) != source_tree_sha256
                or verified_dependencies(root) != dependencies
            ):
                raise NativeReplayError("production worktree changed during shadow planning")
            print(f"native replay planned: manifest={manifest_path}, runtime={runtime}")
            return
        returncode, elapsed = run_build(shadow, build_roots)
        audit_status = 125
        audit_elapsed = 0.0
        audit_output_sha256 = sha256(b"")
        axiom_census: tuple[dict[str, object], ...] = ()
        if returncode == 0:
            (
                audit_status,
                audit_elapsed,
                audit_output_sha256,
                axiom_census,
            ) = run_axiom_audit(
                shadow, build_roots, declarations, audit_output_path
            )
        write_provenance(
            provenance_path,
            manifest=manifest,
            declarations=declarations,
            build_status=returncode,
            build_elapsed=elapsed,
            audit_status=audit_status,
            audit_elapsed=audit_elapsed,
            audit_output_sha256=audit_output_sha256,
            axiom_census=axiom_census,
            execution=execution_environment([sys.executable, *sys.argv]),
        )
        status_after = git_status(root)
        if (
            status_after != status_before
            or tree_digest(root, paths) != source_tree_sha256
            or verified_dependencies(root) != dependencies
        ):
            raise NativeReplayError("production worktree changed during shadow replay")
        print(
            "native replay finished: "
            f"build_status={returncode}, audit_status={audit_status}, "
            f"elapsed={elapsed:.2f}s, runtime={runtime}"
        )
        if returncode or audit_status:
            raise SystemExit(returncode or audit_status)
    finally:
        pass


if __name__ == "__main__":
    try:
        main()
    except NativeReplayError as error:
        raise SystemExit(f"native shadow replay error: {error}") from error
