#!/usr/bin/env python3
"""Check production/fast import separation using catalog replay roots."""

from __future__ import annotations

from collections import deque
from pathlib import Path

from certificate_catalog import ROOT, certificates
from fast_validation_roots import EXACT_ONLY_ROOTS, fast_validation_roots
from lean_source import imports_in_source


def module_name(source: Path) -> str:
    return ".".join(source.relative_to(ROOT).with_suffix("").parts)


def graph() -> dict[str, tuple[str, ...]]:
    answer: dict[str, tuple[str, ...]] = {}
    for source in ROOT.rglob("*.lean"):
        if ".lake" in source.parts:
            continue
        answer[module_name(source)] = imports_in_source(
            source.read_text(encoding="utf-8"), str(source.relative_to(ROOT))
        )
    return answer


def path_to_forbidden(graph: dict[str, tuple[str, ...]], root: str, forbidden: set[str]) -> list[str] | None:
    pending = deque([root])
    parent: dict[str, str | None] = {root: None}
    while pending:
        current = pending.popleft()
        if any(current == prefix or current.startswith(prefix + ".") for prefix in forbidden):
            path: list[str] = []
            cursor: str | None = current
            while cursor is not None:
                path.append(cursor)
                cursor = parent[cursor]
            return list(reversed(path))
        for imported in graph.get(current, ()):
            if imported not in parent:
                parent[imported] = current
                pending.append(imported)
    return None


def fast_replay_failures(
    imports: dict[str, tuple[str, ...]],
    roots: set[str],
    forbidden: set[str],
) -> list[list[str]]:
    failures: list[list[str]] = []
    for root in sorted(roots):
        path = path_to_forbidden(imports, root, forbidden)
        if path:
            failures.append(path)
    return failures


def main() -> None:
    imports = graph()
    production_forbidden = {"CertifiedJLFast"}
    fast_forbidden: set[str] = set()
    for entry in certificates():
        fast_forbidden.add(entry["verified_module"])
        fast_forbidden.update(entry.get("replay_roots", entry["generated_roots"]))
        fast_forbidden.update(entry["sample_modules"])
    fast_forbidden.update(EXACT_ONLY_ROOTS)

    failures: list[str] = []
    production_path = path_to_forbidden(imports, "CertifiedJL", production_forbidden)
    if production_path:
        failures.append("production imports fast code: " + " -> ".join(production_path))
    fast_roots = fast_validation_roots()
    for fast_path in fast_replay_failures(imports, fast_roots, fast_forbidden):
        failures.append(
            "fast validation imports exact replay: " + " -> ".join(fast_path)
        )
    if failures:
        raise SystemExit("import boundary error:\n" + "\n".join(failures))
    print(
        "import boundary verified: production excludes CertifiedJLFast; "
        f"{len(fast_roots)} fast roots exclude {len(fast_forbidden)} "
        "verified/replay roots"
    )


if __name__ == "__main__":
    main()
