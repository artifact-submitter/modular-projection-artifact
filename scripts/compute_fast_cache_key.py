#!/usr/bin/env python3
"""Compute a cache digest from the exact assumption-backed fast source closure."""

from __future__ import annotations

from collections import deque
import hashlib
from pathlib import Path
import sys

from certificate_catalog import ROOT, certificates
from fast_validation_roots import EXACT_ONLY_ROOTS, fast_validation_roots
from lean_source import imports_in_source


CACHE_SCHEMA = b"CertifiedJL-fast-build-cache-v3\0"
BUILD_CONFIGURATION = ("lean-toolchain", "lake-manifest.json", "lakefile.toml")


def module_name(source: Path) -> str:
    return ".".join(source.relative_to(ROOT).with_suffix("").parts)


def import_graph() -> dict[str, tuple[str, ...]]:
    graph: dict[str, tuple[str, ...]] = {}
    for source in ROOT.rglob("*.lean"):
        if ".lake" in source.parts:
            continue
        graph[module_name(source)] = imports_in_source(
            source.read_text(encoding="utf-8"), str(source.relative_to(ROOT))
        )
    return graph


def closure(graph: dict[str, tuple[str, ...]], roots: list[str]) -> set[str]:
    reached: set[str] = set()
    pending = deque(roots)
    while pending:
        module = pending.popleft()
        if module in reached:
            continue
        reached.add(module)
        pending.extend(graph.get(module, ()))
    return reached


def leaked_modules(modules: set[str], forbidden: set[str]) -> list[str]:
    return sorted(
        module for module in modules
        if any(
            module == root or module.startswith(root + ".")
            for root in forbidden
        )
    )


def add_file(digest: "hashlib._Hash", path: Path, root: Path = ROOT) -> None:
    relative = path.relative_to(root).as_posix().encode()
    payload = path.read_bytes()
    digest.update(len(relative).to_bytes(8, "big"))
    digest.update(relative)
    digest.update(len(payload).to_bytes(8, "big"))
    digest.update(payload)


def cache_inputs(
    graph: dict[str, tuple[str, ...]],
    entries: list[dict],
    fast_roots: set[str],
    root: Path = ROOT,
) -> tuple[set[Path], set[str]]:
    fast_modules = closure(graph, sorted(fast_roots))

    forbidden: set[str] = set()
    for entry in entries:
        forbidden.add(entry["verified_module"])
        forbidden.update(entry.get("replay_roots") or entry["generated_roots"])
        forbidden.update(entry["sample_modules"])
    forbidden.update(EXACT_ONLY_ROOTS)
    leaked = leaked_modules(fast_modules, forbidden)
    if leaked:
        raise SystemExit("fast cache closure reaches replay roots: " + ", ".join(leaked))

    def source(module: str) -> Path:
        return root / (module.replace(".", "/") + ".lean")

    sources = {
        source(module)
        for module in fast_modules
        if source(module).is_file()
    }
    fixed_inputs = [root / relative for relative in BUILD_CONFIGURATION]
    sources.update(path for path in fixed_inputs if path.is_file())
    return sources, fast_modules


def input_digest(sources: set[Path], root: Path = ROOT) -> str:
    digest = hashlib.sha256()
    digest.update(CACHE_SCHEMA)
    for path in sorted(sources):
        add_file(digest, path, root)
    return digest.hexdigest()


def main() -> None:
    graph = import_graph()
    entries = certificates()
    sources, fast_modules = cache_inputs(
        graph, entries, fast_validation_roots()
    )

    print(f"digest={input_digest(sources)}")
    print(
        f"fast cache closure: {len(fast_modules)} modules, {len(sources)} files",
        file=sys.stderr,
    )


if __name__ == "__main__":
    main()
