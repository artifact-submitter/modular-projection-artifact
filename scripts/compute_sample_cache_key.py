#!/usr/bin/env python3
"""Compute a cache digest for the selected bounded certificate samples."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import sys

from certificate_catalog import ROOT
from compute_fast_cache_key import BUILD_CONFIGURATION, add_file, closure
from sample_selection import current_snapshot, select_for_repository


CACHE_SCHEMA = b"CertifiedJL-certificate-sample-cache-v1\0"


def sample_cache_inputs(
    modules: tuple[str, ...], snapshot, root: Path = ROOT
) -> set[Path]:
    reached = closure(snapshot.graph, list(modules))
    sources = {
        root / snapshot.module_paths[module]
        for module in reached if module in snapshot.module_paths
    }
    sources.update(root / relative for relative in BUILD_CONFIGURATION)
    return {path for path in sources if path.is_file()}


def sample_digest(modules: tuple[str, ...], sources: set[Path], root: Path = ROOT) -> str:
    digest = hashlib.sha256()
    digest.update(CACHE_SCHEMA)
    for module in modules:
        encoded = module.encode("utf-8")
        digest.update(len(encoded).to_bytes(8, "big"))
        digest.update(encoded)
    for path in sorted(sources):
        add_file(digest, path, root)
    return digest.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--base")
    args = parser.parse_args()
    snapshot = current_snapshot()
    selection = select_for_repository(args.base, current=snapshot)
    sources = sample_cache_inputs(selection.modules, snapshot)
    print(f"digest={sample_digest(selection.modules, sources)}")
    print(f"count={len(selection.modules)}")
    print(
        f"certificate sample selection: {len(selection.modules)} modules; "
        f"{selection.reason}; cache closure {len(sources)} files",
        file=sys.stderr,
    )


if __name__ == "__main__":
    main()
