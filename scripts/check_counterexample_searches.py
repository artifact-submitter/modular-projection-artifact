#!/usr/bin/env python3
"""Reproduce every retained counterexample search output exactly."""

from __future__ import annotations

from pathlib import Path
import sys

from counterexample_catalog import ROOT
from counterexample_probability import ProbabilityError
from search_counterexamples import SearchError, load_manifest, run_search, serialized


SEARCH_ROOT = ROOT / "evidence" / "counterexamples" / "searches"


def check() -> int:
    manifests = sorted(SEARCH_ROOT.glob("*.toml"))
    if not manifests:
        raise SearchError("no retained counterexample search manifests")
    outputs = {path.resolve() for path in SEARCH_ROOT.glob("*.json")}
    expected_outputs: set[Path] = set()
    for path in manifests:
        manifest, digest = load_manifest(path)
        output = (ROOT / manifest["output"]).resolve()
        if output in expected_outputs:
            raise SearchError(f"duplicate retained manifests target {output.relative_to(ROOT)}")
        expected_outputs.add(output)
        content = serialized(run_search(manifest, digest))
        if not output.is_file() or output.read_text(encoding="utf-8") != content:
            raise SearchError(f"retained search output is stale: {output.relative_to(ROOT)}")
    extras = sorted(outputs - expected_outputs)
    if extras:
        raise SearchError(
            "retained search outputs lack manifests: "
            + ", ".join(str(path.relative_to(ROOT)) for path in extras)
        )
    return len(manifests)


if __name__ == "__main__":
    try:
        count = check()
    except (SearchError, ProbabilityError) as error:
        print(f"counterexample search error: {error}", file=sys.stderr)
        raise SystemExit(1)
    print(f"Reproduced {count} retained counterexample search manifest(s).")
