#!/usr/bin/env python3
"""Decide whether a workflow revision can affect the paper or its checks."""

from __future__ import annotations

import argparse
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parent.parent
ALWAYS_RUN_EVENTS = {"schedule", "workflow_dispatch"}
EXACT_INPUTS = {
    ".github/workflows/paper.yml",
    "Makefile",
    "evidence/result-catalog.toml",
    "scripts/generate_formalization_table.py",
}


def affects_paper(paths: list[str]) -> bool:
    return any(path.startswith("paper/") or path in EXACT_INPUTS for path in paths)


def changed_paths(base: str, head: str, root: Path = ROOT) -> list[str] | None:
    """Return the complete Git diff, or None when comparison must fail open."""
    if not base or set(base) == {"0"}:
        return None
    for revision in (base, head):
        result = subprocess.run(
            ["git", "cat-file", "-e", f"{revision}^{{commit}}"], cwd=root
        )
        if result.returncode != 0:
            return None
    payload = subprocess.run(
        ["git", "diff", "--name-only", "-z", base, head, "--"],
        cwd=root,
        check=True,
        stdout=subprocess.PIPE,
    ).stdout
    return [part.decode("utf-8") for part in payload.split(b"\0") if part]


def should_run(event: str, base: str, head: str, root: Path = ROOT) -> bool:
    if event in ALWAYS_RUN_EVENTS:
        return True
    if event not in {"push", "pull_request"}:
        return True
    paths = changed_paths(base, head, root)
    return paths is None or affects_paper(paths)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--event", required=True)
    parser.add_argument("--base", default="")
    parser.add_argument("--head", required=True)
    args = parser.parse_args()
    value = "true" if should_run(args.event, args.base, args.head) else "false"
    print(f"paper_changed={value}")


if __name__ == "__main__":
    main()
