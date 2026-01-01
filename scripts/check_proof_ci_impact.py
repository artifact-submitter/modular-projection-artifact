#!/usr/bin/env python3
"""Skip Lean development checks only for an explicitly manuscript-only diff."""

import argparse
from pathlib import Path

from check_paper_ci_impact import changed_paths


def affects_proofs(paths: list[str] | None) -> bool:
    if paths is None:
        return True
    return any(path.endswith(".lean") or path.startswith((
        "paper/artifact/", "paper/experiments/", "paper/generated/")) or not (
        path.startswith("paper/") or path.startswith("docs/")
        or path in {"README.md", "LICENSE"}) for path in paths)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--event", required=True)
    parser.add_argument("--base", default="")
    parser.add_argument("--head", required=True)
    args = parser.parse_args()
    paths = changed_paths(args.base, args.head, Path(__file__).resolve().parent.parent)
    required = args.event not in {"push", "pull_request"} or affects_proofs(paths)
    print(f"proof_changed={'true' if required else 'false'}")


if __name__ == "__main__":
    main()
