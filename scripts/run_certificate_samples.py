#!/usr/bin/env python3
"""Build the deterministic bounded sample declared at each certificate boundary."""

from __future__ import annotations

import argparse
import subprocess

from certificate_catalog import ROOT
from sample_selection import select_for_repository


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--list", action="store_true", help="print samples without building")
    parser.add_argument("--base", help="select samples affected since this Git revision")
    args = parser.parse_args()
    selection = select_for_repository(args.base)
    print(
        f"certificate sample selection: {len(selection.modules)} modules; "
        f"{selection.reason}"
    )
    for module in selection.modules:
        print(module)
    if not args.list and selection.modules:
        subprocess.run(["lake", "build", *selection.modules], cwd=ROOT, check=True)
        print(f"bounded certificate samples passed: {len(selection.modules)} modules")
    elif not args.list:
        print("bounded certificate samples skipped: no affected sample dependency")


if __name__ == "__main__":
    main()
