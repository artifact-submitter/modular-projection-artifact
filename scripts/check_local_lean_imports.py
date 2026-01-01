#!/usr/bin/env python3
"""Reject dangling project imports, including in opt-in and generated modules."""

from check_fast_import_boundary import graph


def main() -> None:
    imports = graph()
    missing = sorted(
        (source, target)
        for source, targets in imports.items()
        for target in targets
        if (target == "CertifiedJL" or target.startswith("CertifiedJL.")
            or target == "CertifiedJLFast" or target.startswith("CertifiedJLFast."))
        and target not in imports
    )
    if missing:
        raise SystemExit("dangling local Lean imports:\n" + "\n".join(
            f"{source} -> {target}" for source, target in missing))
    print(f"local Lean imports verified: {len(imports)} modules, no dangling references")


if __name__ == "__main__":
    main()
