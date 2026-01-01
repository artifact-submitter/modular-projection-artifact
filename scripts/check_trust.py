#!/usr/bin/env python3
"""Reject trust shortcuts; optionally admit exactly cataloged fast axioms."""

from __future__ import annotations

import argparse
import re
from pathlib import Path

from certificate_catalog import ROOT, certificates, module_source
from lean_source import strip_lean_comments


FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom_or_constant": re.compile(r"^\s*(?:axiom|constant)\s+([A-Za-z_][A-Za-z0-9_']*)\b", re.MULTILINE),
    "unsafe": re.compile(r"^\s*unsafe\b", re.MULTILINE),
    "native_decide": re.compile(r"\bnative_decide\b"),
}
def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--allow-cataloged-fast-assumptions", action="store_true")
    args = parser.parse_args()
    allowed: set[tuple[Path, str]] = set()
    if args.allow_cataloged_fast_assumptions:
        for entry in certificates():
            allowed.add((module_source(entry["fast_module"]), entry["fast_declaration"].rsplit(".", 1)[1]))

    files = sorted((ROOT / "CertifiedJL").rglob("*.lean"))
    files += sorted((ROOT / "Vendor").rglob("*.lean"))
    files.append(ROOT / "CertifiedJL.lean")
    if args.allow_cataloged_fast_assumptions:
        files += sorted((ROOT / "CertifiedJLFast").rglob("*.lean"))
        files.append(ROOT / "CertifiedJLFast.lean")

    failures: list[str] = []
    seen_allowed: set[tuple[Path, str]] = set()
    for path in files:
        source = strip_lean_comments(path.read_text(encoding="utf-8"), str(path))
        for label, pattern in FORBIDDEN.items():
            for match in pattern.finditer(source):
                if label == "axiom_or_constant":
                    key = (path, match.group(1))
                    if key in allowed:
                        seen_allowed.add(key)
                        continue
                line = source.count("\n", 0, match.start()) + 1
                failures.append(f"{path.relative_to(ROOT)}:{line}: {label}")
    if seen_allowed != allowed:
        missing = sorted(f"{p.relative_to(ROOT)}:{n}" for p, n in allowed - seen_allowed)
        failures.append(f"cataloged fast axioms not found: {missing}")
    if failures:
        raise SystemExit("forbidden trust shortcuts found:\n  " + "\n  ".join(failures))
    mode = "production plus cataloged fast" if args.allow_cataloged_fast_assumptions else "production"
    print(f"trust scan verified ({mode}): {len(files)} Lean files")


if __name__ == "__main__":
    main()
