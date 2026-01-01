#!/usr/bin/env python3
"""Require exact agreement between fast assumptions and the catalog."""

from __future__ import annotations

import re
from pathlib import Path

from certificate_catalog import ROOT, certificates, module_source, normalize_type
from lean_source import strip_lean_comments


DECL_RE = re.compile(
    r"^\s*(axiom|constant)\s+([A-Za-z_][A-Za-z0-9_']*)\s*:\s*(.*?)"
    r"(?=^\s*(?:axiom|constant)\s+|^\s*end\b)",
    re.MULTILINE | re.DOTALL,
)


def fail(message: str) -> None:
    raise SystemExit(f"fast assumption error: {message}")


def main() -> None:
    expected: dict[tuple[Path, str], str] = {}
    for entry in certificates():
        full = entry["fast_declaration"]
        leaf = full.rsplit(".", 1)[1]
        expected[(module_source(entry["fast_module"]), leaf)] = normalize_type(
            entry["fast_type"]
        )

    found: dict[tuple[Path, str], str] = {}
    assumption_root = ROOT / "CertifiedJLFast" / "Assumptions"
    for path in sorted(assumption_root.rglob("*.lean")):
        source = strip_lean_comments(path.read_text(encoding="utf-8"), str(path))
        for kind, name, declaration_type in DECL_RE.findall(source):
            if kind != "axiom":
                fail(f"constants are forbidden: {path.relative_to(ROOT)}:{name}")
            found[(path, name)] = normalize_type(declaration_type)
        for token in ("sorry", "admit", "unsafe", "native_decide"):
            if re.search(rf"\b{token}\b", source):
                fail(f"forbidden token {token} in {path.relative_to(ROOT)}")

    if found.keys() != expected.keys():
        missing = sorted(f"{p.relative_to(ROOT)}:{n}" for p, n in expected.keys() - found.keys())
        extra = sorted(f"{p.relative_to(ROOT)}:{n}" for p, n in found.keys() - expected.keys())
        fail(f"catalog mismatch; missing={missing}, extra={extra}")
    for key, expected_type in expected.items():
        if found[key] != expected_type:
            fail(
                f"type mismatch for {key[1]}: catalog={expected_type!r}, "
                f"source={found[key]!r}"
            )
    print(f"fast assumptions verified: {len(found)} exact cataloged axioms")


if __name__ == "__main__":
    main()
