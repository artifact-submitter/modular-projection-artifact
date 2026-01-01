#!/usr/bin/env python3
"""Generate a reviewer entry point from the repository's result catalogs."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import tomllib

ROOT = Path(__file__).resolve().parent.parent
NAME = re.compile(r"^[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)+$")


def entries(root: Path) -> list[dict[str, str]]:
    catalog = tomllib.loads((root / "evidence/result-catalog.toml").read_text())
    contract = tomllib.loads((root / "evidence/theorem-contract.toml").read_text())
    result = []
    for row in catalog["result"]:
        if row.get("verification_class") == "kernel_checked":
            result.append({"id": row["id"], "declaration": row["lean"],
                           "source": row["lean_owner"],
                           "paper_locator": row.get("paper_locator", "")})
    for row in contract.get("claim", []):
        if row.get("verification_class") == "kernel_checked" and row.get("lean"):
            result.append({"id": row["id"], "declaration": row["lean"],
                           "source": row["analytic_owner"],
                           "paper_locator": row.get("paper_locator", "")})
    for row in result:
        if not NAME.fullmatch(row["declaration"]):
            raise ValueError(f"invalid declaration: {row['declaration']}")
        path = Path(row["source"])
        if path.is_absolute() or ".." in path.parts or path.suffix != ".lean":
            raise ValueError(f"invalid source: {path}")
        if not NAME.fullmatch(path.with_suffix("").as_posix().replace("/", ".")):
            raise ValueError(f"invalid source module: {path}")
        if path.parts[0] not in {"CertifiedJL", "Vendor"}:
            raise ValueError(f"review entry is outside production sources: {path}")
        if not (root / path).is_file():
            raise ValueError(f"missing source: {path}")
    if not result:
        raise ValueError("review catalog is empty")
    return result


def render(rows: list[dict[str, str]]) -> str:
    modules = sorted({row["source"][:-5].replace("/", ".") for row in rows})
    lines = [*(f"import {module}" for module in modules), "import Lean", "",
             "/- Generated reviewer entry point. Read each statement and follow its definitions.",
             "The axiom report checks logical dependencies, not correspondence with prose. -/", ""]
    seen = set()
    for row in rows:
        decl = row["declaration"]
        if decl not in seen:
            lines += [f"#check {decl}", f"#print axioms {decl}", ""]
            seen.add(decl)
    lines += ["open Lean in", "run_cmd", "  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]",
              "  let targets : Array Name := #[" + ",\n    ".join("``" + d for d in sorted(seen)) + "]",
              "  for target in targets do", "    let axioms ← Lean.collectAxioms target",
              "    unless axioms.all allowed.contains do",
              '      throwError "unexpected axiom for {target}: {axioms}"', ""]
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--output", type=Path, required=True,
                        help="fresh output directory for Review.lean and theorem-map.json")
    args = parser.parse_args()
    rows = entries(args.root)
    args.output.mkdir(parents=True, exist_ok=False)
    (args.output / "Review.lean").write_text(render(rows))
    (args.output / "theorem-map.json").write_text(json.dumps(rows, indent=2) + "\n")
    print(f"generated review workspace for {len(rows)} catalog entries")


if __name__ == "__main__":
    main()
