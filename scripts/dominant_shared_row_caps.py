#!/usr/bin/env python3
"""Generate direct-cover target shards that reuse certified row caps.

The base 128-bit generator owns the base and 512/floor-73 shards.  This script
owns the four remaining inherited direct-cover target shard families whose
cells are identical except for the documented local retunings.
"""

from argparse import ArgumentParser
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
DOMINANT = ROOT / "CertifiedJL/Certificates/Families/L2Lower/Shared/Dominant"
DATA = DOMINANT / "Data"
REPLAY = DOMINANT / "Replay"
PREFIX = "CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant"

TARGETS = {
    "ConstantDirectCover192Bits128": (192, 12, "retarget"),
    "ConstantDirectCover256Bits192": (256, 9, "tightened"),
    "ConstantDirectCover384Bits192": (384, 43, "tightened"),
    "ConstantDirectCover512Bits192": (512, 71, "inherited"),
}


def base_module(tag: str, kind: str) -> str:
    data = DATA / "ConstantDirectCover128" / f"Shard{tag}.lean"
    # Split data shards carry definitions only.  An exactly inherited target
    # needs the matching replay shard for its proved cap fact; retuned targets
    # prove or import their own cap fact and should keep the data-only import.
    owns_caps = ((kind == "retarget" and tag == "23") or
                 (kind == "tightened" and tag in {"02", "03"}))
    if data.is_file() and owns_caps:
        return f"{PREFIX}.Data.ConstantDirectCover128.Shard{tag}"
    return f"{PREFIX}.Replay.ConstantDirectCover128Shard{tag}"


def source(target: str, rows: int, floor: int, kind: str, tag: str) -> str:
    base = f"ConstantDirectCover128Shard{tag}"
    imports = [
        f"import {PREFIX}.Data.{target}.Data",
        f"import {base_module(tag, kind)}",
    ]
    if kind == "tightened" and tag in {"02", "03"}:
        imports.append(
            f"import {PREFIX}.Replay."
            f"ConstantDirectCover256And384Bits192RowCaps.Shard{tag}")

    if kind == "retarget":
        cell_for = "(fun entry => (retargetEntry entry).cell)"
        certificate_for = "(fun entry => (retargetEntry entry).certificate)"
        cap_expr = (
            f"{base}.entries.all (fun entry =>\n"
            "      rowCapsCheck (retargetEntry entry).cell\n"
            "        (retargetEntry entry).certificate) = true")
        if tag == "23":
            cap_proof = "  decide +kernel"
        else:
            cap_proof = (
                "  exact all_rowCapsCheck_of_eq\n"
                f"    {base}.entries {cell_for}\n"
                f"    {certificate_for}\n"
                "    (by decide +kernel) (by decide +kernel)\n"
                f"    {base}.entries_row_caps")
    elif kind == "tightened":
        cell_for = "(fun entry => entry.cell)"
        certificate_for = "targetCertificate"
        cap_expr = (
            f"{base}.entries.all (fun entry =>\n"
            "      rowCapsCheck entry.cell (targetCertificate entry)) = true")
        if tag in {"02", "03"}:
            cap_proof = (
                "  exact ConstantDirectCover256And384Bits192Caps."
                f"shard{tag}_row_caps")
        else:
            cap_proof = (
                "  exact all_rowCapsCheck_of_eq\n"
                f"    {base}.entries (fun entry => entry.cell) targetCertificate\n"
                "    (by decide +kernel) (by decide +kernel)\n"
                f"    {base}.entries_row_caps")
    else:
        cell_for = "(fun entry => entry.cell)"
        certificate_for = "(fun entry => entry.certificate)"
        cap_expr = (
            f"{base}.entries.all (fun entry =>\n"
            "      rowCapsCheck entry.cell entry.certificate) = true")
        cap_proof = f"  exact {base}.entries_row_caps"

    return "\n".join(imports) + f"""

namespace CertifiedJL.SparseThresholdDominant.{target}

open ConstantNumeric

private theorem shard{tag}_row_caps :
    {cap_expr} := by
{cap_proof}

set_option maxRecDepth 100000 in
private theorem shard{tag}_target_certified :
    {base}.entries.all (fun entry =>
      localTargetCheckFor {rows} {floor} ({cell_for} entry)
        ({certificate_for} entry) budget) = true := by
  decide +kernel

theorem shard{tag}_certified :
    {base}.entries.all targetCheck = true := by
  simpa [targetCheck] using
    all_localCertifiedCheckFor_of_rowCaps {rows} {floor}
      {base}.entries {cell_for}
      {certificate_for} budget shard{tag}_row_caps
      shard{tag}_target_certified

end CertifiedJL.SparseThresholdDominant.{target}
"""


def expected() -> dict[Path, str]:
    return {
        REPLAY / target / f"Shard{tag:02d}.lean":
            source(target, rows, floor, kind, f"{tag:02d}")
        for target, (rows, floor, kind) in TARGETS.items()
        for tag in range(47)
    }


def main() -> None:
    parser = ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()

    sources = expected()
    if args.write:
        for path, text in sources.items():
            path.write_text(text)
        print(f"wrote {len(sources)} inherited direct-cover target shards")
        return

    mismatches = [path for path, text in sources.items()
                  if not path.is_file() or path.read_text() != text]
    if mismatches:
        print("shared-row-cap target shards differ:",
              *(path.relative_to(ROOT) for path in mismatches),
              sep="\n", file=sys.stderr)
        raise SystemExit(1)
    print(f"checked {len(sources)} inherited direct-cover target shards")


if __name__ == "__main__":
    main()
