#!/usr/bin/env python3
"""Generate the compressed constant-tilt low-residual cover at 128 bits.

All rectangle endpoints are exact rationals.  Floating point is used only to
search candidate subdivisions and deliberately rounded certificate endpoints;
Lean's interval replay remains authoritative.
"""

from fractions import Fraction as F
from functools import cache
from math import ceil, comb, cos, exp, floor, log, pi, sqrt
import argparse
from decimal import Decimal, localcontext
import io
from pathlib import Path
import sys
from contextlib import redirect_stdout

R_MAX = F(2500, 2401)
ROW_DEN = 10**6
ROW_MARGIN = 2.0e-4
GROWTH_FACTOR = 1.01


def deterministic_exp(value: float) -> float:
    """Return the correctly rounded binary64 exponential deterministically.

    The generated growth endpoint is the ceiling of a value around 2^103, so
    a one-ulp difference between platform ``libm`` implementations changes the
    emitted integer.  Decimal's specified, correctly rounded exponential at
    ample precision fixes that byte-level portability issue while preserving
    the existing binary64 search input and output format.
    """
    with localcontext() as context:
        context.prec = 100
        return float(context.exp(Decimal.from_float(value)))


def growth_upper_numerator(r_upper: F, zq: F) -> int:
    exponent = 29 * float(zq) * float(r_upper)
    return ceil(deterministic_exp(exponent) * GROWTH_FACTOR)


def modulus_lower(r_lower: F) -> F:
    if 9 * r_lower <= 4:
        return F(2)
    value = floor(1000 * sqrt(float(9 * r_lower)))
    while F(value * value, 1000**2) > 9 * r_lower:
        value -= 1
    return F(value, 1000)


def rho(lower, upper, z):
    h_lower = z * z * lower / (1 + z * lower) ** 2
    h_upper = z * z * upper / (1 + z * upper) ** 2
    h_critical = z / 4 if z * lower <= 1 <= z * upper else 0
    h = max(h_lower, h_upper, h_critical)
    return min(1, 1 - z * lower / 2 * max(0, 1 - h)
               + 3 * (z * upper) ** 2 + 4 * (z * upper) ** 2 * h * h)


def rows(box, zq):
    lower, upper, r_lower, _ = map(float, box)
    z = float(zq)
    modulus = float(modulus_lower(box[2]))
    alpha = z / (1 + z * upper)
    inactive_wrap = 2 * exp(-alpha * modulus * modulus) / (
        1 - exp(-3 * alpha * modulus * modulus))
    active_wrap = exp(-alpha * (modulus - 1) ** 2) / (
        1 - exp(-alpha * (3 * modulus * modulus - 2 * modulus))) + exp(
            -alpha * (modulus + 1) ** 2) / (
        1 - exp(-alpha * (3 * modulus * modulus + 2 * modulus)))
    theta = exp(-pi**2 / (1 + z * upper))
    inactive = 1 / sqrt(1 + z * lower) * (
        1 + 2 * theta / (1 - theta**3)) + inactive_wrap
    active = exp(-z / (1 + z * upper)) * rho(lower, upper, z) + active_wrap
    return inactive, active


def certificate(box, zq):
    inactive, active = rows(box, zq)
    i_num = ceil((inactive + ROW_MARGIN) * ROW_DEN)
    a_num = ceil((active + ROW_MARGIN) * ROW_DEN)
    g_num = growth_upper_numerator(box[3], zq)
    return F(i_num, ROW_DEN), F(a_num, ROW_DEN), F(g_num)


def scaled_certificate_majorant(box, zq):
    inactive, active, growth = map(float, certificate(box, zq))
    answer = 0.0
    for k in range(29, 257):
        body_log = log(growth) + k * log(active) + (256 - k) * log(inactive)
        body = 1.0 if body_log >= 0 else exp(body_log)
        answer += comb(256, k) / 2**256 * body
    return answer * 2**129


@cache
def best_constant(box):
    return min(((F(i, 20), scaled_certificate_majorant(box, F(i, 20)))
                for i in range(20, 161)), key=lambda item: item[1])


def cover(accept=1.82):
    complete = []
    pending = [(F(0), F(1, 2), F(0), R_MAX)]
    evaluated = 0
    while pending:
        box = pending.pop()
        lower, upper, r_lower, r_upper = box
        # Only rectangles strictly above r = 1 + u are infeasible.  Equality
        # remains in the cover, matching the non-strict norm premise.
        if r_lower > 1 + upper:
            continue
        z, value = best_constant(box)
        evaluated += 1
        if value < accept:
            complete.append((box, z, value, certificate(box, z)))
            continue
        u_width = upper - lower
        r_width = r_upper - r_lower
        if max(u_width, r_width) < F(1, 2**30):
            raise RuntimeError((box, z, value))
        if u_width > r_width / 2:
            middle = (lower + upper) / 2
            pending.extend([(lower, middle, r_lower, r_upper),
                            (middle, upper, r_lower, r_upper)])
        else:
            middle = (r_lower + r_upper) / 2
            pending.extend([(lower, upper, r_lower, middle),
                            (lower, upper, middle, r_upper)])
    return evaluated, complete


def cover_tree(box=(F(0), F(1, 2), F(0), R_MAX), accept=1.82):
    """Rebuild the exact binary subdivision used by ``cover``.

    Empty nodes are rectangles strictly above the feasible diagonal
    ``r <= 1 + u``.  Every other leaf is one of the accepted cells emitted in
    the bounded-memory shards.
    """
    lower, upper, r_lower, r_upper = box
    if r_lower > 1 + upper:
        return ("empty", box)
    z, value = best_constant(box)
    if value < accept:
        return ("leaf", box, z, value, certificate(box, z))
    u_width = upper - lower
    r_width = r_upper - r_lower
    if max(u_width, r_width) < F(1, 2**30):
        raise RuntimeError((box, z, value))
    if u_width > r_width / 2:
        middle = (lower + upper) / 2
        return ("u", box, middle,
                cover_tree((lower, middle, r_lower, r_upper), accept),
                cover_tree((middle, upper, r_lower, r_upper), accept))
    middle = (r_lower + r_upper) / 2
    return ("r", box, middle,
            cover_tree((lower, upper, r_lower, middle), accept),
            cover_tree((lower, upper, middle, r_upper), accept))


def q(f):
    return str(f.numerator) if f.denominator == 1 else f"{f.numerator} / {f.denominator}"


def emit_cell(index, item):
    box, z, _, cert = item
    lo, hi, _, rhi = box
    modulus = modulus_lower(box[2])
    inactive, active, growth = cert
    return f'''def cell{index} : Cell where
  lower := {q(lo)}
  upper := {q(hi)}
  thresholdUpper := {q(rhi)}
  modulusLower := {q(modulus)}
  z := {q(z)}

def certificate{index} : Certificate where
  inactiveUpper := {q(inactive)}
  activeUpper := {q(active)}
  growthUpper := {q(growth)}
'''


def emit_shard_source(ordered, shard, shard_size, evaluated):
    first = shard * shard_size
    chosen = ordered[first:first + shard_size]
    namespace = f"ConstantDirectCover128Shard{shard:02d}"
    output = io.StringIO()
    with redirect_stdout(output):
        print(f"-- evaluated {evaluated}")
        print(f"-- accepted {len(ordered)}")
        print(f"-- worst {max(item[2] for item in ordered):.12f}")
        print("import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData")
        print("\nnamespace CertifiedJL")
        print("namespace SparseThresholdDominant")
        print(f"namespace {namespace}\n")
        print("open ConstantNumeric\n")
        for offset, item in enumerate(chosen):
            index = first + offset
            print(emit_cell(index, item))
            print(f"def entry{index} : Entry := ⟨cell{index}, certificate{index}⟩\n")
        names = ", ".join(f"entry{first + j}" for j in range(len(chosen)))
        print(f"def entries : List Entry := [{names}]\n")
        print("theorem entries_valid : entriesValidCheck entries = true := by")
        print("  decide +kernel\n")
        print("set_option maxRecDepth 100000 in")
        print("theorem entries_row_caps : entriesRowCapsCheck entries = true := by")
        print("  decide +kernel\n")
        print("set_option maxRecDepth 100000 in")
        print("theorem entries_target_certified : entriesLocalTargetCheckAt entries")
        print("    (187 / (200 * 2 ^ 128)) = true := by")
        print("  decide +kernel\n")
        print("theorem entries_certified : entriesCertifiedCheckAt entries")
        print("    (187 / (200 * 2 ^ 128)) = true := by")
        print("  exact entriesCertifiedCheckAt_of_checks entries")
        print("    (187 / (200 * 2 ^ 128)) entries_row_caps entries_target_certified\n")
        print(f"end {namespace}")
        print("end SparseThresholdDominant")
        print("end CertifiedJL")
    return output.getvalue()


def emit_shard_data_source(ordered, shard, shard_size, evaluated):
    """Emit the reusable cell and certificate records for a base shard."""
    first = shard * shard_size
    chosen = ordered[first:first + shard_size]
    namespace = f"ConstantDirectCover128Shard{shard:02d}"
    output = io.StringIO()
    with redirect_stdout(output):
        print(f"-- evaluated {evaluated}")
        print(f"-- accepted {len(ordered)}")
        print(f"-- worst {max(item[2] for item in ordered):.12f}")
        print("import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData")
        print("\nnamespace CertifiedJL")
        print("namespace SparseThresholdDominant")
        print(f"namespace {namespace}\n")
        print("open ConstantNumeric\n")
        for offset, item in enumerate(chosen):
            index = first + offset
            print(emit_cell(index, item))
            print(f"def entry{index} : Entry := ⟨cell{index}, certificate{index}⟩\n")
        names = ", ".join(f"entry{first + j}" for j in range(len(chosen)))
        print(f"def entries : List Entry := [{names}]\n")
        print(f"end {namespace}")
        print("end SparseThresholdDominant")
        print("end CertifiedJL")
    return output.getvalue()


def emit_shard_replay_source(shard, evaluated, accepted, worst):
    """Emit only the kernel-replayed checks for a split base shard."""
    namespace = f"ConstantDirectCover128Shard{shard:02d}"
    output = io.StringIO()
    with redirect_stdout(output):
        print(f"-- evaluated {evaluated}")
        print(f"-- accepted {accepted}")
        print(f"-- worst {worst:.12f}")
        print("import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data."
              f"ConstantDirectCover128.Shard{shard:02d}")
        print("\nnamespace CertifiedJL")
        print("namespace SparseThresholdDominant")
        print(f"namespace {namespace}\n")
        print("open ConstantNumeric\n")
        print("theorem entries_valid : entriesValidCheck entries = true := by")
        print("  decide +kernel\n")
        print("set_option maxRecDepth 100000 in")
        print("theorem entries_row_caps : entriesRowCapsCheck entries = true := by")
        print("  decide +kernel\n")
        print("set_option maxRecDepth 100000 in")
        print("theorem entries_target_certified : entriesLocalTargetCheckAt entries")
        print("    (187 / (200 * 2 ^ 128)) = true := by")
        print("  decide +kernel\n")
        print("theorem entries_certified : entriesCertifiedCheckAt entries")
        print("    (187 / (200 * 2 ^ 128)) = true := by")
        print("  exact entriesCertifiedCheckAt_of_checks entries")
        print("    (187 / (200 * 2 ^ 128)) entries_row_caps entries_target_certified\n")
        print(f"end {namespace}")
        print("end SparseThresholdDominant")
        print("end CertifiedJL")
    return output.getvalue()


def emit_aggregate_source(count):
    """Emit the sole cumulative assembly layer for the independent shards."""
    output = io.StringIO()
    with redirect_stdout(output):
        print("import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Soundness.ConstantNumeric")
        for shard in range(count):
            print("import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay."
                  f"ConstantDirectCover128Shard{shard:02d}")
        print("\n/-! # Exact aggregate of the independent 128-bit direct-cover shards -/\n")
        print("namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Aggregate\n")
        print("open ConstantNumeric\n")
        print("@[simp] theorem entriesValidCheck_append (xs ys : List Entry) :")
        print("    entriesValidCheck (xs ++ ys) =")
        print("      (entriesValidCheck xs && entriesValidCheck ys) := by")
        print("  simp [entriesValidCheck]\n")
        print("@[simp] theorem entriesCertifiedCheckAt_append")
        print("    (xs ys : List Entry) (budget : ℚ) :")
        print("    entriesCertifiedCheckAt (xs ++ ys) budget =")
        print("      (entriesCertifiedCheckAt xs budget &&")
        print("        entriesCertifiedCheckAt ys budget) := by")
        print("  simp [entriesCertifiedCheckAt]\n")
        print("end CertifiedJL.SparseThresholdDominant.ConstantDirectCover128Aggregate\n")
        for shard in range(count):
            tag = f"{shard:02d}"
            namespace = f"ConstantDirectCover128Shard{tag}"
            print(f"namespace CertifiedJL.SparseThresholdDominant.{namespace}\n")
            print("open ConstantNumeric\n")
            print("theorem bound_of_mem {entry : Entry} (hmem : entry ∈ entries) :")
            print("    thresholdDominantCellMajorant entry.cell.decode <")
            print("      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=")
            print("  entry_bound_of_mem_of_checks entries (187 / (200 * 2 ^ 128))")
            print("    entries_valid entries_certified hmem\n")
            if shard == 0:
                print("def allEntries : List Entry := entries\n")
            else:
                previous = f"ConstantDirectCover128Shard{shard - 1:02d}"
                print("def allEntries : List Entry :=")
                print(f"  {previous}.allEntries ++ entries\n")
            print("theorem allEntries_valid_check :")
            print("    entriesValidCheck allEntries = true := by")
            if shard == 0:
                print("  simpa [allEntries] using entries_valid\n")
            else:
                print("  simp only [allEntries,")
                print("    ConstantDirectCover128Aggregate.entriesValidCheck_append,")
                print(f"    {previous}.allEntries_valid_check, entries_valid]")
                print("  decide\n")
            print("theorem allEntries_certified_check :")
            print("    entriesCertifiedCheckAt allEntries")
            print("      (187 / (200 * 2 ^ 128)) = true := by")
            if shard == 0:
                print("  simpa [allEntries] using entries_certified\n")
            else:
                print("  simp only [allEntries,")
                print("    ConstantDirectCover128Aggregate.entriesCertifiedCheckAt_append,")
                print(f"    {previous}.allEntries_certified_check, entries_certified]")
                print("  decide\n")
            print("theorem allEntries_valid {entry : Entry}")
            print("    (hmem : entry ∈ allEntries) : entry.cell.Valid := by")
            print("  have hvalid := allEntries_valid_check")
            print("  rw [entriesValidCheck, List.all_eq_true] at hvalid")
            print("  exact (entryValidCheck_sound (hvalid entry hmem)).1\n")
            print("theorem allEntries_bound {entry : Entry}")
            print("    (hmem : entry ∈ allEntries) :")
            print("    thresholdDominantCellMajorant entry.cell.decode <")
            print("      (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=")
            print("  entry_bound_of_mem_of_checks allEntries (187 / (200 * 2 ^ 128))")
            print("    allEntries_valid_check allEntries_certified_check hmem\n")
            if shard + 1 == count:
                print("theorem allEntries_length : allEntries.length = 188 := by")
                print("  decide +kernel\n")
            print(f"end CertifiedJL.SparseThresholdDominant.{namespace}")
            if shard + 1 < count:
                print()
    return output.getvalue()


FLOOR73_NAMESPACE = "ConstantDirectCover512Floor73Bits193"


def emit_floor73_data_source():
    return '''/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

/-! # Shared data for the 512-row, floor-73, 193-bit direct-cover replay -/

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover512Floor73Bits193

open ConstantNumeric

def budget : ℚ := 99999 / (100000 * 2 ^ 193)

def targetCheck (entry : Entry) : Bool :=
  localCertifiedCheckFor 512 73 entry.cell entry.certificate budget

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover512Floor73Bits193
'''


def emit_floor73_shard_source(shard):
    tag = f"{shard:02d}"
    return f'''/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.{FLOOR73_NAMESPACE}.Data
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Shard{tag}

namespace CertifiedJL.SparseThresholdDominant.{FLOOR73_NAMESPACE}

open ConstantNumeric

set_option maxRecDepth 100000 in
private theorem shard{tag}_target_certified :
    ConstantDirectCover128Shard{tag}.entries.all (fun entry =>
      localTargetCheckFor 512 73 entry.cell entry.certificate budget) = true := by
  decide +kernel

theorem shard{tag}_certified :
    ConstantDirectCover128Shard{tag}.entries.all targetCheck = true := by
  simpa [targetCheck] using
    all_localCertifiedCheckFor_of_rowCaps 512 73
      ConstantDirectCover128Shard{tag}.entries (fun entry => entry.cell)
      (fun entry => entry.certificate) budget
      ConstantDirectCover128Shard{tag}.entries_row_caps
      shard{tag}_target_certified

end CertifiedJL.SparseThresholdDominant.{FLOOR73_NAMESPACE}
'''


def emit_floor73_aggregate_source(count):
    output = io.StringIO()
    with redirect_stdout(output):
        print("/-")
        print("Copyright (c) 2026 Anonymous Author. All rights reserved.")
        print("Released under Apache 2.0 license as described in the file LICENSE.")
        print("Authors: Anonymous Author")
        print("-/\n")
        print("import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay."
              "ConstantDirectCover128Selector")
        for shard in range(count):
            print("import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay."
                  f"{FLOOR73_NAMESPACE}.Shard{shard:02d}")
        print("\n/-! # Replayed direct dominant cover for 512 rows, floor 73, and 193 bits -/\n")
        print(f"namespace CertifiedJL.SparseThresholdDominant.{FLOOR73_NAMESPACE}\n")
        print("open ConstantNumeric\n")
        for shard in range(count):
            tag = f"{shard:02d}"
            print(f"private theorem allEntries{tag}_certified :")
            print(f"    ConstantDirectCover128Shard{tag}.allEntries.all")
            print("      targetCheck = true := by")
            if shard == 0:
                print(f"  simpa [ConstantDirectCover128Shard{tag}.allEntries] using")
                print(f"    shard{tag}_certified\n")
            else:
                previous = f"{shard - 1:02d}"
                print(f"  simp [ConstantDirectCover128Shard{tag}.allEntries,")
                print(f"    allEntries{previous}_certified, shard{tag}_certified]\n")
        print("private theorem allEntries_certified :")
        print("    ConstantDirectCover128Shard46.allEntries.all targetCheck = true := by")
        print(f"  exact allEntries{count - 1:02d}_certified\n")
        print("/-- Every cell selected by the inherited no-gap tree satisfies the")
        print("512-row, floor-73, 193-bit high-activity budget. -/")
        print("theorem allEntries_bound {entry : Entry}")
        print("    (hmem : entry ∈ ConstantDirectCover128Shard46.allEntries) :")
        print("    thresholdDominantCellMajorantAt 512 73 (entry.cell.decodeAt 512) <")
        print("      (budget : ℝ) := by")
        print("  apply entry_boundAt_of_mem_of_checks 512 73")
        print("    ConstantDirectCover128Shard46.allEntries budget")
        print("    ConstantDirectCover128Shard46.allEntries_valid_check")
        print("    (by simpa [targetCheck, entriesCertifiedCheckFor] using allEntries_certified)")
        print("    hmem\n")
        print("/-- Exact no-gap direct cover at 512 rows, floor 73, and 193 bits. -/")
        print("theorem exists_cover_cell (u r B : ℝ)")
        print("    (huZero : 0 ≤ u) (huHalf : u ≤ 1 / 2)")
        print("    (hrZero : 0 ≤ r) (hrUpper : r ≤ 2500 / 2401)")
        print("    (hrFeasible : r ≤ 1 + u) (hBtwo : 2 ≤ B)")
        print("    (hrModulus : 9 * r ≤ B ^ 2) :")
        print("    ∃ entry : Entry,")
        print("      entry.cell.Valid ∧")
        print("      (entry.cell.lower : ℝ) ≤ u ∧")
        print("      u ≤ (entry.cell.upper : ℝ) ∧")
        print("      r ≤ (entry.cell.thresholdUpper : ℝ) ∧")
        print("      (entry.cell.modulusLower : ℝ) ≤ B ∧")
        print("      thresholdDominantCellMajorantAt 512 73")
        print("        (entry.cell.decodeAt 512) < (budget : ℝ) :=")
        print("  ConstantDirectCover128Selector.exists_cover_cell_at 512 73 budget")
        print("    (fun _ hmem => allEntries_bound hmem)")
        print("    u r B huZero huHalf hrZero hrUpper hrFeasible hBtwo hrModulus\n")
        print(f"end CertifiedJL.SparseThresholdDominant.{FLOOR73_NAMESPACE}")
    return output.getvalue()



def emit_tree_selector_source(ordered, shard_size):
    """Emit a compact checked-tree interpreter and its exact cover data."""
    count = (len(ordered) + shard_size - 1) // shard_size
    index_of_box = {item[0]: index for index, item in enumerate(ordered)}
    tree = cover_tree()

    def emit_tree(node, indent=0):
        kind = node[0]
        pad = " " * indent
        if kind == "empty":
            return ".empty"
        if kind == "leaf":
            index = index_of_box[node[1]]
            return f".leaf \u27e8{index}, by decide\u27e9"
        _, _, middle, left, right = node
        constructor = "splitU" if kind == "u" else "splitR"
        return (f".{constructor} ({q(middle)})\n{pad}  (" +
                emit_tree(left, indent + 2) + f")\n{pad}  (" +
                emit_tree(right, indent + 2) + ")")

    output = io.StringIO()
    with redirect_stdout(output):
        print("import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay."
              "ConstantDirectCover128Aggregate")
        print("\n/-!\n# Exact no-gap selector for the low-residual 128-bit cover\n\n"
              "A small generic interpreter proves soundness for a binary tree of exact\n"
              "rational boxes. The generated tree is kernel-checked: split children share\n"
              "their closed boundary; empty leaves lie strictly above `r = 1 + u`; and\n"
              "every accepted leaf names one of the independently replayed shard entries.\n"
              "-/\n")
        print("namespace CertifiedJL")
        print("namespace SparseThresholdDominant")
        print("namespace ConstantDirectCover128Selector\n")
        print("open ConstantNumeric\n")
        print("structure Box where")
        print("  uLower : \u211a")
        print("  uUpper : \u211a")
        print("  rLower : \u211a")
        print("  rUpper : \u211a\n")
        print("inductive CoverTree where")
        print("  | empty")
        print(f"  | leaf (index : Fin {len(ordered)})")
        print("  | splitU (middle : \u211a) (left right : CoverTree)")
        print("  | splitR (middle : \u211a) (left right : CoverTree)\n")

        final_tag = f"{count - 1:02d}"
        final_namespace = f"ConstantDirectCover128Shard{final_tag}"
        print(f"private def entries : List Entry := {final_namespace}.allEntries\n")
        print(f"private theorem entries_length : entries.length = {len(ordered)} := by")
        print("  decide +kernel\n")
        print(f"private def entryAt (index : Fin {len(ordered)}) : Entry :=")
        print("  entries.get \u27e8index, by rw [entries_length]; exact index.isLt\u27e9\n")
        print(f"private theorem entryAt_mem (index : Fin {len(ordered)}) :")
        print("    entryAt index \u2208 entries := by")
        print("  unfold entryAt")
        print("  exact List.get_mem _ _\n")
        print(f"private theorem entryAt_valid (index : Fin {len(ordered)}) :")
        print("    (entryAt index).cell.Valid :=")
        print(f"  {final_namespace}.allEntries_valid (entryAt_mem index)\n")
        print(f"private theorem entryAt_bound (index : Fin {len(ordered)}) :")
        print("    thresholdDominantCellMajorant (entryAt index).cell.decode <")
        print("      (((187 / (200 * 2 ^ 128) : \u211a) : \u211d)) :=")
        print(f"  {final_namespace}.allEntries_bound (entryAt_mem index)\n")

        print("private def leafValid (box : Box) (index : Fin "
              f"{len(ordered)}) : Prop :=")
        print("  let entry := entryAt index")
        print("  entry.cell.lower = box.uLower \u2227")
        print("    entry.cell.upper = box.uUpper \u2227")
        print("    entry.cell.thresholdUpper = box.rUpper \u2227")
        print("    (entry.cell.modulusLower = 2 \u2228")
        print("      entry.cell.modulusLower ^ 2 \u2264 9 * box.rLower)\n")
        print("def CoverTree.Valid : CoverTree \u2192 Box \u2192 Prop")
        print("  | .empty, box => 1 + box.uUpper < box.rLower")
        print("  | .leaf index, box => leafValid box index")
        print("  | .splitU middle left right, box =>")
        print("      box.uLower \u2264 middle \u2227 middle \u2264 box.uUpper \u2227")
        print("        left.Valid { box with uUpper := middle } \u2227")
        print("        right.Valid { box with uLower := middle }")
        print("  | .splitR middle left right, box =>")
        print("      box.rLower \u2264 middle \u2227 middle \u2264 box.rUpper \u2227")
        print("        left.Valid { box with rUpper := middle } \u2227")
        print("        right.Valid { box with rLower := middle }\n")
        print("private def CoverTree.decidableValid :")
        print("    (tree : CoverTree) \u2192 (box : Box) \u2192 Decidable (tree.Valid box)")
        print("  | .empty, _ => by")
        print("      unfold CoverTree.Valid")
        print("      infer_instance")
        print("  | .leaf _, _ => by")
        print("      unfold CoverTree.Valid leafValid")
        print("      infer_instance")
        print("  | .splitU middle left right, box => by")
        print("      unfold CoverTree.Valid")
        print("      letI := left.decidableValid { box with uUpper := middle }")
        print("      letI := right.decidableValid { box with uLower := middle }")
        print("      exact inferInstance")
        print("  | .splitR middle left right, box => by")
        print("      unfold CoverTree.Valid")
        print("      letI := left.decidableValid { box with rUpper := middle }")
        print("      letI := right.decidableValid { box with rLower := middle }")
        print("      exact inferInstance\n")
        print("private instance (tree : CoverTree) (box : Box) :")
        print("    Decidable (tree.Valid box) := tree.decidableValid box\n")
        print("def CoverTree.leafIndices : CoverTree \u2192 List (Fin "
              f"{len(ordered)})")
        print("  | .empty => []")
        print("  | .leaf index => [index]")
        print("  | .splitU _ left right | .splitR _ left right =>")
        print("      left.leafIndices ++ right.leafIndices\n")

        print("private theorem CoverTree.sound (tree : CoverTree) (box : Box)")
        print("    (hvalid : tree.Valid box) (P : Cell \u2192 Prop)")
        print("    (hbound : \u2200 index, P (entryAt index).cell) (u r B : \u211d)")
        print("    (huLower : (box.uLower : \u211d) \u2264 u)")
        print("    (huUpper : u \u2264 (box.uUpper : \u211d))")
        print("    (hrLower : (box.rLower : \u211d) \u2264 r)")
        print("    (hrUpper : r \u2264 (box.rUpper : \u211d))")
        print("    (hrFeasible : r \u2264 1 + u) (hBtwo : 2 \u2264 B)")
        print("    (hrModulus : 9 * r \u2264 B ^ 2) :")
        print("    \u2203 entry : Entry,")
        print("      entry.cell.Valid \u2227")
        print("      (entry.cell.lower : \u211d) \u2264 u \u2227")
        print("      u \u2264 (entry.cell.upper : \u211d) \u2227")
        print("      r \u2264 (entry.cell.thresholdUpper : \u211d) \u2227")
        print("      (entry.cell.modulusLower : \u211d) \u2264 B \u2227")
        print("      P entry.cell := by")
        print("  induction tree generalizing box with")
        print("  | empty =>")
        print("      have himpossible : (1 : \u211d) + (box.uUpper : \u211d) <")
        print("          (box.rLower : \u211d) := by exact_mod_cast hvalid")
        print("      exfalso")
        print("      linarith")
        print("  | leaf index =>")
        print("      rcases hvalid with \u27e8huLowerEq, huUpperEq, hrUpperEq, hmodulus\u27e9")
        print("      refine \u27e8entryAt index, entryAt_valid index, ?_, ?_, ?_, ?_,")
        print("        hbound index\u27e9")
        print("      \u00b7 rw [huLowerEq]")
        print("        exact huLower")
        print("      \u00b7 rw [huUpperEq]")
        print("        exact huUpper")
        print("      \u00b7 rw [hrUpperEq]")
        print("        exact hrUpper")
        print("      \u00b7 rcases hmodulus with htwo | hsquare")
        print("        \u00b7 rw [htwo]")
        print("          exact hBtwo")
        print("        \u00b7 have hsquareReal :")
        print("              ((entryAt index).cell.modulusLower : \u211d) ^ 2 \u2264")
        print("                9 * (box.rLower : \u211d) := by exact_mod_cast hsquare")
        print("          have hrScaled : 9 * (box.rLower : \u211d) \u2264 9 * r :=")
        print("            mul_le_mul_of_nonneg_left hrLower (by norm_num)")
        print("          have hmSquare :")
        print("              ((entryAt index).cell.modulusLower : \u211d) ^ 2 \u2264 B ^ 2 :=")
        print("            hsquareReal.trans (hrScaled.trans hrModulus)")
        print("          have hmPositive :")
        print("              0 < ((entryAt index).cell.modulusLower : \u211d) := by")
        print("            have := (entryAt_valid index).1.2.2.2.1")
        print("            exact_mod_cast (lt_trans (by norm_num : (0 : \u211a) < 1) this)")
        print("          nlinarith [hmSquare]")
        print("  | splitU middle left right ihLeft ihRight =>")
        print("      rcases hvalid with \u27e8-, -, hleft, hright\u27e9")
        print("      by_cases hside : u \u2264 (middle : \u211d)")
        print("      \u00b7 exact ihLeft _ hleft huLower hside hrLower hrUpper")
        print("      \u00b7 exact ihRight _ hright (le_of_not_ge hside) huUpper")
        print("          hrLower hrUpper")
        print("  | splitR middle left right ihLeft ihRight =>")
        print("      rcases hvalid with \u27e8-, -, hleft, hright\u27e9")
        print("      by_cases hside : r \u2264 (middle : \u211d)")
        print("      \u00b7 exact ihLeft _ hleft huLower huUpper hrLower hside")
        print("      \u00b7 exact ihRight _ hright huLower huUpper")
        print("          (le_of_not_ge hside) hrUpper\n")

        print("private def rootBox : Box :=")
        print("  \u27e80, 1 / 2, 0, 2500 / 2401\u27e9\n")
        print("private def rootTree : CoverTree :=")
        print("  " + emit_tree(tree, 2) + "\n")
        print("set_option maxRecDepth 100000 in")
        print("private theorem rootTree_valid : rootTree.Valid rootBox := by")
        print("  decide +kernel\n")
        print("set_option maxRecDepth 100000 in")
        print("private theorem rootTree_indices_complete :")
        print(f"    rootTree.leafIndices.length = {len(ordered)} \u2227")
        print("      rootTree.leafIndices.Nodup := by")
        print("  decide +kernel\n")
        print("theorem exists_cover_cell (u r B : \u211d)")
        print("    (huZero : 0 \u2264 u) (huHalf : u \u2264 1 / 2)")
        print("    (hrZero : 0 \u2264 r) (hrUpper : r \u2264 2500 / 2401)")
        print("    (hrFeasible : r \u2264 1 + u) (hBtwo : 2 \u2264 B)")
        print("    (hrModulus : 9 * r \u2264 B ^ 2) :")
        print("    \u2203 entry : Entry,")
        print("      entry.cell.Valid \u2227")
        print("      (entry.cell.lower : \u211d) \u2264 u \u2227")
        print("      u \u2264 (entry.cell.upper : \u211d) \u2227")
        print("      r \u2264 (entry.cell.thresholdUpper : \u211d) \u2227")
        print("      (entry.cell.modulusLower : \u211d) \u2264 B \u2227")
        print("      thresholdDominantCellMajorant entry.cell.decode <")
        print("        (((187 / (200 * 2 ^ 128) : \u211a) : \u211d)) := by")
        print("  apply rootTree.sound rootBox rootTree_valid")
        print("    (fun cell => thresholdDominantCellMajorant cell.decode <")
        print("      (((187 / (200 * 2 ^ 128) : \u211a) : \u211d))) entryAt_bound u r B")
        print("  \u00b7 simpa [rootBox] using huZero")
        print("  \u00b7 simpa [rootBox] using huHalf")
        print("  \u00b7 simpa [rootBox] using hrZero")
        print("  \u00b7 simpa [rootBox] using hrUpper")
        print("  \u00b7 exact hrFeasible")
        print("  \u00b7 exact hBtwo")
        print("  \u00b7 exact hrModulus\n")
        print('''/-- Reuse the exact no-gap geometry tree with a target-dependent semantic
bound proved for every inherited cell. -/
theorem exists_cover_cell_at (rows squaredNormFloor : ℕ) (budget : ℚ)
    (hbound : ∀ entry ∈ ConstantDirectCover128Shard46.allEntries,
      thresholdDominantCellMajorantAt rows squaredNormFloor
          (entry.cell.decodeAt rows) < (budget : ℝ))
    (u r B : ℝ)
    (huZero : 0 ≤ u) (huHalf : u ≤ 1 / 2)
    (hrZero : 0 ≤ r) (hrUpper : r ≤ 2500 / 2401)
    (hrFeasible : r ≤ 1 + u) (hBtwo : 2 ≤ B)
    (hrModulus : 9 * r ≤ B ^ 2) :
    ∃ entry : Entry,
      entry.cell.Valid ∧
      (entry.cell.lower : ℝ) ≤ u ∧
      u ≤ (entry.cell.upper : ℝ) ∧
      r ≤ (entry.cell.thresholdUpper : ℝ) ∧
      (entry.cell.modulusLower : ℝ) ≤ B ∧
      thresholdDominantCellMajorantAt rows squaredNormFloor
        (entry.cell.decodeAt rows) < (budget : ℝ) := by
  apply rootTree.sound rootBox rootTree_valid
    (fun cell => thresholdDominantCellMajorantAt rows squaredNormFloor
      (cell.decodeAt rows) < (budget : ℝ))
    (fun index => hbound (entryAt index) (entryAt_mem index)) u r B
  · simpa [rootBox] using huZero
  · simpa [rootBox] using huHalf
  · simpa [rootBox] using hrZero
  · simpa [rootBox] using hrUpper
  · exact hrFeasible
  · exact hBtwo
  · exact hrModulus

/-- Reuse the exact no-gap geometry tree with an arbitrary semantic property
proved for every inherited cell. This supports target-specific tilt changes
and local cell refinements without duplicating the selector tree. -/
theorem exists_cover_cell_of_property (P : Cell → Prop)
    (hproperty : ∀ entry ∈ ConstantDirectCover128Shard46.allEntries,
      P entry.cell)
    (u r B : ℝ)
    (huZero : 0 ≤ u) (huHalf : u ≤ 1 / 2)
    (hrZero : 0 ≤ r) (hrUpper : r ≤ 2500 / 2401)
    (hrFeasible : r ≤ 1 + u) (hBtwo : 2 ≤ B)
    (hrModulus : 9 * r ≤ B ^ 2) :
    ∃ entry : Entry,
      entry.cell.Valid ∧
      (entry.cell.lower : ℝ) ≤ u ∧
      u ≤ (entry.cell.upper : ℝ) ∧
      r ≤ (entry.cell.thresholdUpper : ℝ) ∧
      (entry.cell.modulusLower : ℝ) ≤ B ∧
      P entry.cell := by
  apply rootTree.sound rootBox rootTree_valid P
    (fun index => hproperty (entryAt index) (entryAt_mem index)) u r B
  · simpa [rootBox] using huZero
  · simpa [rootBox] using huHalf
  · simpa [rootBox] using hrZero
  · simpa [rootBox] using hrUpper
  · exact hrFeasible
  · exact hBtwo
  · exact hrModulus
''')
        print("end ConstantDirectCover128Selector")
        print("end SparseThresholdDominant")
        print("end CertifiedJL")
    return output.getvalue()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--emit", action="store_true")
    parser.add_argument("--shard", type=int)
    parser.add_argument("--shard-size", type=int, default=4)
    parser.add_argument("--all-shards", action="store_true")
    parser.add_argument("--selector", action="store_true")
    parser.add_argument("--out-dir", type=Path)
    parser.add_argument("--check-dir", type=Path)
    parser.add_argument("--check-all-dir", type=Path,
                        help="check all canonical size-four base/floor73 generated sources")
    parser.add_argument("--write-all-dir", type=Path,
                        help="write all canonical size-four base/floor73 generated sources")
    parser.add_argument("--floor73-out-dir", type=Path)
    parser.add_argument("--floor73-check-dir", type=Path)
    args = parser.parse_args()
    evaluated, cells = cover()
    ordered = sorted(cells, key=lambda item: item[2], reverse=True)
    if args.check_all_dir is not None or args.write_all_dir is not None:
        if args.shard_size != 4 or len(ordered) != 188:
            raise SystemExit("canonical direct replay requires 188 entries in size-four shards")
        directory = (args.check_all_dir if args.check_all_dir is not None
                     else args.write_all_dir)
        assert directory is not None
        data_directory = directory / "Data"
        replay_directory = directory / "Replay"
        count = 47
        target_data_directory = data_directory / FLOOR73_NAMESPACE
        target_replay_directory = replay_directory / FLOOR73_NAMESPACE
        split_shards = {2, 3, 23}
        base_data_directory = data_directory / "ConstantDirectCover128"
        expected = {}
        for shard in range(count):
            tag = f"{shard:02d}"
            replay_path = replay_directory / f"ConstantDirectCover128Shard{tag}.lean"
            if shard in split_shards:
                expected[base_data_directory / f"Shard{tag}.lean"] = (
                    emit_shard_data_source(
                        ordered, shard, args.shard_size, evaluated))
                expected[replay_path] = emit_shard_replay_source(
                    shard, evaluated, len(ordered),
                    max(item[2] for item in ordered))
            else:
                expected[replay_path] = emit_shard_source(
                    ordered, shard, args.shard_size, evaluated)
        expected.update({
            replay_directory / "ConstantDirectCover128Aggregate.lean": emit_aggregate_source(count),
            replay_directory / "ConstantDirectCover128Selector.lean":
                emit_tree_selector_source(ordered, args.shard_size),
            target_data_directory / "Data.lean": emit_floor73_data_source(),
            replay_directory / f"{FLOOR73_NAMESPACE}.lean": emit_floor73_aggregate_source(count),
            **{target_replay_directory / f"Shard{shard:02d}.lean": emit_floor73_shard_source(shard)
               for shard in range(count)},
        })
        if args.check_all_dir is not None:
            actual_shards = (
                set(replay_directory.glob("ConstantDirectCover128Shard*.lean")) |
                set(base_data_directory.glob("Shard*.lean")) |
                set(target_replay_directory.glob("Shard*.lean")))
            extra = actual_shards - expected.keys()
            mismatches = [path for path, source in expected.items()
                          if not path.exists() or path.read_text() != source]
            if extra or mismatches:
                raise SystemExit("canonical direct generation differs:\n" + "\n".join(
                    str(path) for path in sorted(extra | set(mismatches))))
            print(f"checked {len(expected)} canonical direct sources: 188 entries, 47 shards per cover")
        else:
            for path, source in expected.items():
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source)
            print(f"wrote {len(expected)} canonical direct sources: 188 entries, 47 shards per cover")
        return
    if args.floor73_out_dir is not None or args.floor73_check_dir is not None:
        directory = (args.floor73_out_dir if args.floor73_out_dir is not None
                     else args.floor73_check_dir)
        assert directory is not None
        target_directory = directory / FLOOR73_NAMESPACE
        if args.floor73_out_dir is not None:
            target_directory.mkdir(parents=True, exist_ok=True)
        count = (len(ordered) + args.shard_size - 1) // args.shard_size
        expected = {
            target_directory / "Data.lean": emit_floor73_data_source(),
            **{
                target_directory / f"Shard{shard:02d}.lean":
                    emit_floor73_shard_source(shard)
                for shard in range(count)
            },
            directory / f"{FLOOR73_NAMESPACE}.lean":
                emit_floor73_aggregate_source(count),
        }
        if args.floor73_check_dir is not None:
            mismatches = [str(path) for path, source in expected.items()
                          if not path.exists() or path.read_text() != source]
            if mismatches:
                print("generated floor-73 files differ:", *mismatches,
                      sep="\n", file=sys.stderr)
                raise SystemExit(1)
            print(f"checked floor-73 data, {count} shards, and aggregate")
        else:
            for path, source in expected.items():
                path.write_text(source)
            print(f"wrote floor-73 data, {count} shards, and aggregate")
        return
    if args.out_dir is not None or args.check_dir is not None:
        directory = args.out_dir if args.out_dir is not None else args.check_dir
        assert directory is not None
        if args.out_dir is not None:
            directory.mkdir(parents=True, exist_ok=True)
        count = (len(ordered) + args.shard_size - 1) // args.shard_size
        expected = {
            directory / f"ConstantDirectCover128Shard{shard:02d}.lean":
                emit_shard_source(ordered, shard, args.shard_size, evaluated)
            for shard in range(count)
        }
        expected[directory / "ConstantDirectCover128Aggregate.lean"] = (
            emit_aggregate_source(count))
        expected[directory / "ConstantDirectCover128Selector.lean"] = (
            emit_tree_selector_source(ordered, args.shard_size))
        if args.check_dir is not None:
            mismatches = [str(path) for path, source in expected.items()
                          if not path.exists() or path.read_text() != source]
            if mismatches:
                print("generated files differ:", *mismatches, sep="\n", file=sys.stderr)
                raise SystemExit(1)
            print(f"checked {count} shards, aggregate, and selector")
        else:
            for path, source in expected.items():
                path.write_text(source)
            print(f"wrote {count} shards, aggregate, and selector")
        return
    if not args.all_shards and not args.selector and args.shard is None:
        print(f"evaluated {evaluated}")
        print(f"accepted {len(cells)}")
        print(f"worst {max(item[2] for item in cells):.12f}")
    if args.selector:
        print(emit_tree_selector_source(ordered, args.shard_size), end="")
    elif args.all_shards:
        count = (len(ordered) + args.shard_size - 1) // args.shard_size
        for shard in range(count):
            print(f"-- BEGIN-SHARD-{shard:02d}")
            print(emit_shard_source(ordered, shard, args.shard_size, evaluated), end="")
            print(f"-- END-SHARD-{shard:02d}")
    elif args.shard is not None:
        print(emit_shard_source(ordered, args.shard, args.shard_size, evaluated), end="")
    elif args.emit:
        for index, item in enumerate(ordered):
            print(emit_cell(index, item))
    else:
        for index, item in enumerate(sorted(cells, key=lambda x: x[2], reverse=True)[:20]):
            box, z, value, cert = item
            print(index, tuple(map(q, box)), q(modulus_lower(box[2])), q(z), value,
                  tuple(map(q, cert)))


if __name__ == "__main__":
    main()
