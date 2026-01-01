#!/usr/bin/env python3
"""Generate sharded Lean replay facts for the compact sparse-upper hybrid.

The emitted endpoints are untrusted data.  Every chunk equality and final
strict comparison is replayed by Lean's kernel in the generated modules.
"""

from __future__ import annotations

import importlib.util
import pathlib
import sys
from fractions import Fraction as F


ROOT = pathlib.Path(__file__).resolve().parents[1]
EXPERIMENT = ROOT / "paper/experiments/sparse-upper-centered-hybrid/verify_centered_hybrid.py"
SPEC = importlib.util.spec_from_file_location("sparse_upper_hybrid_experiment", EXPERIMENT)
assert SPEC is not None and SPEC.loader is not None
EXP = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = EXP
SPEC.loader.exec_module(EXP)

# The experiment imports the shared exact U4 evaluator, whose standalone
# artifact defaults to 512 fractional bits.  This generator must instead use
# exactly the precision of `SparseUpperHybrid.precision` in Lean; otherwise it
# emits numerically valid intervals in the wrong dyadic representation and
# every generated kernel equality is false.
LEAN_PRECISION = 320
EXP.BASE.P = LEAN_PRECISION
EXP.BASE.SCALE = 1 << LEAN_PRECISION
EXP.BASE.ZERO = EXP.BASE.Interval.frac(0)
EXP.BASE.ONE = EXP.BASE.Interval.frac(1)
EXP.ZERO = EXP.BASE.ZERO
EXP.ONE = EXP.BASE.ONE


DENOMINATORS = EXP.COMMITTED_DENOMINATORS
ENDS = EXP.ENDS
CHUNK_SIZE = 10
SHARD_SIZE = 5
CHECK_ONLY = sys.argv[1:] == ["--check"]

if sys.argv[1:] not in ([], ["--check"]):
    raise SystemExit("usage: generate_sparse_upper_hybrid.py [--check]")


def segments(denominators: tuple[int, ...]):
    left = F(0)
    result = []
    for right_int, denominator in zip(ENDS, denominators, strict=True):
        right = F(right_int)
        mesh = F(1, denominator)
        count = int((right - left) / mesh)
        assert left + count * mesh == right
        result.append((left, mesh, count))
        left = right
    return result


def cell(box, left: F, mesh: F):
    right = left + mesh
    cap = EXP.BASE.real_cap_upper(box.profile_left, box.lam)
    expression_left = EXP.BASE.row_expression_on_cell(
        box.profile_left, left, right, box.lam
    )
    expression_right = EXP.BASE.row_expression_on_cell(
        box.profile_right, left, right, box.lam
    )
    row_upper = min(cap.hi, max(expression_left.hi, expression_right.hi))
    return (
        EXP.Interval.frac(mesh)
        * EXP.Interval(0, row_upper).pow_int(EXP.ROWS)
        * EXP.compact_noise_upper(box, left, right)
        * EXP.BASE.exp_neg_upper(
            EXP.GAUSSIAN_SIGMA**2 * left**2 / 2,
            24,
        )
        * EXP.BASE.inverse_sqrt_at_left(left, box.lam)
    )


def chunk_manifest(box_index: int):
    box = EXP.BOXES[box_index]
    manifest = []
    for segment_index, (start, mesh, count) in enumerate(
        segments(DENOMINATORS[box_index])
    ):
        for chunk_start in range(0, count, CHUNK_SIZE):
            chunk_count = min(CHUNK_SIZE, count - chunk_start)
            value = EXP.ZERO
            for offset in range(chunk_count):
                value += cell(box, start + (chunk_start + offset) * mesh, mesh)
            manifest.append((segment_index, chunk_start, chunk_count, value))
    return manifest


def interval_literal(value) -> str:
    return f"⟨{value.lo}, {value.hi}⟩"


def rat_literal(value: F) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator} / {value.denominator}"


def box_literal(box) -> str:
    return (
        "⟨"
        + ", ".join(
            (
                rat_literal(box.profile_left),
                rat_literal(box.profile_right),
                rat_literal(box.lam),
                str(box.count),
                rat_literal(box.half_width),
            )
        )
        + "⟩"
    )


def write(path: pathlib.Path, content: str) -> None:
    if CHECK_ONLY:
        if not path.is_file():
            raise SystemExit(f"missing generated file: {path.relative_to(ROOT)}")
        if path.read_text() != content:
            raise SystemExit(f"stale generated file: {path.relative_to(ROOT)}")
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content)


def emit_data(box_index: int, manifest) -> None:
    name = f"Box{box_index:02d}"
    values = ",\n    ".join(interval_literal(item[3]) for item in manifest)
    write(
        ROOT / f"CertifiedJL/Certificates/Families/L2Upper/Rows256Bits128/Data/{name}.lean",
        f'''/- Generated untrusted endpoints; replayed by Lean kernel shards. -/
import CertifiedJL.Arithmetic.Interval.Interval

namespace CertifiedJL.SparseUpperHybridGenerated.{name}

set_option linter.style.longLine false

def chunks : List (Interval 320) :=
  [ {values} ]

def chunk (index : ℕ) : Interval 320 := chunks.getD index ⟨0, 0⟩

end CertifiedJL.SparseUpperHybridGenerated.{name}
''',
    )


def emit_shards(box_index: int, manifest) -> int:
    name = f"Box{box_index:02d}"
    box = EXP.BOXES[box_index]
    segment_values = segments(DENOMINATORS[box_index])
    shard_count = (len(manifest) + SHARD_SIZE - 1) // SHARD_SIZE
    for shard_index in range(shard_count):
        items = manifest[shard_index * SHARD_SIZE : (shard_index + 1) * SHARD_SIZE]
        theorems = []
        for local_index, (segment_index, start, count, value) in enumerate(items):
            chunk_index = shard_index * SHARD_SIZE + local_index
            segment_start, segment_mesh, segment_count = segment_values[segment_index]
            segment_literal = (
                f"⟨{rat_literal(segment_start)}, {rat_literal(segment_mesh)}, "
                f"{segment_count}⟩"
            )
            theorems.append(
                f'''set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_{chunk_index:03d} :
    segmentChunk {box_literal(box)} {segment_literal} {start} {count} =
      SparseUpperHybridGenerated.{name}.chunk {chunk_index} := by
  change segmentChunk {box_literal(box)} {segment_literal} {start} {count} =
    {interval_literal(value)}
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_{chunk_index:03d}_sideCheck :
    segmentChunkSideCheck {box_literal(box)} {segment_literal} {start} {count} = true := by
  decide +kernel
'''
            )
        write(
            ROOT
            / f"CertifiedJL/Certificates/Families/L2Upper/Rows256Bits128/Replay/Shards/{name}/Shard{shard_index:02d}.lean",
            f'''import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.{name}
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.{name}

set_option linter.style.longLine false

{chr(10).join(theorems)}
end CertifiedJL.SparseUpperHybrid.Internal.{name}
''',
        )
    return shard_count


def emit_verified(box_index: int, manifest, shard_count: int) -> None:
    name = f"Box{box_index:02d}"
    box = EXP.BOXES[box_index]
    segment_values = segments(DENOMINATORS[box_index])
    imports = "\n".join(
        f"import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Shards.{name}.Shard{i:02d}"
        for i in range(shard_count)
    )
    rewrites = ",\n    ".join(
        f"Internal.{name}.chunk_{i:03d}" for i in range(len(manifest))
    )
    plan_values = ",\n    ".join(
        f"⟨{segment_index}, {start}, {count}⟩"
        for segment_index, start, count, _value in manifest
    )
    generated_segments = ",\n      ".join(
        f"⟨{rat_literal(start)}, {rat_literal(mesh)}, {count}⟩"
        for start, mesh, count in segment_values
    )
    chunks_by_segment = {index: [] for index in range(len(segment_values))}
    for chunk_index, (segment_index, start, count, _value) in enumerate(manifest):
        chunks_by_segment[segment_index].append((chunk_index, start, count))
    range_declarations = []
    side_branches = []
    for segment_index, (segment_start, segment_mesh, segment_count) in enumerate(
        segment_values
    ):
        chunks = chunks_by_segment[segment_index]
        range_name = f"segment{segment_index}_chunkRanges"
        range_values = ", ".join(f"({start}, {count})" for _, start, count in chunks)
        side_proofs = ",\n    ".join(
            [
                f"Internal.{name}.chunk_{chunk_index:03d}_sideCheck"
                for chunk_index, _start, _count in chunks
            ]
            + ["True.intro"]
        )
        side_check_proof = (
            f'''by
  simp only [{range_name}, List.all_cons, List.all_nil, Bool.and_eq_true]
  exact ⟨{side_proofs}⟩'''
            if chunks
            else "by rfl"
        )
        segment_literal = (
            f"⟨{rat_literal(segment_start)}, {rat_literal(segment_mesh)}, "
            f"{segment_count}⟩"
        )
        range_declarations.append(
            f'''private def {range_name} : List (ℕ × ℕ) :=
  [ {range_values} ]

private theorem {range_name}_cover :
    chunkRangesCover {segment_count} {range_name} = true := by
  decide +kernel

private theorem {range_name}_sideChecks :
    {range_name}.all (fun chunk =>
      segmentChunkSideCheck {box_literal(box)} {segment_literal}
        chunk.1 chunk.2) = true := {side_check_proof}
'''
        )
        side_branches.append(
            f'''  · exact segmentSideChecks_of_chunkRanges _ _ {range_name}
      {range_name}_cover {range_name}_sideChecks i hi'''
        )
    range_declaration_proof = "\n".join(range_declarations)
    side_branch_proof = "\n".join(side_branches)
    write(
        ROOT / f"CertifiedJL/Certificates/Families/L2Upper/Rows256Bits128/Replay/Verified/{name}.lean",
        f'''{imports}

namespace CertifiedJL.SparseUpperHybrid

open UpperContourKernel

private def certificate : CertificateBox := certificateBoxes.getD {box_index} default

private def generatedCertificate : CertificateBox :=
  ⟨{box_literal(box)},
    [ {generated_segments} ]⟩

private theorem certificate_eq_generated :
    certificate = generatedCertificate := by
  decide +kernel

private def generatedPlan : List Chunk :=
  [ {plan_values} ]

private theorem chunkPlan_eq_generated :
    certificateChunkPlan certificate = generatedPlan := by
  decide +kernel

private theorem computedChunks_eq_generated :
    (certificateChunkPlan certificate).map (certificateChunkValue certificate) =
      SparseUpperHybridGenerated.{name}.chunks := by
  rw [chunkPlan_eq_generated, certificate_eq_generated]
  simp only [generatedPlan, generatedCertificate, certificateChunkValue,
    List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
  rw [{rewrites}]
  norm_num [SparseUpperHybridGenerated.{name}.chunk,
    SparseUpperHybridGenerated.{name}.chunks]
  rfl

{range_declaration_proof}

theorem certificate_{box_index:02d}_finiteTail_lo_eq_zero :
    (finiteIntegralFrom
      ((certificateChunkPlan (certificateBoxes.getD {box_index} default)).map
        (certificateChunkValue (certificateBoxes.getD {box_index} default))) +
      tail (certificateBoxes.getD {box_index} default).box).lo = 0 := by
  change (finiteIntegralFrom
    ((certificateChunkPlan certificate).map (certificateChunkValue certificate)) +
      tail certificate.box).lo = 0
  rw [computedChunks_eq_generated, certificate_eq_generated]
  decide +kernel

theorem certificate_{box_index:02d}_finiteTail_nonneg :
    0 ≤ (finiteIntegralFrom
      ((certificateChunkPlan (certificateBoxes.getD {box_index} default)).map
        (certificateChunkValue (certificateBoxes.getD {box_index} default))) +
      tail (certificateBoxes.getD {box_index} default).box).lo := by
  rw [certificate_{box_index:02d}_finiteTail_lo_eq_zero]

theorem certificate_{box_index:02d}_finiteTail_valid :
    (finiteIntegralFrom
      ((certificateChunkPlan (certificateBoxes.getD {box_index} default)).map
        (certificateChunkValue (certificateBoxes.getD {box_index} default))) +
      tail (certificateBoxes.getD {box_index} default).box).Valid := by
  change (finiteIntegralFrom
    ((certificateChunkPlan certificate).map (certificateChunkValue certificate)) +
      tail certificate.box).Valid
  rw [computedChunks_eq_generated, certificate_eq_generated]
  change (finiteIntegralFrom SparseUpperHybridGenerated.{name}.chunks +
      tail generatedCertificate.box).lo ≤
    (finiteIntegralFrom SparseUpperHybridGenerated.{name}.chunks +
      tail generatedCertificate.box).hi
  decide +kernel

set_option maxRecDepth 10000 in
theorem certificate_{box_index:02d}_sideChecks :
    ∀ segment ∈ (certificateBoxes.getD {box_index} default).segments,
      ∀ i < segment.count,
        hybridCellSideCheck (certificateBoxes.getD {box_index} default).box
          segment i = true := by
  change ∀ segment ∈ certificate.segments, ∀ i < segment.count,
    hybridCellSideCheck certificate.box segment i = true
  rw [certificate_eq_generated]
  intro segment hsegment i hi
  norm_num [generatedCertificate] at hsegment
  rcases hsegment with rfl | rfl | rfl | rfl | rfl
{side_branch_proof}

private def generatedBound : DInterval precision :=
  boxBoundFrom certificate.box SparseUpperHybridGenerated.{name}.chunks

private theorem generatedCheck :
    Interval.upperLTCheck generatedBound 1 = true := by
  decide +kernel

theorem certificate_{box_index:02d}_upperRat_lt :
    (certificateBound (certificateBoxes.getD {box_index} default)).upperRat < 1 := by
  have hbound : certificateBound certificate = generatedBound := by
    simp only [certificateBound, generatedBound,
      computedChunks_eq_generated]
  have hcheck := generatedCheck
  rw [← hbound] at hcheck
  exact Interval.upperLTCheck_sound hcheck

end CertifiedJL.SparseUpperHybrid
''',
    )



def emit_hyperbolic_checks() -> None:
    theorems = []
    for box_index, box in enumerate(EXP.BOXES):
        argument = box.half_width * box.lam
        sinh_value = EXP.sinh_upper(argument)
        cosh_value = EXP.cosh_upper(argument)
        theorems.append(
            f'''theorem box{box_index:02d}_sinhUpper :
    sinhUpper ({rat_literal(argument)}) = {rat_literal(sinh_value)} := by
  decide +kernel

theorem box{box_index:02d}_coshUpperScalar :
    coshUpper ({rat_literal(argument)}) = {rat_literal(cosh_value)} := by
  decide +kernel

theorem box{box_index:02d}_sinh_le :
    Real.sinh ((({rat_literal(argument)} : ℚ) : ℝ)) ≤
      (sinhUpper ({rat_literal(argument)}) : ℝ) := by
  rw [Real.sinh_eq]
  have hp := Real.exp_bound (x := ({rat_literal(argument)} : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -({rat_literal(argument)} : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).1
  rw [box{box_index:02d}_sinhUpper]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith

theorem box{box_index:02d}_cosh_le :
    Real.cosh ((({rat_literal(argument)} : ℚ) : ℝ)) ≤
      (coshUpper ({rat_literal(argument)}) : ℝ) := by
  rw [Real.cosh_eq]
  have hp := Real.exp_bound (x := ({rat_literal(argument)} : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hn := Real.exp_bound (x := -({rat_literal(argument)} : ℝ))
    (n := 25) (by norm_num) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).2
  rw [box{box_index:02d}_coshUpperScalar]
  norm_num [Finset.sum_range_succ] at hp' hn' ⊢
  linarith
'''
        )
    write(
        ROOT / "CertifiedJL/Certificates/Families/L2Upper/Rows256Bits128/Soundness/HyperbolicChecks.lean",
        f'''/- Generated exact scalar checks; replayed by Lean's kernel. -/
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.Core
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

namespace CertifiedJL.SparseUpperHybrid.HyperbolicChecks

set_option linter.style.longLine false

{chr(10).join(theorems)}
end CertifiedJL.SparseUpperHybrid.HyperbolicChecks
''',
    )


def main() -> None:
    total_chunks = 0
    expected_shards: set[pathlib.Path] = set()
    for box_index in range(len(EXP.BOXES)):
        manifest = chunk_manifest(box_index)
        total_chunks += len(manifest)
        emit_data(box_index, manifest)
        shard_count = emit_shards(box_index, manifest)
        name = f"Box{box_index:02d}"
        expected_shards.update(
            ROOT
            / "CertifiedJL/Certificates/Families/L2Upper/Rows256Bits128/Replay/Shards"
            / name
            / f"Shard{shard_index:02d}.lean"
            for shard_index in range(shard_count)
        )
        emit_verified(box_index, manifest, shard_count)
        print(
            f"box={box_index:02d} chunks={len(manifest)} shards={shard_count}"
        )
    shard_root = (
        ROOT
        / "CertifiedJL/Certificates/Families/L2Upper/Rows256Bits128/Replay/Shards"
    )
    actual_shards = set(shard_root.glob("Box*/Shard*.lean"))
    stale_shards = sorted(actual_shards - expected_shards)
    if CHECK_ONLY and stale_shards:
        names = ", ".join(str(path.relative_to(ROOT)) for path in stale_shards)
        raise SystemExit(f"unexpected stale generated shards: {names}")
    for path in stale_shards:
        path.unlink()
    assert total_chunks == 523
    print(f"total chunks={total_chunks}")
    if stale_shards:
        print(f"removed stale shards={len(stale_shards)}")


if __name__ == "__main__":
    main()
