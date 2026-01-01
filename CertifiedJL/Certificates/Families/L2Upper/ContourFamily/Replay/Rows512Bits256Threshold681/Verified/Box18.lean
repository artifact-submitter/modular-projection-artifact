/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box18
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.Box18.Shard000
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.Box18.Shard001

/-! Kernel-checked assembly of upper-contour family box 18. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.Verified

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

private def box18EnumeratedComputedChunks :
    List (UpperContourKernel.DInterval (CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters).precision) :=
  [
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 18 default) ⟨0, 0, 25⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 18 default) ⟨1, 0, 10⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 18 default) ⟨2, 0, 5⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 18 default) ⟨3, 0, 3⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 18 default) ⟨4, 0, 3⟩
  ]

private theorem box18ComputedChunks_eq_enumerated :
    boxComputedChunks CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 18 default) =
      box18EnumeratedComputedChunks := by
  rfl

private theorem box18EnumeratedComputedChunks_eq_generated :
    box18EnumeratedComputedChunks = CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box18.chunks := by
  simp only [box18EnumeratedComputedChunks, CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box18.chunks,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.box_18_segment_00_chunk_000,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.box_18_segment_01_chunk_000,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.box_18_segment_02_chunk_000,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.box_18_segment_03_chunk_000,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.box_18_segment_04_chunk_000]

theorem box18ComputedChunks_eq_generated :
    boxComputedChunks CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 18 default) =
      CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box18.chunks :=
  box18ComputedChunks_eq_enumerated.trans
    box18EnumeratedComputedChunks_eq_generated

private theorem box18GeneratedBound_eq_expected :
    boxPrefactor CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 18 default) *
      boxIntegralFrom CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 18 default)
        CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box18.chunks = CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box18.expectedBound := by
  decide +kernel

theorem box18Bound_eq_expected :
    boxBound CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 18 default) =
      CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box18.expectedBound := by
  simp only [boxBound, boxIntegral, box18ComputedChunks_eq_generated]
  exact box18GeneratedBound_eq_expected

private theorem box18ExpectedCheck_eq_true :
    Interval.upperLTCheck CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box18.expectedBound
      (((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 18 default)).target = true := by
  decide +kernel

theorem box18Check_eq_true :
    boxCheck CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 18 default) = true := by
  rw [boxCheck, box18Bound_eq_expected]
  exact box18ExpectedCheck_eq_true

theorem box18_upperRat_lt :
    (boxBound CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 18 default)).upperRat <
      (((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 18 default)).target :=
  Interval.upperLTCheck_sound box18Check_eq_true

end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.Verified
