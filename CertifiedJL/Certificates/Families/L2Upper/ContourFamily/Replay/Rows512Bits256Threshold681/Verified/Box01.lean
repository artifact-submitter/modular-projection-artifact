/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box01
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.Box01.Shard000
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.Box01.Shard001

/-! Kernel-checked assembly of upper-contour family box 1. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.Verified

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

private def box01EnumeratedComputedChunks :
    List (UpperContourKernel.DInterval (CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters).precision) :=
  [
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 1 default) ⟨0, 0, 25⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 1 default) ⟨1, 0, 10⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 1 default) ⟨2, 0, 5⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 1 default) ⟨3, 0, 3⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 1 default) ⟨4, 0, 3⟩
  ]

private theorem box01ComputedChunks_eq_enumerated :
    boxComputedChunks CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 1 default) =
      box01EnumeratedComputedChunks := by
  rfl

private theorem box01EnumeratedComputedChunks_eq_generated :
    box01EnumeratedComputedChunks = CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box01.chunks := by
  simp only [box01EnumeratedComputedChunks, CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box01.chunks,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.box_01_segment_00_chunk_000,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.box_01_segment_01_chunk_000,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.box_01_segment_02_chunk_000,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.box_01_segment_03_chunk_000,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.box_01_segment_04_chunk_000]

theorem box01ComputedChunks_eq_generated :
    boxComputedChunks CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 1 default) =
      CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box01.chunks :=
  box01ComputedChunks_eq_enumerated.trans
    box01EnumeratedComputedChunks_eq_generated

private theorem box01GeneratedBound_eq_expected :
    boxPrefactor CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 1 default) *
      boxIntegralFrom CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 1 default)
        CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box01.chunks = CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box01.expectedBound := by
  decide +kernel

theorem box01Bound_eq_expected :
    boxBound CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 1 default) =
      CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box01.expectedBound := by
  simp only [boxBound, boxIntegral, box01ComputedChunks_eq_generated]
  exact box01GeneratedBound_eq_expected

private theorem box01ExpectedCheck_eq_true :
    Interval.upperLTCheck CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box01.expectedBound
      (((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 1 default)).target = true := by
  decide +kernel

theorem box01Check_eq_true :
    boxCheck CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 1 default) = true := by
  rw [boxCheck, box01Bound_eq_expected]
  exact box01ExpectedCheck_eq_true

theorem box01_upperRat_lt :
    (boxBound CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 1 default)).upperRat <
      (((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 1 default)).target :=
  Interval.upperLTCheck_sound box01Check_eq_true

end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.Verified
