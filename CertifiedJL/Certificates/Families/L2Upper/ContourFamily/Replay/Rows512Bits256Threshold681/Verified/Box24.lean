/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box24
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.Box24.Shard000
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.Box24.Shard001

/-! Kernel-checked assembly of upper-contour family box 24. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.Verified

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

private def box24EnumeratedComputedChunks :
    List (UpperContourKernel.DInterval (CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters).precision) :=
  [
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 24 default) ⟨0, 0, 25⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 24 default) ⟨1, 0, 10⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 24 default) ⟨2, 0, 5⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 24 default) ⟨3, 0, 3⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 24 default) ⟨4, 0, 3⟩
  ]

private theorem box24ComputedChunks_eq_enumerated :
    boxComputedChunks CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 24 default) =
      box24EnumeratedComputedChunks := by
  rfl

private theorem box24EnumeratedComputedChunks_eq_generated :
    box24EnumeratedComputedChunks = CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box24.chunks := by
  simp only [box24EnumeratedComputedChunks, CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box24.chunks,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.box_24_segment_00_chunk_000,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.box_24_segment_01_chunk_000,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.box_24_segment_02_chunk_000,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.box_24_segment_03_chunk_000,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.box_24_segment_04_chunk_000]

theorem box24ComputedChunks_eq_generated :
    boxComputedChunks CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 24 default) =
      CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box24.chunks :=
  box24ComputedChunks_eq_enumerated.trans
    box24EnumeratedComputedChunks_eq_generated

private theorem box24GeneratedBound_eq_expected :
    boxPrefactor CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 24 default) *
      boxIntegralFrom CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 24 default)
        CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box24.chunks = CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box24.expectedBound := by
  decide +kernel

theorem box24Bound_eq_expected :
    boxBound CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 24 default) =
      CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box24.expectedBound := by
  simp only [boxBound, boxIntegral, box24ComputedChunks_eq_generated]
  exact box24GeneratedBound_eq_expected

private theorem box24ExpectedCheck_eq_true :
    Interval.upperLTCheck CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box24.expectedBound
      (((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 24 default)).target = true := by
  decide +kernel

theorem box24Check_eq_true :
    boxCheck CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 24 default) = true := by
  rw [boxCheck, box24Bound_eq_expected]
  exact box24ExpectedCheck_eq_true

theorem box24_upperRat_lt :
    (boxBound CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 24 default)).upperRat <
      (((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 24 default)).target :=
  Interval.upperLTCheck_sound box24Check_eq_true

end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.Verified
