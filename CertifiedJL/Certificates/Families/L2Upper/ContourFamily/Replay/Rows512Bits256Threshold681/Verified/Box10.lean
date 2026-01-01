/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box10
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.Box10.Shard000
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.Box10.Shard001

/-! Kernel-checked assembly of upper-contour family box 10. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.Verified

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

private def box10EnumeratedComputedChunks :
    List (UpperContourKernel.DInterval (CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters).precision) :=
  [
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 10 default) ⟨0, 0, 25⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 10 default) ⟨1, 0, 10⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 10 default) ⟨2, 0, 5⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 10 default) ⟨3, 0, 3⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 10 default) ⟨4, 0, 3⟩
  ]

private theorem box10ComputedChunks_eq_enumerated :
    boxComputedChunks CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 10 default) =
      box10EnumeratedComputedChunks := by
  rfl

private theorem box10EnumeratedComputedChunks_eq_generated :
    box10EnumeratedComputedChunks = CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box10.chunks := by
  simp only [box10EnumeratedComputedChunks, CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box10.chunks,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.box_10_segment_00_chunk_000,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.box_10_segment_01_chunk_000,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.box_10_segment_02_chunk_000,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.box_10_segment_03_chunk_000,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.box_10_segment_04_chunk_000]

theorem box10ComputedChunks_eq_generated :
    boxComputedChunks CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 10 default) =
      CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box10.chunks :=
  box10ComputedChunks_eq_enumerated.trans
    box10EnumeratedComputedChunks_eq_generated

private theorem box10GeneratedBound_eq_expected :
    boxPrefactor CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 10 default) *
      boxIntegralFrom CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 10 default)
        CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box10.chunks = CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box10.expectedBound := by
  decide +kernel

theorem box10Bound_eq_expected :
    boxBound CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 10 default) =
      CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box10.expectedBound := by
  simp only [boxBound, boxIntegral, box10ComputedChunks_eq_generated]
  exact box10GeneratedBound_eq_expected

private theorem box10ExpectedCheck_eq_true :
    Interval.upperLTCheck CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows512Bits256Threshold681.Box10.expectedBound
      (((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 10 default)).target = true := by
  decide +kernel

theorem box10Check_eq_true :
    boxCheck CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 10 default) = true := by
  rw [boxCheck, box10Bound_eq_expected]
  exact box10ExpectedCheck_eq_true

theorem box10_upperRat_lt :
    (boxBound CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 10 default)).upperRat <
      (((CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes).getD 10 default)).target :=
  Interval.upperLTCheck_sound box10Check_eq_true

end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.Verified
