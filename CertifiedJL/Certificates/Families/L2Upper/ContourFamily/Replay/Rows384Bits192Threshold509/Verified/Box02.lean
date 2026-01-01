/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box02
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509.Box02.Shard000
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509.Box02.Shard001
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509.Box02.Shard002

/-! Kernel-checked assembly of upper-contour family box 2. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509.Verified

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

private def box02EnumeratedComputedChunks :
    List (UpperContourKernel.DInterval (CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters).precision) :=
  [
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default) ⟨0, 0, 25⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default) ⟨0, 25, 25⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default) ⟨0, 50, 25⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default) ⟨0, 75, 25⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default) ⟨0, 100, 25⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default) ⟨0, 125, 25⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default) ⟨1, 0, 25⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default) ⟨1, 25, 25⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default) ⟨1, 50, 25⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default) ⟨2, 0, 20⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default) ⟨3, 0, 20⟩,
    boxChunkValue CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default) ⟨4, 0, 20⟩
  ]

private theorem box02ComputedChunks_eq_enumerated :
    boxComputedChunks CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default) =
      box02EnumeratedComputedChunks := by
  rfl

private theorem box02EnumeratedComputedChunks_eq_generated :
    box02EnumeratedComputedChunks = CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box02.chunks := by
  simp only [box02EnumeratedComputedChunks, CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box02.chunks,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509.box_02_segment_00_chunk_000,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509.box_02_segment_00_chunk_001,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509.box_02_segment_00_chunk_002,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509.box_02_segment_00_chunk_003,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509.box_02_segment_00_chunk_004,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509.box_02_segment_00_chunk_005,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509.box_02_segment_01_chunk_000,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509.box_02_segment_01_chunk_001,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509.box_02_segment_01_chunk_002,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509.box_02_segment_02_chunk_000,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509.box_02_segment_03_chunk_000,
    CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509.box_02_segment_04_chunk_000]

theorem box02ComputedChunks_eq_generated :
    boxComputedChunks CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default) =
      CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box02.chunks :=
  box02ComputedChunks_eq_enumerated.trans
    box02EnumeratedComputedChunks_eq_generated

private theorem box02GeneratedBound_eq_expected :
    boxPrefactor CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default) *
      boxIntegralFrom CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default)
        CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box02.chunks = CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box02.expectedBound := by
  decide +kernel

theorem box02Bound_eq_expected :
    boxBound CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default) =
      CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box02.expectedBound := by
  simp only [boxBound, boxIntegral, box02ComputedChunks_eq_generated]
  exact box02GeneratedBound_eq_expected

private theorem box02ExpectedCheck_eq_true :
    Interval.upperLTCheck CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Data.Rows384Bits192Threshold509.Box02.expectedBound
      (((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default)).target = true := by
  decide +kernel

theorem box02Check_eq_true :
    boxCheck CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default) = true := by
  rw [boxCheck, box02Bound_eq_expected]
  exact box02ExpectedCheck_eq_true

theorem box02_upperRat_lt :
    (boxBound CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters ((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default)).upperRat <
      (((CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes).getD 2 default)).target :=
  Interval.upperLTCheck_sound box02Check_eq_true

end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509.Verified
