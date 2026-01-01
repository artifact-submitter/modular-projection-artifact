/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Box01
import CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.Box01.Shard000
import CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.Box01.Shard001

/-! Kernel-checked assembly of upper-contour family box 1. -/

namespace CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.Verified

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

private def box01EnumeratedComputedChunks :
    List (UpperContourKernel.DInterval (CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters).precision) :=
  [
    boxChunkValue CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 1 default) ⟨0, 0, 1⟩,
    boxChunkValue CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 1 default) ⟨1, 0, 2⟩,
    boxChunkValue CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 1 default) ⟨1, 2, 1⟩
  ]

private theorem box01ComputedChunks_eq_enumerated :
    boxComputedChunks CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 1 default) =
      box01EnumeratedComputedChunks := by
  rfl

private theorem box01EnumeratedComputedChunks_eq_generated :
    box01EnumeratedComputedChunks = CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Box01.chunks := by
  simp only [box01EnumeratedComputedChunks, CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Box01.chunks,
    CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.box_01_segment_00_chunk_000,
    CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.box_01_segment_01_chunk_000,
    CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.box_01_segment_01_chunk_001]

theorem box01ComputedChunks_eq_generated :
    boxComputedChunks CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 1 default) =
      CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Box01.chunks :=
  box01ComputedChunks_eq_enumerated.trans
    box01EnumeratedComputedChunks_eq_generated

private theorem box01GeneratedBound_eq_expected :
    boxPrefactor CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 1 default) *
      boxIntegralFrom CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 1 default)
        CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Box01.chunks = CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Box01.expectedBound := by
  decide +kernel

theorem box01Bound_eq_expected :
    boxBound CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 1 default) =
      CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Box01.expectedBound := by
  simp only [boxBound, boxIntegral, box01ComputedChunks_eq_generated]
  exact box01GeneratedBound_eq_expected

private theorem box01ExpectedCheck_eq_true :
    Interval.upperLTCheck CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Box01.expectedBound
      (((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 1 default)).target = true := by
  decide +kernel

theorem box01Check_eq_true :
    boxCheck CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 1 default) = true := by
  rw [boxCheck, box01Bound_eq_expected]
  exact box01ExpectedCheck_eq_true

theorem box01_upperRat_lt :
    (boxBound CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 1 default)).upperRat <
      (((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 1 default)).target :=
  Interval.upperLTCheck_sound box01Check_eq_true

end CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.Verified
