/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Box00
import CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.Box00.Shard000

/-! Kernel-checked assembly of upper-contour family box 0. -/

namespace CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.Verified

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

private def box00EnumeratedComputedChunks :
    List (UpperContourKernel.DInterval (CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters).precision) :=
  [
    boxChunkValue CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 0 default) ⟨0, 0, 1⟩,
    boxChunkValue CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 0 default) ⟨0, 1, 1⟩
  ]

private theorem box00ComputedChunks_eq_enumerated :
    boxComputedChunks CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 0 default) =
      box00EnumeratedComputedChunks := by
  rfl

private theorem box00EnumeratedComputedChunks_eq_generated :
    box00EnumeratedComputedChunks = CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Box00.chunks := by
  simp only [box00EnumeratedComputedChunks, CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Box00.chunks,
    CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.box_00_segment_00_chunk_000,
    CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.box_00_segment_00_chunk_001]

theorem box00ComputedChunks_eq_generated :
    boxComputedChunks CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 0 default) =
      CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Box00.chunks :=
  box00ComputedChunks_eq_enumerated.trans
    box00EnumeratedComputedChunks_eq_generated

private theorem box00GeneratedBound_eq_expected :
    boxPrefactor CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 0 default) *
      boxIntegralFrom CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 0 default)
        CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Box00.chunks = CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Box00.expectedBound := by
  decide +kernel

theorem box00Bound_eq_expected :
    boxBound CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 0 default) =
      CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Box00.expectedBound := by
  simp only [boxBound, boxIntegral, box00ComputedChunks_eq_generated]
  exact box00GeneratedBound_eq_expected

private theorem box00ExpectedCheck_eq_true :
    Interval.upperLTCheck CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Box00.expectedBound
      (((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 0 default)).target = true := by
  decide +kernel

theorem box00Check_eq_true :
    boxCheck CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 0 default) = true := by
  rw [boxCheck, box00Bound_eq_expected]
  exact box00ExpectedCheck_eq_true

theorem box00_upperRat_lt :
    (boxBound CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 0 default)).upperRat <
      (((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 0 default)).target :=
  Interval.upperLTCheck_sound box00Check_eq_true

end CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.Verified
