/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Data
import CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.Verified.Box00
import CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.Verified.Box01
import CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.HighProfile

/-! Aggregate kernel-verified endpoints for one upper-contour family instance. -/

namespace CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.Verified

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

def verifiedEndpoints :
    List (UpperContourKernel.DInterval (CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters).precision) :=
  CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Data.expectedBounds

theorem boxBounds_eq_verifiedEndpoints :
    (CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).map (boxBound CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters) =
      verifiedEndpoints := by
  change [
    boxBound CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 0 default),
    boxBound CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 1 default)
  ] = [
    CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Box00.expectedBound,
    CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Data.Box01.expectedBound
  ]
  rw [CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.Verified.box00Bound_eq_expected,
    CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.Verified.box01Bound_eq_expected]

theorem allBoxesCheck_eq_true :
    allBoxesCheck CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes = true := by
  change ([
    boxCheck CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 0 default),
    boxCheck CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters ((CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes).getD 1 default)
  ]).all id = true
  simp only [CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.Verified.box00Check_eq_true,
    CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.Verified.box01Check_eq_true]
  rfl

theorem box_upperRat_lt_target {box : ProfileBox}
    (hbox : box ∈ CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes) :
    (boxBound CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters box).upperRat < box.target := by
  simp only [CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes, List.mem_cons, List.not_mem_nil,
    or_false] at hbox
  rcases hbox with rfl | rfl
  · simpa [CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes] using box00_upperRat_lt
  · simpa [CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes] using box01_upperRat_lt

theorem highProfileCheck_eq_true :
    highProfileCheck CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters CertifiedJL.Tests.SparseUpperContourFamilyFixture.highProfile = true :=
  CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.HighProfile.check_eq_true

theorem highProfile_upperRat_lt :
    (highProfileBound CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters CertifiedJL.Tests.SparseUpperContourFamilyFixture.highProfile).upperRat <
      CertifiedJL.Tests.SparseUpperContourFamilyFixture.highProfile.target :=
  CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.HighProfile.upperRat_lt

end CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.Verified
