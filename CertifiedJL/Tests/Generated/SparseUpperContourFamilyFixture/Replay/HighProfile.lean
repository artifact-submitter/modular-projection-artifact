/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Tests.SparseUpperContourFamilyFixture

/-! Independent kernel replay of the high-profile endpoint. -/

namespace CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.HighProfile

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

def expectedBound : Interval (CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters).precision :=
  ⟨0,
      1⟩

theorem bound_eq_expected :
    highProfileBound CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters CertifiedJL.Tests.SparseUpperContourFamilyFixture.highProfile = expectedBound := by
  decide +kernel

private theorem expectedCheck_eq_true :
    Interval.upperLTCheck expectedBound CertifiedJL.Tests.SparseUpperContourFamilyFixture.highProfile.target = true := by
  decide +kernel

theorem check_eq_true :
    highProfileCheck CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters CertifiedJL.Tests.SparseUpperContourFamilyFixture.highProfile = true := by
  rw [highProfileCheck, bound_eq_expected]
  exact expectedCheck_eq_true

theorem upperRat_lt :
    (highProfileBound CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters CertifiedJL.Tests.SparseUpperContourFamilyFixture.highProfile).upperRat < CertifiedJL.Tests.SparseUpperContourFamilyFixture.highProfile.target :=
  Interval.upperLTCheck_sound check_eq_true

end CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.HighProfile
