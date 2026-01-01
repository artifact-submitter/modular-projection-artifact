/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-! Independent kernel replay of the high-profile endpoint. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.HighProfile

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

def expectedBound : Interval (CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters).precision :=
  ⟨0,
      4413857110147684838240957578414950906647515929772527949422151036276573081626117777222611014850199601642155630951598084546196261327201822514848804518282500⟩

theorem bound_eq_expected :
    highProfileBound CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.highProfile = expectedBound := by
  decide +kernel

private theorem expectedCheck_eq_true :
    Interval.upperLTCheck expectedBound CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.highProfile.target = true := by
  decide +kernel

theorem check_eq_true :
    highProfileCheck CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.highProfile = true := by
  rw [highProfileCheck, bound_eq_expected]
  exact expectedCheck_eq_true

theorem upperRat_lt :
    (highProfileBound CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.highProfile).upperRat < CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.highProfile.target :=
  Interval.upperLTCheck_sound check_eq_true

end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows192Bits128Threshold287.HighProfile
