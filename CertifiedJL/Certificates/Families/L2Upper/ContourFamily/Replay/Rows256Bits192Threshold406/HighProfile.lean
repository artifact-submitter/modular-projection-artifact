/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406

/-! Independent kernel replay of the high-profile endpoint. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406.HighProfile

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

def expectedBound : Interval (CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters).precision :=
  ⟨0,
      408754169457272983116042152198806511060253192490452332283724769530492334416757279695833962820744811793878001588309746151616092984795593935567482195104597⟩

theorem bound_eq_expected :
    highProfileBound CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.highProfile = expectedBound := by
  decide +kernel

private theorem expectedCheck_eq_true :
    Interval.upperLTCheck expectedBound CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.highProfile.target = true := by
  decide +kernel

theorem check_eq_true :
    highProfileCheck CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.highProfile = true := by
  rw [highProfileCheck, bound_eq_expected]
  exact expectedCheck_eq_true

theorem upperRat_lt :
    (highProfileBound CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.highProfile).upperRat < CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.highProfile.target :=
  Interval.upperLTCheck_sound check_eq_true

end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits192Threshold406.HighProfile
