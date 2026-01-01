/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509

/-! Independent kernel replay of the high-profile endpoint. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509.HighProfile

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

def expectedBound : Interval (CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters).precision :=
  ⟨0,
      1151347777280095923930100708921108150316268154360152454596231846699922951267990347187574738980883338372831559915788989233917028839793412219136584913594446⟩

theorem bound_eq_expected :
    highProfileBound CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.highProfile = expectedBound := by
  decide +kernel

private theorem expectedCheck_eq_true :
    Interval.upperLTCheck expectedBound CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.highProfile.target = true := by
  decide +kernel

theorem check_eq_true :
    highProfileCheck CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.highProfile = true := by
  rw [highProfileCheck, bound_eq_expected]
  exact expectedCheck_eq_true

theorem upperRat_lt :
    (highProfileBound CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.highProfile).upperRat < CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.highProfile.target :=
  Interval.upperLTCheck_sound check_eq_true

end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509.HighProfile
