/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365

/-! Independent kernel replay of the high-profile endpoint. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365.HighProfile

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

def expectedBound : Interval (CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters).precision :=
  ⟨0,
      2189768231243869685270488003972440843470339342246036722134072183620218913019771685472854396481823008021255925026734502391005746094450819076701497888185211⟩

theorem bound_eq_expected :
    highProfileBound CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.highProfile = expectedBound := by
  decide +kernel

private theorem expectedCheck_eq_true :
    Interval.upperLTCheck expectedBound CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.highProfile.target = true := by
  decide +kernel

theorem check_eq_true :
    highProfileCheck CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.highProfile = true := by
  rw [highProfileCheck, bound_eq_expected]
  exact expectedCheck_eq_true

theorem upperRat_lt :
    (highProfileBound CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.highProfile).upperRat < CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.highProfile.target :=
  Interval.upperLTCheck_sound check_eq_true

end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365.HighProfile
