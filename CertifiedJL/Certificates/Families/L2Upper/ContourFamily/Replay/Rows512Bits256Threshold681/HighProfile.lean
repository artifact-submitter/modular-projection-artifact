/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! Independent kernel replay of the high-profile endpoint. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.HighProfile

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

def expectedBound : Interval (CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters).precision :=
  ⟨0,
      109916459032558373784754213578848241964728047083553262050232978514601692609541044113292723638050301129654047171565688798972978000105705454366021892195906⟩

theorem bound_eq_expected :
    highProfileBound CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.highProfile = expectedBound := by
  decide +kernel

private theorem expectedCheck_eq_true :
    Interval.upperLTCheck expectedBound CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.highProfile.target = true := by
  decide +kernel

theorem check_eq_true :
    highProfileCheck CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.highProfile = true := by
  rw [highProfileCheck, bound_eq_expected]
  exact expectedCheck_eq_true

theorem upperRat_lt :
    (highProfileBound CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.highProfile).upperRat < CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.highProfile.target :=
  Interval.upperLTCheck_sound check_eq_true

end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows512Bits256Threshold681.HighProfile
