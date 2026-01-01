/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.LInf.Upper.Matrix
import CertifiedJL.Projection.LInf.Upper.NinePointSevenFour

/-! # Assumption-backed 192-row specializations -/

namespace CertifiedJLFast.Results.LInf.Upper.Rows192Bits128

open scoped ENNReal

/-- Kernel-checked elementary `487/50` infinity upper tail. -/
theorem ternaryLInfUpper487Over50 :
    CertifiedJL.LInfUpperTailAt
      { distribution := .balancedTernary
        rows := 192
        coordinateThreshold :=
          { numerator := 487, denominator := 50, denominator_pos := by decide } }
      (CertifiedJL.failureTarget 128) := by
  apply CertifiedJL.LInfUpperTailAt.of_oneRow
    (rowBudget := CertifiedJL.failureTarget 128 / (192 : ENNReal))
  · decide
  · simpa [CertifiedJL.NonnegativeRatio.toReal] using
      CertifiedJL.TernaryLInfUpperElementary.ternaryUpper487Over50Rows192Budget128
  · rw [nsmul_eq_mul]
    change (192 : ENNReal) *
        (CertifiedJL.failureTarget 128 / (192 : ENNReal)) ≤
      CertifiedJL.failureTarget 128
    rw [div_eq_mul_inv]
    calc
      (192 : ENNReal) *
          (CertifiedJL.failureTarget 128 * (192 : ENNReal)⁻¹) =
          CertifiedJL.failureTarget 128 *
            ((192 : ENNReal) * (192 : ENNReal)⁻¹) := by
        ac_rfl
      _ = CertifiedJL.failureTarget 128 := by
        rw [ENNReal.mul_inv_cancel (by norm_num) (by finiteness)]
        simp
    exact le_rfl

end CertifiedJLFast.Results.LInf.Upper.Rows192Bits128
