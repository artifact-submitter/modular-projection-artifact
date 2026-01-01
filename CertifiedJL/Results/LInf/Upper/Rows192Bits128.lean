/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.LInf.Upper.Matrix
import CertifiedJL.Projection.LInf.Upper.NinePointSevenFour

/-! # Certified 192-row balanced-ternary modular tails -/

namespace CertifiedJL.Results.LInf.Upper.Rows192Bits128

/-- Elementary balanced-ternary modular infinity upper tail at coordinate
threshold `9.74 * ‖w‖₂`, with no modulus restriction. -/
theorem ternaryLInfUpper487Over50 :
    LInfUpperTailAt
      { distribution := .balancedTernary
        rows := 192
        coordinateThreshold :=
          { numerator := 487, denominator := 50, denominator_pos := by decide } }
      (failureTarget 128) := by
  apply LInfUpperTailAt.of_oneRow
    (rowBudget := failureTarget 128 / (192 : ENNReal))
  · decide
  · simpa [NonnegativeRatio.toReal] using
      TernaryLInfUpperElementary.ternaryUpper487Over50Rows192Budget128
  · rw [nsmul_eq_mul]
    change (192 : ENNReal) * (failureTarget 128 / (192 : ENNReal)) ≤
      failureTarget 128
    rw [div_eq_mul_inv]
    calc
      (192 : ENNReal) * (failureTarget 128 * (192 : ENNReal)⁻¹) =
          failureTarget 128 * ((192 : ENNReal) * (192 : ENNReal)⁻¹) := by
        ac_rfl
      _ = failureTarget 128 := by
        rw [ENNReal.mul_inv_cancel (by norm_num) (by finiteness)]
        simp
    exact le_rfl

end CertifiedJL.Results.LInf.Upper.Rows192Bits128
