/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.LInf.Upper.Elementary

/-! # Certified 512-row balanced-ternary modular tails at 256 bits -/

namespace CertifiedJL.Results.LInf.Upper.Rows512Bits256

/-- Elementary balanced-ternary modular infinity upper tail at the
two-decimal coordinate threshold `13.58 * ‖w‖₂`, with no modulus
restriction. -/
theorem ternaryLInfUpper1358Over100 :
    LInfUpperTailAt
      { distribution := .balancedTernary
        rows := 512
        coordinateThreshold :=
          { numerator := 1358, denominator := 100,
            denominator_pos := by decide } }
      (failureTarget 256) := by
  apply TernaryLInfUpperElementary.matrixUpperTailAt_of_two_mul_exp_neg_sq_lt
    (by decide) _ (by unfold failureTarget; finiteness)
  simpa [NonnegativeRatio.toReal] using
    TernaryLInfUpperElementary.two_mul_exp_neg_1358_over_100_sq_lt

end CertifiedJL.Results.LInf.Upper.Rows512Bits256
