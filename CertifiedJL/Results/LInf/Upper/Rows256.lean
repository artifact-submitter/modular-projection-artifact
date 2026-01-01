/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.LInf.Upper.Matrix
import CertifiedJL.Projection.OneRow.BalancedTernary.CoefficientUniform

/-! # Certified 256-row balanced-ternary modular infinity upper tails -/

namespace CertifiedJL.Results.LInf.Upper.Rows256

/-- Balanced-ternary strict modular infinity upper tail at coordinate
threshold `(39/4) * ‖w‖₂`. The 141-bit coefficient-uniform one-row theorem
loses exactly eight bits across 256 rows. -/
theorem ternaryLInfUpper39Over4Bits133 :
    LInfUpperTailAt
      { distribution := .balancedTernary
        rows := 256
        coordinateThreshold :=
          { numerator := 39, denominator := 4, denominator_pos := by decide } }
      (failureTarget 133) := by
  apply LInfUpperTailAt.of_oneRow (rowBudget := failureTarget 141)
  · decide
  · simpa [NonnegativeRatio.toReal] using
      CertifiedJL.Projection.OneRow.BalancedTernary.CoefficientUniform.ternaryUpper39Over4
  · simpa using nsmul_failureTarget_add_le
      (shares := 256) (bits := 133) (slackBits := 8) (by decide)

/-- The 128-bit interface specialization, obtained from the primary 133-bit
matrix theorem solely by weakening the failure budget. -/
theorem ternaryLInfUpper39Over4 :
    LInfUpperTailAt
      { distribution := .balancedTernary
        rows := 256
        coordinateThreshold :=
          { numerator := 39, denominator := 4, denominator_pos := by decide } }
      (failureTarget 128) := by
  apply ternaryLInfUpper39Over4Bits133.mono_budget
  unfold failureTarget
  exact pow_le_pow_of_le_one (by positivity) (by norm_num) (by norm_num)

end CertifiedJL.Results.LInf.Upper.Rows256
