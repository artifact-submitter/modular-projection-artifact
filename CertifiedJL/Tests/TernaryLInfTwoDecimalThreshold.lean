/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.LInf.Lower.BalancedTernary.FortySevenHundredthsTwoDecimal
import CertifiedJL.Projection.LInf.Lower.BalancedTernary.SixTwentyFifthsTwoDecimal
import CertifiedJL.Projection.LInf.Lower.BalancedTernary.TwentyOneFiftiethTwoDecimal

/-! # Regression canaries for the two-decimal ternary infinity frontiers -/

namespace CertifiedJL.Tests.TernaryLInfTwoDecimalThreshold

open TrigonometricBernstein

example : 0 ≤ rationalPowerValue
    TernaryLInfTwoDecimal.Cap42Tail.tailPower 6 :=
  TernaryLInfTwoDecimal.Cap42Tail.nonnegativeAbove (by norm_num)

example : 0 ≤ rationalPowerValue
    TernaryLInfTwoDecimal.Cap42Tail.tailPower 16 :=
  TernaryLInfTwoDecimal.Cap42Tail.nonnegativeAbove (by norm_num)

example : 0 ≤ rationalPowerValue
    TernaryLInfTwoDecimal.Cap42Tail.tailPower 17 :=
  TernaryLInfTwoDecimal.Cap42Tail.nonnegativeAbove (by norm_num)

example : 0 ≤ rationalPowerValue
    TernaryLInfTwoDecimal.Cap47Tail.tailPower (55589 / 10000 : ℝ) := by
  apply TernaryLInfTwoDecimal.Cap47Tail.nonnegativeAbove
  norm_num

example : 0 ≤ rationalPowerValue
    TernaryLInfTwoDecimal.Cap47Tail.tailPower 16 :=
  TernaryLInfTwoDecimal.Cap47Tail.nonnegativeAbove (by norm_num)

example : 0 ≤ rationalPowerValue
    TernaryLInfTwoDecimal.Cap47Tail.tailPower 17 :=
  TernaryLInfTwoDecimal.Cap47Tail.nonnegativeAbove (by norm_num)

example : (389 / 50 : ℝ) < 62094368 / 7980625 := by norm_num

example : (55589 / 10000 : ℝ) < 608535727569 / 109465205000 := by
  norm_num

set_option maxRecDepth 100000

example {rows d q inputThreshold : ℕ} (w : Fin d → ℤ)
    (J : Matrix (Fin rows) (Fin d) ℤ) :
    LInfThresholdSmallProjection
        (TernaryLInfThresholdLower6Over25TwoDecimal.parametersAt rows)
        inputThreshold q w J ↔
      ∀ j, 625 * (centeredMod q (rowDot J w j)).natAbs ^ 2 ≤
        36 * inputThreshold ^ 2 := by
  simp [LInfThresholdSmallProjection,
    TernaryLInfThresholdLower6Over25TwoDecimal.parametersAt, rowDot]

example {rows d q inputThreshold : ℕ} (w : Fin d → ℤ)
    (J : Matrix (Fin rows) (Fin d) ℤ) :
    LInfThresholdSmallProjection
        (TernaryLInfThresholdLower21Over50TwoDecimal.parametersAt rows)
        inputThreshold q w J ↔
      ∀ j, 2500 * (centeredMod q (rowDot J w j)).natAbs ^ 2 ≤
        441 * inputThreshold ^ 2 := by
  simp [LInfThresholdSmallProjection,
    TernaryLInfThresholdLower21Over50TwoDecimal.parametersAt, rowDot]

example {rows d q inputThreshold : ℕ} (w : Fin d → ℤ)
    (J : Matrix (Fin rows) (Fin d) ℤ) :
    LInfThresholdSmallProjection
        (TernaryLInfThresholdLower47Over100TwoDecimal.parametersAt rows)
        inputThreshold q w J ↔
      ∀ j, 10000 * (centeredMod q (rowDot J w j)).natAbs ^ 2 ≤
        2209 * inputThreshold ^ 2 := by
  simp [LInfThresholdSmallProjection,
    TernaryLInfThresholdLower47Over100TwoDecimal.parametersAt, rowDot]

set_option maxRecDepth 1000

#print axioms SparseLInfLowerTwoDecimal.radMoment_eight_le_gaussian
#print axioms SparseLInfLowerTwoDecimal.rademacherSum_normalized_tail_389_over_50_toReal_lt_fintype
#print axioms TernaryLInfTwoDecimal.Cap42Tail.nonnegativeAbove
#print axioms TernaryLInfTwoDecimal.Cap47Tail.nonnegativeAbove
#print axioms TernaryLInfThresholdLower6Over25TwoDecimal.rowBound_pow_rows256_bits197
#print axioms TernaryLInfThresholdLower21Over50TwoDecimal.rowBound_pow_rows512_bits266
#print axioms TernaryLInfThresholdLower47Over100TwoDecimal.rowBound_pow_rows512_bits206

end CertifiedJL.Tests.TernaryLInfTwoDecimalThreshold
