/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Interval.Reflection
import CertifiedJL.Projection.LInf.Upper.Elementary

/-!
# A 192-row elementary upper-tail budget at threshold 9.74

This module keeps the fractional row budget needed at 192 rows.  Rounding the
one-row estimate down to a power of two loses too much: the elementary
subgaussian estimate is slightly stronger than 128 bits after the 192-way
union bound, but not strong enough to supply a full eighth slack bit.
-/

open scoped ENNReal

namespace CertifiedJL
namespace TernaryLInfUpperElementary

open Probability

private theorem exp_neg_lt {x u : ℚ} (hx : 0 ≤ x)
    (hcheck : Interval.upperLTCheck (Exp.negUpper 160 x 32) u = true) :
    Real.exp (-(x : ℝ)) < (u : ℝ) := by
  exact Interval.lt_of_contains_of_upperLTCheck
    (Exp.negUpper_contains (p := 160) (k := 32) (x := x) hx) hcheck

private theorem exp_neg_237169_div_2500_lt :
    Real.exp (-(237169 / 2500 : ℝ)) <
      (1 / (384 * 2 ^ 128) : ℚ) := by
  have h := exp_neg_lt
      (x := (237169 / 2500 : ℚ))
      (u := (1 / (384 * 2 ^ 128) : ℚ))
      (by norm_num) (by decide +kernel)
  convert h using 1
  · norm_num

private theorem two_mul_exp_neg_237169_div_2500_lt :
    2 * Real.exp (-(237169 / 2500 : ℝ)) <
      (2 : ℝ) ^ (-128 : ℤ) / 192 := by
  calc
    2 * Real.exp (-(237169 / 2500 : ℝ)) <
        2 * (1 / (384 * 2 ^ 128) : ℚ) := by
      gcongr
      exact exp_neg_237169_div_2500_lt
    _ = (2 : ℝ) ^ (-128 : ℤ) / 192 := by
      norm_num [zpow_neg]

/-- At threshold `9.74`, one balanced-ternary row fits one equal share of a
192-row, 128-bit failure budget. -/
theorem ternaryUpper487Over50Rows192Budget128 :
    OneRowUpperTailAt
      { distribution := .balancedTernary, threshold := 487 / 50 }
      (failureTarget 128 / (192 : ENNReal)) := by
  intro d w
  change eventProbability (sparseRademacherRow d)
    (fun row => |euclideanRowDot row w| > (487 / 50) * ‖w‖) <
      failureTarget 128 / (192 : ENNReal)
  have htail := row_tail_toReal_le_two_mul_exp_neg_sq w (487 / 50) (by norm_num)
  have hsq : -((487 / 50 : ℝ) ^ 2) = -(237169 / 2500 : ℝ) := by
    norm_num
  rw [hsq] at htail
  have hreal :
      (eventProbability (sparseRademacherRow d)
        (fun row => |euclideanRowDot row w| > (487 / 50) * ‖w‖)).toReal <
          (2 : ℝ) ^ (-128 : ℤ) / 192 :=
    htail.trans_lt two_mul_exp_neg_237169_div_2500_lt
  apply (ENNReal.toReal_lt_toReal
    (PMF.apply_ne_top _ _) (by unfold failureTarget; finiteness)).mp
  convert hreal using 1
  · rfl
  · norm_num [failureTarget, zpow_neg]

end TernaryLInfUpperElementary
end CertifiedJL
