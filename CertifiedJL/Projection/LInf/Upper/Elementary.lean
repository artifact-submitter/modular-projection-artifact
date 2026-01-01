/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Interval.Reflection
import CertifiedJL.Probability.Distributions.Rademacher.RademacherSubgaussian
import CertifiedJL.Projection.LInf.Upper.Matrix

/-!
# Elementary balanced-ternary upper tails

The bounds here deliberately use only the exact duplicated-sign model and the
standard product-cosh subgaussian estimate. They are slightly weaker than the
certificate-optimized decimal frontier, but scale cheaply to higher security.
-/

open scoped ENNReal

namespace CertifiedJL
namespace TernaryLInfUpperElementary

open Probability

/-- A balanced-ternary row satisfies the usual two-sided subgaussian tail with
variance proxy `‖w‖² / 2`. -/
theorem row_tail_toReal_le_two_mul_exp_neg_sq
    {d : ℕ} (w : EuclideanSpace ℝ (Fin d)) (t : ℝ) (ht : 0 ≤ t) :
    (eventProbability (sparseRademacherRow d)
      (fun row => |euclideanRowDot row w| > t * ‖w‖)).toReal ≤
        2 * Real.exp (-(t ^ 2)) := by
  by_cases hw : w = 0
  · subst w
    simp only [euclideanRowDot_zero, abs_zero, norm_zero, mul_zero,
      gt_iff_lt, lt_self_iff_false, eventProbability_false,
      ENNReal.toReal_zero]
    positivity
  · have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hv : 0 < 2 * ‖w‖ ^ 2 :=
      mul_pos (by norm_num) (sq_pos_of_pos hn)
    have hevent :
        eventProbability (sparseRademacherRow d)
            (fun row => |euclideanRowDot row w| > t * ‖w‖) =
          eventProbability (sparseRademacherRow d)
            (fun row => |2 * euclideanRowDot row w| >
              (2 * t) * ‖w‖) := by
      apply eventProbability_congr
      intro row
      constructor <;> intro h
      · rw [abs_mul]
        norm_num
        nlinarith [norm_nonneg w]
      · rw [abs_mul] at h
        norm_num at h
        nlinarith [norm_nonneg w]
    rw [hevent,
      sparseRademacherRow_two_mul_probability_eq_rademacher]
    have htail :=
      rademacherSum_absTail_toReal_le_two_mul_exp_neg_sq_div_two
        (fun p : Fin d × Fin 2 => w p.1)
        (x := (2 * t) * ‖w‖) (variance := 2 * ‖w‖ ^ 2)
        (mul_nonneg (mul_nonneg (by norm_num) ht) (norm_nonneg w)) hv
        (sum_sq_duplicatedCoefficient_eq_two_mul_norm_sq w)
    have hexponent :
        -(((2 * t) * ‖w‖) ^ 2 / (2 * (2 * ‖w‖ ^ 2))) =
          -(t ^ 2) := by
      field_simp [hn.ne']
    simpa only [hexponent] using htail

/-- Turn the elementary real subgaussian estimate into a coefficient-uniform
one-row theorem at an arbitrary finite `ENNReal` budget. -/
theorem oneRowUpperTailAt_of_two_mul_exp_neg_sq_lt
    (threshold : ℝ) (hthreshold : 0 ≤ threshold)
    {budget : ENNReal} (hbudget : budget ≠ ⊤)
    (hbound : 2 * Real.exp (-(threshold ^ 2)) < budget.toReal) :
    OneRowUpperTailAt
      { distribution := .balancedTernary, threshold := threshold } budget := by
  intro d w
  apply (ENNReal.toReal_lt_toReal (PMF.apply_ne_top _ _) hbudget).mp
  exact (row_tail_toReal_le_two_mul_exp_neg_sq w threshold hthreshold).trans_lt
    hbound

/-- Equal-share matrix assembly for the elementary balanced-ternary
subgaussian estimate. The premise is the exact real inequality
`2 * exp (-threshold²) < totalBudget / rows`; no dyadic rounding of the
per-row budget is required. -/
theorem matrixUpperTailAt_of_two_mul_exp_neg_sq_lt
    {rows : ℕ} (hrows : 0 < rows)
    (threshold : NonnegativeRatio) {totalBudget : ENNReal}
    (htotal : totalBudget ≠ ⊤)
    (hbound :
      2 * Real.exp (-(threshold.toReal ^ 2)) <
        totalBudget.toReal / rows) :
    LInfUpperTailAt
      { distribution := .balancedTernary
        rows := rows
        coordinateThreshold := threshold }
      totalBudget := by
  apply LInfUpperTailAt.of_oneRow
    (rowBudget := totalBudget / (rows : ENNReal)) hrows
  · apply oneRowUpperTailAt_of_two_mul_exp_neg_sq_lt threshold.toReal
    · unfold NonnegativeRatio.toReal
      positivity
    · exact ENNReal.div_ne_top htotal (by
        exact_mod_cast hrows.ne')
    · simpa only [ENNReal.toReal_div, ENNReal.toReal_natCast] using hbound
  · simpa only [nsmul_eq_mul] using
      (ENNReal.mul_div_le (a := (rows : ENNReal)) (b := totalBudget))

private theorem exp_neg_lt {x u : ℚ} (hx : 0 ≤ x)
    (hcheck : Interval.upperLTCheck (Exp.negUpper 288 x 32) u = true) :
    Real.exp (-(x : ℝ)) < (u : ℝ) := by
  exact Interval.lt_of_contains_of_upperLTCheck
    (Exp.negUpper_contains (p := 288) (k := 32) (x := x) hx) hcheck

/-- Exact arithmetic premise for the 256-row, 192-bit elementary upper
bound at the two-decimal threshold `11.81`. -/
theorem two_mul_exp_neg_1181_over_100_sq_lt :
    2 * Real.exp (-((1181 / 100 : ℝ) ^ 2)) <
      (failureTarget 192).toReal / 256 := by
  have h := exp_neg_lt (x := 1394761 / 10000)
    (u := 1 / 2 ^ 201) (by norm_num) (by decide +kernel)
  calc
    2 * Real.exp (-((1181 / 100 : ℝ) ^ 2)) =
        2 * Real.exp (-(1394761 / 10000 : ℝ)) := by norm_num
    _ < 2 * (1 / 2 ^ 201 : ℝ) := by
      apply mul_lt_mul_of_pos_left _ (by norm_num)
      norm_num at h ⊢
      exact h
    _ = (failureTarget 192).toReal / 256 := by
      norm_num [failureTarget, zpow_neg]

/-- Exact arithmetic premise for the 384-row, 192-bit elementary upper
bound at the two-decimal threshold `11.83`. -/
theorem two_mul_exp_neg_1183_over_100_sq_lt :
    2 * Real.exp (-((1183 / 100 : ℝ) ^ 2)) <
      (failureTarget 192).toReal / 384 := by
  have h := exp_neg_lt (x := 1399489 / 10000)
    (u := 1 / (3 * 2 ^ 200)) (by norm_num) (by decide +kernel)
  calc
    2 * Real.exp (-((1183 / 100 : ℝ) ^ 2)) =
        2 * Real.exp (-(1399489 / 10000 : ℝ)) := by norm_num
    _ < 2 * (1 / (3 * 2 ^ 200) : ℝ) := by
      apply mul_lt_mul_of_pos_left _ (by norm_num)
      norm_num at h ⊢
      exact h
    _ = (failureTarget 192).toReal / 384 := by
      norm_num [failureTarget, zpow_neg]

/-- Exact arithmetic premise for the 512-row, 192-bit elementary upper
bound at the two-decimal threshold `11.84`. -/
theorem two_mul_exp_neg_1184_over_100_sq_lt :
    2 * Real.exp (-((1184 / 100 : ℝ) ^ 2)) <
      (failureTarget 192).toReal / 512 := by
  have h := exp_neg_lt (x := 1401856 / 10000)
    (u := 1 / 2 ^ 202) (by norm_num) (by decide +kernel)
  calc
    2 * Real.exp (-((1184 / 100 : ℝ) ^ 2)) =
        2 * Real.exp (-(1401856 / 10000 : ℝ)) := by norm_num
    _ < 2 * (1 / 2 ^ 202 : ℝ) := by
      apply mul_lt_mul_of_pos_left _ (by norm_num)
      norm_num at h ⊢
      exact h
    _ = (failureTarget 192).toReal / 512 := by
      norm_num [failureTarget, zpow_neg]

set_option exponentiation.threshold 1024 in
/-- Exact arithmetic premise for the 512-row, 256-bit elementary upper
bound at the two-decimal threshold `13.58`. -/
theorem two_mul_exp_neg_1358_over_100_sq_lt :
    2 * Real.exp (-((1358 / 100 : ℝ) ^ 2)) <
      (failureTarget 256).toReal / 512 := by
  have h := exp_neg_lt (x := 1844164 / 10000)
    (u := 1 / 2 ^ 266) (by norm_num) (by decide +kernel)
  calc
    2 * Real.exp (-((1358 / 100 : ℝ) ^ 2)) =
        2 * Real.exp (-(1844164 / 10000 : ℝ)) := by norm_num
    _ < 2 * (1 / 2 ^ 266 : ℝ) := by
      apply mul_lt_mul_of_pos_left _ (by norm_num)
      norm_num at h ⊢
      exact h
    _ = (failureTarget 256).toReal / 512 := by
      norm_num [failureTarget, zpow_neg]

end TernaryLInfUpperElementary
end CertifiedJL
