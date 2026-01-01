/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Activity
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Assembly

/-! # Budget split for 512 rows, squared-norm floor 71, and 192 bits -/

open scoped ENNReal

namespace CertifiedJL.Threshold512Bits192

noncomputable def lowActivityBudget : ENNReal :=
  (1 : ENNReal) / 100 * failureTarget 192

noncomputable def highActivityBudget : ENNReal :=
  (99 : ENNReal) / 100 * failureTarget 192

noncomputable def config : ThresholdTailConfig where
  rows := 512
  squaredNormFloor := 71
  bits := 192
  lowBudget := lowActivityBudget
  highBudget := highActivityBudget

theorem budgets_add :
    lowActivityBudget + highActivityBudget = failureTarget 192 := by
  unfold lowActivityBudget highActivityBudget
  rw [← add_mul]
  rw [show (1 : ENNReal) / 100 + 99 / 100 = 1 by
    change (1 : ENNReal) * 100⁻¹ + (99 : ENNReal) * 100⁻¹ = 1
    rw [← add_mul]
    norm_num only [OfNat.ofNat, Nat.cast_ofNat]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  simp

private theorem binomial512_prefix71_scaled :
    100 * (∑ k ∈ Finset.range 71, (512 : ℕ).choose k) * 2 ^ 192 <
      2 ^ 512 := by
  set_option maxRecDepth 10000 in
    decide +kernel

/-- Exact counting places K < 71 below 1/100 of the 192-bit budget. -/
theorem lowActivity
    {d : ℕ} (i : Fin d) :
    eventProbability (sparseRademacherMatrix 512 d)
        (fun J =>
          (dominantActivityCount (matrixDominantActivity i J) : ℕ) < 71) <
      lowActivityBudget := by
  rw [sparse_dominantActivityCount_lt_probability_eq_at 512 i 71]
  unfold lowActivityBudget failureTarget
  set_option maxRecDepth 10000 in
    rw [← ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)]
  repeat' rw [ENNReal.toReal_mul]
  repeat' rw [ENNReal.toReal_div]
  repeat' rw [ENNReal.toReal_pow]
  repeat' rw [ENNReal.toReal_inv]
  repeat' rw [ENNReal.toReal_natCast]
  repeat' rw [ENNReal.toReal_ofNat]
  field_simp
  set_option maxRecDepth 10000 in
    set_option exponentiation.threshold 1024 in
      exact_mod_cast binomial512_prefix71_scaled

theorem highBudget_real :
    highActivityBudget =
      ENNReal.ofReal ((99 / 100 : ℝ) * (2 : ℝ)⁻¹ ^ 192) := by
  symm
  unfold highActivityBudget failureTarget
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 99 / 100)]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100)]
  rw [ENNReal.ofReal_pow
    (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹) 192]
  rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

end CertifiedJL.Threshold512Bits192
