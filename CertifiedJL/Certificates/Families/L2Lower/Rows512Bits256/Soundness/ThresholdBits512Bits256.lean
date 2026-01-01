/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Activity
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Assembly

/-! # Budget split for 512 rows, squared-norm floor 57, and 256 bits -/

open scoped ENNReal

namespace CertifiedJL.Threshold512Bits256

noncomputable def lowActivityBudget : ENNReal :=
  (1 : ENNReal) / 25 * failureTarget 256

noncomputable def highActivityBudget : ENNReal :=
  (24 : ENNReal) / 25 * failureTarget 256

noncomputable def config : ThresholdTailConfig where
  rows := 512
  squaredNormFloor := 57
  bits := 256
  lowBudget := lowActivityBudget
  highBudget := highActivityBudget

theorem budgets_add :
    lowActivityBudget + highActivityBudget = failureTarget 256 := by
  unfold lowActivityBudget highActivityBudget
  rw [← add_mul]
  rw [show (1 : ENNReal) / 25 + 24 / 25 = 1 by
    change (1 : ENNReal) * 25⁻¹ + (24 : ENNReal) * 25⁻¹ = 1
    rw [← add_mul]
    norm_num only [OfNat.ofNat, Nat.cast_ofNat]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  simp

private theorem binomial512_prefix57_scaled :
    25 * (∑ k ∈ Finset.range 57, (512 : ℕ).choose k) * 2 ^ 256 <
      2 ^ 512 := by
  set_option maxRecDepth 10000 in
    decide +kernel

/-- Exact counting places K < 57 below 1/25 of the 256-bit budget. -/
theorem lowActivity
    {d : ℕ} (i : Fin d) :
    eventProbability (sparseRademacherMatrix 512 d)
        (fun J =>
          (dominantActivityCount (matrixDominantActivity i J) : ℕ) < 57) <
      lowActivityBudget := by
  rw [sparse_dominantActivityCount_lt_probability_eq_at 512 i 57]
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
      exact_mod_cast binomial512_prefix57_scaled

theorem highBudget_real :
    highActivityBudget =
      ENNReal.ofReal ((24 / 25 : ℝ) * (2 : ℝ)⁻¹ ^ 256) := by
  symm
  unfold highActivityBudget failureTarget
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 24 / 25)]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 25)]
  rw [ENNReal.ofReal_pow
    (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹) 256]
  rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

end CertifiedJL.Threshold512Bits256
