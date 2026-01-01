/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Activity
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Assembly

/-! # Budget split for 192 rows, squared-norm floor 12, and 128 bits -/

open scoped ENNReal

namespace CertifiedJL.Threshold192Bits128

noncomputable def lowActivityBudget : ENNReal :=
  (1 : ENNReal) / 20 * failureTarget 128

noncomputable def highActivityBudget : ENNReal :=
  (19 : ENNReal) / 20 * failureTarget 128

noncomputable def config : ThresholdTailConfig where
  rows := 192
  squaredNormFloor := 12
  bits := 128
  lowBudget := lowActivityBudget
  highBudget := highActivityBudget

theorem budgets_add :
    lowActivityBudget + highActivityBudget = failureTarget 128 := by
  unfold lowActivityBudget highActivityBudget
  rw [← add_mul]
  rw [show (1 : ENNReal) / 20 + 19 / 20 = 1 by
    change (1 : ENNReal) * 20⁻¹ + (19 : ENNReal) * 20⁻¹ = 1
    rw [← add_mul]
    norm_num only [OfNat.ofNat, Nat.cast_ofNat]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  simp

private theorem binomial192_prefix12_scaled :
    20 * (∑ k ∈ Finset.range 12, (192 : ℕ).choose k) * 2 ^ 128 <
      2 ^ 192 := by
  set_option maxRecDepth 10000 in
    decide +kernel

/-- Exact counting places `K < 12` below `1/20` of the 128-bit budget. -/
theorem lowActivity {d : ℕ} (i : Fin d) :
    eventProbability (sparseRademacherMatrix 192 d)
        (fun J =>
          (dominantActivityCount (matrixDominantActivity i J) : ℕ) < 12) <
      lowActivityBudget := by
  rw [sparse_dominantActivityCount_lt_probability_eq_at 192 i 12]
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
    set_option exponentiation.threshold 512 in
      exact_mod_cast binomial192_prefix12_scaled

theorem highBudget_real :
    highActivityBudget =
      ENNReal.ofReal ((19 / 20 : ℝ) * (2 : ℝ)⁻¹ ^ 128) := by
  symm
  unfold highActivityBudget failureTarget
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 19 / 20)]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 20)]
  rw [ENNReal.ofReal_pow
    (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹) 128]
  rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

end CertifiedJL.Threshold192Bits128
