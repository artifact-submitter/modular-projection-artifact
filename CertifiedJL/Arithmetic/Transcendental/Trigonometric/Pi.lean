/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Real.Sqrt

/-!
# Rational bounds for `π` and square roots

This file records the small, exact transcendental estimates used in the
sparse one-row certificate.  The lower bound on `π` comes from Machin's
identity and the first alternating-series bounds for `arctan`.
-/

namespace CertifiedJL

private theorem arctanCoefficient_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (fun n : ℕ => x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) := by
  apply antitone_nat_of_succ_le
  intro n
  have hxpow : 0 ≤ x ^ (2 * n + 1) := pow_nonneg hx0 _
  have hxsq : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg (x - 1)]
  have hnum : x ^ (2 * (n + 1) + 1) ≤ x ^ (2 * n + 1) := by
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, pow_add]
    nlinarith
  calc
    x ^ (2 * (n + 1) + 1) / ((2 * (n + 1) + 1 : ℕ) : ℝ) ≤
        x ^ (2 * n + 1) / ((2 * (n + 1) + 1 : ℕ) : ℝ) := by
      exact div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) := by
      exact div_le_div_of_nonneg_left hxpow (by positivity) (by norm_num)

private theorem arctan_first_two_lower {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    x - x ^ 3 / 3 ≤ Real.arctan x := by
  have hseries := (Real.hasSum_arctan (x := x) (by simpa [abs_of_nonneg hx0])).tendsto_sum_nat
  have hseries' :
      Filter.Tendsto
        (fun n : ℕ =>
          ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i *
            (x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)))
        Filter.atTop (nhds (Real.arctan x)) := by
    simpa [mul_div_assoc] using hseries
  have hbound :=
    (arctanCoefficient_antitone hx0 hx1.le).alternating_series_le_tendsto hseries' 1
  norm_num [Finset.sum_range_succ] at hbound ⊢
  linarith

private theorem arctan_first_upper {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.arctan x ≤ x := by
  have hseries := (Real.hasSum_arctan (x := x) (by simpa [abs_of_nonneg hx0])).tendsto_sum_nat
  have hseries' :
      Filter.Tendsto
        (fun n : ℕ =>
          ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i *
            (x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)))
        Filter.atTop (nhds (Real.arctan x)) := by
    simpa [mul_div_assoc] using hseries
  have hbound :=
    (arctanCoefficient_antitone hx0 hx1.le).tendsto_le_alternating_series hseries' 0
  norm_num [Finset.sum_range_succ] at hbound ⊢
  simpa using hbound

/--
The rational lower bound `3.14 < π`.

This is derived from Machin's identity
`π / 4 = 4 arctan (1 / 5) - arctan (1 / 239)`, using two terms of the
alternating series for the first arctangent and one term for the second.
-/
theorem pi_gt_157_div_50 : (157 : ℝ) / 50 < Real.pi := by
  have h5 :
      (1 : ℝ) / 5 - ((1 : ℝ) / 5) ^ 3 / 3 ≤ Real.arctan ((1 : ℝ) / 5) :=
    arctan_first_two_lower (by norm_num) (by norm_num)
  have h239 : Real.arctan ((1 : ℝ) / 239) ≤ (1 : ℝ) / 239 :=
    arctan_first_upper (by norm_num) (by norm_num)
  have hmachin := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  norm_num [inv_eq_one_div] at hmachin
  nlinarith

/-- A compact rational upper bound used by the Fourier certificates. -/
theorem pi_lt_63_div_20 : Real.pi < (63 : ℝ) / 20 := by
  nlinarith [Real.pi_lt_d2]

/-- Six-decimal lower bound used by the moderate-Lyapunov certificate. -/
theorem pi_gt_3141592_div_1000000 :
    (3141592 : ℝ) / 1000000 < Real.pi := by
  have h := Real.pi_gt_d6
  norm_num at h ⊢
  exact h

/-- Six-decimal upper bound used by the moderate-Lyapunov certificate. -/
theorem pi_lt_3141593_div_1000000 :
    Real.pi < (3141593 : ℝ) / 1000000 := by
  have h := Real.pi_lt_d6
  norm_num at h ⊢
  exact h

/-- A rational upper bound for the Gaussian normalization `√(2π)`. -/
theorem sqrt_two_pi_lt_251_div_100 :
    Real.sqrt (2 * Real.pi) < (251 : ℝ) / 100 := by
  rw [Real.sqrt_lt' (by norm_num)]
  nlinarith [pi_lt_63_div_20]

/-- Five-decimal upper bound for `√(2π)` used by the sharp D-star budget. -/
theorem sqrt_two_pi_lt_250663_div_100000 :
    Real.sqrt (2 * Real.pi) < (250663 : ℝ) / 100000 := by
  rw [Real.sqrt_lt' (by norm_num)]
  nlinarith [pi_lt_3141593_div_1000000]

/-- The rational lower bound `1.77 < √π`. -/
theorem sqrt_pi_gt_177_div_100 : (177 : ℝ) / 100 < √Real.pi := by
  rw [Real.lt_sqrt (by norm_num)]
  nlinarith [pi_gt_157_div_50]

/-- The certified upper endpoint for the normalized threshold `(39 / 4) √2`. -/
theorem sparseOneRowThreshold_lt_13789_div_1000 :
    (39 : ℝ) / 4 * √2 < 13789 / 1000 := by
  have hsqrt : √(2 : ℝ) < (13789 : ℝ) / 9750 := by
    rw [← sq_lt_sq₀ (Real.sqrt_nonneg _) (by positivity), Real.sq_sqrt (by norm_num)]
    norm_num
  nlinarith

/-- The certified upper endpoint for the Gaussian prefactor `2 / (39 √π)`. -/
theorem two_div_39_mul_sqrt_pi_lt_200_div_6903 :
    (2 : ℝ) / (39 * √Real.pi) < 200 / 6903 := by
  have hden : (6903 : ℝ) / 100 < 39 * √Real.pi := by
    nlinarith [sqrt_pi_gt_177_div_100]
  calc
    (2 : ℝ) / (39 * √Real.pi) < 2 / ((6903 : ℝ) / 100) :=
      div_lt_div_of_pos_left (by norm_num) (by norm_num) hden
    _ = 200 / 6903 := by norm_num

end CertifiedJL
