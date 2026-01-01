import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Intermediate.Modular

/-! # Producer canaries for the intermediate modular-image bound -/

namespace CertifiedJL.Tests

open CertifiedJL

/-- The variable shifted-envelope exponent is pinned literally. -/
theorem intermediate_alpha_shape_canary (r : ℝ) :
    intermediateAlpha r =
      (23 / 10) / (1 + (23 / 10) * (1 - r)) := by
  rfl

/-- The shifted-envelope exponent in L14 is pinned exactly. -/
theorem intermediate_alpha_zero_canary :
    intermediateAlpha0 = (69 / 53 : ℝ) := intermediateAlpha0_eq

/-- L13 retains the inactive series, both asymmetric shifts, and both
half-weights literally. -/
theorem intermediate_l13_shape_canary (r D : ℝ) :
    intermediateL13 r D =
      (∑' n : ℕ, Real.exp
        (-intermediateAlpha r * ((((n : ℝ) + 1) * D) ^ 2))) +
        (1 / 2 : ℝ) * (∑' n : ℕ, Real.exp
          (-intermediateAlpha r *
            ((((n : ℝ) + 1) * D - Real.sqrt r) ^ 2))) +
        (1 / 2 : ℝ) * (∑' n : ℕ, Real.exp
          (-intermediateAlpha r *
            ((((n : ℝ) + 1) * D + Real.sqrt r) ^ 2))) := by
  rfl

/-- The exact three terms, shifts, gaps, and half-weights in L14 are pinned. -/
theorem intermediate_l14_shape_canary (D : ℝ) :
    intermediateL14 D =
      Real.exp (-intermediateAlpha0 * D ^ 2) /
          (1 - Real.exp (-intermediateAlpha0 * (3 * D ^ 2))) +
        (1 / 2 : ℝ) *
          (Real.exp
              (-intermediateAlpha0 * (D - Real.sqrt (2 / 3)) ^ 2) /
            (1 - Real.exp
              (-intermediateAlpha0 *
                (3 * D ^ 2 - 2 * D * Real.sqrt (2 / 3))))) +
        (1 / 2 : ℝ) *
          (Real.exp
              (-intermediateAlpha0 * (D + Real.sqrt (2 / 3)) ^ 2) /
            (1 - Real.exp
              (-intermediateAlpha0 *
                (3 * D ^ 2 + 2 * D * Real.sqrt (2 / 3))))) := by
  rfl

/-- The generic bridge is exercised on a nonsquared asymmetric sequence. -/
theorem gaussian_shift_geometric_canary :
    (∑' n : ℕ, Real.exp (-(1 : ℝ) * ((n : ℝ) + 2))) ≤
      Real.exp (-(1 : ℝ) * 2) / (1 - Real.exp (-(1 : ℝ) * 1)) := by
  exact gaussianShift_tsum_le_geometric (a := 1) (first := 2) (gap := 1)
    (z := fun n : ℕ ↦ (n : ℝ) + 2) (by norm_num) (by norm_num)
    (fun n ↦ by simp [add_comm])

/-- `D=3` directly consumes all three L14 image series and their shifts. -/
theorem intermediate_three_series_three_canary :
    (∑' n : ℕ, Real.exp
        (-intermediateAlpha0 * (((n : ℝ) + 1) * 3) ^ 2)) +
      (1 / 2 : ℝ) * (∑' n : ℕ, Real.exp
        (-intermediateAlpha0 *
          (((n : ℝ) + 1) * 3 - Real.sqrt (2 / 3)) ^ 2)) +
      (1 / 2 : ℝ) * (∑' n : ℕ, Real.exp
        (-intermediateAlpha0 *
          (((n : ℝ) + 1) * 3 + Real.sqrt (2 / 3)) ^ 2)) ≤
      intermediateL14 3 := by
  exact intermediate_three_series_le_L14 (by norm_num)

/-- A strict interior mass checks the exact `r`-to-`2/3` transfer. -/
theorem intermediate_l13_nonendpoint_canary :
    intermediateL13 (3 / 4) 3 ≤ intermediateL13 (2 / 3) 3 := by
  exact intermediateL13_le_two_div_three (by norm_num) (by norm_num) (by norm_num)

/-- The asymmetric minus image directly consumes the delicate endpoint proof. -/
theorem intermediate_minus_image_asymmetric_canary :
    Real.exp (-intermediateAlpha (4 / 5) *
        ((2 * 3 - Real.sqrt (4 / 5)) ^ 2)) ≤
      Real.exp (-intermediateAlpha0 *
        ((2 * 3 - Real.sqrt (2 / 3)) ^ 2)) := by
  convert intermediate_minus_image_le_two_div_three
    (r := (4 / 5 : ℝ)) (D := 3) (n := 1)
    (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num

/-- The inactive image directly consumes its nonendpoint transfer. -/
theorem intermediate_inactive_image_nonendpoint_canary :
    Real.exp (-intermediateAlpha (4 / 5) * ((2 * 3) ^ 2)) ≤
      Real.exp (-intermediateAlpha0 * ((2 * 3) ^ 2)) := by
  convert intermediate_inactive_image_le_two_div_three
    (r := (4 / 5 : ℝ)) (D := 3) (n := 1)
    (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num

/-- The plus image directly consumes the shift away from zero. -/
theorem intermediate_plus_image_asymmetric_canary :
    Real.exp (-intermediateAlpha (4 / 5) *
        ((2 * 3 + Real.sqrt (4 / 5)) ^ 2)) ≤
      Real.exp (-intermediateAlpha0 *
        ((2 * 3 + Real.sqrt (2 / 3)) ^ 2)) := by
  convert intermediate_plus_image_le_two_div_three
    (r := (4 / 5 : ℝ)) (D := 3) (n := 1)
    (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num

/-- The inclusive left endpoint and minimum modulus flow through L12--L14. -/
theorem intermediate_l13_boundary_to_l14_canary :
    intermediateL13 (2 / 3) 3 ≤ intermediateL14 3 := by
  exact intermediateL13_le_L14 (by norm_num) (by norm_num) (by norm_num)

end CertifiedJL.Tests
