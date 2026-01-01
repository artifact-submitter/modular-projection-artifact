import CertifiedJL.Probability.NormalApproximation.Tyurin.EnvelopeBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! An elementary two-exponential majorant for the existing eight-trapezoid
Tyurin core. The convexity argument is independent of all certificate data. -/

namespace CertifiedJL.Probability

theorem exp_scaled_sq_le_chord (a q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Real.exp (a * q ^ 2) ≤ (1 - q ^ 2) + q ^ 2 * Real.exp a := by
  have hq : q ^ 2 ≤ 1 := by nlinarith
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ a)
    (sub_nonneg.mpr hq) (sq_nonneg q) (by ring : 1 - q ^ 2 + q ^ 2 = 1)
  simpa [smul_eq_mul, mul_comm, Real.exp_zero] using h

/-- The exact eight-node second and fourth moments collapse the inner sum. -/
theorem sqExpSqTrapezoid_eight_le_chord (c T : ℝ) (hT : 0 ≤ T) :
    sqExpSqTrapezoid 8 c T ≤
      T ^ 3 * ((1071 : ℝ) / 16384 +
        1681 / 16384 * Real.exp (c * T ^ 2 / 2)) := by
  have hterm (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
      (q * T) ^ 2 / 2 * Real.exp (c * (q * T) ^ 2 / 2) ≤
        (q * T) ^ 2 / 2 *
          ((1 - q ^ 2) + q ^ 2 * Real.exp (c * T ^ 2 / 2)) := by
    have h := exp_scaled_sq_le_chord (c * T ^ 2 / 2) q hq0 hq1
    rw [show c * (q * T) ^ 2 / 2 = (c * T ^ 2 / 2) * q ^ 2 by ring]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have hsum := Finset.sum_le_sum (s := Finset.range 7) (fun i hi =>
    hterm (((i : ℝ) + 1) / 8) (by positivity) (by
      have hi' : i < 7 := Finset.mem_range.mp hi
      have : (i : ℝ) ≤ 6 := by exact_mod_cast (by omega : i ≤ 6)
      linarith))
  unfold sqExpSqTrapezoid trapezoidal_integral
  norm_num only [Nat.cast_ofNat, sub_zero, zero_pow, zero_mul, zero_div,
    zero_add, add_zero] at *
  have hgrid (i : ℕ) : ((i : ℝ) + 1) * T / 8 = (((i : ℝ) + 1) / 8) * T := by ring
  simp_rw [hgrid]
  calc
    _ ≤ T / 8 * ((T ^ 2 / 2 * Real.exp (c * T ^ 2 / 2)) / 2 +
      ∑ i ∈ Finset.range 7, ((((i : ℝ) + 1) / 8) * T) ^ 2 / 2 *
        ((1 - (((i : ℝ) + 1) / 8) ^ 2) +
          (((i : ℝ) + 1) / 8) ^ 2 * Real.exp (c * T ^ 2 / 2))) := by
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) (by positivity)
    _ = _ := by norm_num [Finset.sum_range_succ]; ring

/-- Two signed exponentials replace all nine inner exponential evaluations. -/
theorem weighted_sqExpSqTrapezoid_eight_le_chord
    (c T : ℝ) (hT : 0 ≤ T) :
    Real.exp (-(T ^ 2) / 2) * sqExpSqTrapezoid 8 c T ≤
      T ^ 3 * (1071 / 16384 * Real.exp (-(T ^ 2) / 2) +
        1681 / 16384 * Real.exp ((c - 1) * T ^ 2 / 2)) := by
  calc
    _ ≤ Real.exp (-(T ^ 2) / 2) *
      (T ^ 3 * (1071 / 16384 + 1681 / 16384 * Real.exp (c * T ^ 2 / 2))) :=
        mul_le_mul_of_nonneg_left (sqExpSqTrapezoid_eight_le_chord c T hT)
          (Real.exp_pos _).le
    _ = _ := by
      rw [show (c - 1) * T ^ 2 / 2 = -(T ^ 2) / 2 + c * T ^ 2 / 2 by ring,
        Real.exp_add]
      ring

end CertifiedJL.Probability
