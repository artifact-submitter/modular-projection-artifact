/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.SmoothBounds.HyperbolicProfile
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The Rademacher variance profile

The exponentially tilted Rademacher sum has coordinate variances
`1 - tanh² (x bᵢ)`.  The sparse one-row proof bounds their weighted sum
from below by applying Jensen's inequality to

`z ↦ 1 - tanh² (x √z) = cosh⁻² (x √z)`.

This file proves the required convexity on `[0, ∞)` and packages the exact
finite profile inequality `(O4)`.
-/

open scoped BigOperators

namespace CertifiedJL
namespace Probability

/-- The nonnegative factor controlling the second derivative of the variance profile. -/
noncomputable def rademacherVarianceWitness (t : ℝ) : ℝ :=
  Real.tanh t - t + 3 * t * Real.tanh t ^ 2

/-- The variance profile as a function of the squared coefficient. -/
noncomputable def rademacherVarianceProfile (x z : ℝ) : ℝ :=
  1 - Real.tanh (x * √z) ^ 2

/-- The first derivative of the variance profile away from the origin. -/
noncomputable def rademacherVarianceProfileDeriv (x z : ℝ) : ℝ :=
  -x * Real.tanh (x * √z) *
      (1 - Real.tanh (x * √z) ^ 2) / √z

/-- The second derivative of the variance profile away from the origin. -/
noncomputable def rademacherVarianceProfileDeriv2 (x z : ℝ) : ℝ :=
  x * (1 - Real.tanh (x * √z) ^ 2) *
      rademacherVarianceWitness (x * √z) / (2 * z * √z)

@[simp]
theorem rademacherVarianceWitness_zero :
    rademacherVarianceWitness 0 = 0 := by
  simp [rademacherVarianceWitness]

/-- Derivative of the factor controlling convexity. -/
theorem hasDerivAt_rademacherVarianceWitness (t : ℝ) :
    HasDerivAt rademacherVarianceWitness
      (2 * Real.tanh t ^ 2 +
        6 * t * Real.tanh t * (1 - Real.tanh t ^ 2)) t := by
  have hq := hasDerivAt_tanh t
  have hraw :=
    hq.sub (hasDerivAt_id t) |>.add
      (((hasDerivAt_const t 3).mul (hasDerivAt_id t)).mul (hq.pow 2))
  have hfun :
      Real.tanh - id +
          (fun _ : ℝ => 3) * id * Real.tanh ^ 2 =
        rademacherVarianceWitness := by
    funext y
    simp [rademacherVarianceWitness]
  rw [hfun] at hraw
  apply hraw.congr_deriv
  simp only [Pi.mul_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat, mul_one]
  rw [← one_sub_tanh_sq t]
  ring

/-- The second-derivative witness is nonnegative on `[0, ∞)`. -/
theorem rademacherVarianceWitness_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ rademacherVarianceWitness t := by
  have hmono : MonotoneOn rademacherVarianceWitness (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · exact fun y _ =>
        (hasDerivAt_rademacherVarianceWitness y).continuousAt.continuousWithinAt
    · exact fun y _ =>
        (hasDerivAt_rademacherVarianceWitness y).hasDerivWithinAt
    · intro y hy
      have hy' : 0 ≤ y := (interior_subset hy : y ∈ Set.Ici 0)
      exact add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
        (mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) hy') (tanh_nonneg hy'))
          (sub_nonneg.mpr (Real.tanh_sq_lt_one y).le))
  simpa using
    hmono (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr ht) ht

/-- The variance profile is the reciprocal square of `cosh`. -/
theorem rademacherVarianceProfile_eq_inv_cosh_sq (x z : ℝ) :
    rademacherVarianceProfile x z =
      (Real.cosh (x * √z))⁻¹ ^ 2 := by
  exact one_sub_tanh_sq (x * √z)

/-- First derivative of the variance profile on the positive axis. -/
theorem hasDerivAt_rademacherVarianceProfile
    (x : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (rademacherVarianceProfile x)
      (rademacherVarianceProfileDeriv x z) z := by
  have hsqrt : √z ≠ 0 := (Real.sqrt_pos.2 hz).ne'
  have ht :
      HasDerivAt (fun y : ℝ => x * √y) (x / (2 * √z)) z := by
    exact ((Real.hasDerivAt_sqrt hz.ne').const_mul x).congr_deriv (by ring)
  have hq := (hasDerivAt_tanh (x * √z)).comp z ht
  have hraw := (hasDerivAt_const z 1).sub (hq.pow 2)
  have hfun :
      (fun _ : ℝ => 1) -
          (Real.tanh ∘ fun y : ℝ => x * √y) ^ 2 =
        rademacherVarianceProfile x := by
    funext y
    simp [rademacherVarianceProfile, Function.comp_apply]
  rw [hfun] at hraw
  apply hraw.congr_deriv
  simp only [Function.comp_apply, Nat.cast_ofNat, zero_sub]
  rw [← one_sub_tanh_sq (x * √z)]
  unfold rademacherVarianceProfileDeriv
  field_simp
  ring

/-- Second derivative of the variance profile on the positive axis. -/
theorem hasDerivAt_rademacherVarianceProfileDeriv
    (x : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (rademacherVarianceProfileDeriv x)
      (rademacherVarianceProfileDeriv2 x z) z := by
  have hsqrt : √z ≠ 0 := (Real.sqrt_pos.2 hz).ne'
  have hsq : (√z) ^ 2 = z := Real.sq_sqrt hz.le
  have ht :
      HasDerivAt (fun y : ℝ => x * √y) (x / (2 * √z)) z := by
    exact ((Real.hasDerivAt_sqrt hz.ne').const_mul x).congr_deriv (by ring)
  have hq := (hasDerivAt_tanh (x * √z)).comp z ht
  have hr :
      HasDerivAt
          (fun y : ℝ => 1 - Real.tanh (x * √y) ^ 2)
          (rademacherVarianceProfileDeriv x z) z :=
    hasDerivAt_rademacherVarianceProfile x hz
  have hraw :=
    ((hasDerivAt_const z (-x)).mul (hq.mul hr)).div
      (Real.hasDerivAt_sqrt hz.ne') hsqrt
  have hfun :
      (fun _ : ℝ => -x) *
          ((Real.tanh ∘ fun y : ℝ => x * √y) *
            (fun y : ℝ => 1 - Real.tanh (x * √y) ^ 2)) /
          (fun y : ℝ => √y) =
        rademacherVarianceProfileDeriv x := by
    funext y
    simp only [Function.comp_apply, Pi.mul_apply, Pi.div_apply]
    unfold rademacherVarianceProfileDeriv
    ring
  rw [hfun] at hraw
  apply hraw.congr_deriv
  simp only [Function.comp_apply, Pi.mul_apply]
  rw [← one_sub_tanh_sq (x * √z)]
  unfold rademacherVarianceProfileDeriv
  unfold rademacherVarianceProfileDeriv2
  unfold rademacherVarianceWitness
  set a : ℝ := √z
  set q : ℝ := Real.tanh (x * a)
  field_simp [hsqrt]
  ring_nf
  rw [← hsq]
  ring

/-- The variance profile is continuous on the nonnegative axis. -/
theorem continuousOn_rademacherVarianceProfile (x : ℝ) :
    ContinuousOn (rademacherVarianceProfile x) (Set.Ici 0) := by
  exact (continuous_const.sub
    ((continuous_tanh.comp
      (continuous_const.mul Real.continuous_sqrt)).pow 2)).continuousOn

/-- The variance profile is convex on `[0, ∞)`. -/
theorem convexOn_rademacherVarianceProfile {x : ℝ} (hx : 0 ≤ x) :
    ConvexOn ℝ (Set.Ici 0) (rademacherVarianceProfile x) := by
  rcases hx.eq_or_lt with rfl | hx
  · have hzero :
        rademacherVarianceProfile 0 = (fun _ : ℝ => (1 : ℝ)) := by
      funext z
      simp [rademacherVarianceProfile]
    rw [hzero]
    exact
      (convexOn_const (𝕜 := ℝ) (1 : ℝ) (convex_Ici (0 : ℝ)))
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 0)
    (continuousOn_rademacherVarianceProfile x)
  · intro z hz
    exact (hasDerivAt_rademacherVarianceProfile x
      (by simpa only [interior_Ici, Set.mem_Ioi] using hz)).hasDerivWithinAt
  · intro z hz
    exact (hasDerivAt_rademacherVarianceProfileDeriv x
      (by simpa only [interior_Ici, Set.mem_Ioi] using hz)).hasDerivWithinAt
  · intro z hz
    have hz' : 0 < z := by
      simpa only [interior_Ici, Set.mem_Ioi] using hz
    unfold rademacherVarianceProfileDeriv2
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg hx.le
          (sub_nonneg.mpr (Real.tanh_sq_lt_one (x * √z)).le))
        (rademacherVarianceWitness_nonneg
          (mul_nonneg hx.le (Real.sqrt_nonneg z))))
      (mul_nonneg (mul_nonneg (by norm_num) hz'.le)
        (Real.sqrt_nonneg z))

/--
The exact finite variance-profile inequality `(O4)`.

The weights and Jensen points are both `bᵢ²`; normalization makes the
weighted mean equal to the fourth-moment profile `∑ bᵢ⁴`.
-/
theorem inv_cosh_sq_sqrt_sum_fourth_le_sum
    {ι : Type*} [Fintype ι] (b : ι → ℝ) {x : ℝ}
    (hx : 0 ≤ x) (hnorm : ∑ i, b i ^ 2 = 1) :
    (Real.cosh (x * √(∑ i, b i ^ 4)))⁻¹ ^ 2 ≤
      ∑ i, b i ^ 2 * (Real.cosh (x * b i))⁻¹ ^ 2 := by
  have hjensen :=
    (convexOn_rademacherVarianceProfile hx).map_sum_le
      (t := Finset.univ) (w := fun i => b i ^ 2)
      (p := fun i => b i ^ 2)
      (fun i _ => sq_nonneg (b i)) hnorm
      (fun i _ => Set.mem_Ici.mpr (sq_nonneg (b i)))
  have hmean :
      ∑ i, b i ^ 2 • (b i ^ 2 : ℝ) = ∑ i, b i ^ 4 := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [smul_eq_mul]
    ring
  rw [hmean] at hjensen
  rw [rademacherVarianceProfile_eq_inv_cosh_sq] at hjensen
  have hpoint (i : ι) :
      (Real.cosh (x * √(b i ^ 2)))⁻¹ ^ 2 =
        (Real.cosh (x * b i))⁻¹ ^ 2 := by
    rw [Real.sqrt_sq_eq_abs]
    congr 2
    calc
      Real.cosh (x * |b i|) = Real.cosh |x * b i| := by
        rw [abs_mul, abs_of_nonneg hx]
      _ = Real.cosh (x * b i) := Real.cosh_abs _
  simpa only [smul_eq_mul, rademacherVarianceProfile_eq_inv_cosh_sq,
    hpoint] using hjensen

end Probability
end CertifiedJL
