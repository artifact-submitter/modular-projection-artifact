/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Gaussian.HalfGaussian

/-! Compatibility API for the 512-dimensional half-Gaussian specialization. -/

namespace CertifiedJL.Probability.HalfGaussian512

open scoped BigOperators
open MeasureTheory

noncomputable def halfGaussianDensity (x : ℝ) : ℝ :=
  (Real.sqrt Real.pi)⁻¹ * Real.exp (-x ^ 2)
noncomputable def halfGaussianRadialDensity :
    EuclideanSpace ℝ (Fin 512) → ℝ :=
  fun x => Real.pi⁻¹ ^ 256 * Real.exp (-‖x‖ ^ 2)
noncomputable def halfGaussianProductDensity : (Fin 512 → ℝ) → ℝ :=
  fun x => ∏ i, halfGaussianDensity (x i)
def squaredRadius : (Fin 512 → ℝ) → ℝ := fun x => ∑ i, (x i) ^ 2

theorem integrable_halfGaussianDensity : Integrable halfGaussianDensity := by
  unfold halfGaussianDensity
  have h :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1))
      |>.const_mul (Real.sqrt Real.pi)⁻¹
  apply h.congr
  filter_upwards with x
  congr 2
  ring
theorem integrable_halfGaussianProductDensity : Integrable halfGaussianProductDensity := by
  exact Integrable.fintype_prod
    (μ := fun _ : Fin 512 => (volume : Measure ℝ))
    (fun _ => integrable_halfGaussianDensity)
theorem halfGaussianProductDensity_eq_radial (x : Fin 512 → ℝ) :
    halfGaussianProductDensity x = halfGaussianRadialDensity (WithLp.toLp 2 x) := by
  simpa [halfGaussianProductDensity, halfGaussianDensity, halfGaussianRadialDensity,
    HalfGaussianEven.halfGaussianProductDensity, HalfGaussianEven.halfGaussianDensity,
    HalfGaussianEven.halfGaussianRadialDensity] using
      HalfGaussianEven.halfGaussianProductDensity_eq_radial
        (rows := 512) (shape := 256) (by norm_num) x
theorem halfGaussianProductDensity_eq_exp (x : Fin 512 → ℝ) :
    halfGaussianProductDensity x = Real.pi⁻¹ ^ 256 * Real.exp (-squaredRadius x) := by
  simpa [halfGaussianProductDensity, halfGaussianDensity, squaredRadius,
    HalfGaussianEven.halfGaussianProductDensity, HalfGaussianEven.halfGaussianDensity,
    HalfGaussianEven.squaredRadius] using
      HalfGaussianEven.halfGaussianProductDensity_eq_exp
        (rows := 512) (shape := 256) (by norm_num) x
theorem integral_pow_191_exp_neg_sq_Ioi {a : ℝ} (ha : 0 ≤ a) :
    (∫ r : ℝ in Set.Ioi (Real.sqrt a), r ^ 511 * Real.exp (-r ^ 2)) =
      (1 / 2 : ℝ) * ∫ t : ℝ in Set.Ioi a, t ^ 255 * Real.exp (-t) := by
  simpa using HalfGaussianEven.integral_pow_even_sub_one_exp_neg_sq_Ioi
    (rows := 512) (shape := 256) (by norm_num) (by norm_num) ha

theorem integral_Ioi_mul_exp_neg_mul_sq {c b : ℝ} (hc : 0 < c) (hb : 0 ≤ b) :
    (∫ x : ℝ in Set.Ioi b, x * Real.exp (-c * x ^ 2)) =
      Real.exp (-c * b ^ 2) / (2 * c) :=
  HalfGaussianEven.integral_Ioi_mul_exp_neg_mul_sq hc hb
theorem integral_Ioi_exp_neg_mul_sq_le {c b : ℝ} (hc : 0 < c) (hb : 0 < b) :
    (∫ x : ℝ in Set.Ioi b, Real.exp (-c * x ^ 2)) ≤
      Real.exp (-c * b ^ 2) / (2 * c * b) :=
  HalfGaussianEven.integral_Ioi_exp_neg_mul_sq_le hc hb
theorem integral_abs_ge_exp_neg_mul_sq_le {c b : ℝ} (hc : 0 < c) (hb : 0 < b) :
    (∫ x : ℝ in {x | b ≤ |x|}, Real.exp (-c * x ^ 2)) ≤
      Real.exp (-c * b ^ 2) / (c * b) :=
  HalfGaussianEven.integral_abs_ge_exp_neg_mul_sq_le hc hb

noncomputable def tiltedHalfGaussianDensity (x : ℝ) : ℝ :=
  (Real.sqrt Real.pi)⁻¹ * Real.exp (-(2 / 5 : ℝ) * x ^ 2)
theorem integrable_tiltedHalfGaussianDensity : Integrable tiltedHalfGaussianDensity := by
  exact HalfGaussianEven.integrable_tiltedHalfGaussianDensity
noncomputable def tiltedHalfGaussianProductDensity : (Fin 512 → ℝ) → ℝ :=
  fun x => ∏ i, tiltedHalfGaussianDensity (x i)
theorem integrable_tiltedHalfGaussianProductDensity :
    Integrable tiltedHalfGaussianProductDensity := by
  exact Integrable.fintype_prod (μ := fun _ : Fin 512 => (volume : Measure ℝ))
    (fun _ => integrable_tiltedHalfGaussianDensity)
theorem tiltedHalfGaussianProductDensity_eq_exp (x : Fin 512 → ℝ) :
    tiltedHalfGaussianProductDensity x = Real.pi⁻¹ ^ 256 *
      Real.exp (-(2 / 5 : ℝ) * ∑ i, (x i) ^ 2) := by
  simpa [tiltedHalfGaussianProductDensity, tiltedHalfGaussianDensity,
    HalfGaussianEven.tiltedHalfGaussianProductDensity,
    HalfGaussianEven.tiltedHalfGaussianDensity] using
      HalfGaussianEven.tiltedHalfGaussianProductDensity_eq_exp
        (rows := 512) (shape := 256) (by norm_num) x
theorem halfGaussianProductDensity_eq_exp_mul_tilted (x : Fin 512 → ℝ) :
    halfGaussianProductDensity x = Real.exp (-(3 / 5 : ℝ) * squaredRadius x) *
      tiltedHalfGaussianProductDensity x := by
  rw [halfGaussianProductDensity_eq_exp, tiltedHalfGaussianProductDensity_eq_exp]
  unfold squaredRadius
  rw [show -(∑ i, x i ^ 2) = -(3 / 5 : ℝ) * (∑ i, x i ^ 2) +
      -(2 / 5 : ℝ) * (∑ i, x i ^ 2) by ring, Real.exp_add]
  ring
theorem integral_tiltedHalfGaussianDensity :
    (∫ x : ℝ, tiltedHalfGaussianDensity x) = Real.sqrt (5 / 2 : ℝ) := by
  simpa [tiltedHalfGaussianDensity, HalfGaussianEven.tiltedHalfGaussianDensity] using
    HalfGaussianEven.integral_tiltedHalfGaussianDensity
theorem integral_abs_ge_tiltedHalfGaussianDensity_lt {b : ℝ}
    (hb : 0 < b)
    (hscale : (Real.sqrt Real.pi)⁻¹ / ((2 / 5 : ℝ) * b) < Real.sqrt (5 / 2 : ℝ)) :
    (∫ x : ℝ in {x | b ≤ |x|}, tiltedHalfGaussianDensity x) <
      Real.sqrt (5 / 2 : ℝ) * Real.exp (-(2 / 5 : ℝ) * b ^ 2) := by
  simpa [tiltedHalfGaussianDensity, HalfGaussianEven.tiltedHalfGaussianDensity] using
    HalfGaussianEven.integral_abs_ge_tiltedHalfGaussianDensity_lt hb hscale

noncomputable def coordinateTiltedTailDensity :
    ℝ → Fin 512 → (Fin 512 → ℝ) → ℝ :=
  fun b j x => ∏ i, if i = j then
    {t : ℝ | b ≤ |t|}.indicator tiltedHalfGaussianDensity (x i)
  else tiltedHalfGaussianDensity (x i)
theorem coordinateTiltedTailDensity_nonneg
    (b : ℝ) (j : Fin 512) (x : Fin 512 → ℝ) :
    0 ≤ coordinateTiltedTailDensity b j x := by
  exact HalfGaussianEven.coordinateTiltedTailDensity_nonneg (rows := 512) b j x
theorem coordinateTiltedTailDensity_eq_of_mem
    {b : ℝ} {j : Fin 512} {x : Fin 512 → ℝ} (hj : b ≤ |x j|) :
    coordinateTiltedTailDensity b j x = tiltedHalfGaussianProductDensity x := by
  exact HalfGaussianEven.coordinateTiltedTailDensity_eq_of_mem (rows := 512) hj
theorem integrable_coordinateTiltedTailDensity (b : ℝ) (j : Fin 512) :
    Integrable (coordinateTiltedTailDensity b j) := by
  exact HalfGaussianEven.integrable_coordinateTiltedTailDensity (rows := 512) b j
theorem integral_coordinateTiltedTailDensity (b : ℝ) (j : Fin 512) :
    (∫ x : Fin 512 → ℝ, coordinateTiltedTailDensity b j x) =
      (∫ t : ℝ in {t | b ≤ |t|}, tiltedHalfGaussianDensity t) *
        Real.sqrt (5 / 2 : ℝ) ^ 511 := by
  exact HalfGaussianEven.integral_coordinateTiltedTailDensity (rows := 512) b j

def halfGaussianTruncationSet : ℝ → ℝ → Set (Fin 512 → ℝ) :=
  fun a b => {x | a < squaredRadius x ∧ ∃ j, b ≤ |x j|}
theorem measurableSet_halfGaussianTruncationSet (a b : ℝ) :
    MeasurableSet (halfGaussianTruncationSet a b) := by
  simpa [halfGaussianTruncationSet, squaredRadius,
    HalfGaussianEven.halfGaussianTruncationSet,
    HalfGaussianEven.squaredRadius] using
      HalfGaussianEven.measurableSet_halfGaussianTruncationSet (rows := 512) a b
theorem integral_halfGaussianTruncationSet_lt {a b : ℝ} (hb : 0 < b)
    (hscale : (Real.sqrt Real.pi)⁻¹ / ((2 / 5 : ℝ) * b) < Real.sqrt (5 / 2 : ℝ)) :
    (∫ x : Fin 512 → ℝ in halfGaussianTruncationSet a b,
        halfGaussianProductDensity x) <
      512 * (5 / 2 : ℝ) ^ 256 * Real.exp (-(3 * a + 2 * b ^ 2) / 5) := by
  simpa [halfGaussianTruncationSet, squaredRadius, halfGaussianProductDensity,
    halfGaussianDensity, HalfGaussianEven.halfGaussianTruncationSet,
    HalfGaussianEven.squaredRadius, HalfGaussianEven.halfGaussianProductDensity,
    HalfGaussianEven.halfGaussianDensity] using
    HalfGaussianEven.integral_halfGaussianTruncationSet_lt
    (rows := 512) (shape := 256) (by norm_num) (by norm_num)
    (a := a) (b := b) hb hscale
theorem integral_halfGaussianRadialDensity_tail {a : ℝ} (ha : 0 ≤ a) :
    (∫ x : EuclideanSpace ℝ (Fin 512) in {x | a < ‖x‖ ^ 2},
        halfGaussianRadialDensity x) = gammaSurvivalNat 256 a := by
  simpa [halfGaussianRadialDensity, HalfGaussianEven.halfGaussianRadialDensity] using
    HalfGaussianEven.integral_halfGaussianRadialDensity_tail
    (rows := 512) (shape := 256) (by norm_num) (by norm_num) ha
theorem integral_halfGaussianProductDensity_tail {a : ℝ} (ha : 0 ≤ a) :
    (∫ x : Fin 512 → ℝ in {x | a < ∑ i, (x i) ^ 2},
        halfGaussianProductDensity x) = gammaSurvivalNat 256 a := by
  simpa [halfGaussianProductDensity, halfGaussianDensity,
    HalfGaussianEven.halfGaussianProductDensity,
    HalfGaussianEven.halfGaussianDensity] using
    HalfGaussianEven.integral_halfGaussianProductDensity_tail
    (rows := 512) (shape := 256) (by norm_num) (by norm_num) ha

end CertifiedJL.Probability.HalfGaussian512
