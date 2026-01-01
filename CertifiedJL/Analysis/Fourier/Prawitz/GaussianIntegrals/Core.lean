/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Gaussian.HalfGaussian
import CertifiedJL.Analysis.Fourier.Prawitz.GaussianTerms
import CertifiedJL.Analysis.Fourier.Prawitz.KernelBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Core closed-form Gaussian integrals in the Prawitz decomposition

This file integrates the standard-Gaussian reference-tail term in the
four-term Prawitz decomposition.  The strict cutoff convention is preserved:
the tail is supported on `U₀ < |u|`.

The elementary pointwise comparison

`exp (-u² / 2) / |u| ≤ exp (-u² / 2) |u| / U₀²`

turns the tail into an exactly integrable first Gaussian moment.  Its
two-sided integral is `2 exp (-U₀² / 2)`, giving the closed-form bound
`exp (-U₀² / 2) / (π U₀²)`.
-/

open MeasureTheory ProbabilityTheory Set

namespace CertifiedJL
namespace Probability

/-- The exactly integrable envelope used for the Gaussian reference tail. -/
noncomputable def gaussianReferenceTailEnvelope
    (U₀ u : ℝ) : ℝ :=
  if U₀ < |u| then
    Real.exp (-(u ^ 2) / 2) * |u| /
      (2 * Real.pi * U₀ ^ 2)
  else 0

theorem gaussianReferenceTailEnvelope_nonneg
    (U₀ u : ℝ) :
    0 ≤ gaussianReferenceTailEnvelope U₀ u := by
  unfold gaussianReferenceTailEnvelope
  split_ifs
  · positivity
  · exact le_rfl

theorem measurable_gaussianReferenceTailEnvelope
    (U₀ : ℝ) :
    Measurable (gaussianReferenceTailEnvelope U₀) := by
  unfold gaussianReferenceTailEnvelope
  apply Measurable.ite
    (measurableSet_lt measurable_const continuous_abs.measurable)
  · fun_prop
  · fun_prop

/--
The strict two-sided first-moment Gaussian tail has an exact elementary
value.  The endpoint convention is immaterial to Lebesgue integration, but
the theorem is stated with the strict event used by the paper.
-/
theorem integral_abs_gt_mul_exp_neg_half_sq
    {b : ℝ} (hb : 0 ≤ b) :
    (∫ u : ℝ in {u | b < |u|},
        |u| * Real.exp (-(u ^ 2) / 2)) =
      2 * Real.exp (-(b ^ 2) / 2) := by
  let kernel : ℝ → ℝ :=
    fun u => |u| * Real.exp (-(u ^ 2) / 2)
  have hset :
      {u : ℝ | b < |u|} =
        Iio (-b) ∪ Ioi b := by
    ext u
    simp only [mem_setOf_eq, mem_union, mem_Iio, mem_Ioi, lt_abs]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl h
  have hdisjoint : Disjoint (Iio (-b)) (Ioi b) := by
    rw [Set.disjoint_left]
    intro u huLeft huRight
    rw [mem_Iio] at huLeft
    rw [mem_Ioi] at huRight
    linarith
  have hkernelIntegrable : Integrable kernel := by
    have hbase :=
      integrable_mul_exp_neg_mul_sq
        (by norm_num : (0 : ℝ) < 1 / 2)
    refine hbase.norm.congr ?_
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.exp_nonneg _)]
    simp only [kernel]
    congr 2
    ring
  have heven (u : ℝ) : kernel (-u) = kernel u := by
    simp only [kernel, abs_neg, neg_sq]
  have hleft :
      (∫ u : ℝ in Iio (-b), kernel u) =
        ∫ u : ℝ in Ioi b, kernel u := by
    rw [← integral_Iic_eq_integral_Iio]
    calc
      (∫ u : ℝ in Iic (-b), kernel u) =
          ∫ u : ℝ in Iic (-b), kernel (-u) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro u _
        exact (heven u).symm
      _ = ∫ u : ℝ in Ioi b, kernel u := by
        simpa only [neg_neg] using integral_comp_neg_Iic (-b) kernel
  have hright :
      (∫ u : ℝ in Ioi b, kernel u) =
        Real.exp (-(b ^ 2) / 2) := by
    calc
      (∫ u : ℝ in Ioi b, kernel u) =
          ∫ u : ℝ in Ioi b,
            u * Real.exp (-(1 / 2 : ℝ) * u ^ 2) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        dsimp only [kernel]
        rw [abs_of_nonneg (hb.trans hu.le)]
        congr 2
        ring
      _ = Real.exp (-(1 / 2 : ℝ) * b ^ 2) /
          (2 * (1 / 2 : ℝ)) :=
        integral_Ioi_mul_exp_neg_mul_sq
          (by norm_num : (0 : ℝ) < 1 / 2) hb
      _ = Real.exp (-(b ^ 2) / 2) := by
        norm_num
        ring
  change (∫ u : ℝ in {u | b < |u|}, kernel u) = _
  rw [hset, setIntegral_union hdisjoint measurableSet_Ioi
    hkernelIntegrable.integrableOn hkernelIntegrable.integrableOn,
    hleft, hright]
  ring

theorem integrable_gaussianReferenceTailEnvelope
    (U₀ : ℝ) :
    Integrable (gaussianReferenceTailEnvelope U₀) := by
  let kernel : ℝ → ℝ :=
    fun u => |u| * Real.exp (-(u ^ 2) / 2) /
      (2 * Real.pi * U₀ ^ 2)
  have hkernel : Integrable kernel := by
    have hbase :=
      (integrable_mul_exp_neg_mul_sq
        (by norm_num : (0 : ℝ) < 1 / 2)).norm
    refine (hbase.div_const (2 * Real.pi * U₀ ^ 2)).congr ?_
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.exp_nonneg _)]
    simp only [kernel]
    congr 3
    ring
  have hindicator :
      gaussianReferenceTailEnvelope U₀ =
        {u : ℝ | U₀ < |u|}.indicator kernel := by
    funext u
    by_cases hu : U₀ < |u|
    · simp [gaussianReferenceTailEnvelope, kernel, hu, mul_comm]
    · simp [gaussianReferenceTailEnvelope, kernel, hu]
  rw [hindicator]
  exact hkernel.indicator
    (measurableSet_lt measurable_const continuous_abs.measurable)

/-- Exact integral of the first-moment envelope for the reference tail. -/
theorem integral_gaussianReferenceTailEnvelope
    {U₀ : ℝ} (hU₀ : 0 < U₀) :
    (∫ u : ℝ, gaussianReferenceTailEnvelope U₀ u) =
      Real.exp (-(U₀ ^ 2) / 2) /
        (Real.pi * U₀ ^ 2) := by
  have hden : 2 * Real.pi * U₀ ^ 2 ≠ 0 := by
    positivity
  rw [show (∫ u : ℝ, gaussianReferenceTailEnvelope U₀ u) =
      ∫ u : ℝ in {u | U₀ < |u|},
        (|u| * Real.exp (-(u ^ 2) / 2)) /
          (2 * Real.pi * U₀ ^ 2) by
    rw [← integral_indicator
      (measurableSet_lt measurable_const continuous_abs.measurable)]
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu : U₀ < |u|
    · simp [gaussianReferenceTailEnvelope, hu, mul_comm]
    · simp [gaussianReferenceTailEnvelope, hu]]
  rw [integral_div,
    integral_abs_gt_mul_exp_neg_half_sq hU₀.le]
  field_simp

theorem integrable_prawitzReferenceTailTerm_standardGaussian
    {U₀ : ℝ} (hU₀ : 0 < U₀) :
    Integrable
      (prawitzReferenceTailTerm (gaussianReal 0 1) U₀) := by
  refine Integrable.mono'
    (integrable_gaussianReferenceTailEnvelope U₀)
    (measurable_prawitzReferenceTailTerm
      (gaussianReal 0 1) U₀).aestronglyMeasurable
    (ae_of_all volume fun u => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg
      (prawitzReferenceTailTerm_nonneg
        (gaussianReal 0 1) U₀ u)]
  exact prawitzReferenceTailTerm_standardGaussian_le hU₀

/--
Closed-form standard-Gaussian reference-tail estimate in the real-integral
form.  This is the fourth term of the Prawitz four-term decomposition.
-/
theorem integral_prawitzReferenceTailTerm_standardGaussian_le
    {U₀ : ℝ} (hU₀ : 0 < U₀) :
    (∫ u : ℝ,
        prawitzReferenceTailTerm (gaussianReal 0 1) U₀ u) ≤
      Real.exp (-(U₀ ^ 2) / 2) /
        (Real.pi * U₀ ^ 2) := by
  calc
    (∫ u : ℝ,
        prawitzReferenceTailTerm (gaussianReal 0 1) U₀ u) ≤
        ∫ u : ℝ, gaussianReferenceTailEnvelope U₀ u := by
      exact integral_mono
        (integrable_prawitzReferenceTailTerm_standardGaussian hU₀)
        (integrable_gaussianReferenceTailEnvelope U₀)
        (fun u =>
          prawitzReferenceTailTerm_standardGaussian_le hU₀)
    _ = _ := integral_gaussianReferenceTailEnvelope hU₀

/--
Closed-form standard-Gaussian reference-tail estimate in the nonnegative
integral form consumed by the Prawitz smoothing decomposition.
-/
theorem lintegral_prawitzReferenceTailTerm_standardGaussian_le
    {U₀ : ℝ} (hU₀ : 0 < U₀) :
    (∫⁻ u : ℝ, ENNReal.ofReal
        (prawitzReferenceTailTerm
          (gaussianReal 0 1) U₀ u) ∂volume) ≤
      ENNReal.ofReal
        (Real.exp (-(U₀ ^ 2) / 2) /
          (Real.pi * U₀ ^ 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_prawitzReferenceTailTerm_standardGaussian hU₀)
    (ae_of_all volume fun u =>
      prawitzReferenceTailTerm_nonneg
        (gaussianReal 0 1) U₀ u)]
  exact ENNReal.ofReal_le_ofReal
    (integral_prawitzReferenceTailTerm_standardGaussian_le hU₀)

/-! ## Quantitative cancellation in the Gaussian core correction -/

private theorem abs_cos_sub_one_le
    {x : ℝ} (hx : |x| ≤ 1) :
    |Real.cos x - 1| ≤
      (53 / 96 : ℝ) * |x| ^ 2 := by
  have hpow : |x| ^ 4 ≤ |x| ^ 2 := by
    have hx0 : 0 ≤ |x| := abs_nonneg x
    have hsq : |x| ^ 2 ≤ 1 := pow_le_one₀ hx0 hx
    nlinarith [sq_nonneg (|x| ^ 2)]
  calc
    |Real.cos x - 1| =
        |(Real.cos x - (1 - x ^ 2 / 2)) - x ^ 2 / 2| := by
      congr 1
      ring
    _ ≤ |Real.cos x - (1 - x ^ 2 / 2)| +
        |x ^ 2 / 2| := abs_sub _ _
    _ ≤ |x| ^ 4 * (5 / 96 : ℝ) +
        |x ^ 2 / 2| := by
      gcongr
      exact Real.cos_bound hx
    _ ≤ (53 / 96 : ℝ) * |x| ^ 2 := by
      rw [abs_div, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith

private theorem abs_sub_sin_le
    {x : ℝ} (hx : |x| ≤ 1) :
    |x - Real.sin x| ≤
      (21 / 96 : ℝ) * |x| ^ 3 := by
  have hpow : |x| ^ 4 ≤ |x| ^ 3 := by
    have hx0 : 0 ≤ |x| := abs_nonneg x
    have hcubic : 0 ≤ |x| ^ 3 := pow_nonneg hx0 _
    nlinarith [mul_nonneg hcubic (sub_nonneg.mpr hx)]
  have hsin := Real.sin_bound hx
  calc
    |x - Real.sin x| =
        |-(Real.sin x - (x - x ^ 3 / 6)) + x ^ 3 / 6| := by
      congr 1
      ring
    _ ≤ |-(Real.sin x - (x - x ^ 3 / 6))| +
        |x ^ 3 / 6| := abs_add_le _ _
    _ = |Real.sin x - (x - x ^ 3 / 6)| +
        |x ^ 3 / 6| := by rw [abs_neg]
    _ ≤ |x| ^ 4 * (5 / 96 : ℝ) +
        |x ^ 3 / 6| := by
      have hsin' :
          |Real.sin x - (x - x ^ 3 / 6)| ≤ |x| ^ 4 * (5 / 96) := by
        calc
          |Real.sin x - (x - x ^ 3 / 6)| ≤ |x| ^ 5 / 100 := hsin
          _ ≤ |x| ^ 4 / 100 := by
            apply div_le_div_of_nonneg_right _ (by norm_num)
            calc
              |x| ^ 5 = |x| ^ 4 * |x| := by ring
              _ ≤ |x| ^ 4 * 1 :=
                mul_le_mul_of_nonneg_left hx (pow_nonneg (abs_nonneg x) 4)
              _ = |x| ^ 4 := by ring
          _ ≤ |x| ^ 4 * (5 / 96) := by
            calc
              |x| ^ 4 / 100 = |x| ^ 4 * (1 / 100) := by ring
              _ ≤ |x| ^ 4 * (5 / 96) :=
                mul_le_mul_of_nonneg_left (by norm_num)
                  (pow_nonneg (abs_nonneg x) 4)
      exact add_le_add hsin' le_rfl
    _ ≤ (21 / 96 : ℝ) * |x| ^ 3 := by
      rw [abs_div, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
      nlinarith

private theorem abs_mul_cos_sub_sin_le
    {x : ℝ} (hx : |x| ≤ 1) :
    |x * Real.cos x - Real.sin x| ≤
      (37 / 48 : ℝ) * |x| ^ 3 := by
  calc
    |x * Real.cos x - Real.sin x| =
        |x * (Real.cos x - 1) +
          (x - Real.sin x)| := by
      congr 1
      ring
    _ ≤ |x * (Real.cos x - 1)| +
        |x - Real.sin x| := abs_add_le _ _
    _ = |x| * |Real.cos x - 1| +
        |x - Real.sin x| := by rw [abs_mul]
    _ ≤ |x| * ((53 / 96 : ℝ) * |x| ^ 2) +
        (21 / 96 : ℝ) * |x| ^ 3 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (abs_cos_sub_one_le hx) (abs_nonneg x))
        (abs_sub_sin_le hx)
    _ = (37 / 48 : ℝ) * |x| ^ 3 := by ring

/--
Quantitative cancellation of the removable cotangent singularity.  The
constant is deliberately rational; the only band condition is
`|πt| ≤ 1`.
-/
theorem abs_regularizedFrequencyCot_sub_inv_pi_le
    {t : ℝ} (ht : |Real.pi * t| ≤ 1) :
    |regularizedFrequencyCot t - 1 / Real.pi| ≤
      (37 / 96 : ℝ) * Real.pi ^ 2 * |t| ^ 2 := by
  by_cases ht0 : t = 0
  · subst t
    simp
  let x : ℝ := Real.pi * t
  have hx : |x| ≤ 1 := by simpa only [x] using ht
  have hx0 : x ≠ 0 :=
    mul_ne_zero Real.pi_ne_zero ht0
  have habst : |t| < 1 := by
    have hpione : 1 < Real.pi := by
      exact lt_of_lt_of_le one_lt_two Real.two_le_pi
    have hmul : Real.pi * |t| ≤ 1 := by
      simpa [abs_mul, abs_of_pos Real.pi_pos] using ht
    nlinarith [abs_nonneg t]
  have hsinLower :
      2 / Real.pi * |x| ≤ |Real.sin x| := by
    apply Real.mul_abs_le_abs_sin
    exact hx.trans <| by
      nlinarith [Real.two_le_pi]
  have hsinPos : 0 < |Real.sin x| := by
    have hxPos : 0 < |x| := abs_pos.mpr hx0
    have hcoef : 0 < 2 / Real.pi := div_pos (by norm_num) Real.pi_pos
    exact (mul_pos hcoef hxPos).trans_le hsinLower
  have hdenPos : 0 < Real.pi * |Real.sin x| :=
    mul_pos Real.pi_pos hsinPos
  have hdenLower :
      2 * |x| ≤ Real.pi * |Real.sin x| := by
    calc
      2 * |x| =
          Real.pi * ((2 / Real.pi) * |x|) := by
        field_simp [Real.pi_ne_zero]
      _ ≤ Real.pi * |Real.sin x| :=
        mul_le_mul_of_nonneg_left hsinLower Real.pi_pos.le
  have hidentity :
      regularizedFrequencyCot t - 1 / Real.pi =
        (x * Real.cos x - Real.sin x) /
          (Real.pi * Real.sin x) := by
    rw [regularizedFrequencyCot_eq_mul_cot habst ht0,
      Real.cot_eq_cos_div_sin]
    dsimp only [x]
    have hsinNe : Real.sin (Real.pi * t) ≠ 0 := by
      simpa only [x] using (abs_pos.mp hsinPos)
    have hsinNe' : Real.sin (t * Real.pi) ≠ 0 := by
      simpa only [mul_comm] using hsinNe
    field_simp [Real.pi_ne_zero, hsinNe, hsinNe']
  rw [hidentity, abs_div, abs_mul, abs_of_pos Real.pi_pos]
  have hnum :=
    abs_mul_cos_sub_sin_le hx
  have hratio :
      |x * Real.cos x - Real.sin x| /
          (Real.pi * |Real.sin x|) ≤
        ((37 / 48 : ℝ) * |x| ^ 3) /
          (2 * |x|) := by
    exact div_le_div₀
      (mul_nonneg (by norm_num) (pow_nonneg (abs_nonneg x) _))
      hnum
      (mul_pos (by norm_num) (abs_pos.mpr hx0))
      hdenLower
  calc
    |x * Real.cos x - Real.sin x| /
        (Real.pi * |Real.sin x|) ≤
        ((37 / 48 : ℝ) * |x| ^ 3) /
          (2 * |x|) := hratio
    _ = (37 / 96 : ℝ) * |x| ^ 2 := by
      field_simp [abs_ne_zero.mpr hx0]
      ring
    _ = (37 / 96 : ℝ) * Real.pi ^ 2 * |t| ^ 2 := by
      dsimp only [x]
      rw [abs_mul, abs_of_pos Real.pi_pos]
      ring

/--
The regularized Prawitz remainder vanishes at an explicit quadratic rate in
its imaginary component.  The linear real component is kept exact enough
for the later cutoff integral.
-/
theorem norm_prawitzFrequencyRemainder_le
    {t : ℝ} (htInterior : |t| < 1)
    (htTaylor : |Real.pi * t| ≤ 1) :
    ‖prawitzFrequencyRemainder t‖ ≤
      |t| / 2 +
        (37 / 192 : ℝ) * Real.pi ^ 2 * |t| ^ 2 := by
  have habsNonneg : 0 ≤ |t| := abs_nonneg t
  have honeSub : 0 ≤ 1 - |t| := sub_nonneg.mpr htInterior.le
  let re : ℝ := t * (1 - |t|) / 2
  let im : ℝ :=
    ((1 - |t|) * regularizedFrequencyCot t +
      |t| / Real.pi) / 2 - 1 / (2 * Real.pi)
  have him :
      im = (1 - |t|) / 2 *
        (regularizedFrequencyCot t - 1 / Real.pi) := by
    dsimp only [im]
    field_simp [Real.pi_ne_zero]
    ring
  have hreBound :
      |re| ≤ |t| / 2 := by
    dsimp only [re]
    rw [abs_div, abs_mul, abs_of_nonneg honeSub,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [mul_nonneg habsNonneg honeSub]
  have himBound :
      |im| ≤
        (37 / 192 : ℝ) * Real.pi ^ 2 * |t| ^ 2 := by
    rw [him, abs_mul, abs_div,
      abs_of_nonneg honeSub,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      (1 - |t|) / 2 *
          |regularizedFrequencyCot t - 1 / Real.pi| ≤
          (1 - |t|) / 2 *
            ((37 / 96 : ℝ) * Real.pi ^ 2 * |t| ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (abs_regularizedFrequencyCot_sub_inv_pi_le htTaylor)
          (div_nonneg honeSub (by norm_num))
      _ ≤ (1 / 2 : ℝ) *
            ((37 / 96 : ℝ) * Real.pi ^ 2 * |t| ^ 2) := by
        have hright :
            0 ≤ (37 / 96 : ℝ) * Real.pi ^ 2 * |t| ^ 2 := by
          positivity
        exact mul_le_mul_of_nonneg_right
          (by nlinarith) hright
      _ = (37 / 192 : ℝ) * Real.pi ^ 2 * |t| ^ 2 := by
        ring
  have hkernel :
      prawitzFrequencyRemainder t =
        (re : ℂ) + (im : ℂ) * Complex.I := by
    rw [prawitzFrequencyRemainder,
      regularizedPrawitzFrequencyKernel, if_pos htInterior]
    dsimp only [re, im]
    push_cast
    field_simp [Real.pi_ne_zero]
    ring
  rw [hkernel]
  calc
    ‖(re : ℂ) + (im : ℂ) * Complex.I‖ ≤
        ‖(re : ℂ)‖ + ‖(im : ℂ) * Complex.I‖ :=
      norm_add_le _ _
    _ = |re| + |im| := by simp
    _ ≤ |t| / 2 +
        (37 / 192 : ℝ) * Real.pi ^ 2 * |t| ^ 2 :=
      add_le_add hreBound himBound

/--
Away from zero, the scaled-kernel correction is exactly the regularized
frequency remainder divided by the original frequency.
-/
theorem scaledPrawitzKernel_sub_principalCDFKernel_eq
    {U u : ℝ} (hU : U ≠ 0) (hu : u ≠ 0)
    (hinside : |u / U| < 1) :
    scaledPrawitzKernel U u - principalCDFKernel u =
      ((1 / u : ℝ) : ℂ) *
        prawitzFrequencyRemainder (u / U) := by
  have hratio : u / U ≠ 0 := div_ne_zero hu hU
  rw [scaledPrawitzKernel, prawitzFrequencyRemainder,
    regularizedPrawitzFrequencyKernel_eq_mul hinside hratio]
  unfold principalCDFKernel
  push_cast
  field_simp [hU, hu, Real.pi_ne_zero]

/--
Exact nonsingular scalar interface for the outer-band kernel.  It replaces
the norm of the singular Prawitz kernel by the norm of its regularized
frequency kernel divided by the original frequency.  A sharp scalar bound
on `‖regularizedPrawitzFrequencyKernel t‖` can therefore be inserted without
changing the measure-theoretic outer integral.
-/
theorem norm_scaledPrawitzKernel_eq_regularizedFrequency_div_abs
    {U u : ℝ} (hU : 0 < U) (hu : u ≠ 0)
    (hinside : |u| < U) :
    ‖scaledPrawitzKernel U u‖ =
      ‖regularizedPrawitzFrequencyKernel (u / U)‖ / |u| := by
  have hratio : u / U ≠ 0 := div_ne_zero hu hU.ne'
  have hratioInside : |u / U| < 1 := by
    rw [abs_div, abs_of_pos hU]
    exact (div_lt_one hU).2 hinside
  rw [regularizedPrawitzFrequencyKernel_eq_mul
    hratioInside hratio, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_div, abs_of_pos hU]
  unfold scaledPrawitzKernel
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_div, abs_one, abs_of_pos hU]
  field_simp [abs_ne_zero.mpr hu]

/--
Pointwise bounded form of the Prawitz core correction.  The Taylor band
`|π(u/U)| ≤ 1` is explicit and will be discharged uniformly from the cutoff
condition `π U₀ ≤ U`.
-/
theorem norm_scaledPrawitzKernel_sub_principalCDFKernel_le
    {U u : ℝ} (hU : 0 < U)
    (hinside : |u / U| < 1)
    (hTaylor : |Real.pi * (u / U)| ≤ 1) :
    ‖scaledPrawitzKernel U u - principalCDFKernel u‖ ≤
      1 / (2 * U) +
        (37 / 192 : ℝ) * Real.pi ^ 2 * |u| / U ^ 2 := by
  by_cases hu : u = 0
  · subst u
    simp [scaledPrawitzKernel, principalCDFKernel,
      abs_of_pos hU]
  · have hrem :=
      norm_prawitzFrequencyRemainder_le hinside hTaylor
    rw [scaledPrawitzKernel_sub_principalCDFKernel_eq
      hU.ne' hu hinside, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_div, abs_one,
      div_eq_mul_inv]
    have huAbs : 0 < |u| := abs_pos.mpr hu
    have hUAbs : |U| = U := abs_of_pos hU
    have hratioAbs : |u / U| = |u| / U := by
      rw [abs_div, hUAbs]
    calc
      (1 / |u|) *
          ‖prawitzFrequencyRemainder (u / U)‖ ≤
          (1 / |u|) *
            (|u / U| / 2 +
              (37 / 192 : ℝ) * Real.pi ^ 2 *
                |u / U| ^ 2) := by
        exact mul_le_mul_of_nonneg_left hrem
          (by positivity)
      _ = 1 / (2 * U) +
          (37 / 192 : ℝ) * Real.pi ^ 2 * |u| /
            U ^ 2 := by
        rw [hratioAbs]
        field_simp [hu, hU.ne']

/--
Scaled form of Prawitz's global correction inequality `I.30`.  Unlike the
older local Taylor estimate above, this bound is valid on the full kernel
band `|u| ≤ U` and retains the negative linear term that is numerically
essential in the closed Gaussian budget.
-/
theorem norm_scaledPrawitzKernel_sub_principalCDFKernel_le_global
    {U u : ℝ} (hU : 0 < U) (hinside : |u| ≤ U) :
    ‖scaledPrawitzKernel U u - principalCDFKernel u‖ ≤
      (1 - |u| / U +
        Real.pi ^ 2 * (u / U) ^ 2 / 18) / (2 * U) := by
  have hratio : |u / U| ≤ 1 := by
    rw [abs_div, abs_of_pos hU, div_le_one hU]
    exact hinside
  by_cases hu : u = 0
  · subst u
    simp [scaledPrawitzKernel, principalCDFKernel,
      abs_of_pos hU]
  · have hidentity :
        scaledPrawitzKernel U u - principalCDFKernel u =
          (((1 / U : ℝ) : ℂ) *
            (prawitzKernel (u / U) -
              Complex.I /
                ((2 : ℂ) * (Real.pi : ℂ) *
                  ((u / U : ℝ) : ℂ)))) := by
      unfold scaledPrawitzKernel principalCDFKernel
      push_cast
      field_simp [hU.ne', hu, Real.pi_ne_zero]
    rw [hidentity, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_div, abs_one, abs_of_pos hU]
    have hI30 :=
      norm_prawitzKernel_sub_principal_le hratio
    rw [abs_div, abs_of_pos hU] at hI30
    calc
      (1 / U) *
          ‖prawitzKernel (u / U) -
            Complex.I /
              ((2 : ℂ) * (Real.pi : ℂ) *
                ((u / U : ℝ) : ℂ))‖ ≤
          (1 / U) *
            ((1 - |u| / U +
              Real.pi ^ 2 * (u / U) ^ 2 / 18) / 2) := by
        exact mul_le_mul_of_nonneg_left hI30 (by positivity)
      _ = (1 - |u| / U +
          Real.pi ^ 2 * (u / U) ^ 2 / 18) /
            (2 * U) := by
        field_simp [hU.ne']

/-! ## Gaussian-weighted core correction -/

/-- Integrability of the unnormalized standard-Gaussian kernel. -/
theorem integrable_exp_neg_half_sq :
    Integrable (fun u : ℝ => Real.exp (-(u ^ 2) / 2)) := by
  convert
    integrable_exp_neg_mul_sq
      (by norm_num : (0 : ℝ) < 1 / 2) using 1
  ext u
  congr 1
  ring

/-- The unnormalized standard-Gaussian kernel has total mass `√(2π)`. -/
theorem integral_exp_neg_half_sq :
    (∫ u : ℝ, Real.exp (-(u ^ 2) / 2)) =
      Real.sqrt (2 * Real.pi) := by
  rw [show (fun u : ℝ => Real.exp (-(u ^ 2) / 2)) =
      (fun u : ℝ => Real.exp (-(1 / 2 : ℝ) * u ^ 2)) by
    funext u
    congr 1
    ring]
  rw [integral_gaussian]
  congr 1
  ring

/-- Integrability of the first absolute moment of the Gaussian kernel. -/
theorem integrable_abs_mul_exp_neg_half_sq :
    Integrable
      (fun u : ℝ => |u| * Real.exp (-(u ^ 2) / 2)) := by
  have hbase :=
    (integrable_mul_exp_neg_mul_sq
      (by norm_num : (0 : ℝ) < 1 / 2)).norm
  refine hbase.congr ?_
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.exp_nonneg _)]
  congr 2
  ring

/-- The first absolute moment of the unnormalized Gaussian kernel is `2`. -/
theorem integral_abs_mul_exp_neg_half_sq :
    (∫ u : ℝ, |u| * Real.exp (-(u ^ 2) / 2)) = 2 := by
  rw [show (∫ u : ℝ, |u| * Real.exp (-(u ^ 2) / 2)) =
      ∫ u : ℝ in {u | (0 : ℝ) < |u|},
        |u| * Real.exp (-(u ^ 2) / 2) by
    rw [← integral_indicator
      (measurableSet_lt measurable_const continuous_abs.measurable)]
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu : u = 0
    · subst u
      simp
    · simp [hu]]
  simpa using
    integral_abs_gt_mul_exp_neg_half_sq
      (b := 0) (by norm_num)

/-- Integrability of the second moment of the Gaussian kernel. -/
theorem integrable_sq_mul_exp_neg_half_sq :
    Integrable
      (fun u : ℝ => u ^ 2 * Real.exp (-(u ^ 2) / 2)) := by
  have h :=
    integrable_rpow_mul_exp_neg_mul_sq
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (-1 : ℝ) < 2)
  convert h using 1
  ext u
  rw [Real.rpow_two]
  congr 2
  ring

/--
The second moment of the unnormalized standard-Gaussian kernel is again
`√(2π)`.
-/
theorem integral_sq_mul_exp_neg_half_sq :
    (∫ u : ℝ, u ^ 2 * Real.exp (-(u ^ 2) / 2)) =
      Real.sqrt (2 * Real.pi) := by
  have hvar :
      (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
    have h :=
      variance_fun_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_eq_integral
        (measurable_id' : Measurable (fun x : ℝ => x)).aemeasurable,
      integral_id_gaussianReal] at h
    simpa using h
  rw [integral_gaussianReal_eq_integral_smul
    (by exact one_ne_zero : (1 : NNReal) ≠ 0),
    gaussianPDFReal_def] at hvar
  simp only [NNReal.coe_one, mul_one, sub_zero,
    smul_eq_mul] at hvar
  rw [show (∫ x : ℝ,
      (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-(x ^ 2) / 2) * x ^ 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        ∫ x : ℝ, x ^ 2 * Real.exp (-(x ^ 2) / 2) by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring] at hvar
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by
    positivity
  calc
    (∫ u : ℝ, u ^ 2 * Real.exp (-(u ^ 2) / 2)) =
        Real.sqrt (2 * Real.pi) *
          ((Real.sqrt (2 * Real.pi))⁻¹ *
            ∫ u : ℝ, u ^ 2 * Real.exp (-(u ^ 2) / 2)) := by
      field_simp [hsqrt.ne']
    _ = Real.sqrt (2 * Real.pi) := by
      rw [hvar, mul_one]

/--
Exact first absolute moment on the symmetric core.  Unlike the earlier
uniform-height estimate, this identity preserves the Gaussian damping and
the cutoff dependence.
-/
theorem integral_Icc_abs_mul_exp_neg_half_sq
    {b : ℝ} (hb : 0 ≤ b) :
    (∫ u : ℝ in Icc (-b) b,
        |u| * Real.exp (-(u ^ 2) / 2)) =
      2 * (1 - Real.exp (-(b ^ 2) / 2)) := by
  let f : ℝ → ℝ :=
    fun u => |u| * Real.exp (-(u ^ 2) / 2)
  have hset :
      {u : ℝ | b < |u|}ᶜ = Icc (-b) b := by
    ext u
    simp only [mem_compl_iff, mem_setOf_eq, not_lt, mem_Icc, abs_le]
  have hsum := integral_add_compl (μ := volume)
    (s := {u : ℝ | b < |u|})
    (measurableSet_lt measurable_const continuous_abs.measurable)
    integrable_abs_mul_exp_neg_half_sq
  rw [hset] at hsum
  have htail :
      (∫ u : ℝ in {u | b < |u|}, f u) =
        2 * Real.exp (-(b ^ 2) / 2) := by
    exact integral_abs_gt_mul_exp_neg_half_sq hb
  have hfull : (∫ u : ℝ, f u) = 2 :=
    integral_abs_mul_exp_neg_half_sq
  rw [hfull, htail] at hsum
  change (∫ u : ℝ in Icc (-b) b, f u) =
    2 * (1 - Real.exp (-(b ^ 2) / 2))
  linarith

/--
The integrable Gaussian-weighted envelope for the Prawitz core correction.
It keeps the Gaussian factor that is lost by a uniform-height bound.
-/
noncomputable def gaussianWeightedCoreEnvelope
    (U u : ℝ) : ℝ :=
  (1 / (2 * U)) * Real.exp (-(u ^ 2) / 2) +
    ((37 / 192 : ℝ) * Real.pi ^ 2 / U ^ 2) *
      (|u| * Real.exp (-(u ^ 2) / 2))

theorem gaussianWeightedCoreEnvelope_nonneg
    {U : ℝ} (hU : 0 < U) (u : ℝ) :
    0 ≤ gaussianWeightedCoreEnvelope U u := by
  unfold gaussianWeightedCoreEnvelope
  positivity

theorem integrable_gaussianWeightedCoreEnvelope
    {U : ℝ} (_hU : 0 < U) :
    Integrable (gaussianWeightedCoreEnvelope U) := by
  unfold gaussianWeightedCoreEnvelope
  exact
    (integrable_exp_neg_half_sq.const_mul (1 / (2 * U))
      |>.add
        (integrable_abs_mul_exp_neg_half_sq.const_mul
          ((37 / 192 : ℝ) * Real.pi ^ 2 / U ^ 2)))

/-- Exact integral of the global Gaussian-weighted core envelope. -/
theorem integral_gaussianWeightedCoreEnvelope
    {U : ℝ} (_hU : 0 < U) :
    (∫ u : ℝ, gaussianWeightedCoreEnvelope U u) =
      Real.sqrt (2 * Real.pi) / (2 * U) +
        (37 / 96 : ℝ) * Real.pi ^ 2 / U ^ 2 := by
  unfold gaussianWeightedCoreEnvelope
  rw [integral_add, integral_const_mul, integral_const_mul,
    integral_exp_neg_half_sq, integral_abs_mul_exp_neg_half_sq]
  · ring
  · exact integrable_exp_neg_half_sq.const_mul _
  · exact integrable_abs_mul_exp_neg_half_sq.const_mul _

/--
Pointwise Gaussian-weighted bound for the standard-Gaussian core correction.
The right-hand side is global and integrable, so no interval-length loss is
introduced.
-/
theorem prawitzCoreCorrectionTerm_standardGaussian_le_weighted
    {U₀ U u : ℝ} (_hU₀ : 0 ≤ U₀) (hU : 0 < U)
    (hTaylorCut : Real.pi * U₀ ≤ U) :
    prawitzCoreCorrectionTerm
        (gaussianReal 0 1) U₀ U u ≤
      gaussianWeightedCoreEnvelope U u := by
  by_cases hcore : |u| ≤ U₀
  · have hpione : 1 < Real.pi :=
      lt_of_lt_of_le one_lt_two Real.two_le_pi
    have hU₀ltU : U₀ < U := by
      nlinarith
    have hinside : |u / U| < 1 := by
      rw [abs_div, abs_of_pos hU]
      exact (div_lt_one hU).2 (hcore.trans_lt hU₀ltU)
    have hTaylor : |Real.pi * (u / U)| ≤ 1 := by
      rw [abs_mul, abs_of_pos Real.pi_pos, abs_div,
        abs_of_pos hU, ← mul_div_assoc, div_le_one hU]
      exact (mul_le_mul_of_nonneg_left hcore Real.pi_pos.le).trans
        hTaylorCut
    rw [prawitzCoreCorrectionTerm, if_pos hcore,
      norm_charFun_standardGaussian]
    have hnorm :=
      norm_scaledPrawitzKernel_sub_principalCDFKernel_le
        hU hinside hTaylor
    calc
      ‖scaledPrawitzKernel U u - principalCDFKernel u‖ *
          Real.exp (-(u ^ 2) / 2) ≤
          (1 / (2 * U) +
            (37 / 192 : ℝ) * Real.pi ^ 2 * |u| / U ^ 2) *
            Real.exp (-(u ^ 2) / 2) :=
        mul_le_mul_of_nonneg_right hnorm (Real.exp_nonneg _)
      _ = gaussianWeightedCoreEnvelope U u := by
        unfold gaussianWeightedCoreEnvelope
        ring
  · rw [prawitzCoreCorrectionTerm, if_neg hcore]
    exact gaussianWeightedCoreEnvelope_nonneg hU u

/--
Closed Gaussian-weighted estimate for the third term in the Prawitz
decomposition.  In particular, its leading contribution is
`√(2π)/(2U)`, rather than the `U₀/U` produced by the uniform-height route.
-/
theorem lintegral_prawitzCoreCorrectionTerm_standardGaussian_le_weighted
    {U₀ U : ℝ} (hU₀ : 0 ≤ U₀) (hU : 0 < U)
    (hTaylorCut : Real.pi * U₀ ≤ U) :
    (∫⁻ u : ℝ, ENNReal.ofReal
        (prawitzCoreCorrectionTerm
          (gaussianReal 0 1) U₀ U u) ∂volume) ≤
      ENNReal.ofReal
        (Real.sqrt (2 * Real.pi) / (2 * U) +
          (37 / 96 : ℝ) * Real.pi ^ 2 / U ^ 2) := by
  calc
    (∫⁻ u : ℝ, ENNReal.ofReal
        (prawitzCoreCorrectionTerm
          (gaussianReal 0 1) U₀ U u) ∂volume) ≤
        ∫⁻ u : ℝ, ENNReal.ofReal
          (gaussianWeightedCoreEnvelope U u) ∂volume := by
      apply lintegral_mono
      intro u
      exact ENNReal.ofReal_le_ofReal
        (prawitzCoreCorrectionTerm_standardGaussian_le_weighted
          hU₀ hU hTaylorCut)
    _ = ENNReal.ofReal
        (∫ u : ℝ, gaussianWeightedCoreEnvelope U u) := by
      rw [ofReal_integral_eq_lintegral_ofReal
        (integrable_gaussianWeightedCoreEnvelope hU)
        (ae_of_all volume
          (gaussianWeightedCoreEnvelope_nonneg hU))]
    _ = _ := by rw [integral_gaussianWeightedCoreEnvelope hU]

/-! ## Sharp closed Gaussian budget from the global I.30 inequality -/

/--
The Gaussian-weighted `I.30` envelope on the symmetric core.  Its expanded
form deliberately retains the negative first-moment contribution instead of
discarding it by a triangle inequality.
-/
noncomputable def gaussianSharpCoreEnvelope
    (U₀ U u : ℝ) : ℝ :=
  (Icc (-U₀) U₀).indicator
    (fun x =>
      (1 / (2 * U)) * Real.exp (-(x ^ 2) / 2) -
        (1 / (2 * U ^ 2)) *
          (|x| * Real.exp (-(x ^ 2) / 2)) +
        (Real.pi ^ 2 / (36 * U ^ 3)) *
          (x ^ 2 * Real.exp (-(x ^ 2) / 2))) u

theorem integrable_gaussianSharpCoreEnvelope
    {U₀ U : ℝ} :
    Integrable (gaussianSharpCoreEnvelope U₀ U) := by
  unfold gaussianSharpCoreEnvelope
  exact
    ((integrable_exp_neg_half_sq.const_mul (1 / (2 * U))
      |>.sub
        (integrable_abs_mul_exp_neg_half_sq.const_mul
          (1 / (2 * U ^ 2))))
      |>.add
        (integrable_sq_mul_exp_neg_half_sq.const_mul
          (Real.pi ^ 2 / (36 * U ^ 3))))
      |>.indicator measurableSet_Icc

theorem gaussianSharpCoreEnvelope_nonneg
    {U₀ U : ℝ} (_hU₀ : 0 ≤ U₀) (hU : 0 < U)
    (hcut : U₀ ≤ U) (u : ℝ) :
    0 ≤ gaussianSharpCoreEnvelope U₀ U u := by
  by_cases hu : u ∈ Icc (-U₀) U₀
  · have hcore : |u| ≤ U₀ := by
      simpa [abs_le] using hu
    have hnorm :=
      norm_scaledPrawitzKernel_sub_principalCDFKernel_le_global
        hU (hcore.trans hcut)
    rw [gaussianSharpCoreEnvelope, indicator_of_mem hu]
    calc
      0 ≤ ‖scaledPrawitzKernel U u - principalCDFKernel u‖ *
          Real.exp (-(u ^ 2) / 2) := by
        positivity
      _ ≤ ((1 - |u| / U +
            Real.pi ^ 2 * (u / U) ^ 2 / 18) /
              (2 * U)) *
          Real.exp (-(u ^ 2) / 2) :=
        mul_le_mul_of_nonneg_right hnorm (Real.exp_nonneg _)
      _ = (1 / (2 * U)) * Real.exp (-(u ^ 2) / 2) -
          (1 / (2 * U ^ 2)) *
            (|u| * Real.exp (-(u ^ 2) / 2)) +
          (Real.pi ^ 2 / (36 * U ^ 3)) *
            (u ^ 2 * Real.exp (-(u ^ 2) / 2)) := by
        field_simp [hU.ne']
        ring
  · simp [gaussianSharpCoreEnvelope, hu]

/--
Pointwise domination of the standard-Gaussian correction term by the sharp
`I.30` envelope.  The only cutoff condition is the natural full-band
condition `U₀ ≤ U`.
-/
theorem prawitzCoreCorrectionTerm_standardGaussian_le_sharp
    {U₀ U u : ℝ} (_hU₀ : 0 ≤ U₀) (hU : 0 < U)
    (hcut : U₀ ≤ U) :
    prawitzCoreCorrectionTerm
        (gaussianReal 0 1) U₀ U u ≤
      gaussianSharpCoreEnvelope U₀ U u := by
  by_cases hcore : |u| ≤ U₀
  · have huIcc : u ∈ Icc (-U₀) U₀ := by
      simpa [abs_le] using hcore
    rw [prawitzCoreCorrectionTerm, if_pos hcore,
      norm_charFun_standardGaussian, gaussianSharpCoreEnvelope,
      indicator_of_mem huIcc]
    have hnorm :=
      norm_scaledPrawitzKernel_sub_principalCDFKernel_le_global
        hU (hcore.trans hcut)
    calc
      ‖scaledPrawitzKernel U u - principalCDFKernel u‖ *
          Real.exp (-(u ^ 2) / 2) ≤
          ((1 - |u| / U +
              Real.pi ^ 2 * (u / U) ^ 2 / 18) /
                (2 * U)) *
            Real.exp (-(u ^ 2) / 2) :=
        mul_le_mul_of_nonneg_right hnorm (Real.exp_nonneg _)
      _ = (1 / (2 * U)) * Real.exp (-(u ^ 2) / 2) -
          (1 / (2 * U ^ 2)) *
            (|u| * Real.exp (-(u ^ 2) / 2)) +
          (Real.pi ^ 2 / (36 * U ^ 3)) *
            (u ^ 2 * Real.exp (-(u ^ 2) / 2)) := by
        field_simp [hU.ne']
        ring
  · have huIcc : u ∉ Icc (-U₀) U₀ := by
      simpa [abs_le] using hcore
    simp [prawitzCoreCorrectionTerm, hcore,
      gaussianSharpCoreEnvelope, huIcc]

/-- Exact expansion of the sharp envelope into three symmetric moments. -/
theorem integral_gaussianSharpCoreEnvelope_eq
    {U₀ U : ℝ} :
    (∫ u : ℝ, gaussianSharpCoreEnvelope U₀ U u) =
      (1 / (2 * U)) *
          (∫ u : ℝ in Icc (-U₀) U₀,
            Real.exp (-(u ^ 2) / 2)) -
        (1 / (2 * U ^ 2)) *
          (∫ u : ℝ in Icc (-U₀) U₀,
            |u| * Real.exp (-(u ^ 2) / 2)) +
        (Real.pi ^ 2 / (36 * U ^ 3)) *
          (∫ u : ℝ in Icc (-U₀) U₀,
            u ^ 2 * Real.exp (-(u ^ 2) / 2)) := by
  have hzero :
      IntegrableOn (fun u : ℝ =>
        Real.exp (-(u ^ 2) / 2)) (Icc (-U₀) U₀) :=
    integrable_exp_neg_half_sq.integrableOn
  have hone :
      IntegrableOn (fun u : ℝ =>
        |u| * Real.exp (-(u ^ 2) / 2)) (Icc (-U₀) U₀) :=
    integrable_abs_mul_exp_neg_half_sq.integrableOn
  have htwo :
      IntegrableOn (fun u : ℝ =>
        u ^ 2 * Real.exp (-(u ^ 2) / 2)) (Icc (-U₀) U₀) :=
    integrable_sq_mul_exp_neg_half_sq.integrableOn
  unfold gaussianSharpCoreEnvelope
  rw [integral_indicator measurableSet_Icc]
  calc
    (∫ x : ℝ in Icc (-U₀) U₀,
        (1 / (2 * U)) * Real.exp (-(x ^ 2) / 2) -
          (1 / (2 * U ^ 2)) *
            (|x| * Real.exp (-(x ^ 2) / 2)) +
          (Real.pi ^ 2 / (36 * U ^ 3)) *
            (x ^ 2 * Real.exp (-(x ^ 2) / 2))) =
        (∫ x : ℝ in Icc (-U₀) U₀,
          (1 / (2 * U)) * Real.exp (-(x ^ 2) / 2) -
            (1 / (2 * U ^ 2)) *
              (|x| * Real.exp (-(x ^ 2) / 2))) +
        (∫ x : ℝ in Icc (-U₀) U₀,
          (Real.pi ^ 2 / (36 * U ^ 3)) *
            (x ^ 2 * Real.exp (-(x ^ 2) / 2))) := by
      exact integral_add
        ((hzero.const_mul _).sub (hone.const_mul _))
        (htwo.const_mul _)
    _ = ((∫ x : ℝ in Icc (-U₀) U₀,
          (1 / (2 * U)) * Real.exp (-(x ^ 2) / 2)) -
        (∫ x : ℝ in Icc (-U₀) U₀,
          (1 / (2 * U ^ 2)) *
            (|x| * Real.exp (-(x ^ 2) / 2)))) +
        (∫ x : ℝ in Icc (-U₀) U₀,
          (Real.pi ^ 2 / (36 * U ^ 3)) *
            (x ^ 2 * Real.exp (-(x ^ 2) / 2))) := by
      rw [integral_sub (hzero.const_mul _) (hone.const_mul _)]
    _ = _ := by
      rw [integral_const_mul, integral_const_mul,
        integral_const_mul]

/--
Closed upper bound for the sharp Gaussian correction integral.  The middle
term is negative and exact; only the zeroth and second core moments are
enlarged to their full-line values.
-/
noncomputable def prawitzGaussianSharpCoreBudget
    (U₀ U : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi) / (2 * U) -
    (1 - Real.exp (-(U₀ ^ 2) / 2)) / U ^ 2 +
    Real.pi ^ 2 * Real.sqrt (2 * Real.pi) /
      (36 * U ^ 3)

theorem integral_gaussianSharpCoreEnvelope_le_budget
    {U₀ U : ℝ} (hU₀ : 0 ≤ U₀) (hU : 0 < U) :
    (∫ u : ℝ, gaussianSharpCoreEnvelope U₀ U u) ≤
      prawitzGaussianSharpCoreBudget U₀ U := by
  have hzero :
      (∫ u : ℝ in Icc (-U₀) U₀,
          Real.exp (-(u ^ 2) / 2)) ≤
        Real.sqrt (2 * Real.pi) := by
    rw [← integral_exp_neg_half_sq]
    exact integral_mono_measure Measure.restrict_le_self
      (ae_of_all _ (fun u => Real.exp_nonneg _))
      integrable_exp_neg_half_sq
  have htwo :
      (∫ u : ℝ in Icc (-U₀) U₀,
          u ^ 2 * Real.exp (-(u ^ 2) / 2)) ≤
        Real.sqrt (2 * Real.pi) := by
    rw [← integral_sq_mul_exp_neg_half_sq]
    exact integral_mono_measure Measure.restrict_le_self
      (ae_of_all _ (fun u => by positivity))
      integrable_sq_mul_exp_neg_half_sq
  rw [integral_gaussianSharpCoreEnvelope_eq,
    integral_Icc_abs_mul_exp_neg_half_sq hU₀]
  unfold prawitzGaussianSharpCoreBudget
  have hA : 0 ≤ 1 / (2 * U) := by positivity
  have hC : 0 ≤ Real.pi ^ 2 / (36 * U ^ 3) := by
    positivity
  calc
    (1 / (2 * U)) *
          (∫ u : ℝ in Icc (-U₀) U₀,
            Real.exp (-(u ^ 2) / 2)) -
        (1 / (2 * U ^ 2)) *
          (2 * (1 - Real.exp (-(U₀ ^ 2) / 2))) +
        (Real.pi ^ 2 / (36 * U ^ 3)) *
          (∫ u : ℝ in Icc (-U₀) U₀,
            u ^ 2 * Real.exp (-(u ^ 2) / 2)) ≤
        (1 / (2 * U)) * Real.sqrt (2 * Real.pi) -
          (1 / (2 * U ^ 2)) *
            (2 * (1 - Real.exp (-(U₀ ^ 2) / 2))) +
          (Real.pi ^ 2 / (36 * U ^ 3)) *
            Real.sqrt (2 * Real.pi) := by
      gcongr
    _ = Real.sqrt (2 * Real.pi) / (2 * U) -
        (1 - Real.exp (-(U₀ ^ 2) / 2)) / U ^ 2 +
        Real.pi ^ 2 * Real.sqrt (2 * Real.pi) /
          (36 * U ^ 3) := by
      field_simp [hU.ne']

theorem lintegral_prawitzCoreCorrectionTerm_standardGaussian_le_sharp
    {U₀ U : ℝ} (hU₀ : 0 ≤ U₀) (hU : 0 < U)
    (hcut : U₀ ≤ U) :
    (∫⁻ u : ℝ, ENNReal.ofReal
        (prawitzCoreCorrectionTerm
          (gaussianReal 0 1) U₀ U u) ∂volume) ≤
      ENNReal.ofReal
        (prawitzGaussianSharpCoreBudget U₀ U) := by
  calc
    (∫⁻ u : ℝ, ENNReal.ofReal
        (prawitzCoreCorrectionTerm
          (gaussianReal 0 1) U₀ U u) ∂volume) ≤
        ∫⁻ u : ℝ, ENNReal.ofReal
          (gaussianSharpCoreEnvelope U₀ U u) ∂volume := by
      apply lintegral_mono
      intro u
      exact ENNReal.ofReal_le_ofReal
        (prawitzCoreCorrectionTerm_standardGaussian_le_sharp
          hU₀ hU hcut)
    _ = ENNReal.ofReal
        (∫ u : ℝ, gaussianSharpCoreEnvelope U₀ U u) := by
      rw [ofReal_integral_eq_lintegral_ofReal
        integrable_gaussianSharpCoreEnvelope
        (ae_of_all volume
          (gaussianSharpCoreEnvelope_nonneg
            hU₀ hU hcut))]
    _ ≤ ENNReal.ofReal
        (prawitzGaussianSharpCoreBudget U₀ U) := by
      exact ENNReal.ofReal_le_ofReal
        (integral_gaussianSharpCoreEnvelope_le_budget hU₀ hU)

/--
The sharp closed sum of the Gaussian correction and reference-tail terms.
-/
noncomputable def prawitzGaussianSharpClosedBudget
    (U₀ U : ℝ) : ℝ :=
  prawitzGaussianSharpCoreBudget U₀ U +
    Real.exp (-(U₀ ^ 2) / 2) /
      (Real.pi * U₀ ^ 2)

theorem lintegral_prawitzGaussianTerms_standardGaussian_le_sharpBudget
    {U₀ U : ℝ} (hU₀ : 0 < U₀) (hU : 0 < U)
    (hcut : U₀ ≤ U) :
    (∫⁻ u : ℝ, ENNReal.ofReal
        (prawitzCoreCorrectionTerm
          (gaussianReal 0 1) U₀ U u) ∂volume) +
      (∫⁻ u : ℝ, ENNReal.ofReal
        (prawitzReferenceTailTerm
          (gaussianReal 0 1) U₀ u) ∂volume) ≤
      ENNReal.ofReal
        (prawitzGaussianSharpClosedBudget U₀ U) := by
  have hcore :=
    lintegral_prawitzCoreCorrectionTerm_standardGaussian_le_sharp
      hU₀.le hU hcut
  have htail :=
    lintegral_prawitzReferenceTailTerm_standardGaussian_le hU₀
  have hcoreNonneg :
      0 ≤ prawitzGaussianSharpCoreBudget U₀ U := by
    have hintegralNonneg :
        0 ≤ ∫ u : ℝ, gaussianSharpCoreEnvelope U₀ U u :=
      integral_nonneg
        (gaussianSharpCoreEnvelope_nonneg hU₀.le hU hcut)
    exact hintegralNonneg.trans
      (integral_gaussianSharpCoreEnvelope_le_budget hU₀.le hU)
  have htailNonneg :
      0 ≤ Real.exp (-(U₀ ^ 2) / 2) /
        (Real.pi * U₀ ^ 2) := by
    positivity
  calc
    (∫⁻ u : ℝ, ENNReal.ofReal
        (prawitzCoreCorrectionTerm
          (gaussianReal 0 1) U₀ U u) ∂volume) +
      (∫⁻ u : ℝ, ENNReal.ofReal
        (prawitzReferenceTailTerm
          (gaussianReal 0 1) U₀ u) ∂volume) ≤
        ENNReal.ofReal
          (prawitzGaussianSharpCoreBudget U₀ U) +
        ENNReal.ofReal
          (Real.exp (-(U₀ ^ 2) / 2) /
            (Real.pi * U₀ ^ 2)) :=
      add_le_add hcore htail
    _ = ENNReal.ofReal
        (prawitzGaussianSharpClosedBudget U₀ U) := by
      rw [← ENNReal.ofReal_add hcoreNonneg htailNonneg]
      rfl

/--
The two distribution-independent Gaussian contributions after retaining the
Gaussian weight in the Prawitz core correction.
-/
noncomputable def prawitzGaussianWeightedClosedBudget
    (U₀ U : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi) / (2 * U) +
    (37 / 96 : ℝ) * Real.pi ^ 2 / U ^ 2 +
    Real.exp (-(U₀ ^ 2) / 2) /
      (Real.pi * U₀ ^ 2)

theorem prawitzGaussianWeightedClosedBudget_pos
    {U₀ U : ℝ} (hU₀ : 0 < U₀) (hU : 0 < U) :
    0 < prawitzGaussianWeightedClosedBudget U₀ U := by
  unfold prawitzGaussianWeightedClosedBudget
  positivity

/--
The exact interface exported to the scalar Prawitz certificate: the sum of
the Gaussian core-correction and reference-tail integrals is bounded by one
closed function of the two cutoffs.
-/
theorem lintegral_prawitzGaussianTerms_standardGaussian_le_weightedBudget
    {U₀ U : ℝ} (hU₀ : 0 < U₀) (hU : 0 < U)
    (hTaylorCut : Real.pi * U₀ ≤ U) :
    (∫⁻ u : ℝ, ENNReal.ofReal
        (prawitzCoreCorrectionTerm
          (gaussianReal 0 1) U₀ U u) ∂volume) +
      (∫⁻ u : ℝ, ENNReal.ofReal
        (prawitzReferenceTailTerm
          (gaussianReal 0 1) U₀ u) ∂volume) ≤
      ENNReal.ofReal
        (prawitzGaussianWeightedClosedBudget U₀ U) := by
  have hcore :=
    lintegral_prawitzCoreCorrectionTerm_standardGaussian_le_weighted
      hU₀.le hU hTaylorCut
  have htail :=
    lintegral_prawitzReferenceTailTerm_standardGaussian_le hU₀
  have hcoreNonneg :
      0 ≤ Real.sqrt (2 * Real.pi) / (2 * U) +
        (37 / 96 : ℝ) * Real.pi ^ 2 / U ^ 2 := by
    positivity
  have htailNonneg :
      0 ≤ Real.exp (-(U₀ ^ 2) / 2) /
        (Real.pi * U₀ ^ 2) := by
    positivity
  calc
    (∫⁻ u : ℝ, ENNReal.ofReal
        (prawitzCoreCorrectionTerm
          (gaussianReal 0 1) U₀ U u) ∂volume) +
      (∫⁻ u : ℝ, ENNReal.ofReal
        (prawitzReferenceTailTerm
          (gaussianReal 0 1) U₀ u) ∂volume) ≤
        ENNReal.ofReal
          (Real.sqrt (2 * Real.pi) / (2 * U) +
            (37 / 96 : ℝ) * Real.pi ^ 2 / U ^ 2) +
        ENNReal.ofReal
          (Real.exp (-(U₀ ^ 2) / 2) /
            (Real.pi * U₀ ^ 2)) :=
      add_le_add hcore htail
    _ = ENNReal.ofReal
        (prawitzGaussianWeightedClosedBudget U₀ U) := by
      rw [← ENNReal.ofReal_add hcoreNonneg htailNonneg]
      rfl

/-- Uniform height bounding the Gaussian core correction on `[-U₀,U₀]`. -/
noncomputable def gaussianCoreCorrectionHeight
    (U₀ U : ℝ) : ℝ :=
  1 / (2 * U) +
    (37 / 192 : ℝ) * Real.pi ^ 2 * U₀ / U ^ 2

theorem gaussianCoreCorrectionHeight_nonneg
    {U₀ U : ℝ} (hU₀ : 0 ≤ U₀) (hU : 0 < U) :
    0 ≤ gaussianCoreCorrectionHeight U₀ U := by
  unfold gaussianCoreCorrectionHeight
  positivity

/--
Uniform pointwise bound for the standard-Gaussian core correction.  The
cutoff condition `π U₀ ≤ U` implies both `U₀ < U` and the Taylor band.
-/
theorem prawitzCoreCorrectionTerm_standardGaussian_le_height
    {U₀ U u : ℝ} (hU : 0 < U)
    (hTaylorCut : Real.pi * U₀ ≤ U) :
    prawitzCoreCorrectionTerm
        (gaussianReal 0 1) U₀ U u ≤
      (Icc (-U₀) U₀).indicator
        (fun _ => gaussianCoreCorrectionHeight U₀ U) u := by
  by_cases hcore : |u| ≤ U₀
  · have huUpper : u ≤ U₀ := (abs_le.mp hcore).2
    have huLower : -U₀ ≤ u := (abs_le.mp hcore).1
    have huMem : u ∈ Icc (-U₀) U₀ :=
      ⟨huLower, huUpper⟩
    rw [Set.indicator_of_mem huMem]
    have hU₀ltU : U₀ < U := by
      have hpione : 1 < Real.pi :=
        lt_of_lt_of_le one_lt_two Real.two_le_pi
      nlinarith
    have hinside : |u / U| < 1 := by
      rw [abs_div, abs_of_pos hU]
      exact (div_lt_one hU).2 (hcore.trans_lt hU₀ltU)
    have hTaylor : |Real.pi * (u / U)| ≤ 1 := by
      rw [abs_mul, abs_of_pos Real.pi_pos, abs_div,
        abs_of_pos hU]
      rw [← mul_div_assoc]
      rw [div_le_one hU]
      exact (mul_le_mul_of_nonneg_left hcore Real.pi_pos.le).trans
        hTaylorCut
    rw [prawitzCoreCorrectionTerm, if_pos hcore,
      norm_charFun_standardGaussian]
    have hnorm :=
      norm_scaledPrawitzKernel_sub_principalCDFKernel_le
        hU hinside hTaylor
    have hexp :
        Real.exp (-(u ^ 2) / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg u]
    have hnormNonneg :
        0 ≤ ‖scaledPrawitzKernel U u -
          principalCDFKernel u‖ := norm_nonneg _
    calc
      ‖scaledPrawitzKernel U u - principalCDFKernel u‖ *
          Real.exp (-(u ^ 2) / 2) ≤
          ‖scaledPrawitzKernel U u - principalCDFKernel u‖ * 1 :=
        mul_le_mul_of_nonneg_left hexp hnormNonneg
      _ ≤ (1 / (2 * U) +
          (37 / 192 : ℝ) * Real.pi ^ 2 * |u| / U ^ 2) := by
        simpa using hnorm
      _ ≤ gaussianCoreCorrectionHeight U₀ U := by
        unfold gaussianCoreCorrectionHeight
        have hcoef :
            0 ≤ (37 / 192 : ℝ) * Real.pi ^ 2 := by positivity
        have hU2 : 0 < U ^ 2 := sq_pos_of_pos hU
        gcongr
  · have houtside : u ∉ Icc (-U₀) U₀ := by
      intro hu
      exact hcore (abs_le.mpr hu)
    rw [Set.indicator_of_notMem houtside]
    simp [prawitzCoreCorrectionTerm, hcore]

/--
Closed elementary upper bound for the standard-Gaussian core-correction
integral.  It is intentionally expressed only through the positive cutoffs
`U₀`, `U` and `π`; no unevaluated trigonometric integral remains.
-/
theorem lintegral_prawitzCoreCorrectionTerm_standardGaussian_le
    {U₀ U : ℝ} (hU₀ : 0 ≤ U₀) (hU : 0 < U)
    (hTaylorCut : Real.pi * U₀ ≤ U) :
    (∫⁻ u : ℝ, ENNReal.ofReal
        (prawitzCoreCorrectionTerm
          (gaussianReal 0 1) U₀ U u) ∂volume) ≤
      ENNReal.ofReal
        (2 * U₀ * gaussianCoreCorrectionHeight U₀ U) := by
  let height : ℝ := gaussianCoreCorrectionHeight U₀ U
  have hheight : 0 ≤ height := by
    exact gaussianCoreCorrectionHeight_nonneg hU₀ hU
  calc
    (∫⁻ u : ℝ, ENNReal.ofReal
        (prawitzCoreCorrectionTerm
          (gaussianReal 0 1) U₀ U u) ∂volume) ≤
        ∫⁻ u : ℝ, ENNReal.ofReal
          ((Icc (-U₀) U₀).indicator
            (fun _ => height) u) ∂volume := by
      apply lintegral_mono
      intro u
      exact ENNReal.ofReal_le_ofReal
        (prawitzCoreCorrectionTerm_standardGaussian_le_height
          hU hTaylorCut)
    _ = ∫⁻ u : ℝ, (Icc (-U₀) U₀).indicator
          (fun _ => ENNReal.ofReal height) u ∂volume := by
      apply lintegral_congr
      intro u
      by_cases hu : u ∈ Icc (-U₀) U₀
      · simp [hu]
      · simp [hu]
    _ = volume (Icc (-U₀) U₀) *
          ENNReal.ofReal height := by
      rw [lintegral_indicator_const measurableSet_Icc]
      exact mul_comm _ _
    _ = ENNReal.ofReal (2 * U₀ * height) := by
      rw [Real.volume_Icc]
      rw [show U₀ - -U₀ = 2 * U₀ by ring]
      rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hU₀)]
    _ = ENNReal.ofReal
          (2 * U₀ * gaussianCoreCorrectionHeight U₀ U) := rfl

/--
Expanded certificate-facing form of the Gaussian core-correction bound.
-/
theorem lintegral_prawitzCoreCorrectionTerm_standardGaussian_le_explicit
    {U₀ U : ℝ} (hU₀ : 0 ≤ U₀) (hU : 0 < U)
    (hTaylorCut : Real.pi * U₀ ≤ U) :
    (∫⁻ u : ℝ, ENNReal.ofReal
        (prawitzCoreCorrectionTerm
          (gaussianReal 0 1) U₀ U u) ∂volume) ≤
      ENNReal.ofReal
        (U₀ / U +
          (37 / 96 : ℝ) * Real.pi ^ 2 * U₀ ^ 2 /
            U ^ 2) := by
  have hbound :=
    lintegral_prawitzCoreCorrectionTerm_standardGaussian_le
      hU₀ hU hTaylorCut
  convert hbound using 1
  unfold gaussianCoreCorrectionHeight
  congr 1
  field_simp [hU.ne']
  ring

/-! ## Direct closure of the two Gaussian terms -/

/--
The four-term Fourier comparison with the Gaussian-weighted core correction
and the reference tail combined into the closed scalar budget.  Only the
distribution-specific core discrepancy and outer-band terms remain open.
-/
theorem lintegral_prawitzFourierComparison_standardGaussian_le_weighted_open_terms
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {U₀ U : ℝ} (hU₀ : 0 < U₀) (hU : 0 < U)
    (hTaylorCut : Real.pi * U₀ ≤ U) :
    (∫⁻ u : ℝ, ENNReal.ofReal
        (prawitzFourierComparison
          μ (gaussianReal 0 1) U u) ∂volume) ≤
      (∫⁻ u : ℝ, ENNReal.ofReal
          (prawitzCoreDiscrepancyTerm
            μ (gaussianReal 0 1) U₀ U u) ∂volume) +
      (∫⁻ u : ℝ, ENNReal.ofReal
          (prawitzOuterKernelTerm μ U₀ U u) ∂volume) +
      ENNReal.ofReal
        (prawitzGaussianWeightedClosedBudget U₀ U) := by
  have hpione : 1 < Real.pi :=
    lt_of_lt_of_le one_lt_two Real.two_le_pi
  have hcut : U₀ ≤ U := by
    nlinarith
  have hfour :=
    lintegral_prawitzFourierComparison_le_four_integrals
      μ (gaussianReal 0 1) hcut
  have hgaussian :=
    lintegral_prawitzGaussianTerms_standardGaussian_le_weightedBudget
      hU₀ hU hTaylorCut
  calc
    (∫⁻ u : ℝ, ENNReal.ofReal
        (prawitzFourierComparison
          μ (gaussianReal 0 1) U u) ∂volume) ≤
        (∫⁻ u : ℝ, ENNReal.ofReal
            (prawitzCoreDiscrepancyTerm
              μ (gaussianReal 0 1) U₀ U u) ∂volume) +
        (∫⁻ u : ℝ, ENNReal.ofReal
            (prawitzOuterKernelTerm μ U₀ U u) ∂volume) +
        ((∫⁻ u : ℝ, ENNReal.ofReal
            (prawitzCoreCorrectionTerm
              (gaussianReal 0 1) U₀ U u) ∂volume) +
          (∫⁻ u : ℝ, ENNReal.ofReal
            (prawitzReferenceTailTerm
              (gaussianReal 0 1) U₀ u) ∂volume)) := by
      simpa only [add_assoc] using hfour
    _ ≤
        (∫⁻ u : ℝ, ENNReal.ofReal
            (prawitzCoreDiscrepancyTerm
              μ (gaussianReal 0 1) U₀ U u) ∂volume) +
        (∫⁻ u : ℝ, ENNReal.ofReal
            (prawitzOuterKernelTerm μ U₀ U u) ∂volume) +
        ENNReal.ofReal
          (prawitzGaussianWeightedClosedBudget U₀ U) := by
      gcongr

/--
The four-term Prawitz comparison with its two distribution-independent
Gaussian terms closed.  The first two integrals remain syntactically open,
so later characteristic-function estimates can slot in directly without
being passed as theorem-shaped assumptions.
-/
theorem lintegral_prawitzFourierComparison_standardGaussian_le_open_terms
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {U₀ U : ℝ} (hU₀ : 0 < U₀) (hU : 0 < U)
    (hTaylorCut : Real.pi * U₀ ≤ U) :
    (∫⁻ u : ℝ, ENNReal.ofReal
        (prawitzFourierComparison
          μ (gaussianReal 0 1) U u) ∂volume) ≤
      (∫⁻ u : ℝ, ENNReal.ofReal
          (prawitzCoreDiscrepancyTerm
            μ (gaussianReal 0 1) U₀ U u) ∂volume) +
      (∫⁻ u : ℝ, ENNReal.ofReal
          (prawitzOuterKernelTerm μ U₀ U u) ∂volume) +
      ENNReal.ofReal
        (U₀ / U +
          (37 / 96 : ℝ) * Real.pi ^ 2 * U₀ ^ 2 /
            U ^ 2) +
      ENNReal.ofReal
        (Real.exp (-(U₀ ^ 2) / 2) /
          (Real.pi * U₀ ^ 2)) := by
  have hpione : 1 < Real.pi :=
    lt_of_lt_of_le one_lt_two Real.two_le_pi
  have hcut : U₀ ≤ U := by
    nlinarith
  have hfour :=
    lintegral_prawitzFourierComparison_le_four_integrals
      μ (gaussianReal 0 1) hcut
  have hcore :=
    lintegral_prawitzCoreCorrectionTerm_standardGaussian_le_explicit
      hU₀.le hU hTaylorCut
  have htail :=
    lintegral_prawitzReferenceTailTerm_standardGaussian_le hU₀
  calc
    (∫⁻ u : ℝ, ENNReal.ofReal
        (prawitzFourierComparison
          μ (gaussianReal 0 1) U u) ∂volume) ≤
        (∫⁻ u : ℝ, ENNReal.ofReal
            (prawitzCoreDiscrepancyTerm
              μ (gaussianReal 0 1) U₀ U u) ∂volume) +
        (∫⁻ u : ℝ, ENNReal.ofReal
            (prawitzOuterKernelTerm μ U₀ U u) ∂volume) +
        (∫⁻ u : ℝ, ENNReal.ofReal
            (prawitzCoreCorrectionTerm
              (gaussianReal 0 1) U₀ U u) ∂volume) +
        (∫⁻ u : ℝ, ENNReal.ofReal
            (prawitzReferenceTailTerm
              (gaussianReal 0 1) U₀ u) ∂volume) := hfour
    _ ≤
        (∫⁻ u : ℝ, ENNReal.ofReal
            (prawitzCoreDiscrepancyTerm
              μ (gaussianReal 0 1) U₀ U u) ∂volume) +
        (∫⁻ u : ℝ, ENNReal.ofReal
            (prawitzOuterKernelTerm μ U₀ U u) ∂volume) +
        ENNReal.ofReal
          (U₀ / U +
            (37 / 96 : ℝ) * Real.pi ^ 2 * U₀ ^ 2 /
              U ^ 2) +
        ENNReal.ofReal
          (Real.exp (-(U₀ ^ 2) / 2) /
            (Real.pi * U₀ ^ 2)) := by
      gcongr

end Probability
end CertifiedJL
