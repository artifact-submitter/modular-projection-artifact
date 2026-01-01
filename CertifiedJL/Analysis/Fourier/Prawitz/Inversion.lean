/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Fourier.Beurling.PrawitzFourier

/-!
# The asymmetric Prawitz inversion inequality

This file connects the Beurling spatial majorants to the asymmetric
Prawitz Fourier comparison used by the quantitative Berry--Esseen
estimates.  Singular Fourier expressions are never integrated separately:
we first subtract their common value at frequency zero, and only then use
ordinary Bochner integration.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ComplexConjugate ENNReal Topology

namespace CertifiedJL
namespace Probability

/-- The zero-regularized singular coefficient in a Beurling center. -/
noncomputable def beurlingCenterFrequencyCoefficient
    (U u : ℝ) : ℂ :=
  if u = 0 then 0
  else
    (((beurlingJHat (u / U) /
      (2 * Real.pi * u) : ℝ) : ℂ) * Complex.I)

/--
The regularized Fourier integrand for one Beurling center.  The subtraction
of `1` cancels the apparent singularity at frequency zero.
-/
noncomputable def beurlingCenterRegularizedFrequencyIntegrand
    (μ : Measure ℝ) (U x u : ℝ) : ℂ :=
  beurlingCenterFrequencyCoefficient U u *
    (Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I) *
      charFun μ u - 1)

private theorem measureFrequency_scaled_eq_centerRegularized
    (μ : Measure ℝ) {U x u : ℝ} (hU : 0 < U) :
    beurlingHMeasureFrequencyIntegrand μ (U / (2 * Real.pi)) x
        ((-U⁻¹) * u) =
      ((2 * U : ℝ) : ℂ) *
        beurlingCenterRegularizedFrequencyIntegrand μ U x u := by
  by_cases hu : u = 0
  · subst u
    simp [beurlingHMeasureFrequencyIntegrand,
      beurlingCenterRegularizedFrequencyIntegrand,
      beurlingCenterFrequencyCoefficient]
  · have hU0 : U ≠ 0 := hU.ne'
    have hscaled : (-U⁻¹) * u ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hU0)) hu
    unfold beurlingHMeasureFrequencyIntegrand
      beurlingCenterRegularizedFrequencyIntegrand
      beurlingCenterFrequencyCoefficient
    rw [if_neg hscaled, if_neg hu]
    have harg :
        -2 * Real.pi * ((-U⁻¹) * u) *
            (U / (2 * Real.pi)) = u := by
      field_simp [hU0, Real.pi_ne_zero]
    have hphase :
        2 * Real.pi * ((-U⁻¹) * u) *
            (U / (2 * Real.pi)) * x = -(u * x) := by
      field_simp [hU0, Real.pi_ne_zero]
    rw [harg, hphase]
    have hratio : ((-U⁻¹) * u) = -(u / U) := by
      field_simp [hU0]
    rw [hratio, beurlingJHatC_neg]
    push_cast
    field_simp [hU0, hu, Real.pi_ne_zero]
    rw [Complex.I_sq]
    simp only [neg_mul, one_mul, beurlingJHatC]
    ring

theorem integrable_beurlingCenterRegularizedFrequencyIntegrand
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : Integrable (fun y : ℝ => y) μ)
    {U : ℝ} (hU : 0 < U) (x : ℝ) :
    Integrable (beurlingCenterRegularizedFrequencyIntegrand μ U x) := by
  let g : ℝ → ℂ := fun t =>
    beurlingHMeasureFrequencyIntegrand μ (U / (2 * Real.pi)) x t
  have hg : Integrable g :=
    integrable_beurlingHMeasureFrequencyIntegrand
      μ hmoment (U / (2 * Real.pi)) x
  have hgscale : Integrable (fun u : ℝ => g ((-U⁻¹) * u)) :=
    hg.comp_mul_left'
      (neg_ne_zero.mpr (inv_ne_zero hU.ne'))
  have heq : (fun u : ℝ => g ((-U⁻¹) * u)) =
      fun u => ((2 * U : ℝ) : ℂ) *
        beurlingCenterRegularizedFrequencyIntegrand μ U x u := by
    funext u
    exact measureFrequency_scaled_eq_centerRegularized μ hU
  rw [heq] at hgscale
  have hconst : (((2 * U : ℝ) : ℂ)) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) hU.ne')
  have hscaled := hgscale.const_mul (((2 * U : ℝ) : ℂ)⁻¹)
  refine hscaled.congr (ae_of_all volume fun u => ?_)
  field_simp [hconst]

/--
Exact ordinary-integral formula for one Beurling center at bandwidth
`T = U/(2π)`.
-/
theorem beurlingCDFCenter_eq_half_add_re_regularizedFrequencyIntegral
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : Integrable (fun y : ℝ => y) μ)
    {U : ℝ} (hU : 0 < U) (x : ℝ) :
    beurlingCDFCenter μ (U / (2 * Real.pi)) x =
      1 / 2 +
        (∫ u : ℝ,
          beurlingCenterRegularizedFrequencyIntegrand μ U x u).re := by
  have hH :=
    integral_scaledBeurlingH_eq_re_measureFrequencyIntegral
      μ hmoment (U / (2 * Real.pi)) x
  let g : ℝ → ℂ := fun t =>
    beurlingHMeasureFrequencyIntegrand μ (U / (2 * Real.pi)) x t
  have hscale := Measure.integral_comp_mul_left g (-U⁻¹)
  have habs : |(-U⁻¹)⁻¹| = U := by
    rw [inv_neg, inv_inv, abs_neg, abs_of_pos hU]
  rw [habs] at hscale
  have hcomp :
      (fun u : ℝ => g ((-U⁻¹) * u)) =
        fun u => ((2 * U : ℝ) : ℂ) *
          beurlingCenterRegularizedFrequencyIntegrand μ U x u := by
    funext u
    exact measureFrequency_scaled_eq_centerRegularized μ hU
  rw [hcomp, MeasureTheory.integral_const_mul] at hscale
  have hU0 : U ≠ 0 := hU.ne'
  have heq :
      (∫ t : ℝ, g t) =
        (2 : ℂ) *
          ∫ u : ℝ,
            beurlingCenterRegularizedFrequencyIntegrand μ U x u := by
    apply (mul_left_cancel₀ (show (U : ℂ) ≠ 0 by exact_mod_cast hU0))
    calc
      (U : ℂ) * ∫ t : ℝ, g t =
          ((2 * U : ℝ) : ℂ) *
            ∫ u : ℝ,
              beurlingCenterRegularizedFrequencyIntegrand μ U x u := by
        symm
        exact hscale
      _ = (U : ℂ) *
          ((2 : ℂ) *
            ∫ u : ℝ,
              beurlingCenterRegularizedFrequencyIntegrand μ U x u) := by
        push_cast
        ring
  unfold beurlingCDFCenter
  rw [hH, heq]
  norm_num [Complex.mul_re]
  ring

theorem integrable_beurlingCorrectionFrequencyIntegrand
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {U : ℝ} (hU : 0 < U) (x : ℝ) :
    Integrable (beurlingCorrectionFrequencyIntegrand μ U x) := by
  have htriangle :
      Integrable (fun u : ℝ => beurlingTriangle (U⁻¹ * u)) :=
    integrable_beurlingTriangle.comp_mul_left' (inv_ne_zero hU.ne')
  have hmajorant :
      Integrable (fun u : ℝ =>
        ‖beurlingTriangle (U⁻¹ * u)‖ / (2 * U)) :=
    by
      simpa [div_eq_mul_inv, mul_comm] using
        htriangle.norm.const_mul (1 / (2 * U))
  refine hmajorant.mono' ?_ ?_
  · have heq :
        beurlingCorrectionFrequencyIntegrand μ U x =
          fun u : ℝ =>
            Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I) *
              ((1 / (2 * U) : ℝ) : ℂ) *
              beurlingTriangle (u / U) *
              charFun μ u := by
      funext u
      unfold beurlingCorrectionFrequencyIntegrand
      rw [beurlingTriangle_eq_beurlingKHat]
      push_cast
      ring
    rw [heq]
    have hphase : Continuous (fun u : ℝ =>
        Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I)) := by
      fun_prop
    have htriangleCont : Continuous (fun u : ℝ =>
        beurlingTriangle (u / U)) :=
      continuous_beurlingTriangle.comp (continuous_id.div_const U)
    exact (((hphase.mul continuous_const).mul htriangleCont).measurable.mul
      measurable_charFun).aestronglyMeasurable
  · filter_upwards with u
    unfold beurlingCorrectionFrequencyIntegrand
    rw [norm_mul, norm_mul]
    have hphase :
        ‖Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [hphase, one_mul]
    calc
      ‖((beurlingKHat (u / U) / (2 * U) : ℝ) : ℂ)‖ *
            ‖charFun μ u‖ ≤
          ‖((beurlingKHat (u / U) / (2 * U) : ℝ) : ℂ)‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_charFun_le_one u) (norm_nonneg _)
      _ = ‖beurlingTriangle (U⁻¹ * u)‖ / (2 * U) := by
        rw [mul_one, Complex.norm_real, Real.norm_eq_abs]
        rw [show u / U = U⁻¹ * u by field_simp [hU.ne']]
        rw [beurlingTriangle_eq_beurlingKHat, Complex.norm_real,
          Real.norm_eq_abs]
        have hden : 0 < 2 * U := by positivity
        rw [abs_div, abs_of_pos hden]

/-- Regularized upper Prawitz transform for one law. -/
noncomputable def prawitzUpperRegularizedIntegrand
    (μ : Measure ℝ) (U x u : ℝ) : ℂ :=
  beurlingCenterRegularizedFrequencyIntegrand μ U x u +
    beurlingCorrectionFrequencyIntegrand μ U x u

/-- Regularized lower Prawitz transform for one law. -/
noncomputable def prawitzLowerRegularizedIntegrand
    (μ : Measure ℝ) (U x u : ℝ) : ℂ :=
  beurlingCenterRegularizedFrequencyIntegrand μ U x u -
    beurlingCorrectionFrequencyIntegrand μ U x u

theorem integrable_prawitzUpperRegularizedIntegrand
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : Integrable (fun y : ℝ => y) μ)
    {U : ℝ} (hU : 0 < U) (x : ℝ) :
    Integrable (prawitzUpperRegularizedIntegrand μ U x) :=
  (integrable_beurlingCenterRegularizedFrequencyIntegrand
      μ hmoment hU x).add
    (integrable_beurlingCorrectionFrequencyIntegrand μ hU x)

theorem integrable_prawitzLowerRegularizedIntegrand
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : Integrable (fun y : ℝ => y) μ)
    {U : ℝ} (hU : 0 < U) (x : ℝ) :
    Integrable (prawitzLowerRegularizedIntegrand μ U x) :=
  (integrable_beurlingCenterRegularizedFrequencyIntegrand
      μ hmoment hU x).sub
    (integrable_beurlingCorrectionFrequencyIntegrand μ hU x)

theorem beurlingCDFUpper_eq_half_add_re_regularizedIntegral
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : Integrable (fun y : ℝ => y) μ)
    {U : ℝ} (hU : 0 < U) (x : ℝ) :
    beurlingCDFCenter μ (U / (2 * Real.pi)) x +
        beurlingCDFCorrection μ (U / (2 * Real.pi)) x =
      1 / 2 +
        (∫ u : ℝ, prawitzUpperRegularizedIntegrand μ U x u).re := by
  rw [beurlingCDFCenter_eq_half_add_re_regularizedFrequencyIntegral
      μ hmoment hU x,
    beurlingCDFCorrection_eq_re_frequencyIntegral μ hU x]
  unfold prawitzUpperRegularizedIntegrand
  rw [MeasureTheory.integral_add
      (integrable_beurlingCenterRegularizedFrequencyIntegrand
        μ hmoment hU x)
      (integrable_beurlingCorrectionFrequencyIntegrand μ hU x)]
  simp only [Complex.add_re]
  ring

theorem beurlingCDFLower_eq_half_add_re_regularizedIntegral
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : Integrable (fun y : ℝ => y) μ)
    {U : ℝ} (hU : 0 < U) (x : ℝ) :
    beurlingCDFCenter μ (U / (2 * Real.pi)) x -
        beurlingCDFCorrection μ (U / (2 * Real.pi)) x =
      1 / 2 +
        (∫ u : ℝ, prawitzLowerRegularizedIntegrand μ U x u).re := by
  rw [beurlingCDFCenter_eq_half_add_re_regularizedFrequencyIntegral
      μ hmoment hU x,
    beurlingCDFCorrection_eq_re_frequencyIntegral μ hU x]
  unfold prawitzLowerRegularizedIntegrand
  rw [MeasureTheory.integral_sub
      (integrable_beurlingCenterRegularizedFrequencyIntegrand
        μ hmoment hU x)
      (integrable_beurlingCorrectionFrequencyIntegrand μ hU x)]
  simp only [Complex.sub_re]
  ring

theorem beurlingCenterFrequencyCoefficient_re
    (U u : ℝ) :
    (beurlingCenterFrequencyCoefficient U u).re = 0 := by
  unfold beurlingCenterFrequencyCoefficient
  split_ifs
  · simp
  · simp only [Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]

theorem principalCDFKernel_re (u : ℝ) :
    (principalCDFKernel u).re = 0 := by
  unfold principalCDFKernel
  simp [Complex.div_re]

/--
The regularized upper transform is exactly the phase-shifted truncated
Prawitz transform, apart from its explicit zero-frequency subtraction.
-/
theorem phase_mul_truncatedPrawitzIntegrand_eq
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {U : ℝ} (hU : 0 < U) (x u : ℝ) :
    Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I) *
        truncatedPrawitzIntegrand μ U u =
      beurlingCorrectionFrequencyIntegrand μ U x u +
        beurlingCenterFrequencyCoefficient U u *
          (Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I) *
            charFun μ u) := by
  have hU0 : U ≠ 0 := hU.ne'
  by_cases hu : u = 0
  · subst u
    simp [truncatedPrawitzIntegrand, scaledPrawitzKernel,
      beurlingCorrectionFrequencyIntegrand,
      beurlingCenterFrequencyCoefficient, hU.le]
  · by_cases hsupp : |u| ≤ U
    · rw [truncatedPrawitzIntegrand, if_pos hsupp,
        scaledPrawitzKernel_eq_multipliers hU0 hu]
      unfold beurlingCorrectionFrequencyIntegrand
        beurlingCenterFrequencyCoefficient
      rw [if_neg hu]
      ring
    · have hout : U < |u| := lt_of_not_ge hsupp
      have habsratio : 1 ≤ |u / U| := by
        rw [abs_div, abs_of_pos hU]
        exact (le_div_iff₀ hU).2 (by simpa using hout.le)
      rw [truncatedPrawitzIntegrand, if_neg hsupp]
      unfold beurlingCorrectionFrequencyIntegrand
        beurlingCenterFrequencyCoefficient
      rw [if_neg hu,
        beurlingKHat_eq_zero_of_one_le_abs habsratio,
        beurlingJHat_eq_zero_of_one_le_abs habsratio]
      simp

/-- The regularized principal-CDF transform at a spatial point. -/
noncomputable def regularizedCDFReferenceIntegrand
    (ν : Measure ℝ) (x u : ℝ) : ℂ :=
  principalCDFKernel u *
    (Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I) *
      charFun ν u - 1)

/-- Phase-shifted upper Prawitz comparison integrand. -/
noncomputable def phasedPrawitzUpperComparisonIntegrand
    (μ ν : Measure ℝ) (U x u : ℝ) : ℂ :=
  Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I) *
    (truncatedPrawitzIntegrand μ U u -
      principalCDFKernel u * charFun ν u)

theorem prawitzUpperRegularized_sub_reference_eq
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    {U : ℝ} (hU : 0 < U) (x u : ℝ) :
    prawitzUpperRegularizedIntegrand μ U x u -
        regularizedCDFReferenceIntegrand ν x u =
      phasedPrawitzUpperComparisonIntegrand μ ν U x u +
        (principalCDFKernel u -
          beurlingCenterFrequencyCoefficient U u) := by
  rw [prawitzUpperRegularizedIntegrand,
    beurlingCenterRegularizedFrequencyIntegrand,
    regularizedCDFReferenceIntegrand,
    phasedPrawitzUpperComparisonIntegrand]
  have hphase :=
    phase_mul_truncatedPrawitzIntegrand_eq μ hU x u
  calc
    beurlingCenterFrequencyCoefficient U u *
            (Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I) *
                charFun μ u - 1) +
          beurlingCorrectionFrequencyIntegrand μ U x u -
        principalCDFKernel u *
          (Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I) *
              charFun ν u - 1) =
        (beurlingCorrectionFrequencyIntegrand μ U x u +
            beurlingCenterFrequencyCoefficient U u *
              (Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I) *
                charFun μ u)) -
          Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I) *
            (principalCDFKernel u * charFun ν u) +
          (principalCDFKernel u -
            beurlingCenterFrequencyCoefficient U u) := by ring
    _ = Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I) *
          truncatedPrawitzIntegrand μ U u -
          Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I) *
            (principalCDFKernel u * charFun ν u) +
          (principalCDFKernel u -
            beurlingCenterFrequencyCoefficient U u) := by
      rw [hphase]
    _ = _ := by ring

theorem re_prawitzUpperRegularized_sub_reference_eq
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    {U : ℝ} (hU : 0 < U) (x u : ℝ) :
    (prawitzUpperRegularizedIntegrand μ U x u -
        regularizedCDFReferenceIntegrand ν x u).re =
      (phasedPrawitzUpperComparisonIntegrand μ ν U x u).re := by
  rw [prawitzUpperRegularized_sub_reference_eq μ ν hU x u,
    Complex.add_re, Complex.sub_re,
    principalCDFKernel_re,
    beurlingCenterFrequencyCoefficient_re]
  ring

theorem measurable_regularizedCDFReferenceIntegrand
    (ν : Measure ℝ) [IsFiniteMeasure ν] (x : ℝ) :
    Measurable (regularizedCDFReferenceIntegrand ν x) := by
  unfold regularizedCDFReferenceIntegrand
  exact measurable_principalCDFKernel.mul
    (((by fun_prop : Measurable (fun u : ℝ =>
        Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I))).mul
      measurable_charFun).sub measurable_const)

theorem intervalIntegrable_regularizedCDFReferenceIntegrand
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmoment : Integrable (fun y : ℝ => y) ν)
    (x A B : ℝ) :
    IntervalIntegrable (regularizedCDFReferenceIntegrand ν x)
      volume A B := by
  let g : ℝ → ℝ := fun y => |y - x| / (2 * Real.pi)
  have hy : Integrable (fun y : ℝ => y - x) ν :=
    hmoment.sub (integrable_const x)
  have hg : Integrable g ν := by
    dsimp [g]
    simpa [div_eq_mul_inv, mul_comm] using
      hy.norm.const_mul (1 / (2 * Real.pi))
  let C : ℝ := ∫ y, g y ∂ν
  have hbound : ∀ u : ℝ,
      ‖regularizedCDFReferenceIntegrand ν x u‖ ≤ C := by
    intro u
    unfold regularizedCDFReferenceIntegrand
    rw [← integral_regularizedPointCDFIntegrand ν x u]
    exact norm_integral_le_of_norm_le hg
      (ae_of_all ν fun y =>
        norm_regularizedPointCDFIntegrand_le (y - x) u)
  refine intervalIntegrable_iff.mpr ?_
  refine Integrable.mono'
    (integrableOn_const (C := C) (by
      rw [Real.volume_uIoc]
      exact ENNReal.ofReal_ne_top))
    ((measurable_regularizedCDFReferenceIntegrand ν x).aestronglyMeasurable)
    (ae_of_all (volume.restrict (uIoc A B)) hbound)

theorem prawitzUpperRegularizedIntegrand_eq_zero_of_le_abs
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {U u : ℝ} (hU : 0 < U) (hu : U ≤ |u|) (x : ℝ) :
    prawitzUpperRegularizedIntegrand μ U x u = 0 := by
  have habsratio : 1 ≤ |u / U| := by
    rw [abs_div, abs_of_pos hU]
    exact (le_div_iff₀ hU).2 (by simpa using hu)
  have hu0 : u ≠ 0 := by
    intro huz
    subst u
    simp at hu
    linarith
  unfold prawitzUpperRegularizedIntegrand
    beurlingCenterRegularizedFrequencyIntegrand
    beurlingCenterFrequencyCoefficient
    beurlingCorrectionFrequencyIntegrand
  rw [if_neg hu0,
    beurlingJHat_eq_zero_of_one_le_abs habsratio,
    beurlingKHat_eq_zero_of_one_le_abs habsratio]
  simp

theorem integral_prawitzUpperRegularized_eq_interval
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {U R : ℝ} (hU : 0 < U) (hR : U ≤ R) (x : ℝ) :
    (∫ u : ℝ, prawitzUpperRegularizedIntegrand μ U x u) =
      ∫ u in (-R)..R, prawitzUpperRegularizedIntegrand μ U x u := by
  let f : ℝ → ℂ := prawitzUpperRegularizedIntegrand μ U x
  have hR0 : 0 ≤ R := hU.le.trans hR
  have heq : f = (Icc (-R) R).indicator f := by
    funext u
    by_cases hu : u ∈ Icc (-R) R
    · simp [Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu]
      have habs : R ≤ |u| := by
        rw [mem_Icc, not_and_or] at hu
        rcases hu with hu | hu
        · have : R < -u := by linarith
          have huneg : u < 0 := by linarith
          rw [abs_of_neg huneg]
          linarith
        · have : R < u := lt_of_not_ge hu
          have hupos : 0 < u := by linarith
          rw [abs_of_pos hupos]
          exact this.le
      exact prawitzUpperRegularizedIntegrand_eq_zero_of_le_abs
        μ hU (hR.trans habs) x
  change (∫ u : ℝ, f u) = ∫ u in (-R)..R, f u
  calc
    (∫ u : ℝ, f u) =
        ∫ u : ℝ, (Icc (-R) R).indicator f u := by
      apply integral_congr_ae
      exact ae_of_all volume fun u => congrFun heq u
    _ = ∫ u in Icc (-R) R, f u := by
      rw [integral_indicator measurableSet_Icc]
    _ = ∫ u in (-R)..R, f u := by
      rw [intervalIntegral.integral_of_le (by linarith),
        ← integral_Icc_eq_integral_Ioc]

private theorem intervalIntegral_re_eq_re
    {f : ℝ → ℂ} {A B : ℝ}
    (hAB : A ≤ B) (hf : IntervalIntegrable f volume A B) :
    (∫ u in A..B, (f u).re) = (∫ u in A..B, f u).re := by
  have hf' : Integrable f (volume.restrict (Ioc A B)) := by
    change IntegrableOn f (Ioc A B) volume
    have h := intervalIntegrable_iff.mp hf
    simpa [uIoc_of_le hAB] using h
  rw [intervalIntegral.integral_of_le hAB,
    intervalIntegral.integral_of_le hAB]
  exact integral_re hf'

/--
Finite-cutoff upper Prawitz identity.  This is an ordinary integral:
both singular terms have already been regularized before subtraction.
-/
theorem beurlingCDFUpper_sub_regularizedCDFTransform_eq
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (hmomentμ : Integrable (fun y : ℝ => y) μ)
    (hmomentν : Integrable (fun y : ℝ => y) ν)
    {U R : ℝ} (hU : 0 < U) (hR : U ≤ R) (x : ℝ) :
    (beurlingCDFCenter μ (U / (2 * Real.pi)) x +
        beurlingCDFCorrection μ (U / (2 * Real.pi)) x) -
      (1 / 2 + (regularizedCDFTransform ν x R).re) =
        ∫ u in (-R)..R,
          (phasedPrawitzUpperComparisonIntegrand μ ν U x u).re := by
  let f : ℝ → ℂ := prawitzUpperRegularizedIntegrand μ U x
  let g : ℝ → ℂ := regularizedCDFReferenceIntegrand ν x
  have hR0 : 0 ≤ R := hU.le.trans hR
  have hf : Integrable f :=
    integrable_prawitzUpperRegularizedIntegrand μ hmomentμ hU x
  have hfI : IntervalIntegrable f volume (-R) R :=
    hf.intervalIntegrable
  have hgI : IntervalIntegrable g volume (-R) R :=
    intervalIntegrable_regularizedCDFReferenceIntegrand
      ν hmomentν x (-R) R
  have hfgI : IntervalIntegrable (fun u => f u - g u)
      volume (-R) R := hfI.sub hgI
  have hreal :
      (∫ u in (-R)..R, ((f u - g u).re)) =
        (∫ u in (-R)..R, f u - g u).re :=
    intervalIntegral_re_eq_re (by linarith) hfgI
  have hpoint : ∀ u : ℝ,
      (f u - g u).re =
        (phasedPrawitzUpperComparisonIntegrand μ ν U x u).re := by
    intro u
    exact re_prawitzUpperRegularized_sub_reference_eq
      μ ν hU x u
  rw [beurlingCDFUpper_eq_half_add_re_regularizedIntegral
      μ hmomentμ hU x,
    integral_prawitzUpperRegularized_eq_interval μ hU hR x]
  change
    (1 / 2 + (∫ u in (-R)..R, f u).re) -
        (1 / 2 + (∫ u in (-R)..R, g u).re) =
      ∫ u in (-R)..R,
        (phasedPrawitzUpperComparisonIntegrand μ ν U x u).re
  rw [show
      (1 / 2 + (∫ u in (-R)..R, f u).re) -
          (1 / 2 + (∫ u in (-R)..R, g u).re) =
        ((∫ u in (-R)..R, f u) -
          ∫ u in (-R)..R, g u).re by
    rw [Complex.sub_re]
    ring]
  rw [← intervalIntegral.integral_sub hfI hgI]
  rw [← hreal]
  apply intervalIntegral.integral_congr
  intro u _
  exact hpoint u

theorem norm_phasedPrawitzUpperComparisonIntegrand
    (μ ν : Measure ℝ) (U x u : ℝ) :
    ‖phasedPrawitzUpperComparisonIntegrand μ ν U x u‖ =
      prawitzFourierComparison μ ν U u := by
  unfold phasedPrawitzUpperComparisonIntegrand
    prawitzFourierComparison
  rw [norm_mul, Complex.norm_exp]
  simp

private theorem upperFiniteCutoff_le_fourierNorm
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (hmomentμ : Integrable (fun y : ℝ => y) μ)
    (hmomentν : Integrable (fun y : ℝ => y) ν)
    {U R : ℝ} (hU : 0 < U) (hR : U ≤ R) (x : ℝ)
    (hfinite :
      (∫⁻ u : ℝ, ENNReal.ofReal
        (prawitzFourierComparison μ ν U u) ∂volume) ≠ ∞) :
    (beurlingCDFCenter μ (U / (2 * Real.pi)) x +
        beurlingCDFCorrection μ (U / (2 * Real.pi)) x) -
      (1 / 2 + (regularizedCDFTransform ν x R).re) ≤
      ENNReal.toReal
        (∫⁻ u : ℝ, ENNReal.ofReal
          (prawitzFourierComparison μ ν U u) ∂volume) := by
  let q : ℝ → ℝ := fun u =>
    (phasedPrawitzUpperComparisonIntegrand μ ν U x u).re
  have hR0 : 0 ≤ R := hU.le.trans hR
  have hfiniteIdentity :=
    beurlingCDFUpper_sub_regularizedCDFTransform_eq
      μ ν hmomentμ hmomentν hU hR x
  have hqI : IntervalIntegrable q volume (-R) R := by
    let f : ℝ → ℂ := prawitzUpperRegularizedIntegrand μ U x
    let g : ℝ → ℂ := regularizedCDFReferenceIntegrand ν x
    have hfgI : IntervalIntegrable (fun u => f u - g u)
        volume (-R) R :=
      (integrable_prawitzUpperRegularizedIntegrand
        μ hmomentμ hU x).intervalIntegrable.sub
      (intervalIntegrable_regularizedCDFReferenceIntegrand
        ν hmomentν x (-R) R)
    have hrealI : IntervalIntegrable (fun u => (f u - g u).re)
        volume (-R) R := by
      apply intervalIntegrable_iff.mpr
      have hbase : Integrable (fun u => f u - g u)
          (volume.restrict (uIoc (-R) R)) := by
        change IntegrableOn (fun u => f u - g u) (uIoc (-R) R) volume
        exact intervalIntegrable_iff.mp hfgI
      change Integrable (fun u => (f u - g u).re)
        (volume.restrict (uIoc (-R) R))
      exact hbase.re
    refine hrealI.congr fun u _ => ?_
    dsimp only [q, f, g]
    exact re_prawitzUpperRegularized_sub_reference_eq μ ν hU x u
  have hqRestr : Integrable q (volume.restrict (Ioc (-R) R)) := by
    change IntegrableOn q (Ioc (-R) R) volume
    have h := intervalIntegrable_iff.mp hqI
    simpa [uIoc_of_le (by linarith : -R ≤ R)] using h
  have hlin :
      (∫⁻ u : ℝ, ‖q u‖ₑ ∂(volume.restrict (Ioc (-R) R))) ≤
        ∫⁻ u : ℝ, ENNReal.ofReal
          (prawitzFourierComparison μ ν U u) ∂volume := by
    calc
      (∫⁻ u : ℝ, ‖q u‖ₑ ∂(volume.restrict (Ioc (-R) R))) ≤
          ∫⁻ u : ℝ, ENNReal.ofReal
            (prawitzFourierComparison μ ν U u)
            ∂(volume.restrict (Ioc (-R) R)) := by
        apply lintegral_mono
        intro u
        simp only
        rw [Real.enorm_eq_ofReal_abs]
        apply ENNReal.ofReal_le_ofReal
        calc
          |q u| ≤
              ‖phasedPrawitzUpperComparisonIntegrand μ ν U x u‖ := by
            simpa [q, Real.norm_eq_abs] using
              RCLike.norm_re_le_norm
                (phasedPrawitzUpperComparisonIntegrand μ ν U x u)
          _ = prawitzFourierComparison μ ν U u :=
            norm_phasedPrawitzUpperComparisonIntegrand μ ν U x u
      _ ≤ _ := lintegral_mono' Measure.restrict_le_self le_rfl
  have hnorm :
      |∫ u in (-R)..R, q u| ≤
        ENNReal.toReal
          (∫⁻ u : ℝ, ENNReal.ofReal
            (prawitzFourierComparison μ ν U u) ∂volume) := by
    rw [intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
    calc
      |∫ u in Ioc (-R) R, q u ∂volume| ≤
          ENNReal.toReal
            (∫⁻ u : ℝ, ‖q u‖ₑ
              ∂(volume.restrict (Ioc (-R) R))) := by
        simpa only [Real.norm_eq_abs, Real.enorm_eq_ofReal_abs] using
          norm_integral_le_lintegral_norm
            (μ := volume.restrict (Ioc (-R) R)) q
      _ ≤ _ := ENNReal.toReal_mono hfinite hlin
  rw [hfiniteIdentity]
  exact (le_abs_self _).trans hnorm

/--
One-sided asymmetric Prawitz inversion bound.  The only finiteness premise
is discharged automatically by any finite quantitative four-term bound.
-/
theorem cdfDiscrepancy_le_prawitzFourierComparison_toReal
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (hmomentμ : Integrable (fun y : ℝ => y) μ)
    (hmomentν : Integrable (fun y : ℝ => y) ν)
    {U : ℝ} (hU : 0 < U) (x : ℝ)
    (hfinite :
      (∫⁻ u : ℝ, ENNReal.ofReal
        (prawitzFourierComparison μ ν U u) ∂volume) ≠ ∞) :
    cdf μ x - cdf ν x ≤
      ENNReal.toReal
        (∫⁻ u : ℝ, ENNReal.ofReal
          (prawitzFourierComparison μ ν U u) ∂volume) := by
  have hband :=
    (cdf_mem_beurling_band_absorbing_atom μ
      (show 0 < U / (2 * Real.pi) by positivity) x).1
  have hlimReg :=
    tendsto_regularizedCDFTransform_atTop ν hmomentν x
  have hlimRe :
      Tendsto (fun R : ℝ =>
        (regularizedCDFTransform ν x R).re) atTop
        (𝓝 (midpointCDF ν x - 1 / 2)) :=
    (Complex.continuous_re.tendsto _).comp hlimReg
  have hmid : midpointCDF ν x = cdf ν x :=
    midpointCDF_eq_cdf_of_atomless ν x
  have hlim :
      Tendsto
        (fun R : ℝ =>
          (beurlingCDFCenter μ (U / (2 * Real.pi)) x +
              beurlingCDFCorrection μ (U / (2 * Real.pi)) x) -
            (1 / 2 + (regularizedCDFTransform ν x R).re))
        atTop
        (𝓝 ((beurlingCDFCenter μ (U / (2 * Real.pi)) x +
              beurlingCDFCorrection μ (U / (2 * Real.pi)) x) -
            cdf ν x)) := by
    convert
      (tendsto_const_nhds.sub
        (tendsto_const_nhds.add hlimRe)) using 1
    all_goals rw [hmid]
    all_goals ring_nf
  have hev : ∀ᶠ R : ℝ in atTop,
      (beurlingCDFCenter μ (U / (2 * Real.pi)) x +
          beurlingCDFCorrection μ (U / (2 * Real.pi)) x) -
        (1 / 2 + (regularizedCDFTransform ν x R).re) ≤
        ENNReal.toReal
          (∫⁻ u : ℝ, ENNReal.ofReal
            (prawitzFourierComparison μ ν U u) ∂volume) := by
    filter_upwards [eventually_ge_atTop U] with R hR
    exact upperFiniteCutoff_le_fourierNorm
      μ ν hmomentμ hmomentν hU hR x hfinite
  have hupper :
      (beurlingCDFCenter μ (U / (2 * Real.pi)) x +
          beurlingCDFCorrection μ (U / (2 * Real.pi)) x) -
        cdf ν x ≤
        ENNReal.toReal
          (∫⁻ u : ℝ, ENNReal.ofReal
            (prawitzFourierComparison μ ν U u) ∂volume) :=
    le_of_tendsto hlim hev
  linarith

/-! ## The reflected lower multiplier -/

/--
The lower Prawitz kernel.  The Beurling lower approximation changes the
sign of the real triangle multiplier while retaining the imaginary center
multiplier, hence `K⁻(u) = -conj (K⁺(u)) = -K⁺(-u)`.
-/
noncomputable def scaledPrawitzLowerKernel (U u : ℝ) : ℂ :=
  -scaledPrawitzKernel U (-u)

theorem scaledPrawitzLowerKernel_eq_neg_conj (U u : ℝ) :
    scaledPrawitzLowerKernel U u =
      -conj (scaledPrawitzKernel U u) := by
  rw [scaledPrawitzLowerKernel, scaledPrawitzKernel_neg]

theorem norm_scaledPrawitzLowerKernel (U u : ℝ) :
    ‖scaledPrawitzLowerKernel U u‖ =
      ‖scaledPrawitzKernel U u‖ := by
  rw [scaledPrawitzLowerKernel_eq_neg_conj, norm_neg, Complex.norm_conj]

theorem conj_principalCDFKernel (u : ℝ) :
    conj (principalCDFKernel u) = -principalCDFKernel u := by
  apply Complex.ext
  · simp [principalCDFKernel, Complex.div_re]
  · simp [principalCDFKernel, Complex.div_im]
    ring

theorem norm_scaledPrawitzLowerKernel_sub_principalCDFKernel
    (U u : ℝ) :
    ‖scaledPrawitzLowerKernel U u - principalCDFKernel u‖ =
      ‖scaledPrawitzKernel U u - principalCDFKernel u‖ := by
  rw [scaledPrawitzLowerKernel_eq_neg_conj]
  have h :
      -conj (scaledPrawitzKernel U u) - principalCDFKernel u =
        -conj (scaledPrawitzKernel U u - principalCDFKernel u) := by
    rw [map_sub, conj_principalCDFKernel]
    ring
  rw [h, norm_neg, Complex.norm_conj]

/-- Compactly supported transform using the lower Prawitz kernel. -/
noncomputable def truncatedPrawitzLowerIntegrand
    (μ : Measure ℝ) (U u : ℝ) : ℂ :=
  if |u| ≤ U then
    scaledPrawitzLowerKernel U u * charFun μ u
  else 0

/-- Fourier comparison generated by the lower Prawitz multiplier. -/
noncomputable def prawitzLowerFourierComparison
    (μ ν : Measure ℝ) (U u : ℝ) : ℝ :=
  ‖truncatedPrawitzLowerIntegrand μ U u -
    principalCDFKernel u * charFun ν u‖

theorem measurable_scaledPrawitzLowerKernel (U : ℝ) :
    Measurable (scaledPrawitzLowerKernel U) := by
  unfold scaledPrawitzLowerKernel
  exact (measurable_scaledPrawitzKernel U).comp measurable_neg |>.neg

theorem measurable_truncatedPrawitzLowerIntegrand
    (μ : Measure ℝ) [IsFiniteMeasure μ] (U : ℝ) :
    Measurable (truncatedPrawitzLowerIntegrand μ U) := by
  unfold truncatedPrawitzLowerIntegrand
  exact Measurable.ite
    (measurableSet_le continuous_abs.measurable measurable_const)
    ((measurable_scaledPrawitzLowerKernel U).mul measurable_charFun)
    measurable_const

theorem measurable_prawitzLowerFourierComparison
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (U : ℝ) :
    Measurable (prawitzLowerFourierComparison μ ν U) := by
  unfold prawitzLowerFourierComparison
  exact ((measurable_truncatedPrawitzLowerIntegrand μ U).sub
    (measurable_principalCDFKernel.mul measurable_charFun)).norm

theorem scaledPrawitzLowerKernel_eq_multipliers
    {U u : ℝ} (hU : U ≠ 0) (hu : u ≠ 0) :
    scaledPrawitzLowerKernel U u =
      -((beurlingKHat (u / U) / (2 * U) : ℝ) : ℂ) +
        (((beurlingJHat (u / U) /
          (2 * Real.pi * u) : ℝ) : ℂ) * Complex.I) := by
  rw [scaledPrawitzLowerKernel_eq_neg_conj,
    scaledPrawitzKernel_eq_multipliers hU hu]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem phase_mul_truncatedPrawitzLowerIntegrand_eq
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {U : ℝ} (hU : 0 < U) (x u : ℝ) :
    Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I) *
        truncatedPrawitzLowerIntegrand μ U u =
      beurlingCenterFrequencyCoefficient U u *
          (Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I) *
            charFun μ u) -
        beurlingCorrectionFrequencyIntegrand μ U x u := by
  have hU0 : U ≠ 0 := hU.ne'
  by_cases hu : u = 0
  · subst u
    simp [truncatedPrawitzLowerIntegrand, scaledPrawitzLowerKernel,
      scaledPrawitzKernel, beurlingCorrectionFrequencyIntegrand,
      beurlingCenterFrequencyCoefficient, hU.le]
  · by_cases hsupp : |u| ≤ U
    · rw [truncatedPrawitzLowerIntegrand, if_pos hsupp,
        scaledPrawitzLowerKernel_eq_multipliers hU0 hu]
      unfold beurlingCorrectionFrequencyIntegrand
        beurlingCenterFrequencyCoefficient
      rw [if_neg hu]
      ring
    · have hout : U < |u| := lt_of_not_ge hsupp
      have habsratio : 1 ≤ |u / U| := by
        rw [abs_div, abs_of_pos hU]
        exact (le_div_iff₀ hU).2 (by simpa using hout.le)
      rw [truncatedPrawitzLowerIntegrand, if_neg hsupp]
      unfold beurlingCorrectionFrequencyIntegrand
        beurlingCenterFrequencyCoefficient
      rw [if_neg hu,
        beurlingKHat_eq_zero_of_one_le_abs habsratio,
        beurlingJHat_eq_zero_of_one_le_abs habsratio]
      simp

/-- Phase-shifted lower Prawitz comparison integrand. -/
noncomputable def phasedPrawitzLowerComparisonIntegrand
    (μ ν : Measure ℝ) (U x u : ℝ) : ℂ :=
  Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I) *
    (truncatedPrawitzLowerIntegrand μ U u -
      principalCDFKernel u * charFun ν u)

theorem prawitzLowerRegularized_sub_reference_eq
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    {U : ℝ} (hU : 0 < U) (x u : ℝ) :
    prawitzLowerRegularizedIntegrand μ U x u -
        regularizedCDFReferenceIntegrand ν x u =
      phasedPrawitzLowerComparisonIntegrand μ ν U x u +
        (principalCDFKernel u -
          beurlingCenterFrequencyCoefficient U u) := by
  rw [prawitzLowerRegularizedIntegrand,
    beurlingCenterRegularizedFrequencyIntegrand,
    regularizedCDFReferenceIntegrand,
    phasedPrawitzLowerComparisonIntegrand]
  have hphase :=
    phase_mul_truncatedPrawitzLowerIntegrand_eq μ hU x u
  calc
    beurlingCenterFrequencyCoefficient U u *
            (Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I) *
                charFun μ u - 1) -
          beurlingCorrectionFrequencyIntegrand μ U x u -
        principalCDFKernel u *
          (Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I) *
              charFun ν u - 1) =
        (beurlingCenterFrequencyCoefficient U u *
              (Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I) *
                charFun μ u) -
            beurlingCorrectionFrequencyIntegrand μ U x u) -
          Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I) *
            (principalCDFKernel u * charFun ν u) +
          (principalCDFKernel u -
            beurlingCenterFrequencyCoefficient U u) := by ring
    _ = Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I) *
          truncatedPrawitzLowerIntegrand μ U u -
          Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I) *
            (principalCDFKernel u * charFun ν u) +
          (principalCDFKernel u -
            beurlingCenterFrequencyCoefficient U u) := by
      rw [hphase]
    _ = _ := by ring

theorem re_prawitzLowerRegularized_sub_reference_eq
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    {U : ℝ} (hU : 0 < U) (x u : ℝ) :
    (prawitzLowerRegularizedIntegrand μ U x u -
        regularizedCDFReferenceIntegrand ν x u).re =
      (phasedPrawitzLowerComparisonIntegrand μ ν U x u).re := by
  rw [prawitzLowerRegularized_sub_reference_eq μ ν hU x u,
    Complex.add_re, Complex.sub_re,
    principalCDFKernel_re,
    beurlingCenterFrequencyCoefficient_re]
  ring

theorem prawitzLowerRegularizedIntegrand_eq_zero_of_le_abs
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {U u : ℝ} (hU : 0 < U) (hu : U ≤ |u|) (x : ℝ) :
    prawitzLowerRegularizedIntegrand μ U x u = 0 := by
  have habsratio : 1 ≤ |u / U| := by
    rw [abs_div, abs_of_pos hU]
    exact (le_div_iff₀ hU).2 (by simpa using hu)
  have hu0 : u ≠ 0 := by
    intro huz
    subst u
    simp at hu
    linarith
  unfold prawitzLowerRegularizedIntegrand
    beurlingCenterRegularizedFrequencyIntegrand
    beurlingCenterFrequencyCoefficient
    beurlingCorrectionFrequencyIntegrand
  rw [if_neg hu0,
    beurlingJHat_eq_zero_of_one_le_abs habsratio,
    beurlingKHat_eq_zero_of_one_le_abs habsratio]
  simp

theorem integral_prawitzLowerRegularized_eq_interval
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {U R : ℝ} (hU : 0 < U) (hR : U ≤ R) (x : ℝ) :
    (∫ u : ℝ, prawitzLowerRegularizedIntegrand μ U x u) =
      ∫ u in (-R)..R, prawitzLowerRegularizedIntegrand μ U x u := by
  let f : ℝ → ℂ := prawitzLowerRegularizedIntegrand μ U x
  have hR0 : 0 ≤ R := hU.le.trans hR
  have heq : f = (Icc (-R) R).indicator f := by
    funext u
    by_cases hu : u ∈ Icc (-R) R
    · simp [Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu]
      have habs : R ≤ |u| := by
        rw [mem_Icc, not_and_or] at hu
        rcases hu with hu | hu
        · have : R < -u := by linarith
          have huneg : u < 0 := by linarith
          rw [abs_of_neg huneg]
          linarith
        · have : R < u := lt_of_not_ge hu
          have hupos : 0 < u := by linarith
          rw [abs_of_pos hupos]
          exact this.le
      exact prawitzLowerRegularizedIntegrand_eq_zero_of_le_abs
        μ hU (hR.trans habs) x
  change (∫ u : ℝ, f u) = ∫ u in (-R)..R, f u
  calc
    (∫ u : ℝ, f u) =
        ∫ u : ℝ, (Icc (-R) R).indicator f u := by
      apply integral_congr_ae
      exact ae_of_all volume fun u => congrFun heq u
    _ = ∫ u in Icc (-R) R, f u := by
      rw [integral_indicator measurableSet_Icc]
    _ = ∫ u in (-R)..R, f u := by
      rw [intervalIntegral.integral_of_le (by linarith),
        ← integral_Icc_eq_integral_Ioc]

/-- Finite-cutoff lower Prawitz identity. -/
theorem beurlingCDFLower_sub_regularizedCDFTransform_eq
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (hmomentμ : Integrable (fun y : ℝ => y) μ)
    (hmomentν : Integrable (fun y : ℝ => y) ν)
    {U R : ℝ} (hU : 0 < U) (hR : U ≤ R) (x : ℝ) :
    (beurlingCDFCenter μ (U / (2 * Real.pi)) x -
        beurlingCDFCorrection μ (U / (2 * Real.pi)) x) -
      (1 / 2 + (regularizedCDFTransform ν x R).re) =
        ∫ u in (-R)..R,
          (phasedPrawitzLowerComparisonIntegrand μ ν U x u).re := by
  let f : ℝ → ℂ := prawitzLowerRegularizedIntegrand μ U x
  let g : ℝ → ℂ := regularizedCDFReferenceIntegrand ν x
  have hf : Integrable f :=
    integrable_prawitzLowerRegularizedIntegrand μ hmomentμ hU x
  have hfI : IntervalIntegrable f volume (-R) R :=
    hf.intervalIntegrable
  have hgI : IntervalIntegrable g volume (-R) R :=
    intervalIntegrable_regularizedCDFReferenceIntegrand
      ν hmomentν x (-R) R
  have hfgI : IntervalIntegrable (fun u => f u - g u)
      volume (-R) R := hfI.sub hgI
  have hreal :
      (∫ u in (-R)..R, ((f u - g u).re)) =
        (∫ u in (-R)..R, f u - g u).re :=
    intervalIntegral_re_eq_re (by linarith [hU.le.trans hR]) hfgI
  have hpoint : ∀ u : ℝ,
      (f u - g u).re =
        (phasedPrawitzLowerComparisonIntegrand μ ν U x u).re := by
    intro u
    exact re_prawitzLowerRegularized_sub_reference_eq
      μ ν hU x u
  rw [beurlingCDFLower_eq_half_add_re_regularizedIntegral
      μ hmomentμ hU x,
    integral_prawitzLowerRegularized_eq_interval μ hU hR x]
  change
    (1 / 2 + (∫ u in (-R)..R, f u).re) -
        (1 / 2 + (∫ u in (-R)..R, g u).re) =
      ∫ u in (-R)..R,
        (phasedPrawitzLowerComparisonIntegrand μ ν U x u).re
  rw [show
      (1 / 2 + (∫ u in (-R)..R, f u).re) -
          (1 / 2 + (∫ u in (-R)..R, g u).re) =
        ((∫ u in (-R)..R, f u) -
          ∫ u in (-R)..R, g u).re by
    rw [Complex.sub_re]
    ring]
  rw [← intervalIntegral.integral_sub hfI hgI]
  rw [← hreal]
  apply intervalIntegral.integral_congr
  intro u _
  exact hpoint u

theorem norm_phasedPrawitzLowerComparisonIntegrand
    (μ ν : Measure ℝ) (U x u : ℝ) :
    ‖phasedPrawitzLowerComparisonIntegrand μ ν U x u‖ =
      prawitzLowerFourierComparison μ ν U u := by
  unfold phasedPrawitzLowerComparisonIntegrand
    prawitzLowerFourierComparison
  rw [norm_mul, Complex.norm_exp]
  simp

/--
The reflected lower multiplier obeys the same four-term majorant as the
upper multiplier.  The two equalities of kernel norms above are the entire
reason no second family of quantitative certificates is needed.
-/
theorem prawitzLowerFourierComparison_le_four_terms
    (μ ν : Measure ℝ) {U₀ U u : ℝ}
    (hcut : U₀ ≤ U) :
    prawitzLowerFourierComparison μ ν U u ≤
      prawitzFourTermMajorant μ ν U₀ U u := by
  by_cases hcore : |u| ≤ U₀
  · have hsupport : |u| ≤ U := hcore.trans hcut
    have hnotOuter : ¬U₀ < |u| := not_lt.mpr hcore
    simp only [prawitzLowerFourierComparison,
      truncatedPrawitzLowerIntegrand, prawitzFourTermMajorant,
      prawitzCoreDiscrepancyTerm, prawitzOuterKernelTerm,
      prawitzCoreCorrectionTerm, prawitzReferenceTailTerm,
      if_pos hcore, if_pos hsupport, hnotOuter, false_and, if_false,
      add_zero]
    let K : ℂ := scaledPrawitzLowerKernel U u
    let P : ℂ := principalCDFKernel u
    let f : ℂ := charFun μ u
    let g : ℂ := charFun ν u
    have hdecomp : K * f - P * g =
        K * (f - g) + (K - P) * g := by ring
    rw [show scaledPrawitzLowerKernel U u * charFun μ u -
          principalCDFKernel u * charFun ν u =
        K * f - P * g by rfl]
    rw [hdecomp]
    calc
      ‖K * (f - g) + (K - P) * g‖ ≤
          ‖K * (f - g)‖ + ‖(K - P) * g‖ :=
        norm_add_le _ _
      _ = ‖K‖ * ‖f - g‖ + ‖K - P‖ * ‖g‖ := by
        rw [norm_mul, norm_mul]
      _ = ‖scaledPrawitzKernel U u‖ * ‖f - g‖ +
          ‖scaledPrawitzKernel U u - principalCDFKernel u‖ *
            ‖g‖ := by
        rw [show ‖K‖ = ‖scaledPrawitzKernel U u‖ by
          exact norm_scaledPrawitzLowerKernel U u]
        rw [show ‖K - P‖ =
            ‖scaledPrawitzKernel U u - principalCDFKernel u‖ by
          exact norm_scaledPrawitzLowerKernel_sub_principalCDFKernel U u]
  · have houter : U₀ < |u| := lt_of_not_ge hcore
    by_cases hsupport : |u| ≤ U
    · simp only [prawitzLowerFourierComparison,
        truncatedPrawitzLowerIntegrand, prawitzFourTermMajorant,
        prawitzCoreDiscrepancyTerm, prawitzOuterKernelTerm,
        prawitzCoreCorrectionTerm, prawitzReferenceTailTerm,
        hcore, houter, hsupport, and_self, if_true, if_false,
        zero_add, add_zero]
      calc
        ‖scaledPrawitzLowerKernel U u * charFun μ u -
            principalCDFKernel u * charFun ν u‖ ≤
            ‖scaledPrawitzLowerKernel U u * charFun μ u‖ +
              ‖principalCDFKernel u * charFun ν u‖ :=
          norm_sub_le _ _
        _ = ‖scaledPrawitzKernel U u‖ * ‖charFun μ u‖ +
              ‖principalCDFKernel u‖ * ‖charFun ν u‖ := by
          rw [norm_mul, norm_mul,
            norm_scaledPrawitzLowerKernel]
    · simp only [prawitzLowerFourierComparison,
        truncatedPrawitzLowerIntegrand, prawitzFourTermMajorant,
        prawitzCoreDiscrepancyTerm, prawitzOuterKernelTerm,
        prawitzCoreCorrectionTerm, prawitzReferenceTailTerm,
        hcore, houter, hsupport, and_false, if_true, if_false,
        zero_sub, norm_neg, zero_add, add_zero, norm_mul]
      exact le_rfl

theorem lintegral_prawitzLowerFourierComparison_le_fourTermMajorant
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {U₀ U : ℝ} (hcut : U₀ ≤ U) :
    ∫⁻ u, ENNReal.ofReal
        (prawitzLowerFourierComparison μ ν U u) ∂volume ≤
      ∫⁻ u, ENNReal.ofReal
        (prawitzFourTermMajorant μ ν U₀ U u) ∂volume := by
  apply lintegral_mono
  intro u
  exact ENNReal.ofReal_le_ofReal
    (prawitzLowerFourierComparison_le_four_terms μ ν hcut)

private theorem lowerFiniteCutoff_le_fourierNorm
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (hmomentμ : Integrable (fun y : ℝ => y) μ)
    (hmomentν : Integrable (fun y : ℝ => y) ν)
    {U R : ℝ} (hU : 0 < U) (hR : U ≤ R) (x : ℝ)
    (hfinite :
      (∫⁻ u : ℝ, ENNReal.ofReal
        (prawitzLowerFourierComparison μ ν U u) ∂volume) ≠ ∞) :
    (1 / 2 + (regularizedCDFTransform ν x R).re) -
      (beurlingCDFCenter μ (U / (2 * Real.pi)) x -
        beurlingCDFCorrection μ (U / (2 * Real.pi)) x) ≤
      ENNReal.toReal
        (∫⁻ u : ℝ, ENNReal.ofReal
          (prawitzLowerFourierComparison μ ν U u) ∂volume) := by
  let q : ℝ → ℝ := fun u =>
    (phasedPrawitzLowerComparisonIntegrand μ ν U x u).re
  have hfiniteIdentity :=
    beurlingCDFLower_sub_regularizedCDFTransform_eq
      μ ν hmomentμ hmomentν hU hR x
  have hqI : IntervalIntegrable q volume (-R) R := by
    let f : ℝ → ℂ := prawitzLowerRegularizedIntegrand μ U x
    let g : ℝ → ℂ := regularizedCDFReferenceIntegrand ν x
    have hfgI : IntervalIntegrable (fun u => f u - g u)
        volume (-R) R :=
      (integrable_prawitzLowerRegularizedIntegrand
        μ hmomentμ hU x).intervalIntegrable.sub
      (intervalIntegrable_regularizedCDFReferenceIntegrand
        ν hmomentν x (-R) R)
    have hrealI : IntervalIntegrable (fun u => (f u - g u).re)
        volume (-R) R := by
      apply intervalIntegrable_iff.mpr
      have hbase : Integrable (fun u => f u - g u)
          (volume.restrict (uIoc (-R) R)) := by
        change IntegrableOn (fun u => f u - g u) (uIoc (-R) R) volume
        exact intervalIntegrable_iff.mp hfgI
      change Integrable (fun u => (f u - g u).re)
        (volume.restrict (uIoc (-R) R))
      exact hbase.re
    refine hrealI.congr fun u _ => ?_
    dsimp only [q, f, g]
    exact re_prawitzLowerRegularized_sub_reference_eq μ ν hU x u
  have hlin :
      (∫⁻ u : ℝ, ‖q u‖ₑ ∂(volume.restrict (Ioc (-R) R))) ≤
        ∫⁻ u : ℝ, ENNReal.ofReal
          (prawitzLowerFourierComparison μ ν U u) ∂volume := by
    calc
      (∫⁻ u : ℝ, ‖q u‖ₑ ∂(volume.restrict (Ioc (-R) R))) ≤
          ∫⁻ u : ℝ, ENNReal.ofReal
            (prawitzLowerFourierComparison μ ν U u)
            ∂(volume.restrict (Ioc (-R) R)) := by
        apply lintegral_mono
        intro u
        simp only
        rw [Real.enorm_eq_ofReal_abs]
        apply ENNReal.ofReal_le_ofReal
        calc
          |q u| ≤
              ‖phasedPrawitzLowerComparisonIntegrand μ ν U x u‖ := by
            simpa [q, Real.norm_eq_abs] using
              RCLike.norm_re_le_norm
                (phasedPrawitzLowerComparisonIntegrand μ ν U x u)
          _ = prawitzLowerFourierComparison μ ν U u :=
            norm_phasedPrawitzLowerComparisonIntegrand μ ν U x u
      _ ≤ _ := lintegral_mono' Measure.restrict_le_self le_rfl
  have hnorm :
      |∫ u in (-R)..R, q u| ≤
        ENNReal.toReal
          (∫⁻ u : ℝ, ENNReal.ofReal
            (prawitzLowerFourierComparison μ ν U u) ∂volume) := by
    rw [intervalIntegral.integral_of_le
      (by linarith [hU.le.trans hR] : -R ≤ R)]
    calc
      |∫ u in Ioc (-R) R, q u ∂volume| ≤
          ENNReal.toReal
            (∫⁻ u : ℝ, ‖q u‖ₑ
              ∂(volume.restrict (Ioc (-R) R))) := by
        simpa only [Real.norm_eq_abs, Real.enorm_eq_ofReal_abs] using
          norm_integral_le_lintegral_norm
            (μ := volume.restrict (Ioc (-R) R)) q
      _ ≤ _ := ENNReal.toReal_mono hfinite hlin
  rw [show
      (1 / 2 + (regularizedCDFTransform ν x R).re) -
          (beurlingCDFCenter μ (U / (2 * Real.pi)) x -
            beurlingCDFCorrection μ (U / (2 * Real.pi)) x) =
        -((beurlingCDFCenter μ (U / (2 * Real.pi)) x -
            beurlingCDFCorrection μ (U / (2 * Real.pi)) x) -
          (1 / 2 + (regularizedCDFTransform ν x R).re)) by ring,
    hfiniteIdentity]
  exact (neg_le_abs _).trans hnorm

/-- The reverse one-sided Prawitz inversion bound. -/
theorem reverseCDFDiscrepancy_le_prawitzLowerFourierComparison_toReal
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (hmomentμ : Integrable (fun y : ℝ => y) μ)
    (hmomentν : Integrable (fun y : ℝ => y) ν)
    {U : ℝ} (hU : 0 < U) (x : ℝ)
    (hfinite :
      (∫⁻ u : ℝ, ENNReal.ofReal
        (prawitzLowerFourierComparison μ ν U u) ∂volume) ≠ ∞) :
    cdf ν x - cdf μ x ≤
      ENNReal.toReal
        (∫⁻ u : ℝ, ENNReal.ofReal
          (prawitzLowerFourierComparison μ ν U u) ∂volume) := by
  have hband :=
    (cdf_mem_beurling_band_absorbing_atom μ
      (show 0 < U / (2 * Real.pi) by positivity) x).2
  have hlimReg :=
    tendsto_regularizedCDFTransform_atTop ν hmomentν x
  have hlimRe :
      Tendsto (fun R : ℝ =>
        (regularizedCDFTransform ν x R).re) atTop
        (𝓝 (midpointCDF ν x - 1 / 2)) :=
    (Complex.continuous_re.tendsto _).comp hlimReg
  have hmid : midpointCDF ν x = cdf ν x :=
    midpointCDF_eq_cdf_of_atomless ν x
  have hlim :
      Tendsto
        (fun R : ℝ =>
          (1 / 2 + (regularizedCDFTransform ν x R).re) -
            (beurlingCDFCenter μ (U / (2 * Real.pi)) x -
              beurlingCDFCorrection μ (U / (2 * Real.pi)) x))
        atTop
        (𝓝 (cdf ν x -
            (beurlingCDFCenter μ (U / (2 * Real.pi)) x -
              beurlingCDFCorrection μ (U / (2 * Real.pi)) x))) := by
    convert
      ((tendsto_const_nhds.add hlimRe).sub tendsto_const_nhds)
        using 1
    all_goals rw [hmid]
    all_goals ring_nf
  have hev : ∀ᶠ R : ℝ in atTop,
      (1 / 2 + (regularizedCDFTransform ν x R).re) -
        (beurlingCDFCenter μ (U / (2 * Real.pi)) x -
          beurlingCDFCorrection μ (U / (2 * Real.pi)) x) ≤
        ENNReal.toReal
          (∫⁻ u : ℝ, ENNReal.ofReal
            (prawitzLowerFourierComparison μ ν U u) ∂volume) := by
    filter_upwards [eventually_ge_atTop U] with R hR
    exact lowerFiniteCutoff_le_fourierNorm
      μ ν hmomentμ hmomentν hU hR x hfinite
  have hlower :
      cdf ν x -
          (beurlingCDFCenter μ (U / (2 * Real.pi)) x -
            beurlingCDFCorrection μ (U / (2 * Real.pi)) x) ≤
        ENNReal.toReal
          (∫⁻ u : ℝ, ENNReal.ofReal
            (prawitzLowerFourierComparison μ ν U u) ∂volume) :=
    le_of_tendsto hlim hev
  linarith

/-! ## Two-sided capstone -/

/-- The four nonnegative integrals appearing in the quantitative bound. -/
noncomputable def prawitzFourIntegralBudget
    (μ ν : Measure ℝ) (U₀ U : ℝ) : ℝ≥0∞ :=
  (∫⁻ u, ENNReal.ofReal
      (prawitzCoreDiscrepancyTerm μ ν U₀ U u) ∂volume) +
  (∫⁻ u, ENNReal.ofReal
      (prawitzOuterKernelTerm μ U₀ U u) ∂volume) +
  (∫⁻ u, ENNReal.ofReal
      (prawitzCoreCorrectionTerm ν U₀ U u) ∂volume) +
  (∫⁻ u, ENNReal.ofReal
      (prawitzReferenceTailTerm ν U₀ u) ∂volume)

theorem lintegral_prawitzFourTermMajorant_eq_fourIntegralBudget
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (U₀ U : ℝ) :
    (∫⁻ u, ENNReal.ofReal
        (prawitzFourTermMajorant μ ν U₀ U u) ∂volume) =
      prawitzFourIntegralBudget μ ν U₀ U := by
  unfold prawitzFourIntegralBudget
  calc
    (∫⁻ u, ENNReal.ofReal
        (prawitzFourTermMajorant μ ν U₀ U u) ∂volume) =
        ∫⁻ u,
          ENNReal.ofReal
              (prawitzCoreDiscrepancyTerm μ ν U₀ U u) +
            ENNReal.ofReal
              (prawitzOuterKernelTerm μ U₀ U u) +
            ENNReal.ofReal
              (prawitzCoreCorrectionTerm ν U₀ U u) +
            ENNReal.ofReal
              (prawitzReferenceTailTerm ν U₀ u) ∂volume := by
      apply lintegral_congr
      intro u
      unfold prawitzFourTermMajorant
      rw [ENNReal.ofReal_add
          (add_nonneg
            (add_nonneg
              (prawitzCoreDiscrepancyTerm_nonneg μ ν U₀ U u)
              (prawitzOuterKernelTerm_nonneg μ U₀ U u))
            (prawitzCoreCorrectionTerm_nonneg ν U₀ U u))
          (prawitzReferenceTailTerm_nonneg ν U₀ u)]
      rw [ENNReal.ofReal_add
          (add_nonneg
            (prawitzCoreDiscrepancyTerm_nonneg μ ν U₀ U u)
            (prawitzOuterKernelTerm_nonneg μ U₀ U u))
          (prawitzCoreCorrectionTerm_nonneg ν U₀ U u)]
      rw [ENNReal.ofReal_add
          (prawitzCoreDiscrepancyTerm_nonneg μ ν U₀ U u)
          (prawitzOuterKernelTerm_nonneg μ U₀ U u)]
    _ = _ := by
      rw [lintegral_add_left,
        lintegral_add_left, lintegral_add_left]
      · exact
          (measurable_prawitzCoreDiscrepancyTerm μ ν U₀ U).ennreal_ofReal
      · exact
          ((measurable_prawitzCoreDiscrepancyTerm
              μ ν U₀ U).ennreal_ofReal.add
            (measurable_prawitzOuterKernelTerm
              μ U₀ U).ennreal_ofReal)
      · exact
          (((measurable_prawitzCoreDiscrepancyTerm
              μ ν U₀ U).ennreal_ofReal.add
            (measurable_prawitzOuterKernelTerm
              μ U₀ U).ennreal_ofReal).add
            (measurable_prawitzCoreCorrectionTerm
              ν U₀ U).ennreal_ofReal)

theorem lintegral_prawitzLowerFourierComparison_le_fourIntegralBudget
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {U₀ U : ℝ} (hcut : U₀ ≤ U) :
    (∫⁻ u, ENNReal.ofReal
        (prawitzLowerFourierComparison μ ν U u) ∂volume) ≤
      prawitzFourIntegralBudget μ ν U₀ U := by
  calc
    (∫⁻ u, ENNReal.ofReal
        (prawitzLowerFourierComparison μ ν U u) ∂volume) ≤
        ∫⁻ u, ENNReal.ofReal
          (prawitzFourTermMajorant μ ν U₀ U u) ∂volume :=
      lintegral_prawitzLowerFourierComparison_le_fourTermMajorant
        μ ν hcut
    _ = _ :=
      lintegral_prawitzFourTermMajorant_eq_fourIntegralBudget
        μ ν U₀ U

theorem lintegral_prawitzFourierComparison_le_fourIntegralBudget
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {U₀ U : ℝ} (hcut : U₀ ≤ U) :
    (∫⁻ u, ENNReal.ofReal
        (prawitzFourierComparison μ ν U u) ∂volume) ≤
      prawitzFourIntegralBudget μ ν U₀ U := by
  simpa [prawitzFourIntegralBudget] using
    lintegral_prawitzFourierComparison_le_four_integrals μ ν hcut

/--
Pointwise two-sided Prawitz inversion, already in the four-integral form
consumed by the quantitative characteristic-function estimates.
-/
theorem cdfAbsoluteDiscrepancy_le_prawitzFourIntegralBudget_toReal
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (hmomentμ : Integrable (fun y : ℝ => y) μ)
    (hmomentν : Integrable (fun y : ℝ => y) ν)
    {U₀ U : ℝ} (hU : 0 < U) (hcut : U₀ ≤ U) (x : ℝ)
    (hfinite : prawitzFourIntegralBudget μ ν U₀ U ≠ ∞) :
    cdfAbsoluteDiscrepancy μ ν x ≤
      ENNReal.toReal (prawitzFourIntegralBudget μ ν U₀ U) := by
  let Iupper : ℝ≥0∞ :=
    ∫⁻ u, ENNReal.ofReal
      (prawitzFourierComparison μ ν U u) ∂volume
  let Ilower : ℝ≥0∞ :=
    ∫⁻ u, ENNReal.ofReal
      (prawitzLowerFourierComparison μ ν U u) ∂volume
  have hIupper :
      Iupper ≤ prawitzFourIntegralBudget μ ν U₀ U :=
    lintegral_prawitzFourierComparison_le_fourIntegralBudget
      μ ν hcut
  have hIlower :
      Ilower ≤ prawitzFourIntegralBudget μ ν U₀ U :=
    lintegral_prawitzLowerFourierComparison_le_fourIntegralBudget
      μ ν hcut
  have hIupperFinite : Iupper ≠ ∞ := by
    intro htop
    rw [htop] at hIupper
    exact hfinite (top_unique hIupper)
  have hIlowerFinite : Ilower ≠ ∞ := by
    intro htop
    rw [htop] at hIlower
    exact hfinite (top_unique hIlower)
  have hupper :
      cdf μ x - cdf ν x ≤
        ENNReal.toReal (prawitzFourIntegralBudget μ ν U₀ U) :=
    (cdfDiscrepancy_le_prawitzFourierComparison_toReal
      μ ν hmomentμ hmomentν hU x hIupperFinite).trans
      (ENNReal.toReal_mono hfinite hIupper)
  have hlower :
      cdf ν x - cdf μ x ≤
        ENNReal.toReal (prawitzFourIntegralBudget μ ν U₀ U) :=
    (reverseCDFDiscrepancy_le_prawitzLowerFourierComparison_toReal
      μ ν hmomentμ hmomentν hU x hIlowerFinite).trans
      (ENNReal.toReal_mono hfinite hIlower)
  rw [cdfAbsoluteDiscrepancy, cdfDiscrepancy, abs_le]
  constructor <;> linarith

/--
Kolmogorov-distance Prawitz inversion in real-valued form.  Finiteness is
the natural premise for extracting a real number from the `ℝ≥0∞` budget.
-/
theorem kolmogorovDistance_le_prawitzFourIntegralBudget_toReal
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (hmomentμ : Integrable (fun y : ℝ => y) μ)
    (hmomentν : Integrable (fun y : ℝ => y) ν)
    {U₀ U : ℝ} (hU : 0 < U) (hcut : U₀ ≤ U)
    (hfinite : prawitzFourIntegralBudget μ ν U₀ U ≠ ∞) :
    kolmogorovDistance μ ν ≤
      ENNReal.toReal (prawitzFourIntegralBudget μ ν U₀ U) := by
  unfold kolmogorovDistance
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  exact cdfAbsoluteDiscrepancy_le_prawitzFourIntegralBudget_toReal
    μ ν hmomentμ hmomentν hU hcut x hfinite

/--
Unconditional `ℝ≥0∞` form of the full asymmetric Prawitz inversion
inequality.  This is the canonical theorem for composing with nonnegative
integral estimates: when the budget is infinite the statement is automatic,
and otherwise it reduces to the real-valued capstone above.
-/
theorem ofReal_kolmogorovDistance_le_prawitzFourIntegralBudget
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (hmomentμ : Integrable (fun y : ℝ => y) μ)
    (hmomentν : Integrable (fun y : ℝ => y) ν)
    {U₀ U : ℝ} (hU : 0 < U) (hcut : U₀ ≤ U) :
    ENNReal.ofReal (kolmogorovDistance μ ν) ≤
      prawitzFourIntegralBudget μ ν U₀ U := by
  by_cases hfinite : prawitzFourIntegralBudget μ ν U₀ U = ∞
  · rw [hfinite]
    exact le_top
  · have hreal :=
      kolmogorovDistance_le_prawitzFourIntegralBudget_toReal
        μ ν hmomentμ hmomentν hU hcut hfinite
    calc
      ENNReal.ofReal (kolmogorovDistance μ ν) ≤
          ENNReal.ofReal
            (ENNReal.toReal
              (prawitzFourIntegralBudget μ ν U₀ U)) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = prawitzFourIntegralBudget μ ν U₀ U :=
        ENNReal.ofReal_toReal hfinite

end Probability
end CertifiedJL
