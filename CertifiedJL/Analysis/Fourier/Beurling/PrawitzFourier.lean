/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Fourier.VaalerUpstreamBridge
import CertifiedJL.Analysis.Fourier.Beurling.KFourier
import CertifiedJL.Analysis.Fourier.Prawitz.Smoothing
import CertifiedJL.Probability.NormalApproximation.Shared.CDFMetric

/-!
# The Beurling--Prawitz Fourier bridge

This file turns the global Vaaler identity `H' = 2 Re J` into the
normalization used by the Prawitz smoothing kernel.  The phase is kept
explicit throughout: our characteristic function uses `exp(+iuy)`, while
the convolution is evaluated at `x - y`, hence the frequency-side phase is
`exp(-iux)`.
-/

open Filter FourierTransform MeasureTheory ProbabilityTheory Set
open scoped ComplexConjugate ENNReal Topology

namespace CertifiedJL
namespace Probability

/--
The Beurling approximation is the primitive of the real part of its
band-limited derivative kernel.  This is the ordinary FTC identity, valid
also at the integer lattice because the Vaaler derivative theorem is global.
-/
theorem intervalIntegral_two_re_beurlingJ_eq_beurlingH (x : ℝ) :
    (∫ s in (0 : ℝ)..x, 2 * (beurlingJ s).re) = beurlingH x := by
  have hFTC :
      (∫ s in (0 : ℝ)..x, 2 * (beurlingJ s).re) =
        beurlingH x - beurlingH 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hasDerivAt_beurlingH_two_mul_re_beurlingJ s)
      (((RCLike.continuous_re.comp continuous_beurlingJ).const_mul 2).intervalIntegrable 0 x)
  simpa [beurlingH_zero] using hFTC

/--
The compactly supported inverse-Fourier integral defining `J`, written with
the scalar exponential rather than scalar multiplication.
-/
theorem beurlingJ_eq_frequency_integral (x : ℝ) :
    beurlingJ x =
      ∫ t : ℝ,
        Complex.exp
            (((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I) *
          beurlingJHatC t := by
  rw [beurlingJ_eq_fourierInv, Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards with t
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
  congr 2
  push_cast
  ring_nf

/--
Regularized frequency primitive for `H`.  The value at frequency zero is
irrelevant to Lebesgue integration; choosing zero keeps the formula total
without pretending that the displayed quotient is defined there.
-/
noncomputable def beurlingHFrequencyIntegrand (x t : ℝ) : ℂ :=
  if t = 0 then 0
  else
    beurlingJHatC t *
      (Complex.exp
          (((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I) - 1) /
        (((Real.pi * t : ℝ) : ℂ) * Complex.I)

private theorem integrable_beurlingJ_joint (x : ℝ) :
    Integrable
      (Function.uncurry fun s t : ℝ =>
        (2 : ℂ) *
          Complex.exp
            (((2 * Real.pi * t * s : ℝ) : ℂ) * Complex.I) *
          beurlingJHatC t)
      ((volume.restrict (uIoc (0 : ℝ) x)).prod volume) := by
  have hs : Integrable (fun _ : ℝ => (2 : ℝ))
      (volume.restrict (uIoc (0 : ℝ) x)) := by
    refine integrableOn_const (C := (2 : ℝ)) ?_ (by finiteness)
    rw [Real.volume_uIoc]
    exact ENNReal.ofReal_ne_top
  have hmajorant :
      Integrable (Function.uncurry fun _ t : ℝ =>
        (2 : ℝ) * ‖beurlingJHatC t‖)
      ((volume.restrict (uIoc (0 : ℝ) x)).prod volume) :=
    hs.mul_prod integrable_beurlingJHatC.norm
  refine hmajorant.mono' ?_ ?_
  · have hcont : Continuous
        (Function.uncurry fun s t : ℝ =>
          (2 : ℂ) *
            Complex.exp
              (((2 * Real.pi * t * s : ℝ) : ℂ) * Complex.I) *
            beurlingJHatC t) := by
      apply Continuous.mul
      · apply Continuous.mul
        · exact continuous_const
        · fun_prop
      · exact continuous_beurlingJHatC.comp continuous_snd
    exact hcont.aestronglyMeasurable
  · filter_upwards with p
    rcases p with ⟨s, t⟩
    simp only [Function.uncurry_apply_pair]
    have hexpnorm :
        ‖Complex.exp
          (((2 * Real.pi * t * s : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [norm_mul, norm_mul, hexpnorm, Complex.norm_ofNat]
    norm_num

private theorem intervalIntegral_frequency_slice
    {x t : ℝ} (ht : t ≠ 0) :
    (∫ s in (0 : ℝ)..x,
        (2 : ℂ) *
          Complex.exp
            (((2 * Real.pi * t * s : ℝ) : ℂ) * Complex.I) *
          beurlingJHatC t) =
      beurlingHFrequencyIntegrand x t := by
  let c : ℂ := ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero
      (Complex.ofReal_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) ht))
      Complex.I_ne_zero
  have hexp :
      (∫ s in (0 : ℝ)..x, Complex.exp (c * s)) =
        (Complex.exp (c * x) - Complex.exp (c * 0)) / c :=
    integral_exp_mul_complex hc
  calc
    (∫ s in (0 : ℝ)..x,
        (2 : ℂ) *
          Complex.exp
            (((2 * Real.pi * t * s : ℝ) : ℂ) * Complex.I) *
          beurlingJHatC t) =
        ∫ s in (0 : ℝ)..x,
          ((2 : ℂ) * beurlingJHatC t) *
            Complex.exp (c * s) := by
      apply intervalIntegral.integral_congr
      intro s _
      dsimp [c]
      push_cast
      ring_nf
    _ =
        ((2 : ℂ) * beurlingJHatC t) *
          ∫ s in (0 : ℝ)..x, Complex.exp (c * s) := by
      rw [intervalIntegral.integral_const_mul]
    _ = beurlingHFrequencyIntegrand x t := by
      rw [hexp]
      simp only [mul_zero, Complex.exp_zero]
      unfold beurlingHFrequencyIntegrand
      rw [if_neg ht]
      dsimp [c]
      push_cast
      field_simp

/--
Complex frequency primitive of `H`.  Taking real parts gives the actual
Beurling function; retaining the complex integral makes the phase and later
characteristic-function calculation transparent.
-/
theorem intervalIntegral_two_beurlingJ_eq_frequencyIntegral (x : ℝ) :
    (∫ s in (0 : ℝ)..x, (2 : ℂ) * beurlingJ s) =
      ∫ t : ℝ, beurlingHFrequencyIntegrand x t := by
  calc
    (∫ s in (0 : ℝ)..x, (2 : ℂ) * beurlingJ s) =
        ∫ s in (0 : ℝ)..x,
          ∫ t : ℝ,
            (2 : ℂ) *
              (Complex.exp
                (((2 * Real.pi * t * s : ℝ) : ℂ) * Complex.I) *
                beurlingJHatC t) := by
      apply intervalIntegral.integral_congr
      intro s _
      change (2 : ℂ) * beurlingJ s = _
      rw [beurlingJ_eq_frequency_integral]
      simpa using
        (MeasureTheory.integral_const_mul (μ := volume) (2 : ℂ)
          (fun t : ℝ =>
            Complex.exp
              (((2 * Real.pi * t * s : ℝ) : ℂ) * Complex.I) *
            beurlingJHatC t)).symm
    _ = ∫ t : ℝ,
        ∫ s in (0 : ℝ)..x,
          (2 : ℂ) *
            Complex.exp
              (((2 * Real.pi * t * s : ℝ) : ℂ) * Complex.I) *
            beurlingJHatC t := by
      simpa only [mul_assoc] using
        (intervalIntegral_integral_swap
          (integrable_beurlingJ_joint x))
    _ = ∫ t : ℝ, beurlingHFrequencyIntegrand x t := by
      apply integral_congr_ae
      filter_upwards [volume.ae_ne (0 : ℝ)] with t ht
      exact intervalIntegral_frequency_slice ht

/-- Pointwise frequency representation of the Beurling approximation. -/
theorem beurlingH_eq_re_frequencyIntegral (x : ℝ) :
    beurlingH x =
      (∫ t : ℝ, beurlingHFrequencyIntegrand x t).re := by
  calc
    beurlingH x =
        ∫ s in (0 : ℝ)..x, 2 * (beurlingJ s).re :=
      (intervalIntegral_two_re_beurlingJ_eq_beurlingH x).symm
    _ = ∫ s in (0 : ℝ)..x, ((2 : ℂ) * beurlingJ s).re := by
      apply intervalIntegral.integral_congr
      intro s _
      simp
    _ = (∫ s in (0 : ℝ)..x, (2 : ℂ) * beurlingJ s).re :=
      intervalIntegral.intervalIntegral_re
        ((continuous_const.mul continuous_beurlingJ).intervalIntegrable 0 x)
    _ = (∫ t : ℝ, beurlingHFrequencyIntegrand x t).re := by
      rw [intervalIntegral_two_beurlingJ_eq_frequencyIntegral]

theorem measurable_beurlingHFrequencyIntegrand :
    Measurable (Function.uncurry beurlingHFrequencyIntegrand) := by
  unfold beurlingHFrequencyIntegrand
  apply Measurable.ite
  · change MeasurableSet ((fun p : ℝ × ℝ => p.2) ⁻¹' {0})
    exact measurable_snd (measurableSet_singleton 0)
  · exact measurable_const
  · have hhat : Measurable (fun p : ℝ × ℝ =>
        beurlingJHatC p.2) :=
      continuous_beurlingJHatC.measurable.comp measurable_snd
    have hexp : Measurable (fun p : ℝ × ℝ =>
        Complex.exp
          (((2 * Real.pi * p.2 * p.1 : ℝ) : ℂ) * Complex.I)) := by
      fun_prop
    have hden : Measurable (fun p : ℝ × ℝ =>
        (((Real.pi * p.2 : ℝ) : ℂ) * Complex.I)) := by
      fun_prop
    have hone : Measurable (fun _ : ℝ × ℝ => (1 : ℂ)) :=
      measurable_const
    exact (hhat.mul (hexp.sub hone)).div hden

/--
The removable quotient is dominated by the length of its spatial primitive.
This is the Fubini bound used below; in particular, no estimate on `cot` near
zero is needed.
-/
theorem norm_beurlingHFrequencyIntegrand_le (z t : ℝ) :
    ‖beurlingHFrequencyIntegrand z t‖ ≤
      2 * |z| * ‖beurlingJHatC t‖ := by
  by_cases ht : t = 0
  · simp [beurlingHFrequencyIntegrand, ht]
  · rw [← intervalIntegral_frequency_slice ht]
    calc
      ‖∫ s in (0 : ℝ)..z,
          (2 : ℂ) *
            Complex.exp
              (((2 * Real.pi * t * s : ℝ) : ℂ) * Complex.I) *
            beurlingJHatC t‖ ≤
          (2 * ‖beurlingJHatC t‖) * |z - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro s _
        rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_exp]
        norm_num
      _ = 2 * |z| * ‖beurlingJHatC t‖ := by
        rw [sub_zero]
        ring_nf

private theorem integrable_beurlingH_measure_joint
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hmoment : Integrable (fun y : ℝ => y) μ)
    (T x : ℝ) :
    Integrable
      (Function.uncurry fun y t : ℝ =>
        beurlingHFrequencyIntegrand (T * (x - y)) t)
      (μ.prod volume) := by
  have hy : Integrable (fun y : ℝ => |T * (x - y)|) μ := by
    have hsub : Integrable (fun y : ℝ => x - y) μ :=
      (integrable_const x).sub hmoment
    simpa [abs_mul] using hsub.norm.const_mul |T|
  have hmajorant :
      Integrable (Function.uncurry fun y t : ℝ =>
        (2 * |T * (x - y)|) * ‖beurlingJHatC t‖)
      (μ.prod volume) :=
    (hy.const_mul 2).mul_prod integrable_beurlingJHatC.norm
  refine hmajorant.mono' ?_ ?_
  · have hm : Measurable
        (Function.uncurry fun y t : ℝ =>
          beurlingHFrequencyIntegrand (T * (x - y)) t) :=
      measurable_beurlingHFrequencyIntegrand.comp
        ((measurable_const.mul
          (measurable_const.sub measurable_fst)).prodMk measurable_snd)
    exact hm.aestronglyMeasurable
  · filter_upwards with p
    rcases p with ⟨y, t⟩
    exact norm_beurlingHFrequencyIntegrand_le (T * (x - y)) t

/--
Fubini form of a Beurling center.  The finite first moment is exactly what
dominates the regularized quotient by `|x-y|`.
-/
theorem integral_scaledBeurlingH_eq_re_frequencyIntegral
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hmoment : Integrable (fun y : ℝ => y) μ)
    (T x : ℝ) :
    (∫ y, scaledBeurlingH T (x - y) ∂μ) =
      (∫ t : ℝ,
        ∫ y, beurlingHFrequencyIntegrand (T * (x - y)) t ∂μ).re := by
  have hjoint := integrable_beurlingH_measure_joint μ hmoment T x
  calc
    (∫ y, scaledBeurlingH T (x - y) ∂μ) =
        ∫ y, (∫ t : ℝ,
          beurlingHFrequencyIntegrand (T * (x - y)) t).re ∂μ := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [scaledBeurlingH]
      exact beurlingH_eq_re_frequencyIntegral (T * (x - y))
    _ = (∫ y, ∫ t : ℝ,
          beurlingHFrequencyIntegrand (T * (x - y)) t ∂volume ∂μ).re := by
      have hinner : Integrable
          (fun y => ∫ t : ℝ,
            beurlingHFrequencyIntegrand (T * (x - y)) t) μ := by
        simpa only [Function.uncurry_apply_pair] using
          hjoint.integral_prod_left
      exact integral_re hinner
    _ = (∫ t : ℝ, ∫ y,
          beurlingHFrequencyIntegrand (T * (x - y)) t ∂μ ∂volume).re := by
      rw [integral_integral_swap hjoint]

/-- The result of integrating the regularized `H` frequency kernel in the
spatial variable. -/
noncomputable def beurlingHMeasureFrequencyIntegrand
    (μ : Measure ℝ) (T x t : ℝ) : ℂ :=
  if t = 0 then 0
  else
    beurlingJHatC t *
      (Complex.exp
          (((2 * Real.pi * t * T * x : ℝ) : ℂ) * Complex.I) *
          charFun μ (-2 * Real.pi * t * T) - 1) /
        (((Real.pi * t : ℝ) : ℂ) * Complex.I)

private theorem integrable_frequency_phase
    (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) :
    Integrable (fun y : ℝ =>
      Complex.exp ((((a * y : ℝ) : ℂ) * Complex.I))) μ := by
  have hmeas : AEStronglyMeasurable (fun y : ℝ =>
      Complex.exp ((((a * y : ℝ) : ℂ) * Complex.I))) μ := by
    fun_prop
  simpa using
    (integrable_const (1 : ℂ)).bdd_mul
      (c := 1) hmeas (ae_of_all μ fun y => by
        rw [Complex.norm_exp]
        simp)

theorem integral_beurlingHFrequencyIntegrand
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (T x t : ℝ) :
    (∫ y, beurlingHFrequencyIntegrand (T * (x - y)) t ∂μ) =
      beurlingHMeasureFrequencyIntegrand μ T x t := by
  by_cases ht : t = 0
  · simp [beurlingHFrequencyIntegrand,
      beurlingHMeasureFrequencyIntegrand, ht]
  · unfold beurlingHMeasureFrequencyIntegrand
    rw [if_neg ht]
    have hden :
        (((Real.pi * t : ℝ) : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero
        (Complex.ofReal_ne_zero.mpr
          (mul_ne_zero Real.pi_ne_zero ht))
        Complex.I_ne_zero
    let A : ℂ :=
      beurlingJHatC t /
        (((Real.pi * t : ℝ) : ℂ) * Complex.I)
    let phaseX : ℂ :=
      Complex.exp
        (((2 * Real.pi * t * T * x : ℝ) : ℂ) * Complex.I)
    have hpoint : ∀ y : ℝ,
        beurlingHFrequencyIntegrand (T * (x - y)) t =
          A * (phaseX *
            Complex.exp
              ((((-2 * Real.pi * t * T) * y : ℝ) : ℂ) *
                Complex.I) - 1) := by
      intro y
      unfold beurlingHFrequencyIntegrand
      rw [if_neg ht]
      dsimp [A, phaseX]
      have hexponent :
          (((2 * Real.pi * t * (T * (x - y)) : ℝ) : ℂ) *
              Complex.I) =
            (((2 * Real.pi * t * T * x : ℝ) : ℂ) * Complex.I) +
              ((((-2 * Real.pi * t * T) * y : ℝ) : ℂ) *
                Complex.I) := by
        push_cast
        ring_nf
      rw [hexponent, Complex.exp_add]
      field_simp
    rw [integral_congr_ae (ae_of_all μ hpoint)]
    have hphase :=
      integrable_frequency_phase μ (-2 * Real.pi * t * T)
    have hcf :
        (∫ y,
          Complex.exp
            ((((-2 * Real.pi * t * T) * y : ℝ) : ℂ) *
              Complex.I) ∂μ) =
          charFun μ (-2 * Real.pi * t * T) := by
      rw [charFun_apply_real]
      apply integral_congr_ae
      filter_upwards with y
      congr 1
      push_cast
      ring_nf
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_sub
      (hphase.const_mul phaseX) (integrable_const (1 : ℂ))]
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_const, probReal_univ, one_smul]
    rw [hcf]
    dsimp [A, phaseX]
    field_simp

theorem integral_scaledBeurlingH_eq_re_measureFrequencyIntegral
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : Integrable (fun y : ℝ => y) μ)
    (T x : ℝ) :
    (∫ y, scaledBeurlingH T (x - y) ∂μ) =
      (∫ t : ℝ,
        beurlingHMeasureFrequencyIntegrand μ T x t).re := by
  rw [integral_scaledBeurlingH_eq_re_frequencyIntegral μ hmoment T x]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  exact integral_beurlingHFrequencyIntegrand μ T x t

theorem integrable_beurlingHMeasureFrequencyIntegrand
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : Integrable (fun y : ℝ => y) μ)
    (T x : ℝ) :
    Integrable (beurlingHMeasureFrequencyIntegrand μ T x) := by
  have hjoint := integrable_beurlingH_measure_joint μ hmoment T x
  have hiter : Integrable
      (fun t : ℝ =>
        ∫ y, beurlingHFrequencyIntegrand (T * (x - y)) t ∂μ)
      volume := by
    simpa only [Function.uncurry_apply_pair] using
      hjoint.integral_prod_right
  exact hiter.congr (ae_of_all volume fun t =>
    integral_beurlingHFrequencyIntegrand μ T x t)

/--
The ordinary, zero-regularized frequency integrand for the difference of
two Beurling centers at Prawitz bandwidth `U`.  Its phase is
`exp(-iux)`, matching the `exp(+iuy)` characteristic-function convention.
-/
noncomputable def beurlingCenterDifferenceFrequencyIntegrand
    (μ ν : Measure ℝ) (U x u : ℝ) : ℂ :=
  if u = 0 then 0
  else
    Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I) *
      ((((beurlingJHat (u / U) /
        (2 * Real.pi * u) : ℝ) : ℂ) * Complex.I) *
        (charFun μ u - charFun ν u))

theorem beurlingCDFCenter_sub_eq_re_unscaledFrequencyIntegral
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (hmomentμ : Integrable (fun y : ℝ => y) μ)
    (hmomentν : Integrable (fun y : ℝ => y) ν)
    (T x : ℝ) :
    beurlingCDFCenter μ T x - beurlingCDFCenter ν T x =
      (1 / 2) *
        (∫ t : ℝ,
          (beurlingHMeasureFrequencyIntegrand μ T x t -
            beurlingHMeasureFrequencyIntegrand ν T x t)).re := by
  have hμ :=
    integral_scaledBeurlingH_eq_re_measureFrequencyIntegral
      μ hmomentμ T x
  have hν :=
    integral_scaledBeurlingH_eq_re_measureFrequencyIntegral
      ν hmomentν T x
  have hiμ :=
    integrable_beurlingHMeasureFrequencyIntegrand μ hmomentμ T x
  have hiν :=
    integrable_beurlingHMeasureFrequencyIntegrand ν hmomentν T x
  rw [MeasureTheory.integral_sub hiμ hiν]
  unfold beurlingCDFCenter
  rw [hμ, hν]
  rw [Complex.sub_re]
  ring

private theorem measureFrequencyDifference_scaled
    (μ ν : Measure ℝ) {U x u : ℝ}
    (hU : 0 < U) :
    beurlingHMeasureFrequencyIntegrand μ (U / (2 * Real.pi)) x
          ((-U⁻¹) * u) -
        beurlingHMeasureFrequencyIntegrand ν (U / (2 * Real.pi)) x
          ((-U⁻¹) * u) =
      ((2 * U : ℝ) : ℂ) *
        beurlingCenterDifferenceFrequencyIntegrand μ ν U x u := by
  by_cases hu : u = 0
  · subst u
    simp [beurlingHMeasureFrequencyIntegrand,
      beurlingCenterDifferenceFrequencyIntegrand]
  · have hU0 : U ≠ 0 := hU.ne'
    have hscaled : (-U⁻¹) * u ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hU0)) hu
    unfold beurlingHMeasureFrequencyIntegrand
      beurlingCenterDifferenceFrequencyIntegrand
    rw [if_neg hscaled, if_neg hscaled, if_neg hu]
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
    simp only [neg_mul, one_mul]
    simp only [beurlingJHatC]
    ring

/--
Exact center-difference Fourier identity at the Prawitz scaling
`T = U/(2π)`.
-/
theorem beurlingCDFCenter_sub_eq_re_frequencyIntegral
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (hmomentμ : Integrable (fun y : ℝ => y) μ)
    (hmomentν : Integrable (fun y : ℝ => y) ν)
    {U : ℝ} (hU : 0 < U) (x : ℝ) :
    beurlingCDFCenter μ (U / (2 * Real.pi)) x -
        beurlingCDFCenter ν (U / (2 * Real.pi)) x =
      (∫ u : ℝ,
        beurlingCenterDifferenceFrequencyIntegrand μ ν U x u).re := by
  rw [beurlingCDFCenter_sub_eq_re_unscaledFrequencyIntegral
    μ ν hmomentμ hmomentν (U / (2 * Real.pi)) x]
  let g : ℝ → ℂ := fun t =>
    beurlingHMeasureFrequencyIntegrand μ (U / (2 * Real.pi)) x t -
      beurlingHMeasureFrequencyIntegrand ν (U / (2 * Real.pi)) x t
  have hscale := Measure.integral_comp_mul_left g (-U⁻¹)
  have habs : |(-U⁻¹)⁻¹| = U := by
    rw [inv_neg, inv_inv, abs_neg, abs_of_pos hU]
  rw [habs] at hscale
  have hcomp :
      (fun u : ℝ => g ((-U⁻¹) * u)) =
        fun u => ((2 * U : ℝ) : ℂ) *
          beurlingCenterDifferenceFrequencyIntegrand μ ν U x u := by
    funext u
    exact measureFrequencyDifference_scaled μ ν hU
  rw [hcomp, MeasureTheory.integral_const_mul] at hscale
  have hscale' :
      ((2 * U : ℝ) : ℂ) *
          (∫ u : ℝ,
            beurlingCenterDifferenceFrequencyIntegrand μ ν U x u) =
        ((U : ℝ) : ℂ) * ∫ t : ℝ, g t := by
    simpa only [Complex.real_smul] using hscale
  have hUcomplex : ((U : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hU.ne'
  have hintegral :
      ((1 / 2 : ℝ) : ℂ) * (∫ t : ℝ, g t) =
        ∫ u : ℝ,
          beurlingCenterDifferenceFrequencyIntegrand μ ν U x u := by
    apply (mul_left_cancel₀ hUcomplex)
    calc
      ((U : ℝ) : ℂ) *
          (((1 / 2 : ℝ) : ℂ) * ∫ t : ℝ, g t) =
          (((1 / 2 : ℝ) : ℂ) *
            (((U : ℝ) : ℂ) * ∫ t : ℝ, g t)) := by ring
      _ = (((1 / 2 : ℝ) : ℂ) *
            (((2 * U : ℝ) : ℂ) *
              ∫ u : ℝ,
                beurlingCenterDifferenceFrequencyIntegrand μ ν U x u)) := by
        rw [← hscale']
      _ = ((U : ℝ) : ℂ) *
            ∫ u : ℝ,
              beurlingCenterDifferenceFrequencyIntegrand μ ν U x u := by
        push_cast
        ring
  rw [show (1 / 2 : ℝ) * (∫ t : ℝ, g t).re =
      ((((1 / 2 : ℝ) : ℂ) * ∫ t : ℝ, g t).re) by simp]
  rw [hintegral]

theorem beurlingTriangle_eq_beurlingKHat (t : ℝ) :
    beurlingTriangle t = (beurlingKHat t : ℂ) := by
  by_cases ht : |t| < 1
  · simp [beurlingTriangle, beurlingKHat, ht,
      max_eq_left (by linarith : 0 ≤ 1 - |t|)]
  · have hle : 1 - |t| ≤ 0 := by linarith [not_lt.mp ht]
    simp [beurlingTriangle, beurlingKHat, ht, max_eq_right hle]

theorem beurlingK_eq_frequencyIntegral (z : ℝ) :
    ((beurlingK z : ℝ) : ℂ) =
      ∫ t : ℝ,
        Complex.exp
            (((-2 * Real.pi * t * z : ℝ) : ℂ) * Complex.I) *
          (beurlingKHat t : ℂ) := by
  calc
    ((beurlingK z : ℝ) : ℂ) =
        𝓕 beurlingTriangle z := by
      simpa only [beurlingK] using
        (fourier_beurlingTriangle z).symm
    _ = _ := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      apply integral_congr_ae
      filter_upwards with t
      rw [beurlingTriangle_eq_beurlingKHat]
      simp only [smul_eq_mul]

private theorem integrable_beurlingK_measure_joint
    (μ : Measure ℝ) [IsFiniteMeasure μ] (T x : ℝ) :
    Integrable
      (Function.uncurry fun y t : ℝ =>
        Complex.exp
            (((-2 * Real.pi * t * (T * (x - y)) : ℝ) : ℂ) *
              Complex.I) *
          (beurlingKHat t : ℂ))
      (μ.prod volume) := by
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) μ :=
    integrable_const 1
  have hmajorant :
      Integrable (Function.uncurry fun _ t : ℝ =>
        ‖(beurlingKHat t : ℂ)‖) (μ.prod volume) := by
    have hKhat : Integrable (fun t : ℝ =>
        ‖(beurlingKHat t : ℂ)‖) := by
      have htri := integrable_beurlingTriangle.norm
      simpa only [beurlingTriangle_eq_beurlingKHat] using htri
    change Integrable (fun p : ℝ × ℝ =>
      ‖(beurlingKHat p.2 : ℂ)‖) (μ.prod volume)
    simpa only [one_mul] using hone.mul_prod hKhat
  refine hmajorant.mono' ?_ ?_
  · have hmeas : Measurable
        (Function.uncurry fun y t : ℝ =>
          Complex.exp
              (((-2 * Real.pi * t * (T * (x - y)) : ℝ) : ℂ) *
                Complex.I) *
            (beurlingKHat t : ℂ)) := by
      have hKhat : Measurable (fun t : ℝ =>
          (beurlingKHat t : ℂ)) := by
        have heq :
            (fun t : ℝ => (beurlingKHat t : ℂ)) =
              beurlingTriangle := by
          funext t
          exact (beurlingTriangle_eq_beurlingKHat t).symm
        rw [heq]
        exact continuous_beurlingTriangle.measurable
      exact
        (by fun_prop : Measurable (fun p : ℝ × ℝ =>
          Complex.exp
            (((-2 * Real.pi * p.2 * (T * (x - p.1)) : ℝ) : ℂ) *
              Complex.I))).mul
          (hKhat.comp measurable_snd)
    exact hmeas.aestronglyMeasurable
  · filter_upwards with p
    rcases p with ⟨y, t⟩
    simp only [Function.uncurry_apply_pair]
    have hexpnorm :
        ‖Complex.exp
          (((-2 * Real.pi * t * (T * (x - y)) : ℝ) : ℂ) *
            Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [norm_mul, hexpnorm, one_mul]

theorem integral_scaledBeurlingK_eq_frequencyIntegral
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T x : ℝ) :
    ((∫ y, scaledBeurlingK T (x - y) ∂μ : ℝ) : ℂ) =
      ∫ t : ℝ,
        Complex.exp
            (((-2 * Real.pi * t * T * x : ℝ) : ℂ) * Complex.I) *
          (beurlingKHat t : ℂ) *
          charFun μ (2 * Real.pi * t * T) := by
  have hjoint := integrable_beurlingK_measure_joint μ T x
  rw [← integral_complex_ofReal]
  calc
    (∫ y, ((scaledBeurlingK T (x - y) : ℝ) : ℂ) ∂μ) =
        ∫ y, ∫ t : ℝ,
          Complex.exp
              (((-2 * Real.pi * t * (T * (x - y)) : ℝ) : ℂ) *
                Complex.I) *
            (beurlingKHat t : ℂ) ∂volume ∂μ := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [scaledBeurlingK]
      exact beurlingK_eq_frequencyIntegral (T * (x - y))
    _ = ∫ t : ℝ, ∫ y,
          Complex.exp
              (((-2 * Real.pi * t * (T * (x - y)) : ℝ) : ℂ) *
                Complex.I) *
            (beurlingKHat t : ℂ) ∂μ ∂volume := by
      rw [integral_integral_swap hjoint]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      have hphase :=
        integrable_frequency_phase μ (2 * Real.pi * t * T)
      have hpoint : ∀ y : ℝ,
          Complex.exp
                (((-2 * Real.pi * t * (T * (x - y)) : ℝ) : ℂ) *
                  Complex.I) *
              (beurlingKHat t : ℂ) =
            (Complex.exp
                (((-2 * Real.pi * t * T * x : ℝ) : ℂ) *
                  Complex.I) *
              (beurlingKHat t : ℂ)) *
            Complex.exp
                ((((2 * Real.pi * t * T) * y : ℝ) : ℂ) *
                  Complex.I) := by
        intro y
        have hexponent :
            (((-2 * Real.pi * t * (T * (x - y)) : ℝ) : ℂ) *
                Complex.I) =
              (((-2 * Real.pi * t * T * x : ℝ) : ℂ) *
                Complex.I) +
              ((((2 * Real.pi * t * T) * y : ℝ) : ℂ) *
                Complex.I) := by
          push_cast
          ring
        rw [hexponent, Complex.exp_add]
        ring
      rw [integral_congr_ae (ae_of_all μ hpoint)]
      rw [MeasureTheory.integral_const_mul]
      have hcf :
          (∫ y,
            Complex.exp
              ((((2 * Real.pi * t * T) * y : ℝ) : ℂ) *
                Complex.I) ∂μ) =
            charFun μ (2 * Real.pi * t * T) := by
        rw [charFun_apply_real]
        apply integral_congr_ae
        filter_upwards with y
        congr 1
        push_cast
        ring
      rw [hcf]

/-- Frequency-side squared-sinc correction at bandwidth `U`. -/
noncomputable def beurlingCorrectionFrequencyIntegrand
    (μ : Measure ℝ) (U x u : ℝ) : ℂ :=
  Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I) *
    ((beurlingKHat (u / U) / (2 * U) : ℝ) : ℂ) *
    charFun μ u

theorem beurlingCDFCorrection_eq_re_frequencyIntegral
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {U : ℝ} (hU : 0 < U) (x : ℝ) :
    beurlingCDFCorrection μ (U / (2 * Real.pi)) x =
      (∫ u : ℝ,
        beurlingCorrectionFrequencyIntegrand μ U x u).re := by
  have hU0 : U ≠ 0 := hU.ne'
  have hspatial :=
    integral_scaledBeurlingK_eq_frequencyIntegral
      μ (U / (2 * Real.pi)) x
  let g : ℝ → ℂ := fun t =>
    Complex.exp
        (((-2 * Real.pi * t * (U / (2 * Real.pi)) * x : ℝ) : ℂ) *
          Complex.I) *
      (beurlingKHat t : ℂ) *
      charFun μ (2 * Real.pi * t * (U / (2 * Real.pi)))
  have hscale := Measure.integral_comp_mul_left g U⁻¹
  have habs : |(U⁻¹)⁻¹| = U := by
    rw [inv_inv, abs_of_pos hU]
  rw [habs] at hscale
  have hcomp :
      (fun u : ℝ => g (U⁻¹ * u)) =
        fun u => ((2 * U : ℝ) : ℂ) *
          beurlingCorrectionFrequencyIntegrand μ U x u := by
    funext u
    dsimp [g, beurlingCorrectionFrequencyIntegrand]
    have harg :
        2 * Real.pi * (U⁻¹ * u) * (U / (2 * Real.pi)) = u := by
      field_simp [hU0, Real.pi_ne_zero]
    have hphase :
        -2 * Real.pi * (U⁻¹ * u) *
            (U / (2 * Real.pi)) * x = -(u * x) := by
      field_simp [hU0, Real.pi_ne_zero]
    have hratio : U⁻¹ * u = u / U := by
      field_simp [hU0]
    rw [harg, hphase, hratio]
    push_cast
    field_simp [hU0]
  rw [hcomp, MeasureTheory.integral_const_mul] at hscale
  have hscale' :
      ((2 * U : ℝ) : ℂ) *
          ∫ u : ℝ, beurlingCorrectionFrequencyIntegrand μ U x u =
        ((U : ℝ) : ℂ) * ∫ t : ℝ, g t := by
    simpa only [Complex.real_smul] using hscale
  have hspatialRe :
      (∫ y, scaledBeurlingK (U / (2 * Real.pi)) (x - y) ∂μ) =
        (∫ t : ℝ, g t).re := by
    have := congrArg Complex.re hspatial
    simpa only [Complex.ofReal_re] using this
  unfold beurlingCDFCorrection
  rw [hspatialRe]
  have hUcomplex : ((U : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hU0
  have heq :
      ((1 / 2 : ℝ) : ℂ) * ∫ t : ℝ, g t =
        ∫ u : ℝ, beurlingCorrectionFrequencyIntegrand μ U x u := by
    apply mul_left_cancel₀ hUcomplex
    calc
      ((U : ℝ) : ℂ) *
          (((1 / 2 : ℝ) : ℂ) * ∫ t : ℝ, g t) =
          (((1 / 2 : ℝ) : ℂ) *
            (((U : ℝ) : ℂ) * ∫ t : ℝ, g t)) := by ring
      _ = (((1 / 2 : ℝ) : ℂ) *
            (((2 * U : ℝ) : ℂ) *
              ∫ u : ℝ,
                beurlingCorrectionFrequencyIntegrand μ U x u)) := by
        rw [← hscale']
      _ = ((U : ℝ) : ℂ) *
            ∫ u : ℝ,
              beurlingCorrectionFrequencyIntegrand μ U x u := by
        push_cast
        ring
  rw [show (1 / 2 : ℝ) *
      (∫ t : ℝ, g t).re =
      ((((1 / 2 : ℝ) : ℂ) * ∫ t : ℝ, g t).re) by simp]
  rw [heq]

/--
Uniform (phase-free) Fourier majorant obtained from the exact center and
correction identities.
-/
noncomputable def beurlingPrawitzErrorBound
    (μ ν : Measure ℝ) (U : ℝ) : ℝ :=
  (∫ u : ℝ,
      ‖beurlingCenterDifferenceFrequencyIntegrand μ ν U 0 u‖) +
    (∫ u : ℝ,
      ‖beurlingCorrectionFrequencyIntegrand μ U 0 u‖) +
    (∫ u : ℝ,
      ‖beurlingCorrectionFrequencyIntegrand ν U 0 u‖)

theorem norm_centerDifferenceFrequencyIntegrand_independent
    (μ ν : Measure ℝ) (U x u : ℝ) :
    ‖beurlingCenterDifferenceFrequencyIntegrand μ ν U x u‖ =
      ‖beurlingCenterDifferenceFrequencyIntegrand μ ν U 0 u‖ := by
  unfold beurlingCenterDifferenceFrequencyIntegrand
  by_cases hu : u = 0
  · simp [hu]
  · rw [if_neg hu, if_neg hu]
    rw [norm_mul, norm_mul]
    have hx :
        ‖Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    have hzero :
        ‖Complex.exp (((-(u * 0) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      simp
    simp only [norm_mul, hx, hzero, one_mul]

theorem norm_correctionFrequencyIntegrand_independent
    (μ : Measure ℝ) (U x u : ℝ) :
    ‖beurlingCorrectionFrequencyIntegrand μ U x u‖ =
      ‖beurlingCorrectionFrequencyIntegrand μ U 0 u‖ := by
  unfold beurlingCorrectionFrequencyIntegrand
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  have hx :
      ‖Complex.exp (((-(u * x) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hzero :
      ‖Complex.exp (((-(u * 0) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    simp
  simp only [hx, hzero, one_mul]

/--
Pointwise Prawitz--Beurling smoothing capstone.  The phase is present in the
exact identities above and disappears here only after taking norms.
-/
theorem cdfAbsoluteDiscrepancy_le_beurlingPrawitzErrorBound
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (hmomentμ : Integrable (fun y : ℝ => y) μ)
    (hmomentν : Integrable (fun y : ℝ => y) ν)
    {U : ℝ} (hU : 0 < U) (x : ℝ) :
    cdfAbsoluteDiscrepancy μ ν x ≤
      beurlingPrawitzErrorBound μ ν U := by
  let T : ℝ := U / (2 * Real.pi)
  have hT : 0 < T := by
    dsimp [T]
    positivity
  have hband :=
    abs_cdfDiscrepancy_sub_beurlingCenters_le μ ν hT x
  have hcenter :=
    beurlingCDFCenter_sub_eq_re_frequencyIntegral
      μ ν hmomentμ hmomentν hU x
  have hcorrμ :=
    beurlingCDFCorrection_eq_re_frequencyIntegral μ hU x
  have hcorrν :=
    beurlingCDFCorrection_eq_re_frequencyIntegral ν hU x
  let IC : ℂ := ∫ u : ℝ,
    beurlingCenterDifferenceFrequencyIntegrand μ ν U x u
  let IKμ : ℂ := ∫ u : ℝ,
    beurlingCorrectionFrequencyIntegrand μ U x u
  let IKν : ℂ := ∫ u : ℝ,
    beurlingCorrectionFrequencyIntegrand ν U x u
  have hIC :
      |(beurlingCDFCenter μ T x -
          beurlingCDFCenter ν T x)| ≤
        ∫ u : ℝ,
          ‖beurlingCenterDifferenceFrequencyIntegrand μ ν U 0 u‖ := by
    rw [show T = U / (2 * Real.pi) by rfl, hcenter]
    calc
      |IC.re| ≤ ‖IC‖ := by
        simpa [Real.norm_eq_abs] using RCLike.norm_re_le_norm IC
      _ ≤ ∫ u : ℝ,
          ‖beurlingCenterDifferenceFrequencyIntegrand μ ν U x u‖ :=
        norm_integral_le_integral_norm _
      _ = ∫ u : ℝ,
          ‖beurlingCenterDifferenceFrequencyIntegrand μ ν U 0 u‖ := by
        apply integral_congr_ae
        filter_upwards with u
        exact norm_centerDifferenceFrequencyIntegrand_independent
          μ ν U x u
  have hIKμ :
      beurlingCDFCorrection μ T x ≤
        ∫ u : ℝ,
          ‖beurlingCorrectionFrequencyIntegrand μ U 0 u‖ := by
    rw [show T = U / (2 * Real.pi) by rfl, hcorrμ]
    calc
      IKμ.re ≤ |IKμ.re| := le_abs_self _
      _ ≤ ‖IKμ‖ := by
        simpa [Real.norm_eq_abs] using RCLike.norm_re_le_norm IKμ
      _ ≤ ∫ u : ℝ,
          ‖beurlingCorrectionFrequencyIntegrand μ U x u‖ :=
        norm_integral_le_integral_norm _
      _ = ∫ u : ℝ,
          ‖beurlingCorrectionFrequencyIntegrand μ U 0 u‖ := by
        apply integral_congr_ae
        filter_upwards with u
        exact norm_correctionFrequencyIntegrand_independent μ U x u
  have hIKν :
      beurlingCDFCorrection ν T x ≤
        ∫ u : ℝ,
          ‖beurlingCorrectionFrequencyIntegrand ν U 0 u‖ := by
    rw [show T = U / (2 * Real.pi) by rfl, hcorrν]
    calc
      IKν.re ≤ |IKν.re| := le_abs_self _
      _ ≤ ‖IKν‖ := by
        simpa [Real.norm_eq_abs] using RCLike.norm_re_le_norm IKν
      _ ≤ ∫ u : ℝ,
          ‖beurlingCorrectionFrequencyIntegrand ν U x u‖ :=
        norm_integral_le_integral_norm _
      _ = ∫ u : ℝ,
          ‖beurlingCorrectionFrequencyIntegrand ν U 0 u‖ := by
        apply integral_congr_ae
        filter_upwards with u
        exact norm_correctionFrequencyIntegrand_independent ν U x u
  unfold cdfAbsoluteDiscrepancy beurlingPrawitzErrorBound
  calc
    |cdfDiscrepancy μ ν x| =
        |(cdfDiscrepancy μ ν x -
            (beurlingCDFCenter μ T x -
              beurlingCDFCenter ν T x)) +
          (beurlingCDFCenter μ T x -
            beurlingCDFCenter ν T x)| := by ring_nf
    _ ≤ |cdfDiscrepancy μ ν x -
            (beurlingCDFCenter μ T x -
              beurlingCDFCenter ν T x)| +
          |beurlingCDFCenter μ T x -
              beurlingCDFCenter ν T x| := abs_add_le _ _
    _ ≤ (beurlingCDFCorrection μ T x +
            beurlingCDFCorrection ν T x) +
          |beurlingCDFCenter μ T x -
            beurlingCDFCenter ν T x| :=
      add_le_add hband le_rfl
    _ ≤ _ := by linarith

/-- Kolmogorov-distance form of the Fourier smoothing capstone. -/
theorem kolmogorovDistance_le_beurlingPrawitzErrorBound
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (hmomentμ : Integrable (fun y : ℝ => y) μ)
    (hmomentν : Integrable (fun y : ℝ => y) ν)
    {U : ℝ} (hU : 0 < U) :
    kolmogorovDistance μ ν ≤
      beurlingPrawitzErrorBound μ ν U := by
  unfold kolmogorovDistance
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  exact cdfAbsoluteDiscrepancy_le_beurlingPrawitzErrorBound
    μ ν hmomentμ hmomentν hU x

end Probability
end CertifiedJL
