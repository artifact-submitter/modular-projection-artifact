/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author, Chris Birkbeck
-/

import CertifiedJL.Probability.NormalApproximation.Shared.CDFMetric
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Fourier inversion for distribution functions

This file proves the principal-value Fourier inversion statement used by
the Prawitz smoothing argument.  The singular Fourier kernel is represented
by an ordinary integral only after subtracting its value at frequency zero.
This regularization is essential: the unregularized kernel is not Bochner
integrable on any neighbourhood of zero.

The analytic engine is the classical Dirichlet integral
`∫₀ᵇ sin t / t dt → π / 2`.  Its Frullani--Fubini proof and uniform boundedness
corollary are adapted from Chris Birkbeck's `FourierJordan.lean` in AINTLIB
(commit `dd7e0f33693e2c71f8527ab4bc104e94407fa542`), whose source header declares
the code released under Apache 2.0.

## Main results

* `tendsto_dirichletIntegral_atTop`: the Dirichlet integral.
* `exists_uniform_bound_dirichletIntegral`: a uniform bound for its primitive.
* `tendsto_regularizedCDFTransform`: Fourier inversion at a possible atom,
  returning the midpoint CDF.
* `tendsto_regularizedCDFTransform_closed`: the corresponding closed-`Iic`
  formula with the explicit half-atom correction.
-/

open Filter MeasureTheory ProbabilityTheory Set intervalIntegral
open scoped ComplexConjugate ENNReal Interval Topology

namespace CertifiedJL
namespace Probability

/-! ## The Dirichlet integral -/

private theorem hasDerivAt_exp_sin_primitive (y x : ℝ) :
    HasDerivAt (fun t : ℝ =>
      -(Real.exp (-(y * t)) * (Real.cos t + y * Real.sin t)) / (1 + y ^ 2))
      (Real.exp (-(y * x)) * Real.sin x) x := by
  have h0 : HasDerivAt (fun t : ℝ => y * t) y x := by
    simpa using (hasDerivAt_id x).const_mul y
  have h1 : HasDerivAt (fun t : ℝ => -(y * t)) (-y) x := h0.neg
  have hexp := h1.exp
  have htrig : HasDerivAt (fun t : ℝ => Real.cos t + y * Real.sin t)
      (-Real.sin x + y * Real.cos x) x :=
    (Real.hasDerivAt_cos x).add ((Real.hasDerivAt_sin x).const_mul y)
  have hfull := ((hexp.mul htrig).neg).div_const (1 + y ^ 2)
  have hy2 : (1 + y ^ 2) ≠ 0 := by positivity
  have hval : -(Real.exp (-(y * x)) * -y *
      (Real.cos x + y * Real.sin x) +
      Real.exp (-(y * x)) * (-Real.sin x + y * Real.cos x)) /
      (1 + y ^ 2) = Real.exp (-(y * x)) * Real.sin x := by
    rw [div_eq_iff hy2]
    ring
  rwa [hval] at hfull

private theorem integral_exp_neg_mul_sin (y b : ℝ) :
    ∫ x in (0 : ℝ)..b, Real.exp (-(y * x)) * Real.sin x =
      (1 - Real.exp (-(y * b)) *
        (Real.cos b + y * Real.sin b)) / (1 + y ^ 2) := by
  have hint : IntervalIntegrable
      (fun x : ℝ => Real.exp (-(y * x)) * Real.sin x)
      volume 0 b := by
    refine ContinuousOn.intervalIntegrable ?_
    fun_prop
  have hftc := integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ =>
      -(Real.exp (-(y * t)) * (Real.cos t + y * Real.sin t)) /
        (1 + y ^ 2))
    (fun x _ => hasDerivAt_exp_sin_primitive y x) hint
  rw [hftc]
  simp only [mul_zero, neg_zero, Real.exp_zero, Real.cos_zero,
    Real.sin_zero, add_zero, mul_one]
  ring

private theorem integral_exp_neg_mul_Ioi {x : ℝ} (hx : 0 < x) :
    ∫ y in Ioi (0 : ℝ), Real.exp (-(x * y)) = 1 / x := by
  have hderiv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun y : ℝ => -Real.exp (-(x * y)) / x)
        (Real.exp (-(x * t))) t := by
    intro t _
    have h0 : HasDerivAt (fun y : ℝ => x * y) x t := by
      simpa using (hasDerivAt_id t).const_mul x
    have h1 : HasDerivAt (fun y : ℝ => -(x * y)) (-x) t := h0.neg
    have h2 := (h1.exp.neg).div_const x
    have hval : -(Real.exp (-(x * t)) * -x) / x =
        Real.exp (-(x * t)) := by
      rw [div_eq_iff hx.ne']
      ring
    rwa [hval] at h2
  have hint : IntegrableOn (fun y : ℝ => Real.exp (-(x * y))) (Ioi 0) := by
    have h := exp_neg_integrableOn_Ioi (0 : ℝ) hx
    refine h.congr_fun (fun y _ => ?_) measurableSet_Ioi
    ring_nf
  have htend : Tendsto (fun y : ℝ => -Real.exp (-(x * y)) / x)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => -(x * y)) atTop atBot := by
      refine tendsto_neg_atBot_iff.mpr ?_
      exact Tendsto.const_mul_atTop hx tendsto_id
    simpa using ((Real.tendsto_exp_atBot.comp h1).neg.div_const x)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  rw [h, mul_zero, neg_zero, Real.exp_zero, zero_sub, neg_div, neg_neg,
    one_div]

private theorem dirichletIntegral_fubini {b : ℝ} (hb : 0 < b) :
    (∫ x in (0 : ℝ)..b, Real.sin x / x) =
      ∫ y in Ioi (0 : ℝ),
        (1 - Real.exp (-(y * b)) *
          (Real.cos b + y * Real.sin b)) / (1 + y ^ 2) := by
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun x y => Real.sin x * Real.exp (-(x * y)))
      ((volume.restrict (Ioc (0 : ℝ) b)).prod
        (volume.restrict (Ioi (0 : ℝ)))) := by
    refine Continuous.aestronglyMeasurable ?_
    fun_prop
  have hintSlice : ∀ x ∈ Ioc (0 : ℝ) b,
      Integrable (fun y => Real.sin x * Real.exp (-(x * y)))
        (volume.restrict (Ioi (0 : ℝ))) := by
    intro x hx
    refine Integrable.const_mul ?_ _
    have h := exp_neg_integrableOn_Ioi (0 : ℝ) hx.1
    refine h.congr_fun (fun y _ => ?_) measurableSet_Ioi
    ring_nf
  have hnorm : ∀ x ∈ Ioc (0 : ℝ) b,
      (∫ y in Ioi (0 : ℝ),
        ‖Real.sin x * Real.exp (-(x * y))‖) ≤ 1 := by
    intro x hx
    have hval : (∫ y in Ioi (0 : ℝ),
        ‖Real.sin x * Real.exp (-(x * y))‖) =
        |Real.sin x| * (1 / x) := by
      rw [show (fun y => ‖Real.sin x * Real.exp (-(x * y))‖) =
          fun y => |Real.sin x| * Real.exp (-(x * y)) from
        funext (fun y => by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
            Real.abs_exp])]
      rw [MeasureTheory.integral_const_mul,
        integral_exp_neg_mul_Ioi hx.1]
    rw [hval]
    have hsin : |Real.sin x| ≤ |x| := Real.abs_sin_le_abs
    rw [abs_of_pos hx.1] at hsin
    rw [mul_one_div, div_le_one hx.1]
    exact hsin
  have hprod : Integrable
      (Function.uncurry fun x y => Real.sin x * Real.exp (-(x * y)))
      ((volume.restrict (Ioc (0 : ℝ) b)).prod
        (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff hmeas]
    constructor
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
      exact Eventually.of_forall fun x hx => hintSlice x hx
    · refine Integrable.mono'
        (g := fun _ => (1 : ℝ))
        (integrableOn_const (C := (1 : ℝ)) (by
          rw [Real.volume_Ioc]
          exact ENNReal.ofReal_ne_top))
        ((hmeas.norm).integral_prod_right') ?_
      refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
      refine Eventually.of_forall fun x hx => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hnorm x hx
  have hswap := integral_integral_swap hprod
  rw [intervalIntegral.integral_of_le hb.le]
  calc
    (∫ x in Ioc (0 : ℝ) b, Real.sin x / x) =
        ∫ x in Ioc (0 : ℝ) b,
          (∫ y in Ioi (0 : ℝ),
            Real.sin x * Real.exp (-(x * y))) := by
      refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
      rw [MeasureTheory.integral_const_mul,
        integral_exp_neg_mul_Ioi hx.1,
        mul_one_div]
    _ = ∫ y in Ioi (0 : ℝ),
        (∫ x in Ioc (0 : ℝ) b,
          Real.sin x * Real.exp (-(x * y))) := hswap
    _ = ∫ y in Ioi (0 : ℝ),
        (1 - Real.exp (-(y * b)) *
          (Real.cos b + y * Real.sin b)) / (1 + y ^ 2) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
      rw [← intervalIntegral.integral_of_le hb.le]
      rw [show (fun x => Real.sin x * Real.exp (-(x * y))) =
          fun x => Real.exp (-(y * x)) * Real.sin x from
        funext (fun x => by rw [mul_comm x y, mul_comm])]
      exact integral_exp_neg_mul_sin y b

/-- The classical Dirichlet integral
`∫₀ᵇ sin t / t dt → π / 2` as `b → +∞`. -/
theorem tendsto_dirichletIntegral_atTop :
    Tendsto (fun b : ℝ => ∫ x in (0 : ℝ)..b, Real.sin x / x)
      atTop (𝓝 (Real.pi / 2)) := by
  have hvalue : (Real.pi / 2 : ℝ) =
      ∫ y in Ioi (0 : ℝ), (1 + y ^ 2)⁻¹ := by
    rw [integral_Ioi_inv_one_add_sq]
    simp
  rw [hvalue]
  have heventually :
      (fun b : ℝ => ∫ x in (0 : ℝ)..b, Real.sin x / x) =ᶠ[atTop]
        fun b => ∫ y in Ioi (0 : ℝ),
          (1 - Real.exp (-(y * b)) *
            (Real.cos b + y * Real.sin b)) / (1 + y ^ 2) := by
    filter_upwards [eventually_gt_atTop 0] with b hb
    exact dirichletIntegral_fubini hb
  rw [tendsto_congr' heventually]
  refine tendsto_integral_filter_of_dominated_convergence
    (bound := fun y => (1 + (1 + y) * Real.exp (-y)) /
      (1 + y ^ 2)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun _ => by
      refine Continuous.aestronglyMeasurable ?_
      have hden : ∀ y : ℝ, (1 + y ^ 2) ≠ 0 := fun y => by positivity
      fun_prop (disch := exact hden)
  · filter_upwards [eventually_ge_atTop 1] with b hb
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    refine Eventually.of_forall fun y hy => ?_
    rw [mem_Ioi] at hy
    have hden : 0 < (1 + y ^ 2 : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hden]
    refine div_le_div_of_nonneg_right ?_ hden.le
    have htrig : |Real.cos b + y * Real.sin b| ≤ 1 + y := by
      calc
        |Real.cos b + y * Real.sin b| ≤
            |Real.cos b| + |y * Real.sin b| := abs_add_le _ _
        _ ≤ 1 + y := by
          have hcos := Real.abs_cos_le_one b
          have hsin := Real.abs_sin_le_one b
          rw [abs_mul, abs_of_pos hy]
          nlinarith [abs_nonneg (Real.sin b)]
    have hexp : Real.exp (-(y * b)) ≤ Real.exp (-y) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    calc
      |1 - Real.exp (-(y * b)) *
          (Real.cos b + y * Real.sin b)| ≤
          1 + Real.exp (-(y * b)) *
            |Real.cos b + y * Real.sin b| := by
        have h := norm_sub_le (1 : ℝ)
          (Real.exp (-(y * b)) *
            (Real.cos b + y * Real.sin b))
        simp only [Real.norm_eq_abs, abs_one] at h
        rw [abs_mul, Real.abs_exp] at h
        exact h
      _ ≤ 1 + (1 + y) * Real.exp (-y) := by
        have hmul : Real.exp (-(y * b)) *
            |Real.cos b + y * Real.sin b| ≤
            Real.exp (-y) * (1 + y) :=
          mul_le_mul hexp htrig (abs_nonneg _)
            (Real.exp_pos _).le
        nlinarith
  · have hint1 : IntegrableOn
        (fun y : ℝ => (1 + y ^ 2)⁻¹) (Ioi 0) :=
      integrable_inv_one_add_sq.integrableOn
    have hint2 : IntegrableOn
        (fun y : ℝ => Real.exp (-y)) (Ioi 0) := by
      have h := exp_neg_integrableOn_Ioi
        (0 : ℝ) (by norm_num : (0 : ℝ) < 1)
      refine h.congr_fun (fun y _ => ?_) measurableSet_Ioi
      change Real.exp (-1 * y) = Real.exp (-y)
      rw [neg_one_mul]
    have hint3 : IntegrableOn
        (fun y : ℝ => 2 * Real.exp (-(y / 2))) (Ioi 0) := by
      have h := exp_neg_integrableOn_Ioi
        (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)
      have h' : IntegrableOn
          (fun y : ℝ => Real.exp (-(y / 2))) (Ioi 0) := by
        refine h.congr_fun (fun y _ => ?_) measurableSet_Ioi
        change Real.exp (-(1 / 2) * y) = Real.exp (-(y / 2))
        rw [show (-(1 / 2) * y : ℝ) = -(y / 2) by ring]
      exact h'.const_mul 2
    refine Integrable.mono' ((hint1.add hint2).add hint3) ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      have hden : ∀ y : ℝ, (1 + y ^ 2) ≠ 0 := fun y => by positivity
      fun_prop (disch := exact hden)
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
      refine Eventually.of_forall fun y hy => ?_
      rw [mem_Ioi] at hy
      have hden : 0 < (1 + y ^ 2 : ℝ) := by positivity
      have hden1 : (1 : ℝ) ≤ 1 + y ^ 2 := by nlinarith
      have hnonneg : 0 ≤
          (1 + (1 + y) * Real.exp (-y)) /
            (1 + y ^ 2) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      have hsplit :
          (1 + (1 + y) * Real.exp (-y)) / (1 + y ^ 2) =
            (1 + y ^ 2)⁻¹ +
              ((1 + y) * Real.exp (-y)) / (1 + y ^ 2) := by
        rw [add_div, one_div]
      rw [hsplit]
      have hquot :
          ((1 + y) * Real.exp (-y)) / (1 + y ^ 2) ≤
            (1 + y) * Real.exp (-y) := by
        rw [div_le_iff₀ hden]
        nlinarith [mul_nonneg (by linarith : 0 ≤ (1 + y : ℝ))
          (Real.exp_pos (-y)).le]
      have hyexp : y * Real.exp (-y) ≤
          2 * Real.exp (-(y / 2)) := by
        have h1 : y / 2 + 1 ≤ Real.exp (y / 2) :=
          Real.add_one_le_exp (y / 2)
        have h2 : y ≤ 2 * Real.exp (y / 2) := by linarith
        calc
          y * Real.exp (-y) ≤
              (2 * Real.exp (y / 2)) * Real.exp (-y) :=
            mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
          _ = 2 * Real.exp (-(y / 2)) := by
            rw [mul_assoc, ← Real.exp_add]
            ring_nf
      have hfinal : (1 + y) * Real.exp (-y) ≤
          Real.exp (-y) + 2 * Real.exp (-(y / 2)) := by
        have heq : (1 + y) * Real.exp (-y) =
            Real.exp (-y) + y * Real.exp (-y) := by ring
        rw [heq]
        linarith
      calc
        (1 + y ^ 2)⁻¹ +
            ((1 + y) * Real.exp (-y)) / (1 + y ^ 2) ≤
            (1 + y ^ 2)⁻¹ + (1 + y) * Real.exp (-y) := by
          linarith
        _ ≤ (1 + y ^ 2)⁻¹ +
            (Real.exp (-y) + 2 * Real.exp (-(y / 2))) := by
          linarith
        _ = (fun y : ℝ => (1 + y ^ 2)⁻¹) y +
            (fun y : ℝ => Real.exp (-y)) y +
            (fun y : ℝ => 2 * Real.exp (-(y / 2))) y := by
          ring
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    refine Eventually.of_forall fun y hy => ?_
    rw [mem_Ioi] at hy
    have hzero : Tendsto
        (fun b : ℝ => Real.exp (-(y * b)) *
          (Real.cos b + y * Real.sin b))
        atTop (𝓝 0) := by
      refine squeeze_zero_norm
        (a := fun b => (1 + y) * Real.exp (-(y * b)))
        (fun b => ?_) ?_
      · rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
        have htrig : |Real.cos b + y * Real.sin b| ≤ 1 + y := by
          calc
            |Real.cos b + y * Real.sin b| ≤
                |Real.cos b| + |y * Real.sin b| := abs_add_le _ _
            _ ≤ 1 + y := by
              have hcos := Real.abs_cos_le_one b
              have hsin := Real.abs_sin_le_one b
              rw [abs_mul, abs_of_pos hy]
              nlinarith [abs_nonneg (Real.sin b)]
        calc
          Real.exp (-(y * b)) *
              |Real.cos b + y * Real.sin b| ≤
              Real.exp (-(y * b)) * (1 + y) :=
            mul_le_mul_of_nonneg_left htrig (Real.exp_pos _).le
          _ = (1 + y) * Real.exp (-(y * b)) := by ring
      · have hlin : Tendsto (fun b : ℝ => -(y * b))
            atTop atBot := by
          refine tendsto_neg_atBot_iff.mpr ?_
          exact Tendsto.const_mul_atTop hy tendsto_id
        simpa using
          (Real.tendsto_exp_atBot.comp hlin).const_mul (1 + y)
    have hlim : Tendsto
        (fun b : ℝ =>
          (1 - Real.exp (-(y * b)) *
            (Real.cos b + y * Real.sin b)) /
            (1 + y ^ 2))
        atTop (𝓝 ((1 - 0) / (1 + y ^ 2))) :=
      (Tendsto.const_sub 1 hzero).div_const _
    simpa using hlim

/-- The function `sin x / x`, totalized by division at zero, is interval
integrable on every compact interval. -/
theorem intervalIntegrable_sin_div (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.sin x / x)
      volume a b := by
  refine intervalIntegrable_iff.mpr ?_
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => Real.sin x / x)
      (volume.restrict (uIoc a b)) :=
    (Real.measurable_sin.div measurable_id).aestronglyMeasurable
  refine Integrable.mono'
    (g := fun _ => (1 : ℝ))
    (integrableOn_const (C := (1 : ℝ)) (by
      rw [Real.volume_uIoc]
      exact ENNReal.ofReal_ne_top))
    hmeas ?_
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [abs_div]
      exact div_le_one_of_le₀ Real.abs_sin_le_abs (abs_nonneg _)

/-- A uniform finite bound for all nonnegative truncations of the
Dirichlet integral. -/
theorem exists_uniform_bound_dirichletIntegral :
    ∃ C : ℝ, 0 < C ∧ ∀ b : ℝ, 0 ≤ b →
      |∫ x in (0 : ℝ)..b, Real.sin x / x| ≤ C := by
  let g : ℝ → ℝ := fun b => ∫ x in (0 : ℝ)..b, Real.sin x / x
  have hg : Continuous g :=
    intervalIntegral.continuous_primitive
      (fun a b => intervalIntegrable_sin_div a b) 0
  have htail := tendsto_dirichletIntegral_atTop.eventually
    (Metric.closedBall_mem_nhds (Real.pi / 2) one_pos)
  rw [eventually_atTop] at htail
  obtain ⟨b₀, hb₀⟩ := htail
  obtain ⟨C₀, hC₀⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := max b₀ 0)).exists_bound_of_continuousOn
      hg.continuousOn
  refine ⟨max C₀ (|Real.pi / 2| + 1) + 1, by positivity,
    fun b hb => ?_⟩
  rcases le_or_gt b (max b₀ 0) with hble | hbgt
  · have h := hC₀ b ⟨hb, hble⟩
    rw [Real.norm_eq_abs] at h
    calc
      |g b| ≤ C₀ := h
      _ ≤ max C₀ (|Real.pi / 2| + 1) := le_max_left _ _
      _ ≤ max C₀ (|Real.pi / 2| + 1) + 1 :=
        le_add_of_nonneg_right zero_le_one
  · have hb' : b₀ ≤ b := le_trans (le_max_left _ _) hbgt.le
    have h := hb₀ b hb'
    rw [Real.dist_eq] at h
    calc
      |g b| = |(g b - Real.pi / 2) + Real.pi / 2| := by ring_nf
      _ ≤ |g b - Real.pi / 2| + |Real.pi / 2| := abs_add_le _ _
      _ ≤ 1 + |Real.pi / 2| := by gcongr
      _ = |Real.pi / 2| + 1 := add_comm _ _
      _ ≤ max C₀ (|Real.pi / 2| + 1) := le_max_right _ _
      _ ≤ max C₀ (|Real.pi / 2| + 1) + 1 :=
        le_add_of_nonneg_right zero_le_one

/-! ## The pointwise inversion kernel -/

/--
The midpoint CDF recovered by Fourier inversion at a possible atom.

For a continuous law this is its ordinary closed CDF.  At an atom it is
the average of the strict and closed lower half-line probabilities.
-/
noncomputable def midpointCDF (μ : Measure ℝ) (x : ℝ) : ℝ :=
  (μ.real (Iio x) + μ.real (Iic x)) / 2

theorem midpointCDF_eq_cdf_sub_half_atom
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    midpointCDF μ x = cdf μ x - μ.real {x} / 2 := by
  rw [midpointCDF, probability_le_eq_probability_lt_add_atom,
    cdf_eq_probability_lt_add_atom]
  ring

theorem midpointCDF_eq_cdf_of_atomless
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ] (x : ℝ) :
    midpointCDF μ x = cdf μ x := by
  rw [midpointCDF_eq_cdf_sub_half_atom]
  have hx : μ.real {x} = 0 := by
    simp [measureReal_def, measure_singleton]
  rw [hx]
  ring

/--
The real symmetric principal-value kernel for CDF inversion.

For a displacement `a = y - x`, this is exactly
`-(1/π) ∫₀ᵀ sin(t a)/t dt`.
-/
noncomputable def dirichletCDFKernel (T a : ℝ) : ℝ :=
  -(1 / Real.pi) *
    ∫ t in (0 : ℝ)..T, Real.sin (a * t) / t

private theorem integral_sin_mul_div_eq
    (A v δ : ℝ) (hA : 0 < A) :
    ∫ u in v..δ, Real.sin (A * u) / u =
      ∫ z in (A * v)..(A * δ), Real.sin z / z := by
  have hfun : (fun u : ℝ => Real.sin (A * u) / u) =
      fun u : ℝ => A •
        ((fun z : ℝ => Real.sin z / z) (A * u)) := by
    funext u
    rcases eq_or_ne u 0 with rfl | hu
    · simp
    · rw [smul_eq_mul]
      field_simp
  rw [hfun, intervalIntegral.integral_smul]
  have hcomp := intervalIntegral.integral_comp_mul_left
    (a := v) (b := δ) (c := A)
    (fun z => Real.sin z / z) hA.ne'
  rw [hcomp, smul_smul, mul_inv_cancel₀ hA.ne', one_smul]

private theorem tendsto_sin_mul_div_of_pos {a : ℝ} (ha : 0 < a) :
    Tendsto
      (fun T : ℝ => ∫ t in (0 : ℝ)..T,
        Real.sin (a * t) / t)
      atTop (𝓝 (Real.pi / 2)) := by
  have heq :
      (fun T : ℝ => ∫ t in (0 : ℝ)..T,
        Real.sin (a * t) / t) =
      fun T : ℝ => ∫ z in (0 : ℝ)..(a * T),
        Real.sin z / z := by
    funext T
    simpa using integral_sin_mul_div_eq a 0 T ha
  rw [heq]
  exact tendsto_dirichletIntegral_atTop.comp
    (Tendsto.const_mul_atTop ha tendsto_id)

private theorem tendsto_sin_mul_div_of_neg {a : ℝ} (ha : a < 0) :
    Tendsto
      (fun T : ℝ => ∫ t in (0 : ℝ)..T,
        Real.sin (a * t) / t)
      atTop (𝓝 (-(Real.pi / 2))) := by
  have hpos : 0 < -a := neg_pos.mpr ha
  have hbase := (tendsto_sin_mul_div_of_pos hpos).neg
  refine hbase.congr fun T => ?_
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [neg_mul, Real.sin_neg]
  ring

/-- Pointwise limit of the symmetric CDF inversion kernel. -/
theorem tendsto_dirichletCDFKernel_atTop (a : ℝ) :
    Tendsto (fun T : ℝ => dirichletCDFKernel T a) atTop
      (𝓝 (if a < 0 then (1 / 2 : ℝ)
        else if 0 < a then -(1 / 2 : ℝ) else 0)) := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rw [if_pos ha]
    have h := (tendsto_sin_mul_div_of_neg ha).const_mul
      (-(1 / Real.pi))
    convert h using 1
    · ext T
      rfl
    · have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
  · simp [dirichletCDFKernel]
  · rw [if_neg (not_lt.mpr ha.le), if_pos ha]
    have h := (tendsto_sin_mul_div_of_pos ha).const_mul
      (-(1 / Real.pi))
    convert h using 1
    · ext T
      rfl
    · have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp

/-- The inversion kernel is uniformly bounded, independently of its
displacement and of every nonnegative truncation radius. -/
theorem exists_uniform_bound_dirichletCDFKernel :
    ∃ C : ℝ, 0 < C ∧ ∀ T a : ℝ, 0 ≤ T →
      |dirichletCDFKernel T a| ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_bound_dirichletIntegral
  refine ⟨C / Real.pi, div_pos hC Real.pi_pos, fun T a hT => ?_⟩
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · have hpos : 0 < -a := neg_pos.mpr ha
    have hscaled := integral_sin_mul_div_eq (-a) 0 T hpos
    simp only [mul_zero] at hscaled
    have heq : (∫ t in (0 : ℝ)..T,
        Real.sin (a * t) / t) =
        -(∫ z in (0 : ℝ)..((-a) * T),
          Real.sin z / z) := by
      calc
        (∫ t in (0 : ℝ)..T, Real.sin (a * t) / t) =
            -(∫ t in (0 : ℝ)..T,
              Real.sin ((-a) * t) / t) := by
          rw [← intervalIntegral.integral_neg]
          refine intervalIntegral.integral_congr fun t _ => ?_
          rw [neg_mul, Real.sin_neg]
          ring
        _ = -(∫ z in (0 : ℝ)..((-a) * T),
              Real.sin z / z) := congrArg Neg.neg hscaled
    have hinv : |1 / Real.pi| = 1 / Real.pi :=
      abs_of_pos (one_div_pos.mpr Real.pi_pos)
    rw [dirichletCDFKernel, heq, abs_mul, abs_neg, hinv]
    simp only [abs_neg]
    have hb := hbound ((-a) * T) (mul_nonneg hpos.le hT)
    calc
      (1 / Real.pi) *
          |∫ z in (0 : ℝ)..-a * T, Real.sin z / z| ≤
          (1 / Real.pi) * C :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = C / Real.pi := by ring
  · simp only [dirichletCDFKernel, zero_mul, Real.sin_zero,
      zero_div, intervalIntegral.integral_zero, mul_zero, abs_zero]
    exact div_nonneg hC.le Real.pi_pos.le
  · have heq := integral_sin_mul_div_eq a 0 T ha
    simp only [mul_zero] at heq
    have hinv : |1 / Real.pi| = 1 / Real.pi :=
      abs_of_pos (one_div_pos.mpr Real.pi_pos)
    rw [dirichletCDFKernel, heq, abs_mul, abs_neg, hinv]
    have hb := hbound (a * T) (mul_nonneg ha.le hT)
    calc
      (1 / Real.pi) *
          |∫ z in (0 : ℝ)..a * T, Real.sin z / z| ≤
          (1 / Real.pi) * C :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = C / Real.pi := by ring

theorem stronglyMeasurable_dirichletCDFKernel (T : ℝ) :
    StronglyMeasurable (dirichletCDFKernel T) := by
  have hjoint : StronglyMeasurable
      (fun p : ℝ × ℝ => Real.sin (p.1 * p.2) / p.2) := by
    exact ((Real.measurable_sin.comp
      (measurable_fst.mul measurable_snd)).div
      measurable_snd).stronglyMeasurable
  have hforward := hjoint.integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) T))
  have hbackward := hjoint.integral_prod_right'
    (ν := volume.restrict (Ioc T (0 : ℝ)))
  unfold dirichletCDFKernel intervalIntegral
  exact (hforward.sub hbackward).const_mul _

/-- The three-valued pointwise limit of the symmetric inversion kernel:
`1/2` below `x`, `0` at `x`, and `-1/2` above `x`. -/
noncomputable def cdfJumpKernel (x y : ℝ) : ℝ :=
  if y < x then 1 / 2 else if x < y then -(1 / 2) else 0

theorem tendsto_dirichletCDFKernel_sub_atTop (x y : ℝ) :
    Tendsto (fun T : ℝ => dirichletCDFKernel T (y - x))
      atTop (𝓝 (cdfJumpKernel x y)) := by
  simpa only [cdfJumpKernel, sub_lt_zero, sub_pos] using
    tendsto_dirichletCDFKernel_atTop (y - x)

theorem stronglyMeasurable_cdfJumpKernel (x : ℝ) :
    StronglyMeasurable (cdfJumpKernel x) := by
  unfold cdfJumpKernel
  exact Measurable.stronglyMeasurable <|
    Measurable.ite
      (measurableSet_lt measurable_id measurable_const)
      measurable_const <|
    Measurable.ite
      (measurableSet_lt measurable_const measurable_id)
      measurable_const measurable_const

theorem integral_cdfJumpKernel
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    ∫ y, cdfJumpKernel x y ∂μ = midpointCDF μ x - 1 / 2 := by
  have hfun : cdfJumpKernel x =
      fun y =>
        (Iio x).indicator (fun _ : ℝ => (1 / 2 : ℝ)) y +
        (Ioi x).indicator (fun _ : ℝ => -(1 / 2 : ℝ)) y := by
    funext y
    rcases lt_trichotomy y x with hy | rfl | hy
    · simp [cdfJumpKernel, hy, not_lt.mpr hy.le]
    · simp [cdfJumpKernel]
    · simp [cdfJumpKernel, hy, not_lt.mpr hy.le]
  rw [hfun, MeasureTheory.integral_add]
  · rw [integral_indicator_const _ measurableSet_Iio,
      integral_indicator_const _ measurableSet_Ioi,
      smul_eq_mul, smul_eq_mul, midpointCDF,
      ← one_sub_cdf_eq_probability_gt,
      ← cdf_eq_probability_le]
    ring
  · exact (integrable_const (1 / 2 : ℝ)).indicator measurableSet_Iio
  · exact (integrable_const (-(1 / 2 : ℝ))).indicator measurableSet_Ioi

/-- The measure-side symmetric Dirichlet approximation to a CDF. -/
noncomputable def dirichletCDFApproximation
    (μ : Measure ℝ) (x T : ℝ) : ℝ :=
  ∫ y, dirichletCDFKernel T (y - x) ∂μ

/--
Symmetric Fourier inversion in its measure-side form.

At an atom this converges to the midpoint CDF, not the closed CDF.
-/
theorem tendsto_dirichletCDFApproximation_atTop
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    Tendsto (fun T : ℝ => dirichletCDFApproximation μ x T)
      atTop (𝓝 (midpointCDF μ x - 1 / 2)) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_bound_dirichletCDFKernel
  have hlimit : Tendsto
      (fun T : ℝ => ∫ y, dirichletCDFKernel T (y - x) ∂μ)
      atTop (𝓝 (∫ y, cdfJumpKernel x y ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ : ℝ => C) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun T =>
        ((stronglyMeasurable_dirichletCDFKernel T).comp_measurable
          (measurable_id.sub measurable_const)).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop 0] with T hT
      exact ae_of_all μ fun y => by
        rw [Real.norm_eq_abs]
        exact hbound T (y - x) hT
    · exact integrable_const C
    · exact ae_of_all μ fun y =>
        tendsto_dirichletCDFKernel_sub_atTop x y
  rw [integral_cdfJumpKernel] at hlimit
  exact hlimit

/--
Closed-`Iic` version of measure-side Fourier inversion.  The correction
`μ({x})/2` is explicit and therefore cannot be lost when composing the
result with downstream probability bounds.
-/
theorem tendsto_dirichletCDFApproximation_closed_atTop
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    Tendsto
      (fun T : ℝ =>
        1 / 2 + dirichletCDFApproximation μ x T +
          μ.real {x} / 2)
      atTop (𝓝 (cdf μ x)) := by
  have h := (tendsto_dirichletCDFApproximation_atTop μ x).const_add
    (1 / 2 : ℝ)
  have h' := h.add_const (μ.real {x} / 2)
  have hlimit :
      1 / 2 + (midpointCDF μ x - 1 / 2) +
        μ.real {x} / 2 = cdf μ x := by
    rw [midpointCDF_eq_cdf_sub_half_atom]
    ring
  rw [← hlimit]
  exact h'

/-! ## Identification with the regularized characteristic-function transform -/

/--
The principal Fourier CDF kernel `I/(2πt)`, totalized to zero at `t=0`.
-/
noncomputable def principalCDFKernel (t : ℝ) : ℂ :=
  Complex.I / (((2 * Real.pi * t : ℝ) : ℂ))

/--
The point-mass integrand after subtracting its frequency-zero value.
The subtraction removes the principal-value singularity.
-/
noncomputable def regularizedPointCDFIntegrand (a t : ℝ) : ℂ :=
  principalCDFKernel t *
    (Complex.exp (((t * a : ℝ) : ℂ) * Complex.I) - 1)

theorem measurable_principalCDFKernel :
    Measurable principalCDFKernel := by
  unfold principalCDFKernel
  fun_prop

theorem measurable_regularizedPointCDFIntegrand :
    Measurable (Function.uncurry regularizedPointCDFIntegrand) := by
  unfold regularizedPointCDFIntegrand
  exact (measurable_principalCDFKernel.comp measurable_snd).mul
    (((((Complex.measurable_ofReal.comp
      (measurable_snd.mul measurable_fst)).mul
      measurable_const).cexp).sub measurable_const))

theorem regularizedPointCDFIntegrand_zero (a : ℝ) :
    regularizedPointCDFIntegrand a 0 = 0 := by
  simp [regularizedPointCDFIntegrand, principalCDFKernel]

private theorem regularizedPointCDFIntegrand_add_neg
    (a t : ℝ) :
    regularizedPointCDFIntegrand a t +
      regularizedPointCDFIntegrand a (-t) =
        ((-Real.sin (a * t) / (Real.pi * t) : ℝ) : ℂ) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [regularizedPointCDFIntegrand_zero]
  · unfold regularizedPointCDFIntegrand principalCDFKernel
    have hden : (((2 * Real.pi * t : ℝ) : ℂ)) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) ht)
    have hdenNeg : (((2 * Real.pi * -t : ℝ) : ℂ)) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
          (neg_ne_zero.mpr ht))
    rw [show ((t * a : ℝ) : ℂ) * Complex.I =
        (((a * t : ℝ) : ℂ) * Complex.I) by
      push_cast
      ring]
    rw [show ((-t * a : ℝ) : ℂ) * Complex.I =
        (-(((a * t : ℝ) : ℂ))) * Complex.I by
      push_cast
      ring]
    rw [Complex.exp_mul_I, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg]
    push_cast
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
    field_simp [htC]
    have htrig :
        Complex.cos ((t : ℂ) * (a : ℂ)) +
            Complex.I * Complex.sin ((t : ℂ) * (a : ℂ)) - 1 +
            -(Complex.cos ((t : ℂ) * (a : ℂ)) +
              -(Complex.I * Complex.sin ((t : ℂ) * (a : ℂ))) - 1) =
          2 * (Complex.I *
            Complex.sin ((t : ℂ) * (a : ℂ))) := by
      ring
    rw [htrig]
    calc
      Complex.I * (2 * (Complex.I *
          Complex.sin ((t : ℂ) * (a : ℂ)))) =
          2 * ((Complex.I * Complex.I) *
            Complex.sin ((t : ℂ) * (a : ℂ))) := by ring
      _ = -(2 * Complex.sin ((t : ℂ) * (a : ℂ))) := by
        rw [Complex.I_mul_I]
        ring

theorem norm_regularizedPointCDFIntegrand_le (a t : ℝ) :
    ‖regularizedPointCDFIntegrand a t‖ ≤
      |a| / (2 * Real.pi) := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [regularizedPointCDFIntegrand_zero, norm_zero]
    exact div_nonneg (abs_nonneg _) (by positivity)
  · unfold regularizedPointCDFIntegrand principalCDFKernel
    rw [norm_mul, norm_div, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos Real.pi_pos]
    norm_num
    have hexp :
        ‖Complex.exp ((t : ℂ) * (a : ℂ) * Complex.I) - 1‖ =
          ‖(2 * Real.sin (t * a / 2) : ℝ)‖ := by
      rw [show ((t : ℂ) * (a : ℂ) * Complex.I) =
          Complex.I * ((t * a : ℝ) : ℂ) by
        push_cast
        ring]
      exact Complex.norm_exp_I_mul_ofReal_sub_one (t * a)
    rw [hexp, Real.norm_eq_abs]
    have hsin :
        |2 * Real.sin (t * a / 2)| ≤ |t * a| := by
      calc
        |2 * Real.sin (t * a / 2)| =
            2 * |Real.sin (t * a / 2)| := by
          rw [abs_mul]
          norm_num
        _ ≤ 2 * |t * a / 2| :=
          mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
        _ = |t * a| := by
          rw [abs_div]
          norm_num
          ring
    have htAbs : 0 < |t| := abs_pos.mpr ht
    have hpi : 0 < 2 * Real.pi := by positivity
    have hcoeff :
        |t|⁻¹ * (Real.pi⁻¹ * (1 / 2 : ℝ)) =
          1 / (2 * Real.pi * |t|) := by
      field_simp [htAbs.ne', Real.pi_ne_zero]
    rw [hcoeff]
    calc
      1 / (2 * Real.pi * |t|) *
          |2 * Real.sin (t * a / 2)| ≤
          1 / (2 * Real.pi * |t|) * |t * a| :=
        mul_le_mul_of_nonneg_left hsin (by positivity)
      _ = |a| / (2 * Real.pi) := by
        rw [abs_mul]
        field_simp

theorem intervalIntegrable_regularizedPointCDFIntegrand
    (a A B : ℝ) :
    IntervalIntegrable (regularizedPointCDFIntegrand a)
      volume A B := by
  refine intervalIntegrable_iff.mpr ?_
  refine Integrable.mono'
    (g := fun _ => |a| / (2 * Real.pi))
    (integrableOn_const (C := |a| / (2 * Real.pi)) (by
      rw [Real.volume_uIoc]
      exact ENNReal.ofReal_ne_top))
    ((measurable_regularizedPointCDFIntegrand.comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable) ?_
  exact Eventually.of_forall fun t =>
    norm_regularizedPointCDFIntegrand_le a t

theorem integral_regularizedPointCDFIntegrand_symmetric
    (a T : ℝ) :
    (∫ t in (-T)..T, regularizedPointCDFIntegrand a t) =
      (dirichletCDFKernel T a : ℂ) := by
  let f : ℝ → ℂ := regularizedPointCDFIntegrand a
  have hneg : IntervalIntegrable f volume (-T) 0 :=
    intervalIntegrable_regularizedPointCDFIntegrand a (-T) 0
  have hpos : IntervalIntegrable f volume 0 T :=
    intervalIntegrable_regularizedPointCDFIntegrand a 0 T
  have hreflect :
      (∫ t in (-T)..0, f t) = ∫ t in (0 : ℝ)..T, f (-t) := by
    rw [intervalIntegral.integral_comp_neg]
    simp
  have hreflectInt :
      IntervalIntegrable (fun t : ℝ => f (-t)) volume 0 T := by
    refine intervalIntegrable_iff.mpr ?_
    refine Integrable.mono'
      (g := fun _ => |a| / (2 * Real.pi))
      (integrableOn_const (C := |a| / (2 * Real.pi)) (by
        rw [Real.volume_uIoc]
        exact ENNReal.ofReal_ne_top))
      (((measurable_regularizedPointCDFIntegrand.comp
        (measurable_const.prodMk measurable_id)).comp
        measurable_neg).aestronglyMeasurable) ?_
    exact Eventually.of_forall fun t =>
      norm_regularizedPointCDFIntegrand_le a (-t)
  calc
    (∫ t in (-T)..T, f t) =
        (∫ t in (-T)..0, f t) + ∫ t in (0 : ℝ)..T, f t := by
      symm
      exact intervalIntegral.integral_add_adjacent_intervals hneg hpos
    _ = (∫ t in (0 : ℝ)..T, f (-t)) +
        ∫ t in (0 : ℝ)..T, f t := by rw [hreflect]
    _ = ∫ t in (0 : ℝ)..T, (f (-t) + f t) := by
      rw [intervalIntegral.integral_add hreflectInt hpos]
    _ = ∫ t in (0 : ℝ)..T,
        ((-Real.sin (a * t) / (Real.pi * t) : ℝ) : ℂ) := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [add_comm]
      exact regularizedPointCDFIntegrand_add_neg a t
    _ = Complex.ofReal (∫ t in (0 : ℝ)..T,
        -Real.sin (a * t) / (Real.pi * t)) := by
      exact intervalIntegral.integral_ofReal
    _ = (dirichletCDFKernel T a : ℂ) := by
      apply congrArg Complex.ofReal
      unfold dirichletCDFKernel
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      ring

private theorem integrable_phase
    (μ : Measure ℝ) [IsFiniteMeasure μ] (t x : ℝ) :
    Integrable
      (fun y : ℝ =>
        Complex.exp ((((t * (y - x) : ℝ) : ℂ) * Complex.I)))
      μ := by
  have hmeas : AEStronglyMeasurable
      (fun y : ℝ =>
        Complex.exp ((((t * (y - x) : ℝ) : ℂ) * Complex.I))) μ := by
    refine Continuous.aestronglyMeasurable ?_
    fun_prop
  have h := (integrable_const (1 : ℂ)).bdd_mul
    (c := 1) hmeas (ae_of_all μ fun y => by
      rw [Complex.norm_exp]
      simp)
  simpa using h

theorem integral_regularizedPointCDFIntegrand
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x t : ℝ) :
    ∫ y, regularizedPointCDFIntegrand (y - x) t ∂μ =
      principalCDFKernel t *
        (Complex.exp (((-(t * x) : ℝ) : ℂ) * Complex.I) *
          charFun μ t - 1) := by
  unfold regularizedPointCDFIntegrand
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_sub
    (integrable_phase μ t x) (integrable_const (1 : ℂ))]
  rw [MeasureTheory.integral_const, probReal_univ, one_smul]
  congr 2
  rw [charFun_apply_real, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (ae_of_all μ fun y => ?_)
  dsimp only
  rw [show (t : ℂ) * (y : ℂ) = ((t * y : ℝ) : ℂ) by
    push_cast
    rfl]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/--
The ordinary (not merely formal principal-value) characteristic-function
transform obtained by subtracting the frequency-zero value.
-/
noncomputable def regularizedCDFTransform
    (μ : Measure ℝ) (x T : ℝ) : ℂ :=
  ∫ t in (-T)..T,
    principalCDFKernel t *
      (Complex.exp (((-(t * x) : ℝ) : ℂ) * Complex.I) *
        charFun μ t - 1)

/--
Fubini identification of the regularized characteristic-function transform
with the measure-side Dirichlet approximation.

The finite first moment is used only here, to dominate the regularized joint
integrand by `|y-x|/(2π)`.  The inversion limit itself does not require a
moment assumption.
-/
theorem regularizedCDFTransform_eq_dirichletCDFApproximation
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : Integrable (fun y : ℝ => y) μ)
    (x : ℝ) {T : ℝ} (hT : 0 < T) :
    regularizedCDFTransform μ x T =
      Complex.ofReal (dirichletCDFApproximation μ x T) := by
  let joint : ℝ × ℝ → ℂ := fun p =>
    regularizedPointCDFIntegrand (p.2 - x) p.1
  have hjointMeas : AEStronglyMeasurable joint
      ((volume.restrict (Ioc (-T) T)).prod μ) := by
    change AEStronglyMeasurable
      (fun p : ℝ × ℝ =>
        regularizedPointCDFIntegrand (p.2 - x) p.1)
      ((volume.restrict (Ioc (-T) T)).prod μ)
    exact (measurable_regularizedPointCDFIntegrand.comp
      ((measurable_snd.sub measurable_const).prodMk
        measurable_fst)).aestronglyMeasurable
  have hy : Integrable (fun y : ℝ => y - x) μ :=
    hmoment.sub (integrable_const x)
  have ht : Integrable (fun _ : ℝ => (1 : ℝ))
      (volume.restrict (Ioc (-T) T)) :=
    integrableOn_const (C := (1 : ℝ)) (by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top)
  have hdom : Integrable
      (fun p : ℝ × ℝ => |p.2 - x| / (2 * Real.pi))
      ((volume.restrict (Ioc (-T) T)).prod μ) := by
    have hprod := ht.mul_prod hy.norm
    have hscale := hprod.const_mul (1 / (2 * Real.pi))
    refine hscale.congr (Eventually.of_forall fun p => ?_)
    simp only [one_mul, Real.norm_eq_abs]
    ring
  have hprod : Integrable joint
      ((volume.restrict (Ioc (-T) T)).prod μ) := by
    refine Integrable.mono' hdom hjointMeas ?_
    exact Eventually.of_forall fun p =>
      norm_regularizedPointCDFIntegrand_le (p.2 - x) p.1
  have hprod' : Integrable
      (Function.uncurry fun t y =>
        regularizedPointCDFIntegrand (y - x) t)
      ((volume.restrict (Ioc (-T) T)).prod μ) := by
    change Integrable
      (fun p : ℝ × ℝ =>
        regularizedPointCDFIntegrand (p.2 - x) p.1)
      ((volume.restrict (Ioc (-T) T)).prod μ)
    exact hprod
  have hswap := integral_integral_swap hprod'
  have hwindow : -T ≤ T := by linarith
  unfold regularizedCDFTransform dirichletCDFApproximation
  rw [intervalIntegral.integral_of_le hwindow]
  calc
    (∫ t in Ioc (-T) T,
        principalCDFKernel t *
          (Complex.exp (((-(t * x) : ℝ) : ℂ) * Complex.I) *
            charFun μ t - 1)) =
        ∫ t in Ioc (-T) T,
          (∫ y, joint (t, y) ∂μ) := by
      refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
      exact (integral_regularizedPointCDFIntegrand μ x t).symm
    _ = ∫ y, (∫ t in Ioc (-T) T, joint (t, y)) ∂μ := hswap
    _ = ∫ y, Complex.ofReal
        (dirichletCDFKernel T (y - x)) ∂μ := by
      refine integral_congr_ae (ae_of_all μ fun y => ?_)
      dsimp only
      rw [← intervalIntegral.integral_of_le hwindow]
      exact integral_regularizedPointCDFIntegrand_symmetric (y - x) T
    _ = Complex.ofReal
        (∫ y, dirichletCDFKernel T (y - x) ∂μ) := by
      exact integral_complex_ofReal

/--
Principal-value characteristic-function inversion at a possible atom.

The transform is regularized at frequency zero, hence every term is an
ordinary Bochner integral.  The limit is the midpoint CDF minus `1/2`.
-/
theorem tendsto_regularizedCDFTransform_atTop
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : Integrable (fun y : ℝ => y) μ) (x : ℝ) :
    Tendsto (fun T : ℝ => regularizedCDFTransform μ x T)
      atTop
      (𝓝 (Complex.ofReal (midpointCDF μ x - 1 / 2))) := by
  have hmeasure :=
    (tendsto_dirichletCDFApproximation_atTop μ x).ofReal
  refine hmeasure.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  exact (regularizedCDFTransform_eq_dirichletCDFApproximation
    μ hmoment x hT).symm

/-- Closed-`Iic` characteristic-function inversion with explicit atom
correction. -/
theorem tendsto_regularizedCDFTransform_closed_atTop
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : Integrable (fun y : ℝ => y) μ) (x : ℝ) :
    Tendsto
      (fun T : ℝ =>
        (1 / 2 : ℂ) + regularizedCDFTransform μ x T +
          (μ.real {x} / 2 : ℝ))
      atTop (𝓝 (cdf μ x : ℂ)) := by
  have h := (tendsto_regularizedCDFTransform_atTop
    μ hmoment x).const_add (1 / 2 : ℂ)
  have h' := h.add_const ((μ.real {x} / 2 : ℝ) : ℂ)
  have hlimit :
      (1 / 2 : ℂ) +
          Complex.ofReal (midpointCDF μ x - 1 / 2) +
          (μ.real {x} / 2 : ℝ) =
        (cdf μ x : ℂ) := by
    rw [midpointCDF_eq_cdf_sub_half_atom]
    push_cast
    ring
  rw [← hlimit]
  exact h'

end Probability
end CertifiedJL
