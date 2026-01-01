/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib.Probability.CDF
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.MeasureTheory.Integral.Prod
import CertifiedJL.Probability.Distributions.Gaussian.StandardGaussian

/-!
# Shifted-Gaussian upper-tail inversion boundary

This file proves the U10 strict smoothing step and the real-axis modulus
producer independently of the fourth-order sparse comparison.  The Fourier
inversion and expectation interchange remain separate downstream obligations.
-/

open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate

namespace CertifiedJL

/-- The positive-real vertical line used by the U10 contour integral. -/
noncomputable def verticalLine (lambda u : ℝ) : ℂ :=
  (lambda : ℂ) + (u : ℂ) * Complex.I

/-- The absolutely convergent shifted-Gaussian contour kernel from U10a. -/
noncomputable def shiftedGaussianContourKernel
    (lambda sigma y u : ℝ) : ℂ :=
  Complex.exp
      (verticalLine lambda u * y +
        (sigma : ℂ) ^ 2 * verticalLine lambda u ^ 2 / 2) /
    verticalLine lambda u

/-- Exact absolute-value envelope for the U10 contour kernel. -/
theorem norm_shiftedGaussianContourKernel
    (lambda sigma y u : ℝ) :
    ‖shiftedGaussianContourKernel lambda sigma y u‖ =
      Real.exp
          (lambda * y + sigma ^ 2 * (lambda ^ 2 - u ^ 2) / 2) /
        Real.sqrt (lambda ^ 2 + u ^ 2) := by
  rw [shiftedGaussianContourKernel, norm_div, Complex.norm_exp,
    Complex.norm_def, Complex.normSq_apply]
  congr 1
  · norm_num [verticalLine, pow_two, Complex.div_re, Complex.normSq_apply]
  · norm_num [verticalLine, pow_two]

/-- The positive-real U10 contour kernel is absolutely integrable. -/
theorem integrable_shiftedGaussianContourKernel
    {lambda sigma y : ℝ}
    (hlambda : 0 < lambda) (hsigma : 0 < sigma) :
    Integrable (shiftedGaussianContourKernel lambda sigma y) := by
  let C : ℝ := Real.exp
    (lambda * y + sigma ^ 2 * lambda ^ 2 / 2) / lambda
  have hC : 0 ≤ C := div_nonneg (Real.exp_pos _).le hlambda.le
  have hgaussian : Integrable
      (fun u : ℝ => Real.exp (-(sigma ^ 2 / 2) * u ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  refine Integrable.mono' (hgaussian.const_mul C) ?_ ?_
  · apply Measurable.aestronglyMeasurable
    unfold shiftedGaussianContourKernel verticalLine
    fun_prop
  exact Filter.Eventually.of_forall fun u => by
    rw [norm_shiftedGaussianContourKernel]
    have hsqrt : 0 < Real.sqrt (lambda ^ 2 + u ^ 2) := by
      exact Real.sqrt_pos.2 (by nlinarith [sq_pos_of_pos hlambda, sq_nonneg u])
    have hlambda_sqrt : lambda ≤ Real.sqrt (lambda ^ 2 + u ^ 2) := by
      nlinarith [Real.sq_sqrt (by positivity : 0 ≤ lambda ^ 2 + u ^ 2),
        Real.sqrt_nonneg (lambda ^ 2 + u ^ 2)]
    rw [show lambda * y + sigma ^ 2 * (lambda ^ 2 - u ^ 2) / 2 =
        (lambda * y + sigma ^ 2 * lambda ^ 2 / 2) +
          (-(sigma ^ 2 / 2) * u ^ 2) by ring,
      Real.exp_add]
    dsimp only [C]
    rw [div_mul_eq_mul_div]
    calc
      Real.exp (lambda * y + sigma ^ 2 * lambda ^ 2 / 2) *
            Real.exp (-(sigma ^ 2 / 2) * u ^ 2) /
          Real.sqrt (lambda ^ 2 + u ^ 2) =
          (Real.exp (lambda * y + sigma ^ 2 * lambda ^ 2 / 2) /
            Real.sqrt (lambda ^ 2 + u ^ 2)) *
              Real.exp (-(sigma ^ 2 / 2) * u ^ 2) := by ring
      _ ≤ (Real.exp (lambda * y + sigma ^ 2 * lambda ^ 2 / 2) / lambda) *
            Real.exp (-(sigma ^ 2 / 2) * u ^ 2) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left (Real.exp_pos _).le hlambda
            hlambda_sqrt)
          (Real.exp_pos _).le
      _ = Real.exp (lambda * y + sigma ^ 2 * lambda ^ 2 / 2) *
            Real.exp (-(sigma ^ 2 / 2) * u ^ 2) / lambda := by ring

/-- The absolute contour kernel decays to zero on the positive end of the
vertical line. -/
theorem tendsto_norm_shiftedGaussianContourKernel_atTop
    {lambda sigma y : ℝ}
    (hlambda : 0 < lambda) (hsigma : 0 < sigma) :
    Filter.Tendsto
      (fun u : ℝ => ‖shiftedGaussianContourKernel lambda sigma y u‖)
      Filter.atTop (nhds 0) := by
  let C : ℝ := Real.exp
    (lambda * y + sigma ^ 2 * lambda ^ 2 / 2) / lambda
  have hsq : Filter.Tendsto (fun u : ℝ => u * u)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_atTop₀ Filter.tendsto_id Filter.tendsto_id
  have hquadratic : Filter.Tendsto
      (fun u : ℝ => -(sigma ^ 2 / 2) * (u * u))
      Filter.atTop Filter.atBot := by
    have hcoef : -(sigma ^ 2 / 2) < 0 := by
      exact neg_lt_zero.mpr (div_pos (sq_pos_of_pos hsigma) (by norm_num))
    exact hsq.const_mul_atTop_of_neg hcoef
  have hmajorant : Filter.Tendsto
      (fun u : ℝ => C * Real.exp (-(sigma ^ 2 / 2) * u ^ 2))
      Filter.atTop (nhds 0) := by
    convert (Real.tendsto_exp_atBot.comp hquadratic).const_mul C using 1
    all_goals simp only [Function.comp_apply, mul_zero]
    all_goals ring_nf
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hmajorant
    (Filter.Eventually.of_forall fun u => norm_nonneg _)
    (Filter.Eventually.of_forall fun u => ?_)
  rw [norm_shiftedGaussianContourKernel]
  have hsqrt : 0 < Real.sqrt (lambda ^ 2 + u ^ 2) := by
    exact Real.sqrt_pos.2 (by nlinarith [sq_pos_of_pos hlambda, sq_nonneg u])
  have hlambda_sqrt : lambda ≤ Real.sqrt (lambda ^ 2 + u ^ 2) := by
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ lambda ^ 2 + u ^ 2),
      Real.sqrt_nonneg (lambda ^ 2 + u ^ 2)]
  rw [show lambda * y + sigma ^ 2 * (lambda ^ 2 - u ^ 2) / 2 =
      (lambda * y + sigma ^ 2 * lambda ^ 2 / 2) +
        (-(sigma ^ 2 / 2) * u ^ 2) by ring,
    Real.exp_add]
  dsimp only [C]
  calc
    Real.exp (lambda * y + sigma ^ 2 * lambda ^ 2 / 2) *
          Real.exp (-(sigma ^ 2 / 2) * u ^ 2) /
        Real.sqrt (lambda ^ 2 + u ^ 2) =
        (Real.exp (lambda * y + sigma ^ 2 * lambda ^ 2 / 2) /
          Real.sqrt (lambda ^ 2 + u ^ 2)) *
            Real.exp (-(sigma ^ 2 / 2) * u ^ 2) := by ring
    _ ≤ (Real.exp (lambda * y + sigma ^ 2 * lambda ^ 2 / 2) / lambda) *
          Real.exp (-(sigma ^ 2 / 2) * u ^ 2) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (Real.exp_pos _).le hlambda hlambda_sqrt)
        (Real.exp_pos _).le

private theorem verticalLine_ne_zero
    {lambda u : ℝ} (hlambda : 0 < lambda) :
    verticalLine lambda u ≠ 0 := by
  apply Complex.ne_zero_of_re_pos
  simpa [verticalLine] using hlambda

private theorem integral_exp_neg_verticalLine_Ioi
    {lambda u : ℝ} (hlambda : 0 < lambda) :
    (∫ v : ℝ in Set.Ioi 0,
        Complex.exp (-verticalLine lambda u * v)) =
      1 / verticalLine lambda u := by
  have hre : (-verticalLine lambda u).re < 0 := by
    simpa [verticalLine] using neg_lt_zero.mpr hlambda
  rw [integral_exp_mul_complex_Ioi hre]
  simp

private noncomputable def shiftedGaussianContourJoint
    (lambda sigma y : ℝ) (p : ℝ × ℝ) : ℂ :=
  Complex.exp
    (verticalLine lambda p.1 * (y - p.2) +
      (sigma : ℂ) ^ 2 * verticalLine lambda p.1 ^ 2 / 2)

private theorem norm_shiftedGaussianContourJoint
    (lambda sigma y u v : ℝ) :
    ‖shiftedGaussianContourJoint lambda sigma y (u, v)‖ =
      Real.exp (lambda * y + sigma ^ 2 * lambda ^ 2 / 2) *
        Real.exp (-(sigma ^ 2 / 2) * u ^ 2) *
          Real.exp (-lambda * v) := by
  rw [shiftedGaussianContourJoint, Complex.norm_exp]
  have hexponent :
      (verticalLine lambda u * ((y : ℂ) - v) +
          (sigma : ℂ) ^ 2 * verticalLine lambda u ^ 2 / 2).re =
        (lambda * y + sigma ^ 2 * lambda ^ 2 / 2) +
          (-(sigma ^ 2 / 2) * u ^ 2) + (-lambda * v) := by
    norm_num [verticalLine, pow_two, Complex.div_re, Complex.normSq_apply]
    ring
  rw [hexponent, Real.exp_add, Real.exp_add]

private theorem shiftedGaussianContourKernel_eq_integral_Ioi
    {lambda sigma y u : ℝ} (hlambda : 0 < lambda) :
    shiftedGaussianContourKernel lambda sigma y u =
      ∫ v : ℝ in Set.Ioi 0,
        shiftedGaussianContourJoint lambda sigma y (u, v) := by
  unfold shiftedGaussianContourKernel shiftedGaussianContourJoint
  rw [div_eq_mul_inv, ← one_div,
    ← integral_exp_neg_verticalLine_Ioi hlambda,
    ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  dsimp only
  rw [← Complex.exp_add]
  congr 1
  ring

private theorem integrable_shiftedGaussianContourJoint
    {lambda sigma y : ℝ}
    (hlambda : 0 < lambda) (hsigma : 0 < sigma) :
    Integrable (shiftedGaussianContourJoint lambda sigma y)
      (volume.prod (volume.restrict (Set.Ioi 0))) := by
  have hu : Integrable
      (fun u : ℝ => Real.exp (-(sigma ^ 2 / 2) * u ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  have hv : Integrable
      (fun v : ℝ => Real.exp (-lambda * v))
      (volume.restrict (Set.Ioi 0)) := by
    change IntegrableOn (fun v : ℝ => Real.exp (-lambda * v)) (Set.Ioi 0)
    simpa only [neg_mul] using
      (integrableOn_exp_mul_Ioi (a := -lambda) (by linarith) 0)
  have hmajorant := (hu.mul_prod hv).const_mul
    (Real.exp (lambda * y + sigma ^ 2 * lambda ^ 2 / 2))
  refine Integrable.mono' hmajorant (by
    apply Measurable.aestronglyMeasurable
    unfold shiftedGaussianContourJoint verticalLine
    fun_prop) ?_
  exact Filter.Eventually.of_forall fun p => by
    rw [norm_shiftedGaussianContourJoint]
    norm_num [Real.norm_eq_abs, abs_mul, Real.abs_exp]
    rw [mul_assoc]

private theorem integral_shiftedGaussianContourJoint_left
    {sigma : ℝ} (hsigma : 0 < sigma) (lambda y v : ℝ) :
    (∫ u : ℝ, shiftedGaussianContourJoint lambda sigma y (u, v)) =
      (Real.sqrt (2 * Real.pi) / sigma : ℂ) *
        Complex.exp (-(y - v) ^ 2 / (2 * sigma ^ 2)) := by
  let b : ℂ := -(sigma : ℂ) ^ 2 / 2
  let c : ℂ := Complex.I * (y - v + sigma ^ 2 * lambda)
  let d : ℂ := lambda * (y - v) + sigma ^ 2 * lambda ^ 2 / 2
  have hb : b.re < 0 := by
    dsimp only [b]
    norm_num [pow_two, Complex.div_re, Complex.normSq_apply]
    nlinarith [sq_pos_of_pos hsigma]
  have hfun :
      (fun u : ℝ => shiftedGaussianContourJoint lambda sigma y (u, v)) =
        fun u : ℝ => Complex.exp (b * u ^ 2 + c * u + d) := by
    funext u
    unfold shiftedGaussianContourJoint verticalLine
    congr 1
    dsimp only [b, c, d]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hfun, integral_cexp_quadratic hb]
  have hroot :
      (Real.pi / -b) ^ (1 / 2 : ℂ) =
        (Real.sqrt (2 * Real.pi) / sigma : ℂ) := by
    rw [show Real.pi / -b =
        ((2 * Real.pi / sigma ^ 2 : ℝ) : ℂ) by
      dsimp only [b]
      push_cast
      field_simp]
    have hexponent : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    rw [hexponent, ← Complex.ofReal_cpow (by positivity) (1 / 2 : ℝ),
      ← Complex.ofReal_div]
    congr 1
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by positivity),
      Real.sqrt_sq_eq_abs, abs_of_pos hsigma]
  rw [hroot]
  congr 1
  dsimp only [b, c, d]
  ring_nf
  rw [Complex.I_sq]
  have hsigmaC : (sigma : ℂ) ≠ 0 := by exact_mod_cast hsigma.ne'
  field_simp [hsigmaC]
  ring_nf

/-- The standard Gaussian distribution function `Phi`. -/
noncomputable def standardGaussianCDF (x : ℝ) : ℝ :=
  cdf (gaussianReal 0 1) x

private theorem standardGaussianCDF_eq_integral_Iic (x : ℝ) :
    standardGaussianCDF x =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        ∫ z : ℝ in Set.Iic x, Real.exp (-z ^ 2 / 2) := by
  rw [standardGaussianCDF, cdf_eq_real, measureReal_def,
    gaussianReal_apply_eq_integral 0 (by norm_num) (Set.Iic x)]
  have hnonneg : 0 ≤ ∫ z : ℝ in Set.Iic x, gaussianPDFReal 0 1 z :=
    integral_nonneg fun _ => gaussianPDFReal_nonneg _ _ _
  rw [ENNReal.toReal_ofReal hnonneg]
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [MeasureTheory.integral_const_mul]

private theorem integral_Ioi_shiftedGaussian_eq_cdf
    {sigma : ℝ} (hsigma : 0 < sigma) (y : ℝ) :
    (∫ v : ℝ in Set.Ioi 0,
        Real.exp (-(y - v) ^ 2 / (2 * sigma ^ 2))) =
      sigma * Real.sqrt (2 * Real.pi) *
        standardGaussianCDF (y / sigma) := by
  have htranslate :
      (∫ v : ℝ in Set.Ioi 0,
          Real.exp (-(y - v) ^ 2 / (2 * sigma ^ 2))) =
        ∫ x : ℝ in Set.Ioi (-y),
          Real.exp (-x ^ 2 / (2 * sigma ^ 2)) := by
    rw [← integral_indicator measurableSet_Ioi,
      ← integral_indicator measurableSet_Ioi,
      ← integral_add_right_eq_self
        (fun v : ℝ => (Set.Ioi 0).indicator
          (fun w => Real.exp (-(y - w) ^ 2 / (2 * sigma ^ 2))) v) y]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ Set.Ioi (-y)
    · have hx' : -y < x := hx
      have hxy : x + y ∈ Set.Ioi (0 : ℝ) := by
        rw [Set.mem_Ioi]
        linarith
      dsimp only
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxy]
      congr 1
      ring
    · have hx' : x ≤ -y := by
        simpa only [Set.mem_Ioi, not_lt] using hx
      have hxy : x + y ∉ Set.Ioi (0 : ℝ) := by
        rw [Set.mem_Ioi, not_lt]
        linarith
      dsimp only
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxy]
  have hscaleRaw := integral_comp_mul_left_Ioi
    (fun x : ℝ => Real.exp (-x ^ 2 / (2 * sigma ^ 2)))
    (-y / sigma) hsigma
  have hscale :
      (∫ x : ℝ in Set.Ioi (-y / sigma),
          Real.exp (-x ^ 2 / 2)) =
        sigma⁻¹ * ∫ x : ℝ in Set.Ioi (-y),
          Real.exp (-x ^ 2 / (2 * sigma ^ 2)) := by
    calc
      (∫ x : ℝ in Set.Ioi (-y / sigma), Real.exp (-x ^ 2 / 2)) =
          ∫ x : ℝ in Set.Ioi (-y / sigma),
            Real.exp (-(sigma * x) ^ 2 / (2 * sigma ^ 2)) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
        congr 1
        field_simp
      _ = sigma⁻¹ • ∫ x : ℝ in Set.Ioi (sigma * (-y / sigma)),
          Real.exp (-x ^ 2 / (2 * sigma ^ 2)) := hscaleRaw
      _ = sigma⁻¹ * ∫ x : ℝ in Set.Ioi (-y),
          Real.exp (-x ^ 2 / (2 * sigma ^ 2)) := by
        rw [show sigma * (-y / sigma) = -y by field_simp]
        rfl
  have hreflect :
      (∫ x : ℝ in Set.Ioi (-y / sigma),
          Real.exp (-x ^ 2 / 2)) =
        ∫ x : ℝ in Set.Iic (y / sigma),
          Real.exp (-x ^ 2 / 2) := by
    convert integral_comp_neg_Ioi (-y / sigma)
      (fun x : ℝ => Real.exp (-x ^ 2 / 2)) using 1 <;> ring_nf
  rw [htranslate]
  have hscaled :
      (∫ x : ℝ in Set.Ioi (-y),
          Real.exp (-x ^ 2 / (2 * sigma ^ 2))) =
        sigma * ∫ x : ℝ in Set.Iic (y / sigma),
          Real.exp (-x ^ 2 / 2) := by
    rw [← hreflect, hscale]
    field_simp
  rw [hscaled, standardGaussianCDF_eq_integral_Iic]
  have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  field_simp

/-- Positive-real shifted-Gaussian contour inversion. Every integral in the
statement and proof is an ordinary absolutely convergent Bochner integral. -/
theorem integral_shiftedGaussianContourKernel_eq_cdf
    {lambda sigma y : ℝ}
    (hlambda : 0 < lambda) (hsigma : 0 < sigma) :
    (1 / (2 * Real.pi) : ℂ) *
        ∫ u : ℝ, shiftedGaussianContourKernel lambda sigma y u =
      (standardGaussianCDF (y / sigma) : ℂ) := by
  have hjoint := integrable_shiftedGaussianContourJoint
    (y := y) hlambda hsigma
  have hjoint' : Integrable
      (Function.uncurry fun u v =>
        shiftedGaussianContourJoint lambda sigma y (u, v))
      (volume.prod (volume.restrict (Set.Ioi 0))) := by
    change Integrable (shiftedGaussianContourJoint lambda sigma y)
      (volume.prod (volume.restrict (Set.Ioi 0)))
    exact hjoint
  have hswap := integral_integral_swap hjoint'
  have hkernel :
      (∫ u : ℝ, shiftedGaussianContourKernel lambda sigma y u) =
        ∫ u : ℝ, ∫ v : ℝ in Set.Ioi 0,
          shiftedGaussianContourJoint lambda sigma y (u, v) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    exact shiftedGaussianContourKernel_eq_integral_Ioi hlambda
  rw [hkernel, hswap]
  have hinner :
      (∫ v : ℝ in Set.Ioi 0,
          ∫ u : ℝ, shiftedGaussianContourJoint lambda sigma y (u, v)) =
        (Real.sqrt (2 * Real.pi) / sigma : ℂ) *
          ∫ v : ℝ in Set.Ioi 0,
            Complex.exp (-(y - v) ^ 2 / (2 * sigma ^ 2)) := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    exact integral_shiftedGaussianContourJoint_left hsigma lambda y v
  rw [hinner]
  have hreal :
      (∫ v : ℝ in Set.Ioi 0,
          Complex.exp (-(y - v) ^ 2 / (2 * sigma ^ 2))) =
        ∫ v : ℝ in Set.Ioi 0,
          (Real.exp (-(y - v) ^ 2 / (2 * sigma ^ 2)) : ℂ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    change Complex.exp (-(↑y - ↑v) ^ 2 / (2 * ↑sigma ^ 2)) =
      (Real.exp (-(y - v) ^ 2 / (2 * sigma ^ 2)) : ℂ)
    have hexponent :
        (-(↑y - ↑v) ^ 2 / (2 * ↑sigma ^ 2) : ℂ) =
          ((-(y - v) ^ 2 / (2 * sigma ^ 2) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hexponent]
    exact (Complex.ofReal_exp _).symm
  have hcdfC :
      (∫ v : ℝ in Set.Ioi 0,
          (Real.exp (-(y - v) ^ 2 / (2 * sigma ^ 2)) : ℂ)) =
        (sigma * Real.sqrt (2 * Real.pi) *
          standardGaussianCDF (y / sigma) : ℂ) := by
    rw [integral_complex_ofReal]
    exact_mod_cast integral_Ioi_shiftedGaussian_eq_cdf hsigma y
  rw [hreal, hcdfC]
  have hsigma0 : sigma ≠ 0 := hsigma.ne'
  have hsigmaC : (sigma : ℂ) ≠ 0 := by exact_mod_cast hsigma0
  have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
  have hsqrt_sq : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrt_sqC :
      (Real.sqrt (2 * Real.pi) : ℂ) ^ 2 = 2 * Real.pi := by
    exact_mod_cast hsqrt_sq
  field_simp [hsigmaC]
  rw [hsqrt_sqC]

/-- The standard Gaussian distribution function is strictly increasing. -/
theorem strictMono_standardGaussianCDF : StrictMono standardGaussianCDF := by
  intro x y hxy
  rw [standardGaussianCDF, standardGaussianCDF, cdf_eq_real, cdf_eq_real,
    ← Set.Iic_union_Ioc_eq_Iic hxy.le,
    measureReal_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc]
  refine lt_add_of_pos_right _ (lt_of_le_of_ne measureReal_nonneg ?_)
  intro hzero
  have hgaussian : gaussianReal 0 1 (Set.Ioc x y) = 0 :=
    (measureReal_eq_zero_iff (by finiteness)).mp hzero.symm
  have hvolume : volume (Set.Ioc x y) = 0 :=
    gaussianReal_absolutelyContinuous' 0 (by norm_num) hgaussian
  rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at hvolume
  exact (not_le.mpr (sub_pos.mpr hxy)) hvolume

/-- The standard Gaussian distribution function is everywhere positive. -/
theorem standardGaussianCDF_pos (x : ℝ) : 0 < standardGaussianCDF x := by
  have hstep : x - 1 < x := by linarith
  exact (cdf_nonneg (gaussianReal 0 1) (x - 1)).trans_lt
    (strictMono_standardGaussianCDF hstep)

/-- The standard Gaussian CDF is one minus its strict upper tail.  This
elementary identity lives beside the inversion primitive so centered
smoothers need not import any normal-approximation machinery. -/
theorem standardGaussianCDF_eq_one_sub_tail (x : ℝ) :
    standardGaussianCDF x = 1 - Probability.standardGaussianTail x := by
  rw [standardGaussianCDF, cdf_eq_real]
  have hIic :
      (gaussianReal 0 1).real (Set.Iic x) =
        ∫ y : ℝ in Set.Iic x, Probability.standardGaussianDensity y := by
    rw [Measure.real, gaussianReal_apply_eq_integral 0 (by norm_num)]
    rw [ENNReal.toReal_ofReal]
    · rw [Probability.standardGaussianDensity_eq_gaussianPDFReal]
    · exact setIntegral_nonneg measurableSet_Iic
        (fun y _ => gaussianPDFReal_nonneg 0 1 y)
  rw [hIic]
  have hsplit :
      (∫ y : ℝ in Set.Iic x, Probability.standardGaussianDensity y) +
          Probability.standardGaussianTail x = 1 := by
    unfold Probability.standardGaussianTail
    rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl)
      measurableSet_Ioi
      Probability.integrable_standardGaussianDensity.integrableOn
      Probability.integrable_standardGaussianDensity.integrableOn]
    rw [Set.Iic_union_Ioi, Measure.restrict_univ]
    rw [Probability.standardGaussianDensity_eq_gaussianPDFReal]
    exact integral_gaussianPDFReal_eq_one 0 (by norm_num)
  linarith

/-- Reflection of the standard Gaussian CDF, proved directly from its even
density rather than through a quantitative normal-approximation module. -/
theorem standardGaussianCDF_neg_eq_one_sub (x : ℝ) :
    standardGaussianCDF (-x) = 1 - standardGaussianCDF x := by
  have hneg :
      standardGaussianCDF (-x) =
        Probability.standardGaussianTail x := by
    rw [standardGaussianCDF, cdf_eq_real]
    have hIic :
        (gaussianReal 0 1).real (Set.Iic (-x)) =
          ∫ y : ℝ in Set.Iic (-x),
            Probability.standardGaussianDensity y := by
      rw [Measure.real, gaussianReal_apply_eq_integral 0 (by norm_num)]
      rw [ENNReal.toReal_ofReal]
      · rw [Probability.standardGaussianDensity_eq_gaussianPDFReal]
      · exact setIntegral_nonneg measurableSet_Iic
          (fun y _ => gaussianPDFReal_nonneg 0 1 y)
    rw [hIic]
    unfold Probability.standardGaussianTail
    calc
      (∫ y : ℝ in Set.Iic (-x),
          Probability.standardGaussianDensity y) =
          ∫ y : ℝ in Set.Iic (-x),
            Probability.standardGaussianDensity (-y) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro y _
        simp [Probability.standardGaussianDensity]
      _ = ∫ y : ℝ in Set.Ioi x,
          Probability.standardGaussianDensity y := by
        simpa using
          (integral_comp_neg_Iic (-x)
            Probability.standardGaussianDensity)
  rw [hneg, standardGaussianCDF_eq_one_sub_tail]
  ring

/-- The centered normalization used by the Gaussian--uniform hybrid. -/
theorem standardGaussianCDF_zero : standardGaussianCDF 0 = 1 / 2 := by
  have h := standardGaussianCDF_neg_eq_one_sub 0
  norm_num at h ⊢
  linarith

/-- The strict upper-event indicator used by U10. -/
noncomputable def strictUpperIndicator (t x : ℝ) : ℝ :=
  if t < x then 1 else 0

/-- The shifted Gaussian smoothing function from U10. -/
noncomputable def shiftedGaussianSmoothing
    (sigma theta t x : ℝ) : ℝ :=
  standardGaussianCDF ((x - t + theta * sigma) / sigma) /
    standardGaussianCDF theta

/-- The U10 smoothing function as an absolutely convergent positive-real
contour integral. -/
theorem shiftedGaussianSmoothing_eq_contourIntegral
    {lambda sigma theta t x : ℝ}
    (hlambda : 0 < lambda) (hsigma : 0 < sigma) :
    (shiftedGaussianSmoothing sigma theta t x : ℂ) =
      (1 / (2 * Real.pi * standardGaussianCDF theta) : ℂ) *
        ∫ u : ℝ,
          shiftedGaussianContourKernel lambda sigma
            (x - t + theta * sigma) u := by
  rw [shiftedGaussianSmoothing]
  push_cast
  rw [← integral_shiftedGaussianContourKernel_eq_cdf
    (y := x - t + theta * sigma) hlambda hsigma]
  have hCDF : (standardGaussianCDF theta : ℂ) ≠ 0 := by
    exact_mod_cast (standardGaussianCDF_pos theta).ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/--
The U10 smoothing strictly majorizes the strict event without moving its
endpoint.
-/
theorem strictUpperIndicator_lt_shiftedGaussianSmoothing
    {sigma theta t x : ℝ}
    (hsigma : 0 < sigma) (hx : t < x) :
    strictUpperIndicator t x < shiftedGaussianSmoothing sigma theta t x := by
  have htheta : theta - 1 < theta := by linarith
  have hCDFPos : 0 < standardGaussianCDF theta :=
    (cdf_nonneg (gaussianReal 0 1) (theta - 1)).trans_lt
      (strictMono_standardGaussianCDF htheta)
  have hargument : theta < (x - t + theta * sigma) / sigma := by
    rw [lt_div_iff₀ hsigma]
    nlinarith
  have hnumerator := strictMono_standardGaussianCDF hargument
  rw [strictUpperIndicator, if_pos hx, shiftedGaussianSmoothing]
  calc
    1 = standardGaussianCDF theta / standardGaussianCDF theta :=
      (div_self hCDFPos.ne').symm
    _ < standardGaussianCDF ((x - t + theta * sigma) / sigma) /
        standardGaussianCDF theta :=
      div_lt_div_of_pos_right hnumerator hCDFPos

/-- Pointwise non-strict majorization used before taking expectations. -/
theorem strictUpperIndicator_le_shiftedGaussianSmoothing
    {sigma theta t x : ℝ}
    (hsigma : 0 < sigma) :
    strictUpperIndicator t x ≤ shiftedGaussianSmoothing sigma theta t x := by
  by_cases hx : t < x
  · exact (strictUpperIndicator_lt_shiftedGaussianSmoothing hsigma hx).le
  · have htheta : theta - 1 < theta := by linarith
    have hCDFPos : 0 < standardGaussianCDF theta :=
      (cdf_nonneg (gaussianReal 0 1) (theta - 1)).trans_lt
        (strictMono_standardGaussianCDF htheta)
    rw [strictUpperIndicator, if_neg hx, shiftedGaussianSmoothing]
    exact div_nonneg (cdf_nonneg _ _) hCDFPos.le

/--
The pointwise U10 smoother majorization survives expectation.  This is the
measure-theoretic boundary immediately before the shifted Fourier inversion:
the remaining inversion theorem only has to upper-bound the integral on the
right.
-/
theorem measureReal_strictUpper_preimage_le_integral_shiftedGaussianSmoothing
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {X : Omega → ℝ} (hX : Measurable X)
    {sigma theta t : ℝ} (hsigma : 0 < sigma)
    (hsmooth : Integrable
      (fun omega => shiftedGaussianSmoothing sigma theta t (X omega)) mu) :
    mu.real (X ⁻¹' Set.Ioi t) ≤
      ∫ omega, shiftedGaussianSmoothing sigma theta t (X omega) ∂mu := by
  have hset : MeasurableSet (X ⁻¹' Set.Ioi t) :=
    measurableSet_Ioi.preimage hX
  have hindicator : Integrable
      (fun omega => strictUpperIndicator t (X omega)) mu := by
    have hfun : (fun omega => strictUpperIndicator t (X omega)) =
        (X ⁻¹' Set.Ioi t).indicator (fun _ => (1 : ℝ)) := by
      funext omega
      by_cases h : t < X omega <;>
        simp [strictUpperIndicator, Set.indicator, h]
    rw [hfun]
    exact (integrable_const (1 : ℝ)).indicator hset
  have hle :
      (∫ omega, strictUpperIndicator t (X omega) ∂mu) ≤
        ∫ omega, shiftedGaussianSmoothing sigma theta t (X omega) ∂mu := by
    apply integral_mono_ae hindicator hsmooth
    exact Filter.Eventually.of_forall fun omega =>
      strictUpperIndicator_le_shiftedGaussianSmoothing hsigma
  calc
    mu.real (X ⁻¹' Set.Ioi t) =
        ∫ omega, strictUpperIndicator t (X omega) ∂mu := by
      rw [show (fun omega => strictUpperIndicator t (X omega)) =
          (X ⁻¹' Set.Ioi t).indicator (fun _ => (1 : ℝ)) by
        funext omega
        by_cases h : t < X omega <;>
          simp [strictUpperIndicator, Set.indicator, h]]
      rw [integral_indicator hset, integral_const]
      simp
    _ ≤ _ := hle

/-- At the strict-tail endpoint the shifted smoother is exactly one. -/
theorem shiftedGaussianSmoothing_at_threshold
    {sigma theta t : ℝ} (hsigma : sigma ≠ 0)
    (hCDFPos : 0 < standardGaussianCDF theta) :
    shiftedGaussianSmoothing sigma theta t t = 1 := by
  rw [shiftedGaussianSmoothing]
  have hargument : (t - t + theta * sigma) / sigma = theta := by
    field_simp
    ring
  rw [hargument, div_self hCDFPos.ne']

/-- Complex MGF of the squared observable used by the upper contour. -/
noncomputable def quadraticComplexMGF
    {Omega : Type*} [MeasurableSpace Omega]
    (Z : Omega → ℝ) (mu : Measure Omega) (s : ℂ) : ℂ :=
  complexMGF (fun omega => (Z omega) ^ 2) mu s

/--
The complex MGF of a sum of squares of iid independent observables is the
corresponding power of the one-observable quadratic complex MGF.  The
reference observable may live on a different probability space; in
particular, the statement does not choose a coordinate when `m = 0`.
-/
theorem complexMGF_sum_sq_eq_quadraticComplexMGF_pow
    {Omega Omega0 : Type*} [MeasurableSpace Omega] [MeasurableSpace Omega0]
    {mu : Measure Omega} {mu0 : Measure Omega0} {m : ℕ}
    (Z : Fin m → Omega → ℝ) (Z0 : Omega0 → ℝ)
    (hIndep : iIndepFun Z mu)
    (hIdent : ∀ i, IdentDistrib (Z i) Z0 mu mu0)
    (s : ℂ) :
    complexMGF (fun omega => ∑ i, (Z i omega) ^ 2) mu s =
      quadraticComplexMGF Z0 mu0 s ^ m := by
  rw [complexMGF]
  calc
    (∫ omega, Complex.exp
        (s * (↑(∑ i, (Z i omega) ^ 2) : ℂ)) ∂mu) =
        ∫ omega, ∏ i, Complex.exp
          (s * (Z i omega : ℂ) ^ 2) ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with omega
      rw [← Complex.exp_sum]
      congr 1
      push_cast
      rw [Finset.mul_sum]
    _ = ∏ i, ∫ omega, Complex.exp
          (s * (Z i omega : ℂ) ^ 2) ∂mu := by
      simpa only [Function.comp_apply] using
        hIndep.integral_fun_prod_comp
          (fun i => (hIdent i).aemeasurable_fst)
          (fun _ => by fun_prop : ∀ i,
            AEStronglyMeasurable
              (fun x : ℝ => Complex.exp (s * (x : ℂ) ^ 2))
              (mu.map (Z i)))
    _ = ∏ _i : Fin m, quadraticComplexMGF Z0 mu0 s := by
      apply Finset.prod_congr rfl
      intro i _hi
      have hsq := (hIdent i).sq
      simpa [quadraticComplexMGF, Function.comp_apply, complexMGF] using
        congrFun (complexMGF_congr_identDistrib hsq) s
    _ = quadraticComplexMGF Z0 mu0 s ^ m := by simp

/--
Integrability of the real-axis exponential is exactly the condition needed
for the corresponding quadratic complex exponential on a vertical line.
-/
theorem integrable_quadraticCexp_vertical_of_integrable_real
    {Omega : Type*} [MeasurableSpace Omega]
    {Z : Omega → ℝ} {mu : Measure Omega} {lambda u : ℝ}
    (hZ : AEMeasurable Z mu)
    (hReal : Integrable
      (fun omega => Real.exp (lambda * (Z omega) ^ 2)) mu) :
    Integrable (fun omega =>
      Complex.exp ((lambda + u * Complex.I) * (Z omega : ℂ) ^ 2)) mu := by
  rw [← integrable_norm_iff (by fun_prop)]
  convert hReal using 1
  funext omega
  rw [Complex.norm_exp]
  congr 1
  simp [pow_two, Complex.mul_re, Complex.add_re, Complex.mul_im,
    Complex.add_im]

/-- Values of the quadratic complex MGF at opposite points of a vertical
line are complex conjugates. -/
theorem quadraticComplexMGF_vertical_conj
    {Omega : Type*} [MeasurableSpace Omega]
    (Z : Omega → ℝ) (mu : Measure Omega) (lambda u : ℝ) :
    quadraticComplexMGF Z mu (lambda - u * Complex.I) =
      conj (quadraticComplexMGF Z mu (lambda + u * Complex.I)) := by
  rw [quadraticComplexMGF, quadraticComplexMGF, complexMGF, complexMGF,
    ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with omega
  rw [← Complex.exp_conj]
  congr 1
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.add_re, Complex.mul_im, Complex.add_im]

/-- The powered quadratic complex MGF has the same norm on the two sides of
a vertical line.  This is the exact negative-frequency reduction used after
pairing the two halves of the U10 contour. -/
theorem norm_quadraticComplexMGF_pow_neg_eq
    {Omega : Type*} [MeasurableSpace Omega]
    (Z : Omega → ℝ) (mu : Measure Omega) (lambda u : ℝ) (m : ℕ) :
    ‖quadraticComplexMGF Z mu (lambda - u * Complex.I) ^ m‖ =
      ‖quadraticComplexMGF Z mu (lambda + u * Complex.I) ^ m‖ := by
  rw [quadraticComplexMGF_vertical_conj]
  simp

/-- A positive-frequency majorant also controls the paired negative
frequency, with no symmetry assumption on the law of `Z`. -/
theorem norm_quadraticComplexMGF_pow_neg_le_of_pos
    {Omega : Type*} [MeasurableSpace Omega]
    (Z : Omega → ℝ) (mu : Measure Omega) (lambda u : ℝ) (m : ℕ) {B : ℝ}
    (hB : ‖quadraticComplexMGF Z mu (lambda + u * Complex.I) ^ m‖ ≤ B) :
    ‖quadraticComplexMGF Z mu (lambda - u * Complex.I) ^ m‖ ≤ B := by
  rwa [norm_quadraticComplexMGF_pow_neg_eq]

/--
The exact U10a contour weight after factoring out
`exp ((lambda + u * I) * x)` from the pointwise inversion formula.
-/
noncomputable def shiftedGaussianContourWeight
    (sigma theta t lambda u : ℝ) : ℂ :=
  (1 / (2 * Real.pi * standardGaussianCDF theta) : ℝ) *
    Complex.exp
      ((lambda + u * Complex.I) * (-t + theta * sigma) +
        (sigma ^ 2 / 2 : ℝ) * (lambda + u * Complex.I) ^ 2) /
    (lambda + u * Complex.I)

/-- The U10a weight is the normalized contour kernel at the shifted threshold. -/
theorem shiftedGaussianContourWeight_eq_kernel
    (sigma theta t lambda u : ℝ) :
    shiftedGaussianContourWeight sigma theta t lambda u =
      (1 / (2 * Real.pi * standardGaussianCDF theta) : ℂ) *
        shiftedGaussianContourKernel lambda sigma (-t + theta * sigma) u := by
  unfold shiftedGaussianContourWeight shiftedGaussianContourKernel verticalLine
  push_cast
  ring

/-- Absolute integrability of the exact U10a contour weight. -/
theorem integrable_shiftedGaussianContourWeight
    {sigma theta t lambda : ℝ} (hlambda : 0 < lambda) (hsigma : 0 < sigma) :
    Integrable (shiftedGaussianContourWeight sigma theta t lambda) := by
  have h := (integrable_shiftedGaussianContourKernel
    (y := -t + theta * sigma) hlambda hsigma).const_mul
      (1 / (2 * Real.pi * standardGaussianCDF theta) : ℂ)
  convert h using 1
  funext u
  exact shiftedGaussianContourWeight_eq_kernel sigma theta t lambda u

/-- The positive-real inversion theorem in the exact pointwise form consumed by Fubini. -/
theorem shiftedGaussianSmoothing_contourRepresentation
    {sigma theta t lambda : ℝ} (hlambda : 0 < lambda) (hsigma : 0 < sigma)
    (x : ℝ) :
    (shiftedGaussianSmoothing sigma theta t x : ℂ) =
      ∫ u : ℝ, shiftedGaussianContourWeight sigma theta t lambda u *
        Complex.exp ((lambda + u * Complex.I) * x) := by
  rw [shiftedGaussianSmoothing_eq_contourIntegral hlambda hsigma,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [shiftedGaussianContourWeight_eq_kernel]
  let c : ℂ := 1 / (2 * Real.pi * standardGaussianCDF theta)
  calc
    c * shiftedGaussianContourKernel lambda sigma
        (x - t + theta * sigma) u =
      c * (shiftedGaussianContourKernel lambda sigma
        (-t + theta * sigma) u *
          Complex.exp ((lambda + u * Complex.I) * x)) := by
            congr 1
            unfold shiftedGaussianContourKernel verticalLine
            have hz : ((lambda : ℂ) + u * Complex.I) ≠ 0 := by
              intro hzero
              have hre := congrArg Complex.re hzero
              simp at hre
              linarith
            field_simp [hz]
            rw [← Complex.exp_add]
            congr 2
            push_cast
            ring
    _ = (c * shiftedGaussianContourKernel lambda sigma
          (-t + theta * sigma) u) *
        Complex.exp ((lambda + u * Complex.I) * x) := by ring

/--
Generic expectation-to-contour inequality used by U10.

The only contour-specific premise is `hRepresentation`, the pointwise
positive-real contour identity.  The explicit real-axis exponential
integrability premise is what proves absolute integrability on the product
space and therefore justifies the Fubini swap.  Consequently a downstream
contour theorem can discharge `hRepresentation` without taking ownership of
the probability or Fubini argument.
-/
theorem integral_comp_le_integral_norm_complexMGF_of_contourRepresentation
    {Omega U : Type*} [MeasurableSpace Omega] [MeasurableSpace U]
    {mu : Measure Omega} {nu : Measure U} [SFinite mu] [SFinite nu]
    (X : Omega → ℝ) (H : ℝ → ℝ) (W : U → ℂ) (v : U → ℝ) (lambda : ℝ)
    (hX : Measurable X) (hW : Integrable W nu) (hv : Measurable v)
    (hReal : Integrable (fun omega => Real.exp (lambda * X omega)) mu)
    (hRepresentation : ∀ x,
      (H x : ℂ) = ∫ u, W u *
        Complex.exp ((lambda + v u * Complex.I) * x) ∂nu) :
    (∫ omega, H (X omega) ∂mu) ≤
      ∫ u, ‖W u‖ * ‖complexMGF X mu (lambda + v u * Complex.I)‖ ∂nu := by
  let K : Omega × U → ℂ := fun p =>
    W p.2 * Complex.exp ((lambda + v p.2 * Complex.I) * X p.1)
  have hKMeas : AEStronglyMeasurable K (mu.prod nu) := by
    exact hW.aestronglyMeasurable.comp_snd.mul (by fun_prop)
  have hKInt : Integrable K (mu.prod nu) := by
    refine (hReal.mul_prod hW.norm).mono' hKMeas ?_
    filter_upwards [] with p
    change ‖W p.2 * Complex.exp
      ((lambda + v p.2 * Complex.I) * X p.1)‖ ≤
        Real.exp (lambda * X p.1) * ‖W p.2‖
    rw [norm_mul, Complex.norm_exp]
    have hre :
        ((lambda + v p.2 * Complex.I) * (X p.1 : ℂ)).re =
          lambda * X p.1 := by
      simp [Complex.mul_re, Complex.add_re, Complex.mul_im, Complex.add_im]
    rw [hre, mul_comm]
  have hFubini :
      (∫ omega, ∫ u, K (omega, u) ∂nu ∂mu) =
        ∫ u, W u * complexMGF X mu (lambda + v u * Complex.I) ∂nu := by
    calc
      (∫ omega, ∫ u, K (omega, u) ∂nu ∂mu) =
          ∫ u, ∫ omega, K (omega, u) ∂mu ∂nu :=
        integral_integral_swap hKInt
      _ = ∫ u, W u * complexMGF X mu
          (lambda + v u * Complex.I) ∂nu := by
        apply integral_congr_ae
        filter_upwards [] with u
        simp only [K, complexMGF]
        rw [integral_const_mul]
  have hContour :
      ((∫ omega, H (X omega) ∂mu : ℝ) : ℂ) =
        ∫ u, W u * complexMGF X mu
          (lambda + v u * Complex.I) ∂nu := by
    rw [← integral_complex_ofReal]
    calc
      (∫ omega, (H (X omega) : ℂ) ∂mu) =
          ∫ omega, ∫ u, K (omega, u) ∂nu ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with omega
        simpa only [K] using hRepresentation (X omega)
      _ = _ := hFubini
  calc
    (∫ omega, H (X omega) ∂mu) =
        (∫ u, W u * complexMGF X mu
          (lambda + v u * Complex.I) ∂nu).re := by
      exact_mod_cast congrArg Complex.re hContour
    _ ≤ ‖∫ u, W u * complexMGF X mu
          (lambda + v u * Complex.I) ∂nu‖ := Complex.re_le_norm _
    _ ≤ ∫ u, ‖W u * complexMGF X mu
          (lambda + v u * Complex.I)‖ ∂nu :=
      norm_integral_le_integral_norm _
    _ = ∫ u, ‖W u‖ * ‖complexMGF X mu
          (lambda + v u * Complex.I)‖ ∂nu := by
      congr 1
      funext u
      rw [norm_mul]

/--
Expectation-to-contour inequality with the exact shifted-Gaussian U10a
constants.  A positive-real contour identity can be supplied directly as
`hRepresentation`; all expectation interchange is discharged here.
-/
theorem integral_shiftedGaussianSmoothing_le_contour
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [SFinite mu]
    (X : Omega → ℝ) {sigma theta t lambda : ℝ}
    (hX : Measurable X)
    (hWeight : Integrable
      (shiftedGaussianContourWeight sigma theta t lambda) volume)
    (hReal : Integrable (fun omega => Real.exp (lambda * X omega)) mu)
    (hRepresentation : ∀ x,
      (shiftedGaussianSmoothing sigma theta t x : ℂ) =
        ∫ u : ℝ, shiftedGaussianContourWeight sigma theta t lambda u *
          Complex.exp ((lambda + u * Complex.I) * x)) :
    (∫ omega, shiftedGaussianSmoothing sigma theta t (X omega) ∂mu) ≤
      ∫ u : ℝ, ‖shiftedGaussianContourWeight sigma theta t lambda u‖ *
        ‖complexMGF X mu (lambda + u * Complex.I)‖ := by
  exact integral_comp_le_integral_norm_complexMGF_of_contourRepresentation
    X (shiftedGaussianSmoothing sigma theta t)
      (shiftedGaussianContourWeight sigma theta t lambda) id lambda
      hX hWeight measurable_id hReal hRepresentation

/--
The modulus on a vertical line is bounded by the real-axis quadratic MGF.
This is the complex-axis half of U8 and does not depend on U4.
-/
theorem norm_quadraticComplexMGF_le_real
    {Omega : Type*} [MeasurableSpace Omega]
    (Z : Omega → ℝ) (mu : Measure Omega) (s : ℂ) :
    ‖quadraticComplexMGF Z mu s‖ ≤
      mgf (fun omega => (Z omega) ^ 2) mu s.re := by
  exact norm_complexMGF_le_mgf

/-- The vertical-line modulus bound is preserved under `m`th powers. -/
theorem norm_quadraticComplexMGF_pow_le
    {Omega : Type*} [MeasurableSpace Omega]
    (Z : Omega → ℝ) (mu : Measure Omega) (s : ℂ) (m : ℕ) :
    ‖quadraticComplexMGF Z mu s ^ m‖ ≤
      mgf (fun omega => (Z omega) ^ 2) mu s.re ^ m := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_quadraticComplexMGF_le_real Z mu s) m

end CertifiedJL
