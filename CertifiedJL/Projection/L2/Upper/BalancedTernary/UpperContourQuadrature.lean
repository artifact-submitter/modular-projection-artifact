/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperContour
import CertifiedJL.Analysis.Gaussian.HalfGaussian

/-!
# Sparse upper-contour quadrature identities

This module exposes the exact positive-frequency scalar weight used by the
low-profile rectangle certificate.
-/

namespace CertifiedJL

open MeasureTheory

/-- Exact real factorization of the shifted-Gaussian contour weight. -/
theorem norm_shiftedGaussianContourWeight_eq_quadrature
    (sigma theta threshold lambda frequency : ℝ) :
    ‖shiftedGaussianContourWeight sigma theta threshold lambda frequency‖ =
      (1 / (2 * Real.pi * standardGaussianCDF theta)) *
        Real.exp (-(lambda * (threshold - theta * sigma) -
          sigma ^ 2 * lambda ^ 2 / 2)) *
        Real.exp (-(sigma ^ 2 / 2) * frequency ^ 2) *
        (1 / Real.sqrt (lambda ^ 2 + frequency ^ 2)) := by
  rw [shiftedGaussianContourWeight_eq_kernel, norm_mul,
    norm_shiftedGaussianContourKernel]
  have hcoefficient : 0 < 1 / (2 * Real.pi * standardGaussianCDF theta) := by
    exact one_div_pos.mpr (mul_pos (mul_pos (by norm_num) Real.pi_pos)
      (standardGaussianCDF_pos theta))
  have hdenominatorNorm :
      ‖(2 : ℂ) * (Real.pi : ℂ) * (standardGaussianCDF theta : ℂ)‖ =
        2 * Real.pi * standardGaussianCDF theta := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos Real.pi_pos, abs_of_pos (standardGaussianCDF_pos theta)]
    norm_num
  rw [norm_div, norm_one, hdenominatorNorm]
  rw [show
      lambda * (-threshold + theta * sigma) +
          sigma ^ 2 * (lambda ^ 2 - frequency ^ 2) / 2 =
        -(lambda * (threshold - theta * sigma) -
          sigma ^ 2 * lambda ^ 2 / 2) +
          (-(sigma ^ 2 / 2) * frequency ^ 2) by ring,
    Real.exp_add]
  ring

/-- The scalar Gaussian/reciprocal-square-root quadrature weight decreases
as the positive contour frequency moves to the right. -/
theorem gaussianQuadratureWeight_le_of_le
    {alpha lambda frequencyLeft frequency : ℝ}
    (halpha : 0 ≤ alpha) (hlambda : 0 < lambda)
    (hfrequencyLeft : 0 ≤ frequencyLeft)
    (hfrequency : frequencyLeft ≤ frequency) :
    Real.exp (-alpha * frequency ^ 2) *
        (1 / Real.sqrt (lambda ^ 2 + frequency ^ 2)) ≤
      Real.exp (-alpha * frequencyLeft ^ 2) *
        (1 / Real.sqrt (lambda ^ 2 + frequencyLeft ^ 2)) := by
  have hfrequencyNonneg : 0 ≤ frequency := hfrequencyLeft.trans hfrequency
  have hsquare : frequencyLeft ^ 2 ≤ frequency ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hfrequency)
      (add_nonneg hfrequencyNonneg hfrequencyLeft)]
  have hexponential : Real.exp (-alpha * frequency ^ 2) ≤
      Real.exp (-alpha * frequencyLeft ^ 2) := by
    apply Real.exp_le_exp.mpr
    calc
      -alpha * frequency ^ 2 = -(alpha * frequency ^ 2) := by ring
      _ ≤ -(alpha * frequencyLeft ^ 2) :=
        neg_le_neg (mul_le_mul_of_nonneg_left hsquare halpha)
      _ = -alpha * frequencyLeft ^ 2 := by ring
  have hsqrt : Real.sqrt (lambda ^ 2 + frequencyLeft ^ 2) ≤
      Real.sqrt (lambda ^ 2 + frequency ^ 2) := by
    exact Real.sqrt_le_sqrt (by linarith)
  have hsqrtLeft : 0 < Real.sqrt (lambda ^ 2 + frequencyLeft ^ 2) := by
    positivity
  have hinverse : 1 / Real.sqrt (lambda ^ 2 + frequency ^ 2) ≤
      1 / Real.sqrt (lambda ^ 2 + frequencyLeft ^ 2) :=
    one_div_le_one_div_of_le hsqrtLeft hsqrt
  exact mul_le_mul hexponential hinverse (by positivity) (Real.exp_nonneg _)

/-- The positive-frequency tail used by the certificate is bounded by the
Gaussian Mills factor after discarding the reciprocal square root at the
positive cutoff. -/
theorem integral_Ioi_gaussianQuadratureWeight_le
    {alpha lambda cutoff constant : ℝ}
    (halpha : 0 < alpha) (hlambda : 0 < lambda)
    (hcutoff : 0 < cutoff) (hconstant : 0 ≤ constant) :
    (∫ frequency : ℝ in Set.Ioi cutoff,
        (constant * Real.exp (-alpha * frequency ^ 2) *
          (1 / Real.sqrt (lambda ^ 2 + frequency ^ 2)))) ≤
      (constant * Real.exp (-alpha * cutoff ^ 2) /
        (2 * alpha * cutoff ^ 2)) := by
  let f : ℝ → ℝ := fun frequency =>
    (constant * Real.exp (-alpha * frequency ^ 2) *
      (1 / Real.sqrt (lambda ^ 2 + frequency ^ 2)))
  let g : ℝ → ℝ := fun frequency =>
    (constant / cutoff) * Real.exp (-alpha * frequency ^ 2)
  have hpointwise : ∀ frequency ∈ Set.Ioi cutoff, f frequency ≤ g frequency := by
    intro frequency hfrequency
    have hfrequencyPos : 0 < frequency := hcutoff.trans hfrequency
    have hsqrtFrequency : frequency ≤
        Real.sqrt (lambda ^ 2 + frequency ^ 2) := by
      exact (Real.le_sqrt hfrequencyPos.le (by positivity)).2
        (by nlinarith [sq_nonneg lambda])
    have hinverse : 1 / Real.sqrt (lambda ^ 2 + frequency ^ 2) ≤
        1 / cutoff := by
      exact one_div_le_one_div_of_le hcutoff
        (hfrequency.le.trans hsqrtFrequency)
    dsimp only [f, g]
    calc
      (constant * Real.exp (-alpha * frequency ^ 2) *
          (1 / Real.sqrt (lambda ^ 2 + frequency ^ 2))) ≤
        (constant * Real.exp (-alpha * frequency ^ 2) * (1 / cutoff)) := by
          gcongr
      _ = (constant / cutoff) *
          Real.exp (-alpha * frequency ^ 2) := by ring
  have hgGlobal : Integrable g := by
    exact (integrable_exp_neg_mul_sq halpha).const_mul
      (constant / cutoff)
  have hfMeasurable : AEStronglyMeasurable f := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f]
    fun_prop
  have hf : IntegrableOn f (Set.Ioi cutoff) := by
    apply (hgGlobal.integrableOn).mono' hfMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with frequency hfrequency
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hpointwise frequency hfrequency
    · dsimp only [f]
      positivity
  have hg : IntegrableOn g (Set.Ioi cutoff) := hgGlobal.integrableOn
  calc
    (∫ frequency : ℝ in Set.Ioi cutoff,
        (constant * Real.exp (-alpha * frequency ^ 2) *
          (1 / Real.sqrt (lambda ^ 2 + frequency ^ 2)))) =
        ∫ frequency : ℝ in Set.Ioi cutoff, f frequency := rfl
    _ ≤ ∫ frequency : ℝ in Set.Ioi cutoff, g frequency :=
      setIntegral_mono_on hf hg measurableSet_Ioi hpointwise
    _ = (constant / cutoff) *
        ∫ frequency : ℝ in Set.Ioi cutoff,
          Real.exp (-alpha * frequency ^ 2) := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ (constant / cutoff) *
        (Real.exp (-alpha * cutoff ^ 2) / (2 * alpha * cutoff)) := by
      gcongr
      exact Probability.integral_Ioi_exp_neg_mul_sq_le halpha hcutoff
    _ = constant * Real.exp (-alpha * cutoff ^ 2) /
        (2 * alpha * cutoff ^ 2) := by
      field_simp

/-- Integrating a pointwise upper rectangle over a real `Ioc` cell multiplies
its height by the exact cell length. -/
theorem integral_Ioc_le_length_mul
    {f : ℝ → ℝ} {left right upper : ℝ}
    (hleftRight : left ≤ right)
    (hf : IntegrableOn f (Set.Ioc left right))
    (hupper : ∀ x ∈ Set.Ioc left right, f x ≤ upper) :
    (∫ x : ℝ in Set.Ioc left right, f x) ≤ (right - left) * upper := by
  calc
    (∫ x : ℝ in Set.Ioc left right, f x) ≤
        ∫ _x : ℝ in Set.Ioc left right, upper := by
      exact setIntegral_mono_on hf
        (integrableOn_const (measure_Ioc_lt_top.ne)) measurableSet_Ioc hupper
    _ = (right - left) * upper := by
      rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hleftRight)]

end CertifiedJL
