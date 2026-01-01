/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Distributions.Gaussian.StandardGaussian

/-!
# Gaussian calculations for Esscher tilting

This module isolates the Gaussian analytic calculation in the tilted
Rademacher bound.  We use a location-scale presentation of the normal density
because the standard deviation, rather than the variance, is the natural
parameter of the Esscher argument.
-/

open MeasureTheory

namespace CertifiedJL
namespace Probability

/-- The density of `N(m, s²)`, parametrized by its standard deviation `s`. -/
noncomputable def gaussianLocationScaleDensity
    (m s y : ℝ) : ℝ :=
  s⁻¹ * standardGaussianDensity ((y - m) / s)

theorem integrable_gaussianLocationScaleDensity
    (m : ℝ) {s : ℝ} (hs : s ≠ 0) :
    Integrable (gaussianLocationScaleDensity m s) := by
  unfold gaussianLocationScaleDensity
  have h :=
    (integrable_standardGaussianDensity.comp_div hs).comp_sub_right m
  simpa only [sub_div] using h.const_mul s⁻¹

/--
The upper tail of a location-scale Gaussian is the corresponding standard
Gaussian tail.
-/
theorem integral_Ioi_gaussianLocationScaleDensity
    (m a : ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ y : ℝ in Set.Ioi a, gaussianLocationScaleDensity m s y) =
      standardGaussianTail ((a - m) / s) := by
  let g : ℝ → ℝ := standardGaussianDensity
  have hf : ContinuousOn (fun y : ℝ => (y - m) / s) (Set.Ici a) := by
    fun_prop
  have hft :
      Filter.Tendsto (fun y : ℝ => (y - m) / s)
        Filter.atTop Filter.atTop := by
    simpa only [sub_eq_add_neg, Function.id_def] using
      (Filter.tendsto_atTop_add_const_right
          Filter.atTop (-m) Filter.tendsto_id)
        |>.atTop_div_const hs
  have hff' :
      ∀ y ∈ Set.Ioi a,
        HasDerivWithinAt (fun z : ℝ => (z - m) / s)
          (1 / s) (Set.Ioi y) y := by
    intro y _
    simpa only [id_eq] using
      (((hasDerivAt_id y).sub_const m).div_const s).hasDerivWithinAt
  have hg_cont :
      ContinuousOn g ((fun y : ℝ => (y - m) / s) '' Set.Ioi a) := by
    apply Continuous.continuousOn
    unfold g standardGaussianDensity
    fun_prop
  have hg1 :
      IntegrableOn g ((fun y : ℝ => (y - m) / s) '' Set.Ici a) :=
    integrable_standardGaussianDensity.integrableOn
  have hg2 :
      IntegrableOn
        (fun y => (g ∘ (fun z : ℝ => (z - m) / s)) y * (1 / s))
        (Set.Ici a) := by
    have hglobal :
        Integrable
          (fun y => (g ∘ (fun z : ℝ => (z - m) / s)) y * (1 / s)) := by
      have hbase :
          Integrable (fun y =>
            standardGaussianDensity ((y - m) / s)) := by
        have h :=
          (integrable_standardGaussianDensity.comp_div hs.ne')
            |>.comp_sub_right m
        simpa only [sub_div] using h
      simpa only [g, Function.comp_apply, one_div, mul_comm] using
        hbase.const_mul s⁻¹
    exact hglobal.integrableOn
  have hchange :=
    integral_comp_mul_deriv_Ioi
      (f := fun y : ℝ => (y - m) / s)
      (f' := fun _ => 1 / s)
      (g := g) hf hft hff' hg_cont hg1 hg2
  simpa only [gaussianLocationScaleDensity, g, Function.comp_apply,
    standardGaussianTail, one_div, mul_comm] using hchange

/-- Pointwise completion of the square for the Esscher-weighted density. -/
theorem exp_mul_gaussianLocationScaleDensity_eq
    (t m y : ℝ) {s : ℝ} (hs : s ≠ 0) :
    Real.exp (-t * y) * gaussianLocationScaleDensity m s y =
      Real.exp (-t * m + t ^ 2 * s ^ 2 / 2) *
        gaussianLocationScaleDensity (m - t * s ^ 2) s y := by
  unfold gaussianLocationScaleDensity standardGaussianDensity
  have hexp :
      Real.exp (-t * y) *
          Real.exp (-((y - m) / s) ^ 2 / 2) =
        Real.exp (-t * m + t ^ 2 * s ^ 2 / 2) *
          Real.exp (-((y - (m - t * s ^ 2)) / s) ^ 2 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  calc
    Real.exp (-t * y) *
        (s⁻¹ * ((Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-((y - m) / s) ^ 2 / 2))) =
      s⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹ *
        (Real.exp (-t * y) *
          Real.exp (-((y - m) / s) ^ 2 / 2)) := by ring
    _ = s⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹ *
        (Real.exp (-t * m + t ^ 2 * s ^ 2 / 2) *
          Real.exp (-((y - (m - t * s ^ 2)) / s) ^ 2 / 2)) := by
      rw [hexp]
    _ = Real.exp (-t * m + t ^ 2 * s ^ 2 / 2) *
        (s⁻¹ * ((Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-((y - (m - t * s ^ 2)) / s) ^ 2 / 2))) := by
      ring

/--
Exact completion-of-square identity for an exponentially weighted Gaussian
upper tail.
-/
theorem integral_Ioi_exp_mul_gaussianLocationScaleDensity
    (t m a : ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ y : ℝ in Set.Ioi a,
        Real.exp (-t * y) * gaussianLocationScaleDensity m s y) =
      Real.exp (-t * m + t ^ 2 * s ^ 2 / 2) *
        standardGaussianTail ((a - m) / s + t * s) := by
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun y _ => exp_mul_gaussianLocationScaleDensity_eq t m y hs.ne')]
  rw [integral_const_mul,
    integral_Ioi_gaussianLocationScaleDensity (m - t * s ^ 2) a hs]
  congr 2
  field_simp
  ring

/--
Mathlib's Gaussian density with variance `s²` agrees with the
location--scale density used by the Esscher calculation when `s > 0`.
-/
theorem gaussianPDFReal_sq_eq_locationScale
    (m y : ℝ) {s : ℝ} (hs : 0 < s) :
    ProbabilityTheory.gaussianPDFReal m
        (NNReal.mk (s ^ 2) (sq_nonneg s)) y =
      gaussianLocationScaleDensity m s y := by
  unfold ProbabilityTheory.gaussianPDFReal gaussianLocationScaleDensity
    standardGaussianDensity
  have hsqrt : Real.sqrt (s ^ 2) = s :=
    (Real.sqrt_sq_eq_abs s).trans (abs_of_pos hs)
  change (Real.sqrt (2 * Real.pi * s ^ 2))⁻¹ *
      Real.exp (-(y - m) ^ 2 / (2 * s ^ 2)) =
    s⁻¹ * ((Real.sqrt (2 * Real.pi))⁻¹ *
      Real.exp (-((y - m) / s) ^ 2 / 2))
  rw [show Real.sqrt (2 * Real.pi * s ^ 2) =
      Real.sqrt (2 * Real.pi) * s by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi), hsqrt]]
  field_simp

/--
The exact Gaussian Esscher integral, stated directly for Mathlib's Gaussian
probability measure with variance `s²`.
-/
theorem integral_Ioi_exp_mul_gaussianReal_sq
    (t m a : ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ y : ℝ in Set.Ioi a, Real.exp (-t * y)
        ∂(ProbabilityTheory.gaussianReal m
          (NNReal.mk (s ^ 2) (sq_nonneg s)))) =
      Real.exp (-t * m + t ^ 2 * s ^ 2 / 2) *
        standardGaussianTail ((a - m) / s + t * s) := by
  have hv : NNReal.mk (s ^ 2) (sq_nonneg s) ≠ 0 := by
    intro hv0
    have hcoe := congrArg (fun v : NNReal => (v : ℝ)) hv0
    change s ^ 2 = 0 at hcoe
    exact (pow_ne_zero 2 hs.ne') hcoe
  rw [← integral_indicator measurableSet_Ioi]
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul hv]
  rw [show (fun y : ℝ =>
      ProbabilityTheory.gaussianPDFReal m
          (NNReal.mk (s ^ 2) (sq_nonneg s)) y •
        (Set.Ioi a).indicator (fun y => Real.exp (-t * y)) y) =
      (Set.Ioi a).indicator (fun y =>
        Real.exp (-t * y) * gaussianLocationScaleDensity m s y) by
    funext y
    by_cases hy : y ∈ Set.Ioi a
    · simp [hy, gaussianPDFReal_sq_eq_locationScale m y hs, mul_comm]
    · simp [hy]]
  rw [integral_indicator measurableSet_Ioi]
  exact integral_Ioi_exp_mul_gaussianLocationScaleDensity t m a hs

/--
The `N(m,s²)` law is the affine image `sG+m` of the standard Gaussian.
-/
theorem gaussianReal_sq_eq_map_standard
    (m s : ℝ) :
    ProbabilityTheory.gaussianReal m
        (NNReal.mk (s ^ 2) (sq_nonneg s)) =
      Measure.map (fun y : ℝ => s * y + m)
        (ProbabilityTheory.gaussianReal 0 1) := by
  have h0 :
      ProbabilityTheory.HasLaw id
        (ProbabilityTheory.gaussianReal 0 1)
        (ProbabilityTheory.gaussianReal 0 1) :=
    ProbabilityTheory.HasLaw.id
  have hs := ProbabilityTheory.gaussianReal_const_mul h0 s
  have hm := ProbabilityTheory.gaussianReal_add_const hs m
  simpa [id_eq] using hm.map_eq.symm

/--
The exact exponent cancellation after applying the Gaussian Mills bound in
the Esscher argument.
-/
theorem esscherGaussianTail_le_mills
    (A x m : ℝ) {s : ℝ} (hx : 0 < x) (hs : 0 < s) (hmx : m ≤ x) :
    Real.exp (A + x ^ 2 * s ^ 2 / 2 - x * m) *
        standardGaussianTail ((x - m) / s + x * s) ≤
      Real.exp (A - x ^ 2) *
        Real.exp (-((x - m) / s) ^ 2 / 2) /
          (Real.sqrt (2 * Real.pi) * ((x - m) / s + x * s)) := by
  have hzeta : 0 ≤ (x - m) / s :=
    div_nonneg (sub_nonneg.mpr hmx) hs.le
  have hz : 0 < (x - m) / s + x * s :=
    add_pos_of_nonneg_of_pos hzeta (mul_pos hx hs)
  have hexp :
      Real.exp (A + x ^ 2 * s ^ 2 / 2 - x * m) *
          Real.exp (-((x - m) / s + x * s) ^ 2 / 2) =
        Real.exp (A - x ^ 2) *
          Real.exp (-((x - m) / s) ^ 2 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have hdiv := congrArg
    (fun q : ℝ =>
      q / (Real.sqrt (2 * Real.pi) * ((x - m) / s + x * s)))
    hexp
  calc
    Real.exp (A + x ^ 2 * s ^ 2 / 2 - x * m) *
        standardGaussianTail ((x - m) / s + x * s) ≤
      Real.exp (A + x ^ 2 * s ^ 2 / 2 - x * m) *
        (Real.exp (-((x - m) / s + x * s) ^ 2 / 2) /
          (Real.sqrt (2 * Real.pi) * ((x - m) / s + x * s))) := by
      gcongr
      exact standardGaussianTail_le_mills hz
    _ = Real.exp (A - x ^ 2) *
        Real.exp (-((x - m) / s) ^ 2 / 2) /
          (Real.sqrt (2 * Real.pi) * ((x - m) / s + x * s)) := by
      calc
        _ = (Real.exp (A + x ^ 2 * s ^ 2 / 2 - x * m) *
              Real.exp (-((x - m) / s + x * s) ^ 2 / 2)) /
            (Real.sqrt (2 * Real.pi) *
              ((x - m) / s + x * s)) := by ring
        _ = (Real.exp (A - x ^ 2) *
              Real.exp (-((x - m) / s) ^ 2 / 2)) /
            (Real.sqrt (2 * Real.pi) *
              ((x - m) / s + x * s)) := hdiv
        _ = _ := by ring

/--
The coarser cancellation form used by (O6): after Mills, discard the
nonpositive Gaussian exponent and use `ζ + xs ≥ xs`.
-/
theorem esscherGaussianTail_le_cancelled
    (A x m : ℝ) {s : ℝ} (hx : 0 < x) (hs : 0 < s) (hmx : m ≤ x) :
    Real.exp (A + x ^ 2 * s ^ 2 / 2 - x * m) *
        standardGaussianTail ((x - m) / s + x * s) ≤
      Real.exp (A - x ^ 2) /
        (Real.sqrt (2 * Real.pi) * (x * s)) := by
  have hzeta : 0 ≤ (x - m) / s :=
    div_nonneg (sub_nonneg.mpr hmx) hs.le
  have hz : 0 < (x - m) / s + x * s :=
    add_pos_of_nonneg_of_pos hzeta (mul_pos hx hs)
  have hxs : 0 < x * s := mul_pos hx hs
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
  calc
    Real.exp (A + x ^ 2 * s ^ 2 / 2 - x * m) *
        standardGaussianTail ((x - m) / s + x * s) ≤
      Real.exp (A - x ^ 2) *
        Real.exp (-((x - m) / s) ^ 2 / 2) /
          (Real.sqrt (2 * Real.pi) * ((x - m) / s + x * s)) :=
        esscherGaussianTail_le_mills A x m hx hs hmx
    _ ≤ Real.exp (A - x ^ 2) * 1 /
          (Real.sqrt (2 * Real.pi) * ((x - m) / s + x * s)) := by
      gcongr
      exact Real.exp_le_one_iff.mpr
        (div_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (sq_nonneg _)) (by norm_num))
    _ ≤ Real.exp (A - x ^ 2) /
        (Real.sqrt (2 * Real.pi) * (x * s)) := by
      rw [mul_one]
      exact div_le_div_of_nonneg_left (Real.exp_nonneg _)
        (mul_pos hsqrt hxs) (mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left hzeta) hsqrt.le)

end Probability
end CertifiedJL
