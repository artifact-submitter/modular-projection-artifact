/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Gaussian.GaussianEsscher
import CertifiedJL.Probability.NormalApproximation.Shared.ExponentialLayerCake
import CertifiedJL.Probability.Distributions.Rademacher.RademacherEsscher
import CertifiedJL.Probability.Distributions.Rademacher.RademacherLyapunovProfile

/-!
# Esscher bounds from quantitative normal approximation

This module assembles the exact finite change of measure, the direct
exponential layer-cake transfer, and the Gaussian completion-of-the-square
calculation.  The main theorem deliberately accepts a pointwise CDF estimate:
the later quantitative Berry--Esseen module supplies that estimate.  Thus the
analytic boundary is explicit, while no final public theorem can accidentally
hide Berry--Esseen as an axiom or theorem-shaped assumption.
-/

open scoped BigOperators

open MeasureTheory ProbabilityTheory Set

namespace CertifiedJL
namespace Probability

/-- Mean of a normalized Rademacher sum after exponential tilting at `x`. -/
noncomputable def rademacherTiltedMean
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i, b i * Real.tanh (x * b i)

/-- Standard deviation of the tilted Rademacher sum. -/
noncomputable def rademacherTiltedStdDev
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ) : ℝ :=
  Real.sqrt (rademacherTiltedVariance b x)

/-- Law of the weighted sign sum under the coordinatewise exponential tilt. -/
noncomputable def rademacherTiltedSumLaw
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ) : Measure ℝ :=
  (biasedSignProductPMF (fun i => x * b i)).toMeasure.map
    (rademacherSum b)

/-- Law of the centered, variance-normalized tilted sum. -/
noncomputable def rademacherTiltedStandardizedLaw
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ) : Measure ℝ :=
  (rademacherTiltedSumLaw b x).map fun y =>
    (y - rademacherTiltedMean b x) /
      rademacherTiltedStdDev b x

instance rademacherTiltedSumLaw_isProbabilityMeasure
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ) :
    IsProbabilityMeasure (rademacherTiltedSumLaw b x) := by
  unfold rademacherTiltedSumLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_of_finite (rademacherSum b)).aemeasurable

instance rademacherTiltedStandardizedLaw_isProbabilityMeasure
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ) :
    IsProbabilityMeasure (rademacherTiltedStandardizedLaw b x) := by
  unfold rademacherTiltedStandardizedLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/--
A Kolmogorov bound for the standardized tilted sum gives the corresponding
pointwise CDF bound against `N(m,s²)` before standardization.
-/
theorem tiltedCDF_le_of_standardized_kolmogorov
    {ι : Type*} [Fintype ι] (b : ι → ℝ) {x ε : ℝ}
    (hnorm : ∑ i, b i ^ 2 = 1)
    (hK :
      kolmogorovDistance
          (rademacherTiltedStandardizedLaw b x)
          (gaussianReal 0 1) ≤ ε) :
    ∀ z,
      |cdf (rademacherTiltedSumLaw b x) z -
          cdf (gaussianReal
            (rademacherTiltedMean b x)
            (NNReal.mk (rademacherTiltedStdDev b x ^ 2)
              (sq_nonneg (rademacherTiltedStdDev b x)))) z| ≤ ε := by
  let μ : Measure ℝ := rademacherTiltedSumLaw b x
  let m : ℝ := rademacherTiltedMean b x
  let s : ℝ := rademacherTiltedStdDev b x
  let γ : Measure ℝ := gaussianReal 0 1
  have hs : 0 < s :=
    sqrt_rademacherTiltedVariance_pos b x hnorm
  intro z
  let q : ℝ := (z - m) / s
  have hμ :
      cdf (rademacherTiltedStandardizedLaw b x) q =
        cdf μ z := by
    have hfun :
        (fun y : ℝ => (y - m) / s) =
          fun y : ℝ => s⁻¹ * y + (-m / s) := by
      funext y
      field_simp
      ring
    unfold rademacherTiltedStandardizedLaw
    change cdf (μ.map fun y : ℝ => (y - m) / s) q = cdf μ z
    rw [hfun, cdf_map_affine_pos μ (inv_pos.mpr hs) (-m / s)]
    congr 2
    dsimp only [q]
    field_simp
    ring
  have hγ :
      cdf (gaussianReal m
          (NNReal.mk (s ^ 2) (sq_nonneg s))) z =
        cdf γ q := by
    rw [gaussianReal_sq_eq_map_standard]
    change cdf (γ.map fun y : ℝ => s * y + m) z = cdf γ q
    rw [cdf_map_affine_pos γ hs m]
  have hpoint :=
    cdfAbsoluteDiscrepancy_le_kolmogorovDistance
      (rademacherTiltedStandardizedLaw b x) γ q
  change
    |cdf (rademacherTiltedSumLaw b x) z -
        cdf (gaussianReal
          (rademacherTiltedMean b x)
          (NNReal.mk (rademacherTiltedStdDev b x ^ 2)
            (sq_nonneg (rademacherTiltedStdDev b x)))) z| ≤ ε
  change |cdf μ z -
      cdf (gaussianReal m (NNReal.mk (s ^ 2) (sq_nonneg s))) z| ≤ ε
  rw [← hμ, hγ]
  exact hpoint.trans (by simpa only [γ] using hK)

/-- The elementary global inequality `u tanh u ≤ u²`. -/
theorem mul_tanh_le_sq (u : ℝ) :
    u * Real.tanh u ≤ u ^ 2 := by
  rcases le_total 0 u with hu | hu
  · simpa only [pow_two] using
      (mul_le_mul_of_nonneg_left (tanh_le_self hu) hu)
  · have hneg : 0 ≤ -u := neg_nonneg.mpr hu
    have h := mul_le_mul_of_nonneg_left (tanh_le_self hneg) hneg
    rw [Real.tanh_neg] at h
    nlinarith

/--
The tilted mean does not cross the tilt point for a normalized coefficient
profile.  This is the `ζ ≥ 0` fact needed by Mills' inequality.
-/
theorem rademacherTiltedMean_le
    {ι : Type*} [Fintype ι] (b : ι → ℝ) {x : ℝ}
    (hx : 0 < x) (hnorm : ∑ i, b i ^ 2 = 1) :
    rademacherTiltedMean b x ≤ x := by
  have hpoint : ∀ i,
      b i * Real.tanh (x * b i) ≤ x * b i ^ 2 := by
    intro i
    have h := mul_tanh_le_sq (x * b i)
    nlinarith
  calc
    rademacherTiltedMean b x =
        ∑ i, b i * Real.tanh (x * b i) := rfl
    _ ≤ ∑ i, x * b i ^ 2 :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = x := by rw [← Finset.mul_sum, hnorm, mul_one]

/-- The tilted partition function is the exponential of the log-cosh sum. -/
theorem rademacherTiltPartition_eq_exp_sum_log_cosh
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ) :
    rademacherTiltPartition x b =
      Real.exp (∑ i, Real.log (Real.cosh (x * b i))) := by
  unfold rademacherTiltPartition
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact (Real.exp_log (Real.cosh_pos _)).symm

/--
The finite tilted expectation is the exponentially weighted strict upper
tail integral of the tilted sum law.
-/
theorem rademacherTiltedUpperExpectation_eq_integral
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ) :
    rademacherTiltedUpperExpectation x b =
      ∫ y in Ioi x, Real.exp (-x * y)
        ∂(rademacherTiltedSumLaw b x) := by
  classical
  rw [← integral_indicator measurableSet_Ioi]
  unfold rademacherTiltedSumLaw
  rw [integral_map
    (measurable_of_finite (rademacherSum b)).aemeasurable
    (((by fun_prop : Measurable (fun y : ℝ => Real.exp (-x * y)))
      |>.indicator measurableSet_Ioi).aestronglyMeasurable)]
  rw [← biasedSignProductExpectation_eq_integral]
  rfl

/--
One-sided Esscher estimate from any direct CDF comparison with the
variance-matched Gaussian law.
-/
theorem rademacherUpperTail_toReal_le_of_cdf
    {ι : Type*} [Fintype ι] (b : ι → ℝ) {x ε : ℝ}
    (hx : 0 < x)
    (hnorm : ∑ i, b i ^ 2 = 1)
    (hCDF : ∀ z,
      |cdf (rademacherTiltedSumLaw b x) z -
          cdf (gaussianReal
            (rademacherTiltedMean b x)
            (NNReal.mk (rademacherTiltedStdDev b x ^ 2)
              (sq_nonneg (rademacherTiltedStdDev b x)))) z| ≤ ε) :
    (eventProbability (rademacherPMF ι)
        (fun bits => x < rademacherSum b bits)).toReal ≤
      rademacherTiltPartition x b *
        (Real.exp
            (-x * rademacherTiltedMean b x +
              x ^ 2 * rademacherTiltedStdDev b x ^ 2 / 2) *
            standardGaussianTail
              ((x - rademacherTiltedMean b x) /
                  rademacherTiltedStdDev b x +
                x * rademacherTiltedStdDev b x) +
          2 * ε * Real.exp (-x ^ 2)) := by
  let μ : Measure ℝ := rademacherTiltedSumLaw b x
  let m : ℝ := rademacherTiltedMean b x
  let s : ℝ := rademacherTiltedStdDev b x
  let ν : Measure ℝ :=
    gaussianReal m (NNReal.mk (s ^ 2) (sq_nonneg s))
  have hs : 0 < s := by
    exact sqrt_rademacherTiltedVariance_pos b x hnorm
  have hCDF' : ∀ z, |cdf μ z - cdf ν z| ≤ ε := by
    simpa only [μ, ν, m, s] using hCDF
  have htransfer :=
    abs_integral_exponential_strictUpper_sub_le
      (μ := μ) (ν := ν) (ε := ε) (a := x) (t := x) hx hCDF'
  have htransfer' :
      |(∫ y in Ioi x, Real.exp (-x * y) ∂μ) -
          (∫ y in Ioi x, Real.exp (-x * y) ∂ν)| ≤
        2 * ε * Real.exp (-x ^ 2) := by
    simpa only [pow_two, neg_mul] using htransfer
  have hμle :
      (∫ y in Ioi x, Real.exp (-x * y) ∂μ) ≤
        (∫ y in Ioi x, Real.exp (-x * y) ∂ν) +
          2 * ε * Real.exp (-x ^ 2) := by
    have hdiff :
        (∫ y in Ioi x, Real.exp (-x * y) ∂μ) -
            (∫ y in Ioi x, Real.exp (-x * y) ∂ν) ≤
          2 * ε * Real.exp (-x ^ 2) :=
      (le_abs_self _).trans htransfer'
    linarith
  rw [rademacherUpperTail_toReal_eq_tilted,
    rademacherTiltedUpperExpectation_eq_integral]
  have hpartition :
      0 ≤ rademacherTiltPartition x b :=
    (rademacherTiltPartition_pos x b).le
  apply mul_le_mul_of_nonneg_left _ hpartition
  calc
    (∫ y in Ioi x, Real.exp (-x * y)
        ∂rademacherTiltedSumLaw b x) =
        ∫ y in Ioi x, Real.exp (-x * y) ∂μ := rfl
    _ ≤ (∫ y in Ioi x, Real.exp (-x * y) ∂ν) +
        2 * ε * Real.exp (-x ^ 2) := hμle
    _ = Real.exp (-x * m + x ^ 2 * s ^ 2 / 2) *
          standardGaussianTail ((x - m) / s + x * s) +
        2 * ε * Real.exp (-x ^ 2) := by
      rw [integral_Ioi_exp_mul_gaussianReal_sq x m x hs]
    _ = _ := by rfl

/--
One-sided Esscher estimate supplied by a Kolmogorov bound for the centered,
variance-normalized tilted sum.
-/
theorem rademacherUpperTail_toReal_le_of_standardized_kolmogorov
    {ι : Type*} [Fintype ι] (b : ι → ℝ) {x ε : ℝ}
    (hx : 0 < x)
    (hnorm : ∑ i, b i ^ 2 = 1)
    (hK :
      kolmogorovDistance
          (rademacherTiltedStandardizedLaw b x)
          (gaussianReal 0 1) ≤ ε) :
    (eventProbability (rademacherPMF ι)
        (fun bits => x < rademacherSum b bits)).toReal ≤
      rademacherTiltPartition x b *
        (Real.exp
            (-x * rademacherTiltedMean b x +
              x ^ 2 * rademacherTiltedStdDev b x ^ 2 / 2) *
            standardGaussianTail
              ((x - rademacherTiltedMean b x) /
                  rademacherTiltedStdDev b x +
                x * rademacherTiltedStdDev b x) +
          2 * ε * Real.exp (-x ^ 2)) := by
  apply rademacherUpperTail_toReal_le_of_cdf b hx hnorm
  exact tiltedCDF_le_of_standardized_kolmogorov b hnorm hK

end Probability
end CertifiedJL
