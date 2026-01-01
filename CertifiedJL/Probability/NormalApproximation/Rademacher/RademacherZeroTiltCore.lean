/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Distributions.Rademacher.RademacherEsscherBound

/-!
# Lightweight zero-tilt Rademacher identities

This module contains only the structural identities that identify the zero-tilt
Rademacher law and Lyapunov ratio.  Keeping them separate from the global
`3/5` Berry--Esseen certificate lets downstream Prawitz developments use the
zero-tilt law without importing the large Tyurin certificate bundle.
-/

open scoped BigOperators ENNReal

open MeasureTheory ProbabilityTheory

namespace CertifiedJL
namespace Probability

universe u

/-- The law of a finite weighted family of uniform Rademacher signs. -/
noncomputable def rademacherSumLaw
    {ι : Type u} [Fintype ι] (b : ι → ℝ) : Measure ℝ :=
  (rademacherPMF ι).toMeasure.map (rademacherSum b)

/-- At zero bias, the finite biased-sign product PMF is uniform. -/
theorem biasedSignProductPMF_zero
    {ι : Type u} [Fintype ι] :
    biasedSignProductPMF (fun _ : ι => (0 : ℝ)) = rademacherPMF ι := by
  apply PMF.ext
  intro bits
  rw [← ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  rw [biasedSignProductPMF_likelihoodRatio]
  simp

/--
For a variance-one profile, the standardized tilted law at zero is exactly
the ordinary weighted Rademacher law.
-/
theorem rademacherTiltedStandardizedLaw_zero
    {ι : Type u} [Fintype ι] (b : ι → ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1) :
    rademacherTiltedStandardizedLaw b 0 = rademacherSumLaw b := by
  unfold rademacherTiltedStandardizedLaw rademacherTiltedSumLaw
    rademacherTiltedMean rademacherTiltedStdDev
    rademacherTiltedVariance rademacherSumLaw
  rw [show biasedSignProductPMF (fun i => 0 * b i) = rademacherPMF ι by
    simpa using (biasedSignProductPMF_zero (ι := ι))]
  simp only [zero_mul, Real.tanh_zero, mul_zero, Finset.sum_const_zero,
    Real.cosh_zero, inv_one, one_pow, mul_one, hnorm, Real.sqrt_one,
    sub_zero, div_one]
  rw [Measure.map_map]
  · rfl
  · fun_prop
  · exact measurable_of_finite _

/-- At zero tilt, the Lyapunov ratio is the absolute third-moment sum. -/
theorem rademacherLyapunovRatio_zero
    {ι : Type u} [Fintype ι] (b : ι → ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1) :
    rademacherLyapunovRatio b 0 = ∑ i, |b i| ^ 3 := by
  unfold rademacherLyapunovRatio rademacherLyapunovNumerator
    rademacherTiltedVariance
  simp only [zero_mul, Real.tanh_zero, Real.cosh_zero, inv_one, one_pow]
  norm_num
  rw [hnorm, Real.sqrt_one, one_pow, div_one]

end Probability
end CertifiedJL
