/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.NormalApproximation.Shared.CDFMetric
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Closed-interval transfer from Kolmogorov distance

Uniform CDF control transfers to a closed interval with a loss of twice the
Kolmogorov error when the comparator has no atom at the lower endpoint. The
source measure may have atoms, so the proof uses the left limit of its CDF;
replacing the closed interval by `(a, b]` would lose precisely this boundary
information.
-/

open MeasureTheory ProbabilityTheory Set Filter Function

namespace CertifiedJL
namespace Probability

/-- A closed interval is the difference between a CDF value and a CDF left limit. -/
theorem probability_Icc_eq_cdf_sub_leftLim
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a b : ℝ} (hab : a ≤ b) :
    μ.real (Icc a b) = cdf μ b - leftLim (cdf μ) a := by
  calc
    μ.real (Icc a b) = (cdf μ).measure.real (Icc a b) :=
      congrArg (fun ρ : Measure ℝ => ρ.real (Icc a b))
        (measure_cdf μ).symm
    _ = cdf μ b - leftLim (cdf μ) a := by
      rw [measureReal_def, StieltjesFunction.measure_Icc]
      rw [ENNReal.toReal_ofReal]
      exact sub_nonneg.mpr
        (((cdf μ).mono.leftLim_le le_rfl).trans ((cdf μ).mono hab))

/-- A CDF has no jump from the left at a point carrying no mass. -/
theorem cdf_leftLim_eq_of_measure_singleton_eq_zero
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {a : ℝ}
    (ha : ν {a} = 0) :
    leftLim (cdf ν) a = cdf ν a := by
  have hmeasure : (cdf ν).measure {a} = 0 := by
    rw [measure_cdf ν]
    exact ha
  rw [StieltjesFunction.measure_singleton] at hmeasure
  have hle : cdf ν a - leftLim (cdf ν) a ≤ 0 :=
    ENNReal.ofReal_eq_zero.mp hmeasure
  have hge : 0 ≤ cdf ν a - leftLim (cdf ν) a :=
    sub_nonneg.mpr ((cdf ν).mono.leftLim_le le_rfl)
  linarith

/--
Kolmogorov control transfers to a closed interval when the comparator has no
atom at the lower endpoint. The source measure is allowed to have an atom at
either endpoint.
-/
theorem probability_Icc_le_add_two_mul_of_kolmogorovDistance
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    {δ a b : ℝ} (hab : a ≤ b) (hνa : ν {a} = 0)
    (hK : kolmogorovDistance μ ν ≤ δ) :
    μ.real (Icc a b) ≤ ν.real (Icc a b) + 2 * δ := by
  have hpoint (x : ℝ) : |cdf μ x - cdf ν x| ≤ δ :=
    (cdfAbsoluteDiscrepancy_le_kolmogorovDistance μ ν x).trans hK
  have hupper (x : ℝ) : cdf μ x ≤ cdf ν x + δ := by
    have h := (abs_le.mp (hpoint x)).2
    linarith
  have hlower (x : ℝ) : cdf ν x - δ ≤ cdf μ x := by
    have h := (abs_le.mp (hpoint x)).1
    linarith
  have hleft : leftLim (cdf ν) a - δ ≤ leftLim (cdf μ) a := by
    apply le_of_tendsto_of_tendsto'
      ((cdf ν).mono.tendsto_leftLim a |>.sub tendsto_const_nhds)
      ((cdf μ).mono.tendsto_leftLim a)
    exact hlower
  have hcontinuous :=
    cdf_leftLim_eq_of_measure_singleton_eq_zero ν hνa
  rw [hcontinuous] at hleft
  rw [probability_Icc_eq_cdf_sub_leftLim μ hab,
    probability_Icc_eq_cdf_sub_leftLim ν hab, hcontinuous]
  linarith [hupper b]

/-- Closed-interval transfer against any atomless comparator. -/
theorem probability_Icc_le_add_two_mul_of_kolmogorovDistance_of_atomless
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [NullSingletonClass ν]
    {δ a b : ℝ} (hab : a ≤ b)
    (hK : kolmogorovDistance μ ν ≤ δ) :
    μ.real (Icc a b) ≤ ν.real (Icc a b) + 2 * δ :=
  probability_Icc_le_add_two_mul_of_kolmogorovDistance
    μ ν hab (measure_singleton a) hK

/-- Closed-interval transfer against the standard Gaussian law. -/
theorem probability_Icc_le_standardGaussian_add_two_mul
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ a b : ℝ} (hab : a ≤ b)
    (hK : kolmogorovDistance μ (gaussianReal 0 1) ≤ δ) :
    μ.real (Icc a b) ≤
      (gaussianReal 0 1).real (Icc a b) + 2 * δ := by
  let : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  exact
    probability_Icc_le_add_two_mul_of_kolmogorovDistance_of_atomless
      μ (gaussianReal 0 1) hab hK

end Probability
end CertifiedJL
