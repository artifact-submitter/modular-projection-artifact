/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Distributions.Rademacher.RademacherEntropyProfile
import CertifiedJL.Probability.Distributions.Rademacher.RademacherSubgaussian

/-!
# Entropy-aware Chernoff bound for Rademacher profiles

This is the elementary large-profile branch used by the sparse one-row
theorem.  It keeps the exact product-cosh moment generating function and the
fourth-moment entropy defect instead of discarding both in the generic
subgaussian estimate.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory Set

namespace CertifiedJL
namespace Probability

universe u

/--
At tilt `x`, a normalized Rademacher profile with fourth-root parameter `B`
has strict upper tail at most
`exp (-x²/2 - rademacherEntropyDefect (xB))`.
-/
theorem rademacherSum_upperTail_toReal_le_entropyProfile
    {ι : Type u} [Fintype ι] (b : ι → ℝ) {x B : ℝ}
    (hx : 0 ≤ x) (hB : 0 ≤ B)
    (hnorm : ∑ i, b i ^ 2 = 1)
    (hbound : ∀ i, |b i| ≤ B)
    (hfourth : ∑ i, b i ^ 4 = B ^ 4) :
    (eventProbability (rademacherPMF ι)
        (fun bits => x < rademacherSum b bits)).toReal ≤
      Real.exp (-x ^ 2 / 2 - rademacherEntropyDefect (x * B)) := by
  have hmarkov := measure_ge_le_exp_mul_mgf
    (μ := (rademacherPMF ι).toMeasure)
    (X := rademacherSum b) x hx (Integrable.of_finite)
  have hlog :=
    sum_log_cosh_sub_quadratic_le b hx hB hbound hfourth
  have hsquare :
      ∑ i, (x * b i) ^ 2 = x ^ 2 := by
    simp only [mul_pow]
    rw [← Finset.mul_sum, hnorm, mul_one]
  have hsum :
      ∑ i, Real.log (Real.cosh (x * b i)) ≤
        x ^ 2 / 2 - rademacherEntropyDefect (x * B) := by
    rw [Finset.sum_sub_distrib] at hlog
    have hsquareHalf :
        (∑ i, (x * b i) ^ 2 / 2) = x ^ 2 / 2 := by
      rw [← Finset.sum_div, hsquare]
    rw [hsquareHalf] at hlog
    linarith
  have hmgf :
      mgf (rademacherSum b) (rademacherPMF ι).toMeasure x ≤
        Real.exp (x ^ 2 / 2 - rademacherEntropyDefect (x * B)) := by
    rw [mgf, rademacherSum_integral_exp_eq_prod_cosh]
    rw [show (∏ i, Real.cosh (x * b i)) =
        Real.exp (∑ i, Real.log (Real.cosh (x * b i))) by
      rw [Real.exp_sum]
      apply Finset.prod_congr rfl
      intro i _
      exact (Real.exp_log (Real.cosh_pos _)).symm]
    exact Real.exp_le_exp.mpr hsum
  rw [eventProbability_eq_toMeasure]
  calc
    (rademacherPMF ι).toMeasure.real
        {bits | x < rademacherSum b bits} ≤
      (rademacherPMF ι).toMeasure.real
        {bits | x ≤ rademacherSum b bits} := by
          apply measureReal_mono
          · intro bits hbits
            change x < rademacherSum b bits at hbits
            change x ≤ rademacherSum b bits
            exact hbits.le
          · exact measure_ne_top _ _
    _ ≤ Real.exp (-x * x) *
          mgf (rademacherSum b) (rademacherPMF ι).toMeasure x := hmarkov
    _ ≤ Real.exp (-x * x) *
          Real.exp (x ^ 2 / 2 - rademacherEntropyDefect (x * B)) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
    _ = Real.exp (-x ^ 2 / 2 - rademacherEntropyDefect (x * B)) := by
      rw [← Real.exp_add]
      congr 1
      ring

end Probability
end CertifiedJL
