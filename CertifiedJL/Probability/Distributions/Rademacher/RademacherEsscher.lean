/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Distributions.Rademacher.BiasedSignProduct

/-!
# Exact Esscher identity for finite Rademacher sums

This file performs the change of measure used by the sparse one-row proof.
Everything is an equality of finite sums: no Radon--Nikodym or
almost-everywhere side condition is hidden in the API.
-/

open scoped BigOperators

namespace CertifiedJL
namespace Probability

/-- The moment-generating partition function of a Rademacher sum. -/
noncomputable def rademacherTiltPartition
    {ι : Type*} [Fintype ι] (x : ℝ) (a : ι → ℝ) : ℝ :=
  ∏ i, Real.cosh (x * a i)

/-- The product partition function is strictly positive. -/
theorem rademacherTiltPartition_pos
    {ι : Type*} [Fintype ι] (x : ℝ) (a : ι → ℝ) :
    0 < rademacherTiltPartition x a := by
  unfold rademacherTiltPartition
  exact Finset.prod_pos fun i _ => Real.cosh_pos (x * a i)

/-- The exponentially weighted strict upper-tail observable. -/
noncomputable def rademacherTiltedUpperObservable
    {ι : Type*} [Fintype ι] (x : ℝ) (a : ι → ℝ)
    (bits : ι → Bool) : ℝ :=
  if x < rademacherSum a bits then
    Real.exp (-x * rademacherSum a bits)
  else 0

/-- The strict upper tail, represented as an expectation under the tilt. -/
noncomputable def rademacherTiltedUpperExpectation
    {ι : Type*} [Fintype ι] (x : ℝ) (a : ι → ℝ) : ℝ :=
  biasedSignProductExpectation (fun i => x * a i)
    (rademacherTiltedUpperObservable x a)

/--
Exact finite Esscher change of measure for a strict Rademacher upper tail.
-/
theorem rademacherUpperTail_toReal_eq_tilted
    {ι : Type*} [Fintype ι] (x : ℝ) (a : ι → ℝ) :
    (eventProbability (rademacherPMF ι)
      (fun bits => x < rademacherSum a bits)).toReal =
      rademacherTiltPartition x a *
        rademacherTiltedUpperExpectation x a := by
  classical
  rw [eventProbability_toReal_eq_sum]
  unfold rademacherTiltedUpperExpectation
    biasedSignProductExpectation
  rw [tsum_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro bits _
  rw [biasedSignProductPMF_likelihoodRatio_rademacherSum]
  unfold rademacherTiltedUpperObservable rademacherTiltPartition
  by_cases htail : x < rademacherSum a bits
  · simp only [htail, if_true]
    have hpartition :
        (∏ i, Real.cosh (x * a i)) ≠ 0 :=
      (rademacherTiltPartition_pos x a).ne'
    field_simp [hpartition]
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
    simp
  · simp only [htail, if_false, mul_zero]

end Probability
end CertifiedJL
