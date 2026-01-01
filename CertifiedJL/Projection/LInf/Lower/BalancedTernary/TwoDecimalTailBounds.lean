/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Finite.PMF
import CertifiedJL.Analysis.SmoothBounds.PowerSums
import CertifiedJL.Probability.Distributions.Rademacher.RademacherExactMoments

/-!
# Shared polynomial and eighth-moment tails for two-decimal lower bounds
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace CertifiedJL.SparseLInfLowerTwoDecimal

open Probability

theorem radMoment_eight_le_gaussian
    {n : ℕ} (a : Fin n → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) :
    radMoment a 8 ≤ 105 := by
  let x : Fin n → ℝ := fun i => a i ^ 2
  have hx : ∀ i, 0 ≤ x i := fun i => sq_nonneg _
  have hxsum : ∑ i, x i = 1 := ha
  have h23 : powerSum x 2 ^ 2 ≤ powerSum x 3 :=
    powerSum_two_sq_le_powerSum_three hx hxsum
  have hpoly : 0 ≤
      420 * powerSum x 2 - 588 * powerSum x 3 + 272 * powerSum x 4 := by
    unfold powerSum
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_nonneg
    intro i _
    dsimp [x]
    nlinarith [sq_nonneg (136 * (a i) ^ 2 - 147)]
  rw [radMoment_eight_exact]
  change 105 * powerSum x 1 ^ 4 - 420 * powerSum x 1 ^ 2 * powerSum x 2 +
      448 * powerSum x 1 * powerSum x 3 + 140 * powerSum x 2 ^ 2 -
        272 * powerSum x 4 ≤ 105
  have hP1 : powerSum x 1 = 1 := by
    simpa only [powerSum, pow_one] using hxsum
  rw [hP1]
  norm_num
  nlinarith

theorem radMoment_eight_le_gaussian_fintype
    {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) :
    radMoment a 8 ≤ 105 := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let a' : Fin (Fintype.card ι) → ℝ := fun i => a (e i)
  have ha' : ∑ i, a' i ^ 2 = 1 := by
    dsimp [a']
    rw [Equiv.sum_comp e (fun i => a i ^ 2)]
    exact ha
  calc
    radMoment a 8 = radMoment a' 8 := (radMoment_equiv e a 8).symm
    _ ≤ 105 := radMoment_eight_le_gaussian a' ha'

theorem rademacherSum_normalized_tail_389_over_50_toReal_lt_fintype
    {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) :
    (eventProbability (rademacherPMF ι)
      (fun bits => (389 / 50 : ℝ) ≤ (rademacherSum a bits) ^ 2)).toReal <
        287 / 10000 := by
  classical
  let event : (ι → Bool) → Prop := fun bits =>
    (389 / 50 : ℝ) ≤ (rademacherSum a bits) ^ 2
  let F : (ι → Bool) → ℝ := fun bits =>
    (rademacherSum a bits) ^ 8 / (389 / 50 : ℝ) ^ 4
  have hpoint (bits : ι → Bool) :
      (if event bits then (1 : ℝ) else 0) ≤ F bits := by
    by_cases he : event bits
    · rw [if_pos he]
      dsimp only [F]
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < (389 / 50 : ℝ) ^ 4)).2
      have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 389 / 50)
        he 4
      simpa only [one_mul, ← pow_mul] using hpow
    · rw [if_neg he]
      dsimp only [F]
      positivity
  have hprob := finitePMF_eventProbability_toReal_le_integral
    (rademacherPMF ι) event F hpoint
  have hE := radMoment_eight_le_gaussian_fintype a ha
  have hintegral :
      (∫ bits, F bits ∂(rademacherPMF ι).toMeasure) =
        radMoment a 8 / (389 / 50 : ℝ) ^ 4 := by
    dsimp only [F]
    rw [integral_div, integral_rademacher_eq_expect_fintype]
    rfl
  rw [hintegral] at hprob
  have hdiv := div_le_div_of_nonneg_right hE
    (by positivity : (0 : ℝ) ≤ (389 / 50 : ℝ) ^ 4)
  exact hprob.trans_lt (hdiv.trans_lt (by norm_num))

theorem rademacherSum_normalized_tail_36567_over_5000_toReal_lt_fintype
    {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) :
    (eventProbability (rademacherPMF ι)
      (fun bits ↦ (36567 / 5000 : ℝ) ≤ (rademacherSum a bits) ^ 2)).toReal <
        367039 / 10000000 := by
  classical
  let event : (ι → Bool) → Prop := fun bits ↦
    (36567 / 5000 : ℝ) ≤ (rademacherSum a bits) ^ 2
  let F : (ι → Bool) → ℝ := fun bits ↦
    (rademacherSum a bits) ^ 8 / (36567 / 5000 : ℝ) ^ 4
  have hpoint (bits : ι → Bool) :
      (if event bits then (1 : ℝ) else 0) ≤ F bits := by
    by_cases he : event bits
    · rw [if_pos he]
      dsimp only [F]
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < (36567 / 5000 : ℝ) ^ 4)).2
      have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 36567 / 5000)
        he 4
      simpa only [one_mul, ← pow_mul] using hpow
    · rw [if_neg he]
      dsimp only [F]
      positivity
  have hprob := finitePMF_eventProbability_toReal_le_integral
    (rademacherPMF ι) event F hpoint
  have hE := radMoment_eight_le_gaussian_fintype a ha
  have hintegral :
      (∫ bits, F bits ∂(rademacherPMF ι).toMeasure) =
        radMoment a 8 / (36567 / 5000 : ℝ) ^ 4 := by
    dsimp only [F]
    rw [integral_div, integral_rademacher_eq_expect_fintype]
    rfl
  rw [hintegral] at hprob
  have hdiv := div_le_div_of_nonneg_right hE
    (by positivity : (0 : ℝ) ≤ (36567 / 5000 : ℝ) ^ 4)
  exact hprob.trans_lt (hdiv.trans_lt (by norm_num))

end CertifiedJL.SparseLInfLowerTwoDecimal
