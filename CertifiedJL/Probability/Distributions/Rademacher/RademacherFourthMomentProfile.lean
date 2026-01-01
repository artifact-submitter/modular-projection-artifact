/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The fourth-moment profile of a normalized coefficient vector

For a finite real coefficient vector `b`, the profile parameter

`B = sqrt (sqrt (∑ i, b i ^ 4))`

is the nonnegative fourth root of its fourth moment.  This file packages the
elementary facts needed by the coefficient-uniform Rademacher tail bound:
each coefficient has absolute value at most `B`, and a vector of squared norm
one has `B ≤ 1`.
-/

open scoped BigOperators

namespace CertifiedJL
namespace Probability

/-- The nonnegative fourth root of the fourth moment of `b`. -/
noncomputable def rademacherFourthMomentProfile
    {ι : Type*} [Fintype ι] (b : ι → ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (∑ i, b i ^ 4))

theorem rademacherFourthMoment_nonneg
    {ι : Type*} [Fintype ι] (b : ι → ℝ) :
    0 ≤ ∑ i, b i ^ 4 :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem rademacherFourthMomentProfile_nonneg
    {ι : Type*} [Fintype ι] (b : ι → ℝ) :
    0 ≤ rademacherFourthMomentProfile b := by
  exact Real.sqrt_nonneg _

theorem rademacherFourthMomentProfile_pow_four
    {ι : Type*} [Fintype ι] (b : ι → ℝ) :
    rademacherFourthMomentProfile b ^ 4 = ∑ i, b i ^ 4 := by
  let ρ : ℝ := ∑ i, b i ^ 4
  have hρ : 0 ≤ ρ := rademacherFourthMoment_nonneg b
  have hsqrtρ : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg _
  change Real.sqrt (Real.sqrt ρ) ^ 4 = ρ
  calc
    Real.sqrt (Real.sqrt ρ) ^ 4 =
        (Real.sqrt (Real.sqrt ρ) ^ 2) ^ 2 := by ring
    _ = (Real.sqrt ρ) ^ 2 := by rw [Real.sq_sqrt hsqrtρ]
    _ = ρ := Real.sq_sqrt hρ

theorem abs_le_rademacherFourthMomentProfile
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (i : ι) :
    |b i| ≤ rademacherFourthMomentProfile b := by
  have hterm :
      b i ^ 4 ≤ ∑ j, b j ^ 4 := by
    exact Finset.single_le_sum (f := fun j => b j ^ 4)
      (fun j _ => by positivity) (Finset.mem_univ i)
  apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num)
    (rademacherFourthMomentProfile_nonneg b)
  have habs : |b i| ^ 4 = b i ^ 4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity)]
  rw [habs, rademacherFourthMomentProfile_pow_four]
  exact hterm

theorem rademacherFourthMoment_le_one
    {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1) :
    ∑ i, b i ^ 4 ≤ 1 := by
  calc
    ∑ i, b i ^ 4 ≤ ∑ i, b i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi :
          b i ^ 2 ≤ ∑ j, b j ^ 2 := by
        exact Finset.single_le_sum (f := fun j => b j ^ 2)
          (fun j _ => sq_nonneg (b j)) (Finset.mem_univ i)
      rw [hnorm] at hi
      nlinarith [sq_nonneg (b i)]
    _ = 1 := hnorm

theorem rademacherFourthMomentProfile_le_one
    {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1) :
    rademacherFourthMomentProfile b ≤ 1 := by
  apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by norm_num)
  rw [rademacherFourthMomentProfile_pow_four, one_pow]
  exact rademacherFourthMoment_le_one b hnorm

end Probability
end CertifiedJL
