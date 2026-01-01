/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib

/-!
# Elementary inequalities for finite power sums

These dimension-free inequalities are independent of any tail threshold or
projection endpoint.
-/

open scoped BigOperators

namespace CertifiedJL.Probability

/-- The `k`th power sum of a finite real family. -/
noncomputable def powerSum {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (k : ℕ) : ℝ := ∑ i, x i ^ k

theorem powerSum_nonneg {ι : Type*} [Fintype ι]
    {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (k : ℕ) :
    0 ≤ powerSum x k := by
  unfold powerSum
  exact Finset.sum_nonneg fun i _ => pow_nonneg (hx i) k

theorem powerSum_two_sq_le_powerSum_three
    {ι : Type*} [Fintype ι] {x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1) :
    powerSum x 2 ^ 2 ≤ powerSum x 3 := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
    (fun i => Real.sqrt (x i)) (fun i => x i * Real.sqrt (x i))
  have hleft :
      (∑ i, Real.sqrt (x i) * (x i * Real.sqrt (x i))) =
        ∑ i, x i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [show Real.sqrt (x i) * (x i * Real.sqrt (x i)) =
      x i * (Real.sqrt (x i)) ^ 2 by ring, Real.sq_sqrt (hx i)]
    ring
  have hfirst : (∑ i, (Real.sqrt (x i)) ^ 2) = ∑ i, x i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.sq_sqrt (hx i)]
  have hsecond :
      (∑ i, (x i * Real.sqrt (x i)) ^ 2) = ∑ i, x i ^ 3 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow, Real.sq_sqrt (hx i)]
    ring
  rw [hleft, hfirst, hsecond, hsum, one_mul] at hcs
  simpa only [powerSum] using hcs

theorem powerSum_two_le_max
    {ι : Type*} [Fintype ι] {x : ι → ℝ} {m : ℝ}
    (hx : ∀ i, 0 ≤ x i) (hle : ∀ i, x i ≤ m)
    (hsum : ∑ i, x i = 1) :
    powerSum x 2 ≤ m := by
  unfold powerSum
  calc
    (∑ i, x i ^ 2) ≤ ∑ i, m * x i := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [hx i, hle i]
    _ = m := by rw [← Finset.mul_sum, hsum, mul_one]

theorem powerSum_three_le_max_mul_two
    {ι : Type*} [Fintype ι] {x : ι → ℝ} {m : ℝ}
    (hx : ∀ i, 0 ≤ x i) (hle : ∀ i, x i ≤ m) :
    powerSum x 3 ≤ m * powerSum x 2 := by
  unfold powerSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [hx i, hle i, sq_nonneg (x i)]

theorem powerSum_five_le_max_mul_four
    {ι : Type*} [Fintype ι] {x : ι → ℝ} {m : ℝ}
    (hx : ∀ i, 0 ≤ x i) (hle : ∀ i, x i ≤ m) :
    powerSum x 5 ≤ m * powerSum x 4 := by
  unfold powerSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h4 : 0 ≤ x i ^ 4 := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr (hle i)) h4]

theorem powerSum_four_le_max_sq_mul_two
    {ι : Type*} [Fintype ι] {x : ι → ℝ} {m : ℝ}
    (hx : ∀ i, 0 ≤ x i) (hle : ∀ i, x i ≤ m) :
    powerSum x 4 ≤ m ^ 2 * powerSum x 2 := by
  unfold powerSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hm0 : 0 ≤ m := (hx i).trans (hle i)
  have hsq : x i ^ 2 ≤ m ^ 2 := (sq_le_sq₀ (hx i) hm0).2 (hle i)
  calc
    x i ^ 4 = x i ^ 2 * x i ^ 2 := by ring
    _ ≤ m ^ 2 * x i ^ 2 :=
      mul_le_mul_of_nonneg_right hsq (sq_nonneg (x i))

theorem max_cube_le_powerSum_three
    {ι : Type*} [Fintype ι] {x : ι → ℝ} {m : ℝ}
    (hx : ∀ i, 0 ≤ x i) (hmax : ∃ i, x i = m) :
    m ^ 3 ≤ powerSum x 3 := by
  obtain ⟨i, hi⟩ := hmax
  rw [← hi]
  unfold powerSum
  exact Finset.single_le_sum (fun j _ => pow_nonneg (hx j) 3)
    (Finset.mem_univ i)

end CertifiedJL.Probability
