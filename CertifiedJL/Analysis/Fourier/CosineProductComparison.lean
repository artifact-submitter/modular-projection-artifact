/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Fourier.CosineGaussianComparison

/-!
# Product cosine--Gaussian comparison

This file lifts the scalar cosine--Gaussian comparison (S2) to the finite
product estimate used by Gaussian replacement (S1).  The proof is the exact
telescoping argument from Section 05b of the Certified JL paper.
-/

namespace CertifiedJL

open scoped BigOperators

private theorem abs_prod_sub_prod_le_sum {ι : Type*}
    (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, |f i| ≤ 1) (hg : ∀ i ∈ s, |g i| ≤ 1) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfs : |∏ i ∈ s, f i| ≤ 1 := by
        rw [Finset.abs_prod]
        simpa using Finset.prod_le_one (fun i hi => abs_nonneg (f i))
          (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      have hga : |g a| ≤ 1 := hg a (Finset.mem_insert_self _ _)
      have hi := ih
        (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      calc
        |(∏ i ∈ insert a s, f i) - ∏ i ∈ insert a s, g i| =
            |(f a - g a) * (∏ i ∈ s, f i) +
              g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| := by
          simp only [Finset.prod_insert ha]
          congr 1
          ring
        _ ≤ |(f a - g a) * (∏ i ∈ s, f i)| +
              |g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| := abs_add_le _ _
        _ = |f a - g a| * |∏ i ∈ s, f i| +
              |g a| * |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| := by
          rw [abs_mul, abs_mul]
        _ ≤ |f a - g a| * 1 + 1 * (∑ i ∈ s, |f i - g i|) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hfs (abs_nonneg _))
            (mul_le_mul hga hi (abs_nonneg _) zero_le_one)
        _ = ∑ i ∈ insert a s, |f i - g i| := by simp [ha]

/-- **Finite cosine--Gaussian telescope (S1/S2).**  For arbitrary real
coefficients, the characteristic function of their independent sign sum
differs from the centered Gaussian characteristic function with matching
variance by at most the fourth-power replacement cost.

This is the pointwise estimate in the proof of (S1), before integrating
against the Gaussian Fourier kernel. -/
theorem abs_prod_cos_sub_exp_neg_sum_sq_half_le {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (t : ℝ) :
    |(∏ i, Real.cos (c i * t)) -
        Real.exp (-(∑ i, c i ^ 2) * t ^ 2 / 2)| ≤
      (∑ i, c i ^ 4) * t ^ 4 / 12 := by
  classical
  have hgauss :
      (∏ i, Real.exp (-((c i * t) ^ 2) / 2)) =
        Real.exp (-(∑ i, c i ^ 2) * t ^ 2 / 2) := by
    rw [← Real.exp_sum]
    congr 1
    simp_rw [mul_pow]
    rw [show (∑ i, -(c i ^ 2 * t ^ 2) / 2) =
        (∑ i, c i ^ 2) * (-t ^ 2 / 2) by
      calc
        _ = ∑ i, c i ^ 2 * (-t ^ 2 / 2) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := (Finset.sum_mul Finset.univ (fun i => c i ^ 2)
          (-t ^ 2 / 2)).symm]
    ring
  calc
    |(∏ i, Real.cos (c i * t)) -
        Real.exp (-(∑ i, c i ^ 2) * t ^ 2 / 2)| =
        |(∏ i, Real.cos (c i * t)) -
          ∏ i, Real.exp (-((c i * t) ^ 2) / 2)| := by rw [hgauss]
    _ ≤ ∑ i, |Real.cos (c i * t) -
          Real.exp (-((c i * t) ^ 2) / 2)| := by
      simpa only [Finset.prod_const_one, Finset.card_univ, one_pow,
        Finset.sum_const_zero] using
        (abs_prod_sub_prod_le_sum Finset.univ
          (fun i => Real.cos (c i * t))
          (fun i => Real.exp (-((c i * t) ^ 2) / 2))
          (fun i _ => Real.abs_cos_le_one (c i * t))
          (fun i _ => by
            rw [abs_of_pos (Real.exp_pos _)]
            exact Real.exp_le_one_iff.mpr (by
              nlinarith [sq_nonneg (c i * t)])))
    _ ≤ ∑ i, (c i * t) ^ 4 / 12 := by
      exact Finset.sum_le_sum fun i _ =>
        abs_cos_sub_exp_neg_half_sq_le (c i * t)
    _ = (∑ i, c i ^ 4) * t ^ 4 / 12 := by
      simp_rw [mul_pow]
      rw [show (∑ i, c i ^ 4 * t ^ 4 / 12) =
          (∑ i, c i ^ 4) * (t ^ 4 / 12) by
        calc
          _ = ∑ i, c i ^ 4 * (t ^ 4 / 12) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = _ := (Finset.sum_mul Finset.univ (fun i => c i ^ 4)
            (t ^ 4 / 12)).symm]
      ring

end CertifiedJL
