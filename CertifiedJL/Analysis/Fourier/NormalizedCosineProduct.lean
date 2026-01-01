/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Fourier.ElementaryCosineSmallBall

/-!
# Normalized cosine-product bounds

This module tensorizes the elementary pointwise cosine bound over a normalized
Euclidean vector at an arbitrary frequency below `π/2`.
-/

open scoped BigOperators

namespace CertifiedJL.Probability

/-- The cosine-square product of a normalized vector is subgaussian. -/
theorem normalized_cosineProduct_le_exp_neg_sq {d : ℕ}
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ≠ 0) {α : ℝ}
    (hα0 : 0 ≤ α) (hαpi : α < Real.pi / 2) :
    (∏ i, Real.cos (α * v i / ‖v‖) ^ 2) ≤ Real.exp (-(α ^ 2)) := by
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hfactor (i : Fin d) :
      Real.cos (α * v i / ‖v‖) ^ 2 ≤
        Real.exp (-((α * v i / ‖v‖) ^ 2)) := by
    apply CertifiedJL.cos_sq_le_exp_neg_sq
    have hcoord := CertifiedJL.abs_coord_le_norm v i
    rw [abs_div, abs_mul, abs_of_nonneg hα0, abs_of_pos hn]
    apply lt_of_le_of_lt _ hαpi
    apply (div_le_iff₀ hn).2
    nlinarith
  calc
    (∏ i, Real.cos (α * v i / ‖v‖) ^ 2) ≤
        ∏ i, Real.exp (-((α * v i / ‖v‖) ^ 2)) :=
      Finset.prod_le_prod (fun _ _ => sq_nonneg _) (fun i _ => hfactor i)
    _ = Real.exp (∑ i, -((α * v i / ‖v‖) ^ 2)) := by rw [Real.exp_sum]
    _ = Real.exp (-(α ^ 2)) := by
      congr 1
      rw [Finset.sum_neg_distrib]
      simp_rw [div_pow, mul_pow]
      rw [← Finset.sum_div, ← Finset.mul_sum,
        ← EuclideanSpace.real_norm_sq_eq]
      field_simp [hn.ne']

end CertifiedJL.Probability
