/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperRow
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic

/-!
# Normalization of the doubled-sign sparse profile

The sparse entry `(ε₁ + ε₂) / 2` is represented by two independent signs with
coefficient `aᵢ / 2`.  This file records the exact finite profile identities
needed by the fourth-order row comparison.  In particular, the variance is
`1/2`, the duplicated fourth profile is `r/8`, and the duplicated sixth profile
is the sixth profile of `a` divided by `32`.

These are proved identities for the coefficient representation, rather than
casts of the variance constant.  They are the first production consumer of
`sparseNormalizedVariance`.
-/

open scoped BigOperators

namespace CertifiedJL

/- The finite power-sum estimate is kept local to this sparse normalization
   boundary so the upper-row module does not depend on an unrelated normal
   approximation implementation. -/
private theorem sparseUpper_sum_rpow_le_rpow_sum
    {ι : Type*} (s : Finset ι) (f : ι → ℝ) {p : ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hp : 1 ≤ p) :
    ∑ i ∈ s, f i ^ p ≤ (∑ i ∈ s, f i) ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using Real.zero_rpow_nonneg p
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      have hfi : 0 ≤ f i := hf i (Finset.mem_insert_self i s)
      have hsum : 0 ≤ ∑ j ∈ s, f j :=
        Finset.sum_nonneg fun j hj =>
          hf j (Finset.mem_insert_of_mem hj)
      calc
        f i ^ p + ∑ j ∈ s, f j ^ p ≤
            f i ^ p + (∑ j ∈ s, f j) ^ p := by
          gcongr
          exact ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
        _ ≤ (f i + ∑ j ∈ s, f j) ^ p :=
          Real.add_rpow_le_rpow_add hfi hsum hp

/-- The coefficient of either duplicated sign underlying a normalized sparse row. -/
noncomputable def sparseUpperDuplicatedCoefficient {d : ℕ} (a : Fin d → ℝ)
    (p : Fin d × Fin 2) : ℝ :=
  a p.1 / 2

theorem sum_sq_sparseUpperDuplicatedCoefficient
    {d : ℕ} (a : Fin d → ℝ)
    (hsq : ∑ i, a i ^ 2 = 1) :
    ∑ p : Fin d × Fin 2,
        sparseUpperDuplicatedCoefficient a p ^ 2 =
      (sparseNormalizedVariance : ℝ) := by
  norm_num [sparseNormalizedVariance]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, sparseUpperDuplicatedCoefficient]
  calc
    (∑ x, ((a x / 2) ^ 2 + (a x / 2) ^ 2)) =
        ∑ x, (a x ^ 2 / 2) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = (∑ x, a x ^ 2) / 2 := by rw [Finset.sum_div]
    _ = (1 / 2 : ℝ) := by rw [hsq]

theorem sum_fourth_sparseUpperDuplicatedCoefficient
    {d : ℕ} (a : Fin d → ℝ) :
    ∑ p : Fin d × Fin 2,
        sparseUpperDuplicatedCoefficient a p ^ 4 =
      sparseProfileFourthMoment a / 8 := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, sparseUpperDuplicatedCoefficient,
    sparseProfileFourthMoment]
  calc
    (∑ x, ((a x / 2) ^ 4 + (a x / 2) ^ 4)) =
        ∑ x, (a x ^ 4 / 8) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = (∑ x, a x ^ 4) / 8 := by rw [Finset.sum_div]

theorem sum_sixth_sparseUpperDuplicatedCoefficient
    {d : ℕ} (a : Fin d → ℝ) :
    ∑ p : Fin d × Fin 2,
        sparseUpperDuplicatedCoefficient a p ^ 6 =
      (∑ i, a i ^ 6) / 32 := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, sparseUpperDuplicatedCoefficient]
  calc
    (∑ x, ((a x / 2) ^ 6 + (a x / 2) ^ 6)) =
        ∑ x, (a x ^ 6 / 32) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = (∑ x, a x ^ 6) / 32 := by rw [Finset.sum_div]

theorem sum_sixth_sparseUpperDuplicatedCoefficient_le
    {d : ℕ} (a : Fin d → ℝ) :
    ∑ p : Fin d × Fin 2,
        sparseUpperDuplicatedCoefficient a p ^ 6 ≤
      (sparseProfileFourthMoment a *
          Real.sqrt (sparseProfileFourthMoment a)) / 32 := by
  rw [sum_sixth_sparseUpperDuplicatedCoefficient,
    sparseProfileFourthMoment]
  have hfour_nonneg : 0 ≤ ∑ i, a i ^ 4 := by positivity
  have hterm (i : Fin d) :
      a i ^ 6 ≤ (a i ^ 4) ^ (3 / 2 : ℝ) := by
    have hsqrt : Real.sqrt (a i ^ 4) = a i ^ 2 := by
      rw [show a i ^ 4 = (a i ^ 2) ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hrpow :
        (a i ^ 4) ^ (3 / 2 : ℝ) = a i ^ 4 * a i ^ 2 := by
      rw [show (3 / 2 : ℝ) = 1 + (1 / 2 : ℝ) by norm_num,
        Real.rpow_add' (by positivity) (by norm_num), Real.rpow_one,
        ← Real.sqrt_eq_rpow, hsqrt]
    calc
      a i ^ 6 ≤ a i ^ 6 := le_refl _
      _ = a i ^ 4 * a i ^ 2 := by ring
      _ = (a i ^ 4) ^ (3 / 2 : ℝ) := hrpow.symm
  have hsum :
      (∑ i, a i ^ 6) ≤ ∑ i, (a i ^ 4) ^ (3 / 2 : ℝ) :=
    Finset.sum_le_sum (fun i _ => hterm i)
  have hpower :
      (∑ i, (a i ^ 4) ^ (3 / 2 : ℝ)) ≤
        (∑ i, a i ^ 4) ^ (3 / 2 : ℝ) := by
    simpa using
      (sparseUpper_sum_rpow_le_rpow_sum Finset.univ
      (fun i : Fin d => a i ^ 4)
      (fun i _ => by positivity)
      (by norm_num : (1 : ℝ) ≤ 3 / 2))
  have hroot :
      (∑ i, a i ^ 4) ^ (3 / 2 : ℝ) =
        (∑ i, a i ^ 4) * Real.sqrt (∑ i, a i ^ 4) := by
    rw [show (3 / 2 : ℝ) = 1 + (1 / 2 : ℝ) by norm_num]
    rw [Real.rpow_add' hfour_nonneg (by norm_num)]
    rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hpower' :
      (∑ i, (a i ^ 4) ^ (3 / 2 : ℝ)) ≤
        (∑ i, a i ^ 4) * Real.sqrt (∑ i, a i ^ 4) := by
    exact hpower.trans_eq hroot
  exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 32)).2
    (hsum.trans hpower')

end CertifiedJL
