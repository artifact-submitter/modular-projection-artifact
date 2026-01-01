/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Distributions.Entry
import CertifiedJL.Probability.Finite.Counting
import CertifiedJL.Projection.Counterexamples.L2Upper.Statements
import Mathlib.Data.Fintype.Pi
import Mathlib.Probability.ProbabilityMassFunction.Binomial

/-!
# Exact sparse all-ones row distribution

This module proves the exact centered-binomial probability mass function of
one sparse-Rademacher row evaluated at the all-ones vector. It is the reusable
discrete input to the upper-336 endpoint counterexample.
-/

open scoped ENNReal

namespace CertifiedJL
open Probability
namespace Probability.SparseAllOnes

/-! ## Exact all-ones row distribution -/

/-- Flatten the two sign bits underlying every sparse entry. -/
def sparseRowSeedEquivBits (d : ℕ) :
    SparseRowSeed d ≃ (Fin (2 * d) → Bool) where
  toFun seed t :=
    pairBit (seed (finProdFinEquiv.symm t).2)
      (finProdFinEquiv.symm t).1
  invFun bits i :=
    bitPair fun j => bits (finProdFinEquiv (j, i))
  left_inv seed := by
    funext i
    change bitPair
      (fun j =>
        pairBit
          (seed (finProdFinEquiv.symm
            (finProdFinEquiv (j, i))).2)
          (finProdFinEquiv.symm
            (finProdFinEquiv (j, i))).1) = seed i
    simp
  right_inv bits := by
    funext t
    let ij := finProdFinEquiv.symm t
    change pairBit
      (bitPair fun j => bits (finProdFinEquiv (j, ij.2)))
        ij.1 = bits t
    rw [pairBit_bitPair]
    exact congrArg bits (finProdFinEquiv.apply_symm_apply t)

/-- Number of positive signs among the `2d` underlying bits. -/
def sparseRowTrueCount {d : ℕ} (seed : SparseRowSeed d) : ℕ :=
  (boolSupport (sparseRowSeedEquivBits d seed)).card

/-- Integer sum of one sparse row against the all-ones vector. -/
def sparseAllOnesRowSum {d : ℕ} (seed : SparseRowSeed d) : ℤ :=
  ∑ i, sparseBit (seed i)

/-- The sparse row sum is the centered count of its `2d` sign bits. -/
theorem sparseAllOnesRowSum_eq_trueCount {d : ℕ}
    (seed : SparseRowSeed d) :
    sparseAllOnesRowSum seed =
      (sparseRowTrueCount seed : ℤ) - d := by
  have havg :
      2 * sparseAllOnesRowSum seed =
        ∑ i, (signBit (seed i).1 + signBit (seed i).2) := by
    unfold sparseAllOnesRowSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact sparseBit_eq_average (seed i)
  have hflatten :
      (∑ i, (signBit (seed i).1 + signBit (seed i).2)) =
        ∑ t : Fin (2 * d),
          signBit (sparseRowSeedEquivBits d seed t) := by
    calc
      (∑ i, (signBit (seed i).1 + signBit (seed i).2)) =
          ∑ ji : Fin 2 × Fin d,
            signBit (pairBit (seed ji.2) ji.1) := by
        rw [Fintype.sum_prod_type, Fin.sum_univ_two,
          ← Finset.sum_add_distrib]
        rfl
      _ = ∑ t : Fin (2 * d),
          signBit (sparseRowSeedEquivBits d seed t) := by
        rw [← finProdFinEquiv.sum_comp]
        apply Finset.sum_congr rfl
        intro ji _
        change
          signBit (pairBit (seed ji.2) ji.1) =
            signBit
              (pairBit
                (seed (finProdFinEquiv.symm
                  (finProdFinEquiv ji)).2)
                (finProdFinEquiv.symm
                  (finProdFinEquiv ji)).1)
        rw [finProdFinEquiv.symm_apply_apply]
  have hsign :=
    sum_signBit_eq_trueCount (sparseRowSeedEquivBits d seed)
  rw [hflatten, hsign] at havg
  change sparseAllOnesRowSum seed =
    ((boolSupport (sparseRowSeedEquivBits d seed)).card : ℤ) - d
  push_cast at havg ⊢
  omega

/-- Flattening identifies every true-count fiber with a Boolean count fiber. -/
def sparseRowTrueCountFiberEquiv (d t : ℕ) :
    {seed : SparseRowSeed d // sparseRowTrueCount seed = t} ≃
      {bits : Fin (2 * d) → Bool //
        (boolSupport bits).card = t} :=
  Equiv.subtypeEquiv (sparseRowSeedEquivBits d) fun _ => Iff.rfl

theorem card_sparseRowTrueCount_fiber (d t : ℕ) :
    Fintype.card
        {seed : SparseRowSeed d // sparseRowTrueCount seed = t} =
      (2 * d).choose t := by
  rw [Fintype.card_congr (sparseRowTrueCountFiberEquiv d t)]
  simpa using card_bool_true_count (Fin (2 * d)) t

theorem card_sparseRowSeed (d : ℕ) :
    Fintype.card (SparseRowSeed d) = 2 ^ (2 * d) := by
  classical
  rw [Fintype.card_fun, Fintype.card_prod]
  simp only [Fintype.card_bool, Fintype.card_fin]
  rw [show (2 * 2 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]

theorem card_sparseSeed (rows d : ℕ) :
    Fintype.card (SparseSeed rows d) = (2 ^ (2 * d)) ^ rows := by
  rw [Fintype.card_fun, card_sparseRowSeed, Fintype.card_fin]

/-- The exact PMF of one all-ones sparse row sum. -/
noncomputable def sparseAllOnesRowPMF (d : ℕ) : PMF ℤ :=
  (PMF.uniformOfFintype (SparseRowSeed d)).map sparseAllOnesRowSum

theorem sparseAllOnesRowPMF_apply_nat {d k : ℕ} :
    sparseAllOnesRowPMF d (k : ℤ) =
      (Nat.choose (2 * d) (d + k) : ℝ≥0∞) *
        (4 ^ d : ℝ≥0∞)⁻¹ := by
  classical
  rw [sparseAllOnesRowPMF, map_uniform_apply_eq_card]
  have hfiber :
      Fintype.card
          {seed : SparseRowSeed d //
            sparseAllOnesRowSum seed = (k : ℤ)} =
        (2 * d).choose (d + k) := by
    let e :
        {seed : SparseRowSeed d //
            sparseAllOnesRowSum seed = (k : ℤ)} ≃
          {seed : SparseRowSeed d //
            sparseRowTrueCount seed = d + k} :=
      Equiv.subtypeEquiv (Equiv.refl _) fun seed => by
        rw [sparseAllOnesRowSum_eq_trueCount]
        exact_mod_cast
          (show
            (sparseRowTrueCount seed : ℤ) - d = k ↔
              sparseRowTrueCount seed = d + k by omega)
    rw [Fintype.card_congr e, card_sparseRowTrueCount_fiber]
  rw [hfiber]
  congr 1
  norm_num [SparseRowSeed, Fintype.card_fun, Fintype.card_prod,
    Fintype.card_bool, pow_mul]

theorem sparseAllOnesRowPMF_apply_int {d : ℕ} (k : ℤ)
    (hk : k.natAbs ≤ d) :
    sparseAllOnesRowPMF d k =
      (Nat.choose (2 * d) (d + k.natAbs) : ℝ≥0∞) *
        (4 ^ d : ℝ≥0∞)⁻¹ := by
  cases k with
  | ofNat n =>
    simpa using sparseAllOnesRowPMF_apply_nat (d := d) (k := n)
  | negSucc n =>
    classical
    rw [sparseAllOnesRowPMF, map_uniform_apply_eq_card]
    have hn : n + 1 ≤ d := by simpa using hk
    have hfiber :
        Fintype.card
            {seed : SparseRowSeed d //
              sparseAllOnesRowSum seed = Int.negSucc n} =
          (2 * d).choose (d - (n + 1)) := by
      let e :
          {seed : SparseRowSeed d //
              sparseAllOnesRowSum seed = Int.negSucc n} ≃
            {seed : SparseRowSeed d //
              sparseRowTrueCount seed = d - (n + 1)} :=
        Equiv.subtypeEquiv (Equiv.refl _) fun seed => by
          rw [sparseAllOnesRowSum_eq_trueCount]
          change
            (sparseRowTrueCount seed : ℤ) - d = -(n + 1 : ℕ) ↔
              sparseRowTrueCount seed = d - (n + 1)
          constructor
          · intro h
            have hcast :
                (sparseRowTrueCount seed : ℤ) =
                  (d : ℤ) - (n + 1 : ℕ) := by omega
            exact_mod_cast hcast
          · intro h
            rw [h]
            push_cast
            omega
      rw [Fintype.card_congr e, card_sparseRowTrueCount_fiber]
    rw [hfiber]
    have hchoose :
        (2 * d).choose (d - (n + 1)) =
          (2 * d).choose (d + (n + 1)) := by
      have hle : d + (n + 1) ≤ 2 * d := by omega
      have hsub : 2 * d - (d + (n + 1)) = d - (n + 1) := by
        omega
      rw [← hsub, Nat.choose_symm hle]
    rw [hchoose]
    congr 1
    simp

end Probability.SparseAllOnes
end CertifiedJL
