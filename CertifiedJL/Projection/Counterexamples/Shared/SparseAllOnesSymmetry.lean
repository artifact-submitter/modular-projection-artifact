/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Unrestricted.Normalization
import CertifiedJL.Projection.Counterexamples.Shared.SparseAllOnesRow
import Mathlib.Tactic

/-!
# Sign symmetry for a sparse all-ones row

Negating both bits in every sparse-entry seed negates the corresponding
all-ones row sum.  Together with the exact central fiber, this counts the
strictly negative half of the law without enumerating its `4^d` seeds.
-/

namespace CertifiedJL.Probability.SparseAllOnes

open Probability

theorem two_mul_card_event_le_of_pair_disjoint
    {α : Type*} [Fintype α] (e : α ≃ α) (event : α → Prop)
    [DecidablePred event]
    (hpair : ∀ x, event x → event (e x) → False) :
    2 * Fintype.card {x : α // event x} ≤ Fintype.card α := by
  classical
  let A : Finset α := Finset.univ.filter event
  let B : Finset α := Finset.univ.filter fun x => event (e x)
  have hcardAB : A.card = B.card := by
    have hequiv : {x : α // event (e x)} ≃ {x : α // event x} :=
      Equiv.subtypeEquiv e (fun _ => Iff.rfl)
    calc
      A.card = Fintype.card {x : α // event x} :=
        (Fintype.card_subtype event).symm
      _ = Fintype.card {x : α // event (e x)} :=
        (Fintype.card_congr hequiv).symm
      _ = B.card := Fintype.card_subtype fun x => event (e x)
  have hdisjoint : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have hevent : event x := by simpa [A] using hxA
    have hevent' : event (e x) := by simpa [B] using hxB
    exact hpair x hevent hevent'
  calc
    2 * Fintype.card {x : α // event x} = A.card + B.card := by
      rw [← hcardAB, two_mul, Fintype.card_subtype]
    _ = (A ∪ B).card := (Finset.card_union_of_disjoint hdisjoint).symm
    _ ≤ Fintype.card α := by simpa using Finset.card_le_univ (A ∪ B)

theorem card_int_trichotomy {α : Type*} [Fintype α] (f : α → ℤ) :
    Fintype.card {x : α // f x < 0} +
        Fintype.card {x : α // f x = 0} +
        Fintype.card {x : α // 0 < f x} =
      Fintype.card α := by
  classical
  let negative : Finset α := Finset.univ.filter fun x => f x < 0
  let zero : Finset α := Finset.univ.filter fun x => f x = 0
  let positive : Finset α := Finset.univ.filter fun x => 0 < f x
  have hdisjointNZ : Disjoint negative zero := by
    rw [Finset.disjoint_left]
    intro x hn hz
    simp only [negative, Finset.mem_filter, Finset.mem_univ, true_and] at hn
    simp only [zero, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    omega
  have hdisjointNP : Disjoint negative positive := by
    rw [Finset.disjoint_left]
    intro x hn hp
    simp only [negative, Finset.mem_filter, Finset.mem_univ, true_and] at hn
    simp only [positive, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    omega
  have hdisjointZP : Disjoint zero positive := by
    rw [Finset.disjoint_left]
    intro x hz hp
    simp only [zero, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    simp only [positive, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    omega
  have hdisjointUnion : Disjoint (negative ∪ zero) positive := by
    rw [Finset.disjoint_union_left]
    exact ⟨hdisjointNP, hdisjointZP⟩
  rw [Fintype.card_subtype, Fintype.card_subtype, Fintype.card_subtype]
  change negative.card + zero.card + positive.card = Finset.univ.card
  calc
    negative.card + zero.card + positive.card =
        (negative ∪ zero).card + positive.card := by
      rw [Finset.card_union_of_disjoint hdisjointNZ]
    _ = ((negative ∪ zero) ∪ positive).card := by
      rw [Finset.card_union_of_disjoint hdisjointUnion]
    _ = Finset.univ.card := by
      congr 1
      ext x
      simp only [negative, zero, positive, Finset.mem_union,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro _
        trivial
      · intro _
        rcases lt_trichotomy (f x) 0 with h | h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h

def negateSparseRowSeed {d : ℕ} (seed : SparseRowSeed d) : SparseRowSeed d :=
  fun i => negateSparsePairSeed (seed i)

@[simp]
theorem negateSparseRowSeed_involutive {d : ℕ} (seed : SparseRowSeed d) :
    negateSparseRowSeed (negateSparseRowSeed seed) = seed := by
  funext i
  exact negateSparsePairSeed_involutive (seed i)

def negateSparseRowSeedEquiv (d : ℕ) : SparseRowSeed d ≃ SparseRowSeed d where
  toFun := negateSparseRowSeed
  invFun := negateSparseRowSeed
  left_inv := negateSparseRowSeed_involutive
  right_inv := negateSparseRowSeed_involutive

@[simp]
theorem sparseAllOnesRowSum_negate {d : ℕ} (seed : SparseRowSeed d) :
    sparseAllOnesRowSum (negateSparseRowSeed seed) =
      -sparseAllOnesRowSum seed := by
  simp [sparseAllOnesRowSum, negateSparseRowSeed,
    sparseBit_negateSparsePairSeed, Finset.sum_neg_distrib]

def negativePositiveEquiv (d : ℕ) :
    {seed : SparseRowSeed d // sparseAllOnesRowSum seed < 0} ≃
      {seed : SparseRowSeed d // 0 < sparseAllOnesRowSum seed} :=
  Equiv.subtypeEquiv (negateSparseRowSeedEquiv d) fun seed => by
    change sparseAllOnesRowSum seed < 0 ↔
      0 < sparseAllOnesRowSum (negateSparseRowSeed seed)
    rw [sparseAllOnesRowSum_negate]
    omega

theorem card_negative_eq_card_positive (d : ℕ) :
    Fintype.card {seed : SparseRowSeed d // sparseAllOnesRowSum seed < 0} =
      Fintype.card {seed : SparseRowSeed d // 0 < sparseAllOnesRowSum seed} :=
  Fintype.card_congr (negativePositiveEquiv d)

def zeroSumTrueCountEquiv (d : ℕ) :
    {seed : SparseRowSeed d // sparseAllOnesRowSum seed = 0} ≃
      {seed : SparseRowSeed d // sparseRowTrueCount seed = d} :=
  Equiv.subtypeEquiv (Equiv.refl _) fun seed => by
    rw [sparseAllOnesRowSum_eq_trueCount]
    exact_mod_cast
      (show (sparseRowTrueCount seed : ℤ) - d = 0 ↔
        sparseRowTrueCount seed = d by omega)

theorem card_zero_sum (d : ℕ) :
    Fintype.card {seed : SparseRowSeed d // sparseAllOnesRowSum seed = 0} =
      (2 * d).choose d := by
  rw [Fintype.card_congr (zeroSumTrueCountEquiv d),
    card_sparseRowTrueCount_fiber]

theorem card_negative_add_zero_add_positive (d : ℕ) :
    Fintype.card {seed : SparseRowSeed d // sparseAllOnesRowSum seed < 0} +
        Fintype.card {seed : SparseRowSeed d // sparseAllOnesRowSum seed = 0} +
        Fintype.card {seed : SparseRowSeed d // 0 < sparseAllOnesRowSum seed} =
      Fintype.card (SparseRowSeed d) := by
  classical
  let negative : Finset (SparseRowSeed d) :=
    Finset.univ.filter fun seed => sparseAllOnesRowSum seed < 0
  let zero : Finset (SparseRowSeed d) :=
    Finset.univ.filter fun seed => sparseAllOnesRowSum seed = 0
  let positive : Finset (SparseRowSeed d) :=
    Finset.univ.filter fun seed => 0 < sparseAllOnesRowSum seed
  rw [Fintype.card_subtype, Fintype.card_subtype, Fintype.card_subtype]
  change negative.card + zero.card + positive.card = Finset.univ.card
  have hdisjointNZ : Disjoint negative zero := by
    rw [Finset.disjoint_left]
    intro seed hn hz
    simp only [negative, Finset.mem_filter, Finset.mem_univ, true_and] at hn
    simp only [zero, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    omega
  have hdisjointNP : Disjoint negative positive := by
    rw [Finset.disjoint_left]
    intro seed hn hp
    simp only [negative, Finset.mem_filter, Finset.mem_univ, true_and] at hn
    simp only [positive, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    omega
  have hdisjointZP : Disjoint zero positive := by
    rw [Finset.disjoint_left]
    intro seed hz hp
    simp only [zero, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    simp only [positive, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    omega
  have hdisjointUnion : Disjoint (negative ∪ zero) positive := by
    rw [Finset.disjoint_union_left]
    exact ⟨hdisjointNP, hdisjointZP⟩
  calc
    negative.card + zero.card + positive.card =
        (negative ∪ zero).card + positive.card := by
      rw [Finset.card_union_of_disjoint hdisjointNZ]
    _ = ((negative ∪ zero) ∪ positive).card := by
      rw [Finset.card_union_of_disjoint hdisjointUnion]
    _ = Finset.univ.card := by
      congr 1
      ext seed
      simp only [negative, zero, positive, Finset.mem_union,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro _
        trivial
      · intro _
        rcases lt_trichotomy (sparseAllOnesRowSum seed) 0 with h | h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h

theorem two_mul_card_negative_add_central (d : ℕ) :
    2 * Fintype.card
          {seed : SparseRowSeed d // sparseAllOnesRowSum seed < 0} +
        (2 * d).choose d =
      4 ^ d := by
  have hpartition := card_negative_add_zero_add_positive d
  have hzero := card_zero_sum d
  have hsymm := card_negative_eq_card_positive d
  have htotal : Fintype.card (SparseRowSeed d) = 4 ^ d := by
    rw [card_sparseRowSeed]
    simp [pow_mul]
  omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
-- Kernel reduction of the exact central binomial coefficient needs a larger budget.
theorem quarter_card_le_negative_card_dimension12 :
    4 ^ 12 ≤
      4 * Fintype.card
        {seed : SparseRowSeed 12 // sparseAllOnesRowSum seed < 0} := by
  have h := two_mul_card_negative_add_central 12
  have hchoose : (24 : ℕ).choose 12 = 2704156 := by decide
  have h' : 2 * Fintype.card
        {seed : SparseRowSeed 12 // sparseAllOnesRowSum seed < 0} +
      2704156 = 16777216 := by
    simpa only [Nat.reduceMul, hchoose, Nat.reducePow] using h
  norm_num only [Nat.reducePow] at ⊢
  omega

end CertifiedJL.Probability.SparseAllOnes
