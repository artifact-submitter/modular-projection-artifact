/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Distributions.Rademacher.RademacherSubgaussian
import Mathlib.Algebra.BigOperators.Expect

/-!
# Exact finite Rademacher moments

This module defines the uniform finite expectation of a Rademacher sum and
proves the one-coordinate recurrences used to derive its even moments.  The
construction is dimension-free and uses only exact finite sums.
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace CertifiedJL.Probability

noncomputable local instance (priority := 10000) rademacherMomentsDecidableEq (α : Type*) :
    DecidableEq α := Classical.decEq α

/-- The exact uniform finite expectation of the `k`th power of a Rademacher sum. -/
noncomputable def radMoment {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (k : ℕ) : ℝ := by
  classical
  exact 𝔼 bits : ι → Bool, (rademacherSum a bits) ^ k

lemma rademacherSum_option {α : Type*} [Fintype α]
    (a : Option α → ℝ) (bits : Option α → Bool) :
    rademacherSum a bits =
      (signBit (bits none) : ℝ) * a none +
        rademacherSum (fun i => a (some i)) (fun i => bits (some i)) := by
  unfold rademacherSum
  rw [Fintype.sum_option]

lemma radMoment_option_two {α : Type*} [Fintype α]
    (a : Option α → ℝ) :
    radMoment a 2 =
      radMoment (fun i => a (some i)) 2 + (a none) ^ 2 := by
  classical
  let e := Equiv.piOptionEquivProd (β := fun _ : Option α => Bool)
  let tail : α → ℝ := fun i => a (some i)
  let g : Bool × (α → Bool) → ℝ := fun p =>
    ((signBit p.1 : ℝ) * a none + rademacherSum tail p.2) ^ 2
  have he : radMoment a 2 = 𝔼 p : Bool × (α → Bool), g p := by
    unfold radMoment
    apply Fintype.expect_equiv e _ _
    intro bits
    dsimp [e, g, tail]
    rw [rademacherSum_option]
    rfl
  rw [he]
  have hp := Finset.expect_product (Finset.univ : Finset Bool)
    (Finset.univ : Finset (α → Bool)) g
  change (𝔼 p : Bool × (α → Bool), g p) = _
  rw [show (𝔼 p : Bool × (α → Bool), g p) =
      𝔼 b : Bool, 𝔼 bits : α → Bool, g (b, bits) by
        simpa only [Finset.univ_product_univ] using hp]
  have hbool (bits : α → Bool) :
      (𝔼 b : Bool, g (b, bits)) =
        (rademacherSum tail bits) ^ 2 + (a none) ^ 2 := by
    simp only [Fintype.expect_eq_sum_div_card, Fintype.card_bool,
      Fintype.sum_bool]
    dsimp [g]
    simp [signBit]
    ring
  rw [Finset.expect_comm]
  simp_rw [hbool]
  rw [Finset.expect_add_distrib, Fintype.expect_const]
  rfl

lemma radMoment_option_four {α : Type*} [Fintype α]
    (a : Option α → ℝ) :
    radMoment a 4 =
      radMoment (fun i => a (some i)) 4 +
      6 * (a none) ^ 2 * radMoment (fun i => a (some i)) 2 +
      (a none) ^ 4 := by
  classical
  let e := Equiv.piOptionEquivProd (β := fun _ : Option α => Bool)
  let tail : α → ℝ := fun i => a (some i)
  let g : Bool × (α → Bool) → ℝ := fun p =>
    ((signBit p.1 : ℝ) * a none + rademacherSum tail p.2) ^ 4
  have he : radMoment a 4 = 𝔼 p : Bool × (α → Bool), g p := by
    unfold radMoment
    apply Fintype.expect_equiv e _ _
    intro bits
    dsimp [e, g, tail]
    rw [rademacherSum_option]
    rfl
  rw [he]
  have hp := Finset.expect_product (Finset.univ : Finset Bool)
    (Finset.univ : Finset (α → Bool)) g
  change (𝔼 p : Bool × (α → Bool), g p) = _
  rw [show (𝔼 p : Bool × (α → Bool), g p) =
      𝔼 b : Bool, 𝔼 bits : α → Bool, g (b, bits) by
        simpa only [Finset.univ_product_univ] using hp]
  rw [Finset.expect_comm]
  have hbool (bits : α → Bool) :
      (𝔼 b : Bool, g (b, bits)) =
        (rademacherSum tail bits) ^ 4 +
        6 * (a none) ^ 2 * (rademacherSum tail bits) ^ 2 +
        (a none) ^ 4 := by
    simp only [Fintype.expect_eq_sum_div_card, Fintype.card_bool,
      Fintype.sum_bool]
    dsimp [g]
    simp [signBit]
    ring
  simp_rw [hbool]
  simp only [Finset.expect_add_distrib, Fintype.expect_const]
  unfold radMoment
  rw [← Finset.mul_expect]

lemma radMoment_option_six {α : Type*} [Fintype α]
    (a : Option α → ℝ) :
    radMoment a 6 =
      radMoment (fun i => a (some i)) 6 +
      15 * (a none) ^ 2 * radMoment (fun i => a (some i)) 4 +
      15 * (a none) ^ 4 * radMoment (fun i => a (some i)) 2 +
      (a none) ^ 6 := by
  classical
  let e := Equiv.piOptionEquivProd (β := fun _ : Option α => Bool)
  let tail : α → ℝ := fun i => a (some i)
  let g : Bool × (α → Bool) → ℝ := fun p =>
    ((signBit p.1 : ℝ) * a none + rademacherSum tail p.2) ^ 6
  have he : radMoment a 6 = 𝔼 p : Bool × (α → Bool), g p := by
    unfold radMoment
    apply Fintype.expect_equiv e _ _
    intro bits
    dsimp [e, g, tail]
    rw [rademacherSum_option]
    rfl
  rw [he]
  have hp := Finset.expect_product (Finset.univ : Finset Bool)
    (Finset.univ : Finset (α → Bool)) g
  change (𝔼 p : Bool × (α → Bool), g p) = _
  rw [show (𝔼 p : Bool × (α → Bool), g p) =
      𝔼 b : Bool, 𝔼 bits : α → Bool, g (b, bits) by
        simpa only [Finset.univ_product_univ] using hp]
  rw [Finset.expect_comm]
  have hbool (bits : α → Bool) :
      (𝔼 b : Bool, g (b, bits)) =
        (rademacherSum tail bits) ^ 6 +
        15 * (a none) ^ 2 * (rademacherSum tail bits) ^ 4 +
        15 * (a none) ^ 4 * (rademacherSum tail bits) ^ 2 +
        (a none) ^ 6 := by
    simp only [Fintype.expect_eq_sum_div_card, Fintype.card_bool,
      Fintype.sum_bool]
    dsimp [g]
    simp [signBit]
    ring
  simp_rw [hbool]
  simp only [Finset.expect_add_distrib, Fintype.expect_const]
  unfold radMoment
  rw [← Finset.mul_expect, ← Finset.mul_expect]

lemma rademacherSum_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (a : β → ℝ) (bits : α → Bool) :
    rademacherSum (fun i => a (e i)) bits =
      rademacherSum a ((Equiv.arrowCongr e (Equiv.refl Bool)) bits) := by
  unfold rademacherSum
  apply Fintype.sum_equiv e
  intro i
  simp

lemma radMoment_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (a : β → ℝ) (k : ℕ) :
    radMoment (fun i => a (e i)) k = radMoment a k := by
  unfold radMoment
  apply Fintype.expect_equiv (Equiv.arrowCongr e (Equiv.refl Bool))
  intro bits
  rw [rademacherSum_equiv]

end CertifiedJL.Probability
