/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Distributions.Rademacher.RademacherMoments

/-!
# Closed formulas for Rademacher moments through degree ten

The formulas are proved by exact finite induction from the recurrences in
`RademacherMoments`.  They are reusable independently of the sparse infinity
endpoint.
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace CertifiedJL.Probability

noncomputable local instance (priority := 10000) rademacherExactMomentsDecidableEq
    (α : Type*) :
    DecidableEq α := Classical.decEq α

/-- The measure integral under the finite Rademacher PMF is the uniform finite
expectation. This bridge is independent of any particular tail polynomial. -/
theorem integral_rademacher_eq_expect_fintype
    {ι : Type*} [Fintype ι] (f : (ι → Bool) → ℝ) :
    (∫ bits, f bits ∂(rademacherPMF ι).toMeasure) =
      𝔼 bits : ι → Bool, f bits := by
  classical
  rw [finitePMF_integral_eq_sum]
  simp only [rademacherPMF, uniformPiPMF_eq_uniformOfFintype,
    PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, Fintype.expect_eq_sum_div_card]
  rw [div_eq_mul_inv, mul_comm, Finset.mul_sum]

lemma radMoment_option_eight {α : Type*} [Fintype α]
    (a : Option α → ℝ) :
    radMoment a 8 =
      radMoment (fun i => a (some i)) 8 +
      28 * (a none) ^ 2 * radMoment (fun i => a (some i)) 6 +
      70 * (a none) ^ 4 * radMoment (fun i => a (some i)) 4 +
      28 * (a none) ^ 6 * radMoment (fun i => a (some i)) 2 +
      (a none) ^ 8 := by
  classical
  let e := Equiv.piOptionEquivProd (β := fun _ : Option α => Bool)
  let tail : α → ℝ := fun i => a (some i)
  let g : Bool × (α → Bool) → ℝ := fun p =>
    ((signBit p.1 : ℝ) * a none + rademacherSum tail p.2) ^ 8
  have he : radMoment a 8 = 𝔼 p : Bool × (α → Bool), g p := by
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
        (rademacherSum tail bits) ^ 8 +
        28 * (a none) ^ 2 * (rademacherSum tail bits) ^ 6 +
        70 * (a none) ^ 4 * (rademacherSum tail bits) ^ 4 +
        28 * (a none) ^ 6 * (rademacherSum tail bits) ^ 2 +
        (a none) ^ 8 := by
    simp only [Fintype.expect_eq_sum_div_card, Fintype.card_bool,
      Fintype.sum_bool]
    dsimp [g]
    simp [signBit]
    ring
  simp_rw [hbool]
  simp only [Finset.expect_add_distrib, Fintype.expect_const]
  unfold radMoment
  rw [← Finset.mul_expect, ← Finset.mul_expect, ← Finset.mul_expect]

lemma radMoment_option_ten {α : Type*} [Fintype α]
    (a : Option α → ℝ) :
    radMoment a 10 =
      radMoment (fun i => a (some i)) 10 +
      45 * (a none) ^ 2 * radMoment (fun i => a (some i)) 8 +
      210 * (a none) ^ 4 * radMoment (fun i => a (some i)) 6 +
      210 * (a none) ^ 6 * radMoment (fun i => a (some i)) 4 +
      45 * (a none) ^ 8 * radMoment (fun i => a (some i)) 2 +
      (a none) ^ 10 := by
  classical
  let e := Equiv.piOptionEquivProd (β := fun _ : Option α => Bool)
  let tail : α → ℝ := fun i => a (some i)
  let g : Bool × (α → Bool) → ℝ := fun p =>
    ((signBit p.1 : ℝ) * a none + rademacherSum tail p.2) ^ 10
  have he : radMoment a 10 = 𝔼 p : Bool × (α → Bool), g p := by
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
        (rademacherSum tail bits) ^ 10 +
        45 * (a none) ^ 2 * (rademacherSum tail bits) ^ 8 +
        210 * (a none) ^ 4 * (rademacherSum tail bits) ^ 6 +
        210 * (a none) ^ 6 * (rademacherSum tail bits) ^ 4 +
        45 * (a none) ^ 8 * (rademacherSum tail bits) ^ 2 +
        (a none) ^ 10 := by
    simp only [Fintype.expect_eq_sum_div_card, Fintype.card_bool,
      Fintype.sum_bool]
    dsimp [g]
    simp [signBit]
    ring
  simp_rw [hbool]
  simp only [Finset.expect_add_distrib, Fintype.expect_const]
  unfold radMoment
  rw [← Finset.mul_expect, ← Finset.mul_expect, ← Finset.mul_expect,
    ← Finset.mul_expect]

noncomputable def coeffPowerSum {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (k : ℕ) : ℝ := ∑ i, (a i ^ 2) ^ k

theorem coeffPowerSum_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (a : β → ℝ) (k : ℕ) :
    coeffPowerSum (fun i => a (e i)) k = coeffPowerSum a k := by
  unfold coeffPowerSum
  exact Equiv.sum_comp e (fun i => (a i ^ 2) ^ k)

theorem coeffPowerSum_option {α : Type*} [Fintype α]
    (a : Option α → ℝ) (k : ℕ) :
    coeffPowerSum a k =
      coeffPowerSum (fun i => a (some i)) k + (a none ^ 2) ^ k := by
  unfold coeffPowerSum
  rw [Fintype.sum_option]
  ring

set_option maxHeartbeats 1000000 in
theorem radMoment_two_exact {n : ℕ} (a : Fin n → ℝ) :
    radMoment a 2 = coeffPowerSum a 1 := by
  classical
  induction n with
  | zero => simp [radMoment, rademacherSum, coeffPowerSum]
  | succ n ih =>
      let e : Option (Fin n) ≃ Fin (n + 1) := (finSuccEquiv n).symm
      let ao : Option (Fin n) → ℝ := fun i => a (e i)
      have hm := radMoment_equiv e a 2
      have hp := coeffPowerSum_equiv e a 1
      change radMoment a 2 = coeffPowerSum a 1
      rw [← hm, ← hp]
      change radMoment ao 2 = coeffPowerSum ao 1
      rw [radMoment_option_two, ih, coeffPowerSum_option]
      ring

set_option maxHeartbeats 1000000 in
theorem radMoment_four_exact {n : ℕ} (a : Fin n → ℝ) :
    radMoment a 4 =
      3 * coeffPowerSum a 1 ^ 2 - 2 * coeffPowerSum a 2 := by
  classical
  induction n with
  | zero => simp [radMoment, rademacherSum, coeffPowerSum]
  | succ n ih =>
      let e : Option (Fin n) ≃ Fin (n + 1) := (finSuccEquiv n).symm
      let ao : Option (Fin n) → ℝ := fun i => a (e i)
      have hm := radMoment_equiv e a 4
      have hp1 := coeffPowerSum_equiv e a 1
      have hp2 := coeffPowerSum_equiv e a 2
      rw [← hm, ← hp1, ← hp2]
      change radMoment ao 4 =
        3 * coeffPowerSum ao 1 ^ 2 - 2 * coeffPowerSum ao 2
      rw [radMoment_option_four, ih, radMoment_two_exact,
        coeffPowerSum_option, coeffPowerSum_option]
      ring

set_option maxHeartbeats 1000000 in
theorem radMoment_six_exact {n : ℕ} (a : Fin n → ℝ) :
    radMoment a 6 =
      15 * coeffPowerSum a 1 ^ 3 -
      30 * coeffPowerSum a 1 * coeffPowerSum a 2 +
      16 * coeffPowerSum a 3 := by
  classical
  induction n with
  | zero => simp [radMoment, rademacherSum, coeffPowerSum]
  | succ n ih =>
      let e : Option (Fin n) ≃ Fin (n + 1) := (finSuccEquiv n).symm
      let ao : Option (Fin n) → ℝ := fun i => a (e i)
      have hm := radMoment_equiv e a 6
      have hp1 := coeffPowerSum_equiv e a 1
      have hp2 := coeffPowerSum_equiv e a 2
      have hp3 := coeffPowerSum_equiv e a 3
      rw [← hm, ← hp1, ← hp2, ← hp3]
      change radMoment ao 6 = 15 * coeffPowerSum ao 1 ^ 3 -
        30 * coeffPowerSum ao 1 * coeffPowerSum ao 2 +
        16 * coeffPowerSum ao 3
      rw [radMoment_option_six, ih, radMoment_four_exact,
        radMoment_two_exact, coeffPowerSum_option,
        coeffPowerSum_option, coeffPowerSum_option]
      ring

set_option maxHeartbeats 2000000 in
theorem radMoment_eight_exact {n : ℕ} (a : Fin n → ℝ) :
    radMoment a 8 =
      105 * coeffPowerSum a 1 ^ 4 -
      420 * coeffPowerSum a 1 ^ 2 * coeffPowerSum a 2 +
      448 * coeffPowerSum a 1 * coeffPowerSum a 3 +
      140 * coeffPowerSum a 2 ^ 2 - 272 * coeffPowerSum a 4 := by
  classical
  induction n with
  | zero => simp [radMoment, rademacherSum, coeffPowerSum]
  | succ n ih =>
      let e : Option (Fin n) ≃ Fin (n + 1) := (finSuccEquiv n).symm
      let ao : Option (Fin n) → ℝ := fun i => a (e i)
      have hm := radMoment_equiv e a 8
      have hp1 := coeffPowerSum_equiv e a 1
      have hp2 := coeffPowerSum_equiv e a 2
      have hp3 := coeffPowerSum_equiv e a 3
      have hp4 := coeffPowerSum_equiv e a 4
      rw [← hm, ← hp1, ← hp2, ← hp3, ← hp4]
      change radMoment ao 8 = 105 * coeffPowerSum ao 1 ^ 4 -
        420 * coeffPowerSum ao 1 ^ 2 * coeffPowerSum ao 2 +
        448 * coeffPowerSum ao 1 * coeffPowerSum ao 3 +
        140 * coeffPowerSum ao 2 ^ 2 - 272 * coeffPowerSum ao 4
      rw [radMoment_option_eight, ih, radMoment_six_exact,
        radMoment_four_exact, radMoment_two_exact,
        coeffPowerSum_option, coeffPowerSum_option,
        coeffPowerSum_option, coeffPowerSum_option]
      ring

set_option maxHeartbeats 3000000 in
theorem radMoment_ten_exact {n : ℕ} (a : Fin n → ℝ) :
    radMoment a 10 =
      945 * coeffPowerSum a 1 ^ 5 -
      6300 * coeffPowerSum a 1 ^ 3 * coeffPowerSum a 2 +
      10080 * coeffPowerSum a 1 ^ 2 * coeffPowerSum a 3 +
      6300 * coeffPowerSum a 1 * coeffPowerSum a 2 ^ 2 -
      12240 * coeffPowerSum a 1 * coeffPowerSum a 4 -
      6720 * coeffPowerSum a 2 * coeffPowerSum a 3 +
      7936 * coeffPowerSum a 5 := by
  classical
  induction n with
  | zero => simp [radMoment, rademacherSum, coeffPowerSum]
  | succ n ih =>
      let e : Option (Fin n) ≃ Fin (n + 1) := (finSuccEquiv n).symm
      let ao : Option (Fin n) → ℝ := fun i => a (e i)
      have hm := radMoment_equiv e a 10
      have hp1 := coeffPowerSum_equiv e a 1
      have hp2 := coeffPowerSum_equiv e a 2
      have hp3 := coeffPowerSum_equiv e a 3
      have hp4 := coeffPowerSum_equiv e a 4
      have hp5 := coeffPowerSum_equiv e a 5
      rw [← hm, ← hp1, ← hp2, ← hp3, ← hp4, ← hp5]
      change radMoment ao 10 = 945 * coeffPowerSum ao 1 ^ 5 -
        6300 * coeffPowerSum ao 1 ^ 3 * coeffPowerSum ao 2 +
        10080 * coeffPowerSum ao 1 ^ 2 * coeffPowerSum ao 3 +
        6300 * coeffPowerSum ao 1 * coeffPowerSum ao 2 ^ 2 -
        12240 * coeffPowerSum ao 1 * coeffPowerSum ao 4 -
        6720 * coeffPowerSum ao 2 * coeffPowerSum ao 3 +
        7936 * coeffPowerSum ao 5
      rw [radMoment_option_ten, ih, radMoment_eight_exact,
        radMoment_six_exact, radMoment_four_exact, radMoment_two_exact,
        coeffPowerSum_option, coeffPowerSum_option, coeffPowerSum_option,
        coeffPowerSum_option, coeffPowerSum_option]
      ring

end CertifiedJL.Probability
