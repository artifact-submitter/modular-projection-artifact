/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Unrestricted.Soundness
import CertifiedJL.Projection.Counterexamples.Shared.SparseAllOnesSymmetry
import CertifiedJL.Statements.L2.Lower
import Mathlib.Tactic

/-!
# A finite 132-bit obstruction for the 192-row threshold floor 12

The witness is `(q,b,w) = (301,100,(100,1))`.  If the dominant coordinate
is active in fewer than twelve rows, failure is automatic.  At exactly
twelve active rows, failure still occurs whenever the signed sum of the
twelve tail entries is negative.  The latter conditional event has mass at
least one quarter by exact finite sign symmetry.
-/

open scoped BigOperators ENNReal

namespace CertifiedJL.Counterexamples.ThresholdLowerRows192Floor12

open Probability

def parameters : L2ThresholdLowerParameters :=
  { distribution := .balancedTernary
    rows := 192
    squaredNormFloor := NonnegativeRatio.ofNat 12
    modulusMargin := NonnegativeRatio.ofNat 3 }

def witness : Fin 2 → ℤ := fun i => if i = 0 then 100 else 1

theorem witness_centered : CenteredInput 301 witness := by
  intro i
  fin_cases i <;> norm_num [witness, centeredInterval]

theorem witness_sqNorm : sqNorm witness = 10001 := by
  decide

def dominantCount (seed : SparseSeed 192 2) : ℕ :=
  ∑ row, (sparseBit (seed row 0)).natAbs ^ 2

def crossSum (seed : SparseSeed 192 2) : ℤ :=
  ∑ row, sparseBit (seed row 0) * sparseBit (seed row 1)

def tailProjectionSqNorm (seed : SparseSeed 192 2) : ℕ :=
  ∑ row, (sparseBit (seed row 1)).natAbs ^ 2

theorem sparseBit_sq_eq_activity (pair : Bool × Bool) :
    (sparseBit pair).natAbs ^ 2 = if sparsePairActivity pair then 1 else 0 := by
  rcases pair with ⟨left, right⟩
  cases left <;> cases right <;> decide

theorem dominantCount_eq_sum (seed : SparseSeed 192 2) :
    dominantCount seed =
      ∑ row, (sparseBit (seed row 0)).natAbs ^ 2 := by
  rfl

theorem tailProjectionSqNorm_le (seed : SparseSeed 192 2) : tailProjectionSqNorm seed ≤ 192 := by
  unfold tailProjectionSqNorm
  calc
    (∑ row : Fin 192, (sparseBit (seed row 1)).natAbs ^ 2) ≤
        ∑ _row : Fin 192, 1 := by
      apply Finset.sum_le_sum
      intro row _
      rcases h : seed row 1 with ⟨left, right⟩
      cases left <;> cases right <;> decide
    _ = 192 := by simp

theorem rowDot_witness (seed : SparseSeed 192 2) (row : Fin 192) :
    rowDot (sparseMatrix seed) witness row =
      100 * sparseBit (seed row 0) + sparseBit (seed row 1) := by
  simp [rowDot, sparseMatrix, sparseRow, witness, Fin.sum_univ_two]
  ring

theorem centered_rowDot_witness (seed : SparseSeed 192 2) (row : Fin 192) :
    centeredMod 301 (rowDot (sparseMatrix seed) witness row) =
      rowDot (sparseMatrix seed) witness row := by
  rw [centeredMod_eq_self (by norm_num)]
  rw [rowDot_witness]
  rcases hdominant : seed row 0 with ⟨dleft, dright⟩
  rcases htail : seed row 1 with ⟨tleft, tright⟩
  cases dleft <;> cases dright <;> cases tleft <;> cases tright <;>
    norm_num [sparseBit, centeredInterval]

theorem projectionSqNorm_cast (seed : SparseSeed 192 2) (row : Fin 192) :
    ((centeredMod 301
        (rowDot (sparseMatrix seed) witness row)).natAbs ^ 2 : ℤ) =
      10000 * (sparseBit (seed row 0)).natAbs ^ 2 +
        200 * (sparseBit (seed row 0) * sparseBit (seed row 1)) +
        (sparseBit (seed row 1)).natAbs ^ 2 := by
  rw [centered_rowDot_witness, rowDot_witness]
  rcases hdominant : seed row 0 with ⟨dleft, dright⟩
  rcases htail : seed row 1 with ⟨tleft, tright⟩
  cases dleft <;> cases dright <;> cases tleft <;> cases tright <;>
    decide

set_option maxRecDepth 10000 in
theorem modularProjectionSqNorm_witness (seed : SparseSeed 192 2) :
    (modularProjectionSqNorm 301 (sparseMatrix seed) witness : ℤ) =
      10000 * dominantCount seed + 200 * crossSum seed + tailProjectionSqNorm seed := by
  unfold modularProjectionSqNorm
  simp only [crossSum, tailProjectionSqNorm, dominantCount]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro row _
  simpa only [Int.natCast_natAbs] using projectionSqNorm_cast seed row

theorem projectionSqNorm_le_activity (seed : SparseSeed 192 2) (row : Fin 192) :
    (centeredMod 301 (rowDot (sparseMatrix seed) witness row)).natAbs ^ 2 ≤
      10200 * (sparseBit (seed row 0)).natAbs ^ 2 + 1 := by
  rw [centered_rowDot_witness, rowDot_witness]
  rcases hdominant : seed row 0 with ⟨dleft, dright⟩
  rcases htail : seed row 1 with ⟨tleft, tright⟩
  cases dleft <;> cases dright <;> cases tleft <;> cases tright <;>
    decide

theorem modularProjectionSqNorm_le_of_dominantCount_lt_twelve
    (seed : SparseSeed 192 2) (hcount : dominantCount seed < 12) :
    modularProjectionSqNorm 301 (sparseMatrix seed) witness < 120000 := by
  unfold modularProjectionSqNorm
  calc
    (∑ row,
        (centeredMod 301
          (rowDot (sparseMatrix seed) witness row)).natAbs ^ 2) ≤
        ∑ row, (10200 * (sparseBit (seed row 0)).natAbs ^ 2 + 1) := by
      apply Finset.sum_le_sum
      intro row _
      exact projectionSqNorm_le_activity seed row
    _ = 10200 * dominantCount seed + 192 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← dominantCount_eq_sum]
      simp
    _ < 120000 := by omega

theorem modularProjectionSqNorm_lt_of_count_eq_twelve_crossSum_neg
    (seed : SparseSeed 192 2) (hcount : dominantCount seed = 12)
    (hcross : crossSum seed < 0) :
    modularProjectionSqNorm 301 (sparseMatrix seed) witness < 120000 := by
  have henergy := modularProjectionSqNorm_witness seed
  have htail := tailProjectionSqNorm_le seed
  have htail' : (tailProjectionSqNorm seed : ℤ) ≤ 192 := by exact_mod_cast htail
  have hlt : (modularProjectionSqNorm 301 (sparseMatrix seed) witness : ℤ) < 120000 := by
    rw [henergy, hcount]
    omega
  exact_mod_cast hlt

theorem failure_of_dominantCount_lt_twelve
    (seed : SparseSeed 192 2) (hcount : dominantCount seed < 12) :
    L2ThresholdLowerFailure (NonnegativeRatio.ofNat 12) 100 301 witness
      (sparseMatrix seed) := by
  unfold L2ThresholdLowerFailure
  simpa [NonnegativeRatio.ofNat] using
    modularProjectionSqNorm_le_of_dominantCount_lt_twelve seed hcount

theorem failure_of_count_eq_twelve_crossSum_neg
    (seed : SparseSeed 192 2) (hcount : dominantCount seed = 12)
    (hcross : crossSum seed < 0) :
    L2ThresholdLowerFailure (NonnegativeRatio.ofNat 12) 100 301 witness
      (sparseMatrix seed) := by
  unfold L2ThresholdLowerFailure
  simpa [NonnegativeRatio.ofNat] using
    modularProjectionSqNorm_lt_of_count_eq_twelve_crossSum_neg seed hcount hcross

def tailIndex : DominantRemainderIndex (0 : Fin 2) := ⟨1, by decide⟩

def conditionalRowCross (activity : DominantActivity 192)
    (conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2))
    (row : Fin 192) : ℤ :=
  (if activity row then signBit (conditional.1 row) else 0) *
    sparseBit (conditional.2 row tailIndex)

def conditionalCrossSum (activity : DominantActivity 192)
    (conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2)) : ℤ :=
  ∑ row, conditionalRowCross activity conditional row

theorem crossSum_sparseSeedOfDominantView
    (activity : DominantActivity 192)
    (conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2)) :
    crossSum (sparseSeedOfDominantView (0 : Fin 2) (activity, conditional)) =
      conditionalCrossSum activity conditional := by
  unfold crossSum conditionalCrossSum conditionalRowCross
  apply Finset.sum_congr rfl
  intro row _
  simp [sparseSeedOfDominantView, sparseBit_ofActivitySign, tailIndex]

def cycleSparsePairSeed : Bool × Bool → Bool × Bool
  | (false, false) => (false, true)
  | (false, true) => (true, true)
  | (true, true) => (true, false)
  | (true, false) => (false, false)

def cycleSparsePairSeedInv : Bool × Bool → Bool × Bool
  | (false, true) => (false, false)
  | (true, true) => (false, true)
  | (true, false) => (true, true)
  | (false, false) => (true, false)

def cycleSparsePairSeedEquiv : Bool × Bool ≃ Bool × Bool where
  toFun := cycleSparsePairSeed
  invFun := cycleSparsePairSeedInv
  left_inv pair := by rcases pair with ⟨left, right⟩; cases left <;> cases right <;> rfl
  right_inv pair := by rcases pair with ⟨left, right⟩; cases left <;> cases right <;> rfl

theorem sparseBit_cycle_ne (pair : Bool × Bool) :
    sparseBit (cycleSparsePairSeed pair) ≠ sparseBit pair := by
  rcases pair with ⟨left, right⟩
  cases left <;> cases right <;> decide

noncomputable def cycleConditionalAt (selected : Fin 192) :
    DominantConditionalSeeds (m := 192) (0 : Fin 2) ≃
      DominantConditionalSeeds (m := 192) (0 : Fin 2) :=
  Equiv.prodCongr (Equiv.refl _) <|
    Equiv.piCongrRight fun row =>
      Equiv.piCongrRight fun coordinate =>
        if row = selected ∧ coordinate = tailIndex then
          cycleSparsePairSeedEquiv
        else Equiv.refl _

theorem cycleConditionalAt_apply_selected
    (selected : Fin 192)
    (conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2)) :
    (cycleConditionalAt selected conditional).2 selected tailIndex =
      cycleSparsePairSeed (conditional.2 selected tailIndex) := by
  simp [cycleConditionalAt, cycleSparsePairSeedEquiv]

theorem cycleConditionalAt_apply_of_ne
    (selected row : Fin 192) (hne : row ≠ selected)
    (conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2)) :
    (cycleConditionalAt selected conditional).2 row tailIndex =
      conditional.2 row tailIndex := by
  simp [cycleConditionalAt, hne]

theorem cycleConditionalAt_signs
    (selected : Fin 192)
    (conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2)) :
    (cycleConditionalAt selected conditional).1 = conditional.1 := by
  rfl

theorem conditionalCrossSum_eq_rest_add
    (activity : DominantActivity 192) (selected : Fin 192)
    (conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2)) :
    conditionalCrossSum activity conditional =
      (∑ row ∈ (Finset.univ : Finset (Fin 192)).erase selected,
        conditionalRowCross activity conditional row) +
      conditionalRowCross activity conditional selected := by
  unfold conditionalCrossSum
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ selected)]

theorem conditionalCrossSum_cycle_ne_of_active
    (activity : DominantActivity 192) (selected : Fin 192)
    (hactive : activity selected = true)
    (conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2)) :
    conditionalCrossSum activity (cycleConditionalAt selected conditional) ≠
      conditionalCrossSum activity conditional := by
  rw [conditionalCrossSum_eq_rest_add activity selected,
    conditionalCrossSum_eq_rest_add activity selected]
  have hrest :
      (∑ row ∈ (Finset.univ : Finset (Fin 192)).erase selected,
          conditionalRowCross activity (cycleConditionalAt selected conditional) row) =
        ∑ row ∈ (Finset.univ : Finset (Fin 192)).erase selected,
          conditionalRowCross activity conditional row := by
    apply Finset.sum_congr rfl
    intro row hrow
    have hne : row ≠ selected := Finset.ne_of_mem_erase hrow
    simp [conditionalRowCross, cycleConditionalAt_signs,
      cycleConditionalAt_apply_of_ne selected row hne]
  rw [hrest]
  simp only [conditionalRowCross, hactive, if_true,
    cycleConditionalAt_signs, cycleConditionalAt_apply_selected]
  intro heq
  have hsign : signBit (conditional.1 selected) ≠ 0 := by
    cases conditional.1 selected <;> decide
  apply sparseBit_cycle_ne (conditional.2 selected tailIndex)
  exact mul_left_cancel₀ hsign (add_left_cancel heq)

theorem central_pair_disjoint_of_active
    (activity : DominantActivity 192) (selected : Fin 192)
    (hactive : activity selected = true)
    (conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2))
    (hzero : conditionalCrossSum activity conditional = 0)
    (hcycle : conditionalCrossSum activity
      (cycleConditionalAt selected conditional) = 0) : False := by
  exact conditionalCrossSum_cycle_ne_of_active activity selected hactive conditional
    (hcycle.trans hzero.symm)

noncomputable def negateConditional :
    DominantConditionalSeeds (m := 192) (0 : Fin 2) ≃
      DominantConditionalSeeds (m := 192) (0 : Fin 2) :=
  Equiv.prodCongr (Equiv.refl _)
    (negateDominantRemainderSeedsEquiv (m := 192) (0 : Fin 2))

theorem conditionalCrossSum_negate
    (activity : DominantActivity 192)
    (conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2)) :
    conditionalCrossSum activity (negateConditional conditional) =
      -conditionalCrossSum activity conditional := by
  change (∑ row, (if activity row then signBit (conditional.1 row) else 0) *
      sparseBit (negateSparsePairSeed (conditional.2 row tailIndex))) =
    -(∑ row, (if activity row then signBit (conditional.1 row) else 0) *
      sparseBit (conditional.2 row tailIndex))
  simp_rw [sparseBit_negateSparsePairSeed]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro row _
  ring

noncomputable def conditionalNegativePositiveEquiv (activity : DominantActivity 192) :
    {conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2) //
        conditionalCrossSum activity conditional < 0} ≃
      {conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2) //
        0 < conditionalCrossSum activity conditional} :=
  Equiv.subtypeEquiv negateConditional fun conditional => by
    rw [conditionalCrossSum_negate]
    omega

theorem conditional_negative_card_eq_positive_card
    (activity : DominantActivity 192) :
    Fintype.card
        {conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2) //
          conditionalCrossSum activity conditional < 0} =
      Fintype.card
        {conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2) //
          0 < conditionalCrossSum activity conditional} :=
  Fintype.card_congr (conditionalNegativePositiveEquiv activity)

theorem exists_active_of_count_eq_twelve
    (activity : DominantActivity 192)
    (hcount : (dominantActivityCount activity : ℕ) = 12) :
    ∃ selected, activity selected = true := by
  have hcard : (boolSupport activity).card = 12 := by
    simpa [dominantActivityCount] using hcount
  have hpos : 0 < (boolSupport activity).card := by omega
  obtain ⟨selected, hselected⟩ := Finset.card_pos.mp hpos
  exact ⟨selected, by simpa [boolSupport] using hselected⟩

theorem conditional_central_twice_le_card
    (activity : DominantActivity 192)
    (hcount : (dominantActivityCount activity : ℕ) = 12) :
    2 * Fintype.card
        {conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2) //
          conditionalCrossSum activity conditional = 0} ≤
      Fintype.card
        (DominantConditionalSeeds (m := 192) (0 : Fin 2)) := by
  classical
  obtain ⟨selected, hactive⟩ := exists_active_of_count_eq_twelve activity hcount
  exact Probability.SparseAllOnes.two_mul_card_event_le_of_pair_disjoint
    (cycleConditionalAt selected)
    (fun conditional => conditionalCrossSum activity conditional = 0)
    (central_pair_disjoint_of_active activity selected hactive)

theorem conditional_total_card_le_four_negative_card
    (activity : DominantActivity 192)
    (hcount : (dominantActivityCount activity : ℕ) = 12) :
    Fintype.card
        (DominantConditionalSeeds (m := 192) (0 : Fin 2)) ≤
      4 * Fintype.card
        {conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2) //
          conditionalCrossSum activity conditional < 0} := by
  have hpartition := Probability.SparseAllOnes.card_int_trichotomy
    (conditionalCrossSum activity)
  have hsymm := conditional_negative_card_eq_positive_card activity
  have hcentral := conditional_central_twice_le_card activity hcount
  omega

theorem reconstructedDominantSquare
    (activity : DominantActivity 192)
    (conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2))
    (row : Fin 192) :
    (sparseBit
      (sparseSeedOfDominantView (0 : Fin 2) (activity, conditional) row 0)).natAbs ^ 2 =
      if activity row = true then 1 else 0 := by
  cases hactivity : activity row <;>
    cases hconditional : conditional.1 row <;>
      simp [sparseSeedOfDominantView, sparseBit_ofActivitySign, signBit,
        hactivity, hconditional]

set_option maxRecDepth 10000 in
theorem dominantCount_sparseSeedOfDominantView
    (activity : DominantActivity 192)
    (conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2)) :
    dominantCount
        (sparseSeedOfDominantView (0 : Fin 2) (activity, conditional)) =
      dominantActivityCount activity := by
  change (∑ row, (sparseBit
      (sparseSeedOfDominantView (0 : Fin 2) (activity, conditional) row 0)).natAbs ^ 2) =
    (boolSupport activity).card
  calc
    (∑ row, (sparseBit
        (sparseSeedOfDominantView (0 : Fin 2)
          (activity, conditional) row 0)).natAbs ^ 2) =
        ∑ row, if activity row = true then 1 else 0 :=
      Finset.sum_congr rfl fun row _ =>
        reconstructedDominantSquare activity conditional row
    _ = (boolSupport activity).card := by
      unfold boolSupport
      exact Finset.sum_boole (R := ℕ)
        (fun row : Fin 192 => activity row = true) Finset.univ

theorem reconstructed_failure_of_cross_negative
    (activity : DominantActivity 192)
    (hcount : (dominantActivityCount activity : ℕ) = 12)
    (conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2))
    (hcross : conditionalCrossSum activity conditional < 0) :
    L2ThresholdLowerFailure (NonnegativeRatio.ofNat 12) 100 301 witness
      (sparseMatrixOfDominantView (0 : Fin 2) (activity, conditional)) := by
  apply failure_of_count_eq_twelve_crossSum_neg
  · rw [dominantCount_sparseSeedOfDominantView activity conditional]
    exact hcount
  · simpa [sparseMatrixOfDominantView] using
      (crossSum_sparseSeedOfDominantView activity conditional ▸ hcross)

def embedConditionalNegative
    (activity : DominantActivity 192)
    (hcount : (dominantActivityCount activity : ℕ) = 12) :
    {conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2) //
        conditionalCrossSum activity conditional < 0} →
      {conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2) //
        L2ThresholdLowerFailure (NonnegativeRatio.ofNat 12) 100 301 witness
          (sparseMatrixOfDominantView (0 : Fin 2) (activity, conditional))} :=
  fun conditional =>
    ⟨conditional.1,
      reconstructed_failure_of_cross_negative activity hcount
        conditional.1 conditional.2⟩

theorem embedConditionalNegative_injective
    (activity : DominantActivity 192)
    (hcount : (dominantActivityCount activity : ℕ) = 12) :
    Function.Injective (embedConditionalNegative activity hcount) := by
  intro left right heq
  apply Subtype.ext
  exact congrArg (fun value => value.1) heq

theorem conditional_negative_card_le_failure_card
    (activity : DominantActivity 192)
    (hcount : (dominantActivityCount activity : ℕ) = 12) :
    Nat.card
        {conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2) //
          conditionalCrossSum activity conditional < 0} ≤
      Nat.card
        {conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2) //
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat 12) 100 301 witness
            (sparseMatrixOfDominantView (0 : Fin 2) (activity, conditional))} :=
  Nat.card_le_card_of_injective
    (embedConditionalNegative activity hcount)
    (embedConditionalNegative_injective activity hcount)

theorem quarter_le_nat_ratio {total negative : ℕ}
    (htotalPos : 0 < total) (htotal : total ≤ 4 * negative) :
    (1 / 4 : ℝ) ≤ (negative : ℝ) / total := by
  have htotalPosReal : (0 : ℝ) < total := by exact_mod_cast htotalPos
  apply (le_div_iff₀ htotalPosReal).2
  have htotalReal : (total : ℝ) ≤ 4 * negative := by exact_mod_cast htotal
  linarith

set_option maxRecDepth 10000 in
theorem conditional_failure_probability_toReal_ge_quarter
    (activity : DominantActivity 192)
    (hcount : (dominantActivityCount activity : ℕ) = 12) :
    (1 / 4 : ℝ) ≤
      (eventProbability
        (dominantConditionalMatrixPMF (0 : Fin 2) activity)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 12) 100 301 witness)).toReal := by
  classical
  rw [dominantConditionalMatrixPMF,
    Probability.eventProbability_map_uniform_eq_card]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]
  let total := Fintype.card
    (DominantConditionalSeeds (m := 192) (0 : Fin 2))
  let negative := Fintype.card
    {conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2) //
      conditionalCrossSum activity conditional < 0}
  let failure := Fintype.card
    {conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2) //
      L2ThresholdLowerFailure (NonnegativeRatio.ofNat 12) 100 301 witness
        (sparseMatrixOfDominantView (0 : Fin 2) (activity, conditional))}
  have htotal : total ≤ 4 * negative := by
    exact conditional_total_card_le_four_negative_card activity hcount
  have hnegative : negative ≤ failure := by
    dsimp only [negative, failure]
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
    exact conditional_negative_card_le_failure_card activity hcount
  have htotalPosNat : 0 < total := Fintype.card_pos
  have htotalPosReal : (0 : ℝ) < total := by exact_mod_cast htotalPosNat
  change (1 / 4 : ℝ) ≤ (failure : ℝ) * (total : ℝ)⁻¹
  have hquarter : (1 / 4 : ℝ) ≤ (negative : ℝ) / total :=
    quarter_le_nat_ratio htotalPosNat htotal
  calc
    (1 / 4 : ℝ) ≤ (negative : ℝ) / total := hquarter
    _ ≤ (failure : ℝ) / total := by
      gcongr
    _ = (failure : ℝ) * (total : ℝ)⁻¹ := by rw [div_eq_mul_inv]

def conditionalFailureEquivOfCountLtTwelve
    (activity : DominantActivity 192)
    (hcount : (dominantActivityCount activity : ℕ) < 12) :
    DominantConditionalSeeds (m := 192) (0 : Fin 2) ≃
      {conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2) //
        L2ThresholdLowerFailure (NonnegativeRatio.ofNat 12) 100 301 witness
          (sparseMatrixOfDominantView (0 : Fin 2) (activity, conditional))} where
  toFun conditional :=
    ⟨conditional, failure_of_dominantCount_lt_twelve
      (sparseSeedOfDominantView (0 : Fin 2) (activity, conditional))
      (by
        rw [dominantCount_sparseSeedOfDominantView activity conditional]
        exact hcount)⟩
  invFun conditional := conditional.1
  left_inv _ := rfl
  right_inv conditional := by apply Subtype.ext; rfl

theorem conditional_failure_probability_toReal_eq_one_of_count_lt_twelve
    (activity : DominantActivity 192)
    (hcount : (dominantActivityCount activity : ℕ) < 12) :
    (eventProbability
      (dominantConditionalMatrixPMF (0 : Fin 2) activity)
      (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 12) 100 301 witness)).toReal = 1 := by
  classical
  rw [dominantConditionalMatrixPMF,
    Probability.eventProbability_map_uniform_eq_card]
  rw [show Fintype.card
      {conditional : DominantConditionalSeeds (m := 192) (0 : Fin 2) //
        L2ThresholdLowerFailure (NonnegativeRatio.ofNat 12) 100 301 witness
          (sparseMatrixOfDominantView (0 : Fin 2) (activity, conditional))} =
      Fintype.card (DominantConditionalSeeds (m := 192) (0 : Fin 2)) by
    exact Fintype.card_congr
      (conditionalFailureEquivOfCountLtTwelve activity hcount).symm]
  rw [ENNReal.mul_inv_cancel]
  · norm_num
  · exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos :
      0 < Fintype.card (DominantConditionalSeeds (m := 192) (0 : Fin 2))))
  · finiteness

noncomputable def conditionalLowerProfile (k : Fin 193) : ℝ :=
  if (k : ℕ) = 11 then 1 else if (k : ℕ) = 12 then 1 / 4 else 0

theorem conditionalLowerProfile_nonneg (k : Fin 193) :
    0 ≤ conditionalLowerProfile k := by
  unfold conditionalLowerProfile
  split_ifs <;> norm_num

theorem conditional_failure_probability_toReal_ge_profile
    (activity : DominantActivity 192) :
    conditionalLowerProfile (dominantActivityCount activity) ≤
      (eventProbability
        (dominantConditionalMatrixPMF (0 : Fin 2) activity)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 12) 100 301 witness)).toReal := by
  unfold conditionalLowerProfile
  split_ifs with h11 h12
  · rw [conditional_failure_probability_toReal_eq_one_of_count_lt_twelve
      activity (by omega)]
  · exact conditional_failure_probability_toReal_ge_quarter activity h12
  · exact ENNReal.toReal_nonneg

theorem failure_probability_toReal_ge_binomial_profile :
    dominantBinomialAverageAt 192 conditionalLowerProfile ≤
      (eventProbability (sparseRademacherMatrix 192 2)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 12) 100 301 witness)).toReal := by
  rw [sparseMatrix_eventProbability_toReal_eq_dominantAverage
    (0 : Fin 2)
    (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 12) 100 301 witness)]
  rw [← dominantActivityAverage_eq_binomialAverage_at 192 conditionalLowerProfile]
  apply Finset.sum_le_sum
  intro activity _
  exact mul_le_mul_of_nonneg_left
    (conditional_failure_probability_toReal_ge_profile activity)
    (by positivity)

def kEleven : Fin 193 := ⟨11, by decide⟩
def kTwelve : Fin 193 := ⟨12, by decide⟩

set_option maxRecDepth 10000 in
theorem binomial_profile_ge_two_bins :
    (((192 : ℕ).choose 11 : ℝ) / 2 ^ 192) +
        (((192 : ℕ).choose 12 : ℝ) / 2 ^ 192) * (1 / 4) ≤
      dominantBinomialAverageAt 192 conditionalLowerProfile := by
  unfold dominantBinomialAverageAt
  let term : Fin 193 → ℝ := fun k =>
    (((192 : ℕ).choose (k : ℕ) : ℝ) / 2 ^ 192) * conditionalLowerProfile k
  have hnonneg : ∀ k : Fin 193, 0 ≤ term k := by
    intro k
    exact mul_nonneg (by positivity) (conditionalLowerProfile_nonneg k)
  calc
    (((192 : ℕ).choose 11 : ℝ) / 2 ^ 192) +
          (((192 : ℕ).choose 12 : ℝ) / 2 ^ 192) * (1 / 4) =
        ∑ k ∈ ({kEleven, kTwelve} : Finset (Fin 193)), term k := by
      simp [term, kEleven, kTwelve, conditionalLowerProfile]
    _ ≤ ∑ k ∈ (Finset.univ : Finset (Fin 193)), term k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ {kEleven, kTwelve})
      intro k _ _
      exact hnonneg k
    _ = ∑ k : Fin 193,
        (((192 : ℕ).choose (k : ℕ) : ℝ) / 2 ^ 192) *
          conditionalLowerProfile k := rfl

private theorem two_bin_scaled_gt :
    4 * 2 ^ (192 - 132) <
      4 * ((192 : ℕ).choose 11) + (192 : ℕ).choose 12 := by
  set_option maxRecDepth 10000 in
    decide +kernel

theorem failureTarget132_toReal_lt_two_bins :
    (failureTarget 132).toReal <
      (((192 : ℕ).choose 11 : ℝ) / 2 ^ 192) +
        (((192 : ℕ).choose 12 : ℝ) / 2 ^ 192) * (1 / 4) := by
  unfold failureTarget
  rw [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  have hscaled :
      (4 * 2 ^ (192 - 132) : ℝ) <
        4 * ((192 : ℕ).choose 11) + (192 : ℕ).choose 12 := by
    exact_mod_cast two_bin_scaled_gt
  norm_num only [Nat.reduceSub] at hscaled
  field_simp
  norm_num only [Nat.cast_ofNat]
  nlinarith [hscaled]

theorem failureProbability_gt_failureTarget132 :
    eventProbability (sparseRademacherMatrix 192 2)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 12) 100 301 witness) >
      failureTarget 132 := by
  change failureTarget 132 <
    eventProbability (sparseRademacherMatrix 192 2)
      (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 12) 100 301 witness)
  rw [← ENNReal.toReal_lt_toReal]
  · exact failureTarget132_toReal_lt_two_bins |>.trans_le
      (binomial_profile_ge_two_bins.trans
        failure_probability_toReal_ge_binomial_profile)
  · unfold failureTarget
    exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by norm_num))
  · unfold eventProbability
    exact PMF.apply_ne_top _ _

/-- The 192-row balanced-ternary threshold-floor-12 theorem is false at
132 bits. -/
theorem bits132_false :
    ¬ L2ThresholdLowerTailAt parameters (failureTarget 132) := by
  intro h
  have hclaimed := h 301 2 witness 100 (by norm_num) witness_centered
    (by norm_num) (by simp [InputThresholdAtMostNorm, witness_sqNorm])
    (by norm_num [InputThresholdWithinModulus, parameters,
      NonnegativeRatio.ofNat])
  simp only [parameters, ProjectionDistribution.matrixPMF_balancedTernary] at hclaimed
  exact (not_lt_of_ge failureProbability_gt_failureTarget132.le) hclaimed

end CertifiedJL.Counterexamples.ThresholdLowerRows192Floor12
