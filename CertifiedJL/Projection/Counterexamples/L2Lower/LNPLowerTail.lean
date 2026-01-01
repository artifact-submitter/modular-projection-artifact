/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Activity
import CertifiedJL.Model.Modular.Centered
import CertifiedJL.Probability.Finite.Counting
import CertifiedJL.Statements.L2.Lower
import Mathlib.Tactic

/-!
# Exact counterexamples to the LNP lower-tail premises

This module records finite counterexamples to the `κ = 1` and `κ = 2`
lower-tail estimates used in LNP Lemmas 2.8--2.10.  The `κ = 2` law below is
the sum of two independent balanced-ternary entries, represented by four
uniform bits at each matrix position.
-/

open scoped BigOperators ENNReal

namespace CertifiedJL.Counterexamples.LNPLowerTail

open Probability

set_option maxRecDepth 10000

/-! ## The `κ = 1` counterexample -/

/-- The one-coordinate basis-vector witness for the `κ = 1` estimate. -/
def kappaOneWitness : Fin 1 → ℤ := fun _ => 1

private theorem sparseBit_sq_eq_activity (pair : Bool × Bool) :
    (sparseBit pair).natAbs ^ 2 = if sparsePairActivity pair then 1 else 0 := by
  rcases pair with ⟨left, right⟩
  cases left <;> cases right <;> decide

private theorem sparseBit_sq_eq_dominantView {rows : ℕ}
    (seed : SparseSeed rows 1) (row : Fin rows) :
    (sparseBit (seed row 0)).natAbs ^ 2 =
      if (dominantSeedView (0 : Fin 1) seed).1 row then 1 else 0 := by
  change (sparseBit (seed row 0)).natAbs ^ 2 =
    if sparsePairActivity (seed row 0) then 1 else 0
  exact sparseBit_sq_eq_activity (seed row 0)

set_option maxRecDepth 10000 in
private theorem projectionSqNorm_kappaOne_sparseMatrix {rows : ℕ}
    (seed : SparseSeed rows 1) :
    projectionSqNorm (sparseMatrix seed) kappaOneWitness =
      (dominantActivityCount
        (matrixDominantActivity (0 : Fin 1) (sparseMatrix seed)) : ℕ) := by
  classical
  rw [matrixDominantActivity_sparseMatrix]
  simp only [projectionSqNorm, rowDot, kappaOneWitness, mul_one, Fin.sum_univ_one,
    dominantActivityCount, boolSupport, sparseMatrix, sparseRow]
  rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro row _
  exact sparseBit_sq_eq_dominantView seed row

/-- The exact discrete `κ = 1` small-squared-norm probability is the lower
binomial tail through squared norm `12`. -/
theorem kappaOneProbability_exact :
    eventProbability (sparseRademacherMatrix 256 1)
        (fun J => projectionSqNorm J kappaOneWitness < 13) =
      ((∑ k ∈ Finset.range 13, (256 : ℕ).choose k : ℕ) : ℝ≥0∞) *
        ((2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [sparseRademacherMatrix_eq_map_uniformSeed]
  rw [eventProbability_map_congr
    (PMF.uniformOfFintype (SparseSeed 256 1))
    sparseMatrix sparseMatrix
    (fun J => projectionSqNorm J kappaOneWitness < 13)
    (fun J =>
      (dominantActivityCount
        (matrixDominantActivity (0 : Fin 1) J) : ℕ) < 13)
    (fun seed => by rw [projectionSqNorm_kappaOne_sparseMatrix])]
  rw [← sparseRademacherMatrix_eq_map_uniformSeed]
  exact sparse_dominantActivityCount_lt_probability_eq (0 : Fin 1) 13

/-- The discrete `κ = 1` lower event at squared threshold `13` has
probability strictly greater than `2⁻²⁵⁶`. -/
theorem kappaOneCounterexample :
    eventProbability (sparseRademacherMatrix 256 1)
        (fun J => projectionSqNorm J kappaOneWitness < 13) >
      failureTarget 256 := by
  have hsum :
      1 < ∑ k ∈ Finset.range 13, (256 : ℕ).choose k := by
    have hone : 1 ∈ Finset.range 13 := by simp
    have hle : (256 : ℕ).choose 1 ≤
        ∑ k ∈ Finset.range 13, (256 : ℕ).choose k :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hone
    have hchoose : 1 < (256 : ℕ).choose 1 := by norm_num
    exact hchoose.trans_le hle
  rw [kappaOneProbability_exact]
  change
    (2 : ℝ≥0∞)⁻¹ ^ 256 <
      ((∑ k ∈ Finset.range 13, (256 : ℕ).choose k : ℕ) : ℝ≥0∞) *
        ((2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹
  rw [← ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  field_simp
  have hsumReal : (1 : ℝ) <
      ∑ k ∈ Finset.range 13, (256 : ℕ).choose k := by
    exact_mod_cast hsum
  simp only [Nat.cast_ofNat, Nat.cast_pow]
  calc
    (2 : ℝ) ^ 256 = 2 ^ 256 * 1 := by ring
    _ < 2 ^ 256 *
        (↑(∑ k ∈ Finset.range 13, (256 : ℕ).choose k) : ℝ) :=
      mul_lt_mul_of_pos_left hsumReal (by positivity)

/-- The exact `κ = 1` probability formula together with its strict violation
of the printed `2⁻²⁵⁶` bound. -/
theorem kappaOnePrintedCounterexample :
    eventProbability (sparseRademacherMatrix 256 1)
        (fun J => projectionSqNorm J kappaOneWitness < 13) =
        ((∑ k ∈ Finset.range 13, (256 : ℕ).choose k : ℕ) : ℝ≥0∞) *
          ((2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ ∧
      eventProbability (sparseRademacherMatrix 256 1)
          (fun J => projectionSqNorm J kappaOneWitness < 13) >
        failureTarget 256 :=
  ⟨kappaOneProbability_exact, kappaOneCounterexample⟩

/-! ## The `κ = 2` counterexample -/

/-- Four uniform bits grouped as two independent balanced-ternary seeds. -/
abbrev BinTwoEntrySeed := (Bool × Bool) × (Bool × Bool)

/-- Independent four-bit seeds for every entry of a `κ = 2` matrix. -/
abbrev BinTwoSeed (rows d : ℕ) := Fin rows → Fin d → BinTwoEntrySeed

/-- One `κ = 2` entry, as the sum of two independent balanced-ternary entries. -/
def binTwoEntry (seed : BinTwoEntrySeed) : ℤ :=
  sparseBit seed.1 + sparseBit seed.2

/-- Interpret the independent four-bit seeds as an integer matrix. -/
def binTwoMatrix {rows d : ℕ} (seed : BinTwoSeed rows d) :
    Fin rows → Fin d → ℤ :=
  fun row i => binTwoEntry (seed row i)

/-- The finite `κ = 2` matrix distribution used by LNP. -/
noncomputable def binTwoMatrixPMF (rows d : ℕ) :
    PMF (Fin rows → Fin d → ℤ) :=
  (PMF.uniformOfFintype (BinTwoSeed rows d)).map binTwoMatrix

/-- The one-coordinate basis-vector witness for the `κ = 2` estimate. -/
def kappaTwoWitness : Fin 1 → ℤ := fun _ => 1

private def rowValue (seed : BinTwoEntrySeed) : ℤ := binTwoEntry seed

private abbrev OneRowSeed := {seed : BinTwoEntrySeed // (rowValue seed).natAbs = 1}
private abbrev ZeroRowSeed := {seed : BinTwoEntrySeed // rowValue seed = 0}

private theorem card_oneRowSeed : Fintype.card OneRowSeed = 8 := by decide
private theorem card_zeroRowSeed : Fintype.card ZeroRowSeed = 6 := by decide

private abbrev Support25 :=
  {support : Finset (Fin 256) // support.card = 25}

private abbrev SimpleEventSeed :=
  Σ support : Support25,
    ({i : Fin 256 // i ∈ support.1} → OneRowSeed) ×
      ({i : Fin 256 // i ∉ support.1} → ZeroRowSeed)

private def assembleSimpleEventSeed (x : SimpleEventSeed) : BinTwoSeed 256 1 :=
  fun row _ =>
    if hrow : row ∈ x.1.1 then
      (x.2.1 ⟨row, hrow⟩).1
    else
      (x.2.2 ⟨row, hrow⟩).1

private theorem assembleSimpleEventSeed_support (x : SimpleEventSeed) :
    Finset.univ.filter
        (fun row =>
          (rowValue (assembleSimpleEventSeed x row 0)).natAbs = 1) =
      x.1.1 := by
  classical
  ext row
  by_cases hrow : row ∈ x.1.1
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hrow,
      iff_true]
    rw [assembleSimpleEventSeed, dif_pos hrow]
    exact (x.2.1 ⟨row, hrow⟩).2
  · have hzero := (x.2.2 ⟨row, hrow⟩).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hrow,
      iff_false]
    rw [assembleSimpleEventSeed, dif_neg hrow, hzero]
    norm_num

private theorem assembleSimpleEventSeed_injective :
    Function.Injective assembleSimpleEventSeed := by
  classical
  rintro ⟨support, oneSeeds, zeroSeeds⟩
    ⟨support', oneSeeds', zeroSeeds'⟩ h
  have hsupportVal : support.1 = support'.1 := by
    rw [← assembleSimpleEventSeed_support
      ⟨support, oneSeeds, zeroSeeds⟩,
      ← assembleSimpleEventSeed_support
        ⟨support', oneSeeds', zeroSeeds'⟩]
    exact congrArg
      (fun seed => Finset.univ.filter
        (fun row => (rowValue (seed row 0)).natAbs = 1)) h
  have hsupport : support = support' := Subtype.ext hsupportVal
  subst support'
  have hone : oneSeeds = oneSeeds' := by
    funext i
    apply Subtype.ext
    have hi := congrFun (congrFun h i.1) (0 : Fin 1)
    simpa [assembleSimpleEventSeed, i.2] using hi
  have hzero : zeroSeeds = zeroSeeds' := by
    funext i
    apply Subtype.ext
    have hi := congrFun (congrFun h i.1) (0 : Fin 1)
    simpa [assembleSimpleEventSeed, i.2] using hi
  subst oneSeeds'
  subst zeroSeeds'
  rfl

private theorem projectionSqNorm_eq_oneSupport_card {rows : ℕ}
    (seed : BinTwoSeed rows 1)
    (hrows : ∀ row,
      (binTwoEntry (seed row 0)).natAbs = 0 ∨
        (binTwoEntry (seed row 0)).natAbs = 1) :
    projectionSqNorm (binTwoMatrix seed) kappaTwoWitness =
      (Finset.univ.filter
        (fun row => (binTwoEntry (seed row 0)).natAbs = 1)).card := by
  classical
  simp only [projectionSqNorm, rowDot, kappaTwoWitness, mul_one, Fin.sum_univ_one,
    binTwoMatrix]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro row _
  rcases hrows row with hzero | hone
  · simp [hzero]
  · simp [hone]

private theorem projectionSqNorm_assembleSimpleEventSeed (x : SimpleEventSeed) :
    projectionSqNorm (binTwoMatrix (assembleSimpleEventSeed x)) kappaTwoWitness = 25 := by
  rw [projectionSqNorm_eq_oneSupport_card]
  · rw [show
      Finset.univ.filter (fun row =>
          (binTwoEntry (assembleSimpleEventSeed x row 0)).natAbs = 1) =
        x.1.1 by
      apply Finset.ext
      intro row
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hrow : row ∈ x.1.1
      · rw [assembleSimpleEventSeed, dif_pos hrow]
        constructor
        · intro _
          exact hrow
        · intro _
          simpa only [rowValue] using (x.2.1 ⟨row, hrow⟩).2
      · rw [assembleSimpleEventSeed, dif_neg hrow]
        have hzero := (x.2.2 ⟨row, hrow⟩).2
        simp only [rowValue] at hzero
        constructor
        · intro hone
          rw [hzero] at hone
          norm_num at hone
        · intro hs
          exact (hrow hs).elim]
    exact x.1.2
  · intro row
    by_cases hrow : row ∈ x.1.1
    · right
      rw [assembleSimpleEventSeed, dif_pos hrow]
      simpa only [rowValue] using (x.2.1 ⟨row, hrow⟩).2
    · left
      rw [assembleSimpleEventSeed, dif_neg hrow]
      have hzero := (x.2.2 ⟨row, hrow⟩).2
      simp only [rowValue] at hzero
      rw [hzero]
      norm_num

private def simpleEventEmbedding :
    SimpleEventSeed ↪
      {seed : BinTwoSeed 256 1 //
        projectionSqNorm (binTwoMatrix seed) kappaTwoWitness < 26} where
  toFun x := ⟨assembleSimpleEventSeed x, by
    rw [projectionSqNorm_assembleSimpleEventSeed]
    norm_num⟩
  inj' x y h := assembleSimpleEventSeed_injective (congrArg Subtype.val h)

set_option maxRecDepth 10000 in
private theorem card_simpleEventSeed :
    Fintype.card SimpleEventSeed =
      (256 : ℕ).choose 25 * 8 ^ 25 * 6 ^ 231 := by
  classical
  simp only [SimpleEventSeed, Fintype.card_sigma, Fintype.card_prod,
    Fintype.card_fun, card_oneRowSeed, card_zeroRowSeed]
  rw [show
      (∑ support : Support25,
        8 ^ Fintype.card {i : Fin 256 // i ∈ support.1} *
          6 ^ Fintype.card {i : Fin 256 // i ∉ support.1}) =
        ∑ _support : Support25, 8 ^ 25 * 6 ^ 231 by
    apply Finset.sum_congr rfl
    intro support _
    rw [show Fintype.card {i : Fin 256 // i ∈ support.1} = 25 by
      simpa using support.2]
    rw [Fintype.card_subtype_compl]
    simp [support.2]]
  have hsupports : Fintype.card Support25 = (256 : ℕ).choose 25 := by
    simp [Support25]
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [Nat.mul_assoc]
  rw [show (Finset.univ : Finset Support25).card =
      (256 : ℕ).choose 25 by
    simpa only [Finset.card_univ, Nat.cast_id] using hsupports]
  simp only [Nat.cast_id]

private theorem card_binTwoSeed_256_1 :
    Fintype.card (BinTwoSeed 256 1) = 16 ^ 256 := by
  simp [BinTwoSeed, BinTwoEntrySeed]

set_option maxRecDepth 10000 in
private theorem simpleEvent_probability_le :
    ((256 : ℕ).choose 25 * 8 ^ 25 * 6 ^ 231 : ℝ≥0∞) *
        ((16 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ ≤
      eventProbability (binTwoMatrixPMF 256 1)
        (fun J => projectionSqNorm J kappaTwoWitness < 26) := by
  rw [binTwoMatrixPMF]
  rw [Probability.eventProbability_map_uniform_eq_card]
  rw [card_binTwoSeed_256_1]
  have hcard :
      (256 : ℕ).choose 25 * 8 ^ 25 * 6 ^ 231 ≤
      Fintype.card
        {seed : BinTwoSeed 256 1 //
          projectionSqNorm (binTwoMatrix seed) kappaTwoWitness < 26} := by
    rw [← card_simpleEventSeed]
    exact Fintype.card_le_of_injective _ simpleEventEmbedding.injective
  have hcard' := (Nat.cast_le (α := ℝ≥0∞)).2 hcard
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hcard'
  exact mul_le_mul hcard' le_rfl bot_le bot_le

/-- The exact integer comparison behind the `κ = 2` probability violation.
This is the cross-multiplied form
`choose 256 25 * 3^231 / 2^718 > 2⁻²⁵⁶`. -/
theorem kappaTwo_integerComparison :
    (2 : ℕ) ^ 462 < (256 : ℕ).choose 25 * 3 ^ 231 := by
  rw [Nat.choose_eq_fast_choose]
  decide +kernel

set_option maxRecDepth 10000 in
private theorem simpleEvent_probability_gt :
    ((256 : ℕ).choose 25 * 8 ^ 25 * 6 ^ 231 : ℝ≥0∞) *
        ((16 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ > failureTarget 256 := by
  change
    (2 : ℝ≥0∞)⁻¹ ^ 256 <
      ((256 : ℕ).choose 25 * 8 ^ 25 * 6 ^ 231 : ℝ≥0∞) *
        ((16 ^ 256 : ℕ) : ℝ≥0∞)⁻¹
  have hscaled :
      (16 : ℕ) ^ 256 <
        2 ^ 256 * ((256 : ℕ).choose 25 * 8 ^ 25 * 6 ^ 231) := by
    rw [Nat.choose_eq_fast_choose]
    decide +kernel
  rw [← ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_mul]
  field_simp
  exact_mod_cast hscaled

/-- For a one-coordinate input and the exact `κ = 2` row distribution, the
unreduced squared-norm event below `26` has probability greater than
`2⁻²⁵⁶`. -/
theorem kappaTwoCounterexample :
    eventProbability (binTwoMatrixPMF 256 1)
        (fun J => projectionSqNorm J kappaTwoWitness < 26) >
      failureTarget 256 :=
  simpleEvent_probability_gt.trans_le simpleEvent_probability_le

private theorem centered_binTwo_row (seed : BinTwoSeed 256 1)
    (row : Fin 256) :
    centeredMod 41 (rowDot (binTwoMatrix seed) kappaTwoWitness row) =
      rowDot (binTwoMatrix seed) kappaTwoWitness row := by
  rw [centeredMod_eq_self (by norm_num)]
  simp only [rowDot, kappaTwoWitness, mul_one, Fin.sum_univ_one,
    binTwoMatrix, binTwoEntry]
  rcases hleft : (seed row 0).1 with ⟨a, b⟩
  rcases hright : (seed row 0).2 with ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [sparseBit, centeredInterval]

private theorem modularProjectionSqNorm_binTwo_eq_projectionSqNorm (seed : BinTwoSeed 256 1) :
    modularProjectionSqNorm 41 (binTwoMatrix seed) kappaTwoWitness =
      projectionSqNorm (binTwoMatrix seed) kappaTwoWitness := by
  unfold modularProjectionSqNorm projectionSqNorm
  apply Finset.sum_congr rfl
  intro row _
  rw [centered_binTwo_row]

/-- The exact admissible instance `(q,d,b,w) = (41,1,1,e₁)` refutes the
unshifted modular conclusion stated in LNP Lemma 2.10.  The counterexample
does not by itself refute the masked conclusion of Lemma 2.9. -/
theorem lemmaTwoTenCounterexample :
    Odd 41 ∧
      CenteredInput 41 kappaTwoWitness ∧
      0 < (1 : ℕ) ∧
      InputThresholdAtMostNorm 1 kappaTwoWitness ∧
      41 * 1 * 1 ≤ 41 ∧
      eventProbability (binTwoMatrixPMF 256 1)
          (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 26)
            1 41 kappaTwoWitness) >
        failureTarget 256 := by
  refine ⟨by norm_num, ?_, by norm_num, ?_, by norm_num, ?_⟩
  · intro i
    fin_cases i
    norm_num [kappaTwoWitness, centeredInterval]
  · norm_num [InputThresholdAtMostNorm, kappaTwoWitness, sqNorm]
  · rw [show
      eventProbability (binTwoMatrixPMF 256 1)
          (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 26)
            1 41 kappaTwoWitness) =
        eventProbability (binTwoMatrixPMF 256 1)
          (fun J => projectionSqNorm J kappaTwoWitness < 26) by
      rw [binTwoMatrixPMF]
      exact eventProbability_map_congr
        (PMF.uniformOfFintype (BinTwoSeed 256 1))
        binTwoMatrix binTwoMatrix
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 26)
          1 41 kappaTwoWitness)
        (fun J => projectionSqNorm J kappaTwoWitness < 26)
        (fun seed => by
          simp only [L2ThresholdLowerFailure, NonnegativeRatio.ofNat,
            one_mul, Nat.reducePow]
          rw [modularProjectionSqNorm_binTwo_eq_projectionSqNorm])]
    exact kappaTwoCounterexample

end CertifiedJL.Counterexamples.LNPLowerTail
