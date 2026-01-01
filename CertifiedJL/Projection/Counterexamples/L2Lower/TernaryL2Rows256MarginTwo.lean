/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Finite.WeightedConvolution
import CertifiedJL.Projection.Counterexamples.Shared.SparseAllOnesRow
import CertifiedJL.Statements.L2.Lower
import Mathlib.Tactic

/-!
# The 256-row modulus-two obstruction at squared floor 29

For `q = 9`, public threshold `b = 4`, and the all-ones input in dimension
16, one row has centered squared energy in `{0, 1, 4, 9, 16}`.  Its exact
five-class weights have denominator `2^32`.  A truncated exact convolution
over 256 rows proves that the strict energy event below `29 * 4^2 = 464`
has probability greater than `2^-128`.

The fixed witness is admissible for every exact rational modulus margin at
most `9/4`; the public margin-two theorem is a specialization.
-/

open scoped BigOperators ENNReal

namespace CertifiedJL.Counterexamples.TernaryL2Rows256MarginTwo

open Probability Probability.SparseAllOnes

def nineFourths : NonnegativeRatio :=
  { numerator := 9, denominator := 4, denominator_pos := by decide }

def parameters (margin : NonnegativeRatio) : L2ThresholdLowerParameters :=
  { distribution := .balancedTernary
    rows := 256
    squaredNormFloor := NonnegativeRatio.ofNat 29
    modulusMargin := margin }

def parametersTwo : L2ThresholdLowerParameters :=
  parameters (NonnegativeRatio.ofNat 2)

def witness : Fin 16 → ℤ := fun _ => 1

theorem witness_centered : CenteredInput 9 witness := by
  intro i
  simp [witness, centeredInterval]

theorem witness_sqNorm : sqNorm witness = 4 ^ 2 := by
  norm_num [sqNorm, witness]

/-- The true count of the 32 row bits, bundled with its elementary bound. -/
def trueCountOutcome (seed : SparseRowSeed 16) : Fin 33 :=
  ⟨sparseRowTrueCount seed, by
    have hle := Finset.card_le_univ (boolSupport (sparseRowSeedEquivBits 16 seed))
    simp only [Fintype.card_fin] at hle
    unfold sparseRowTrueCount
    omega⟩

/-- The centered absolute residue class, one of `0,1,2,3,4`. -/
def rowClassOfTrueCount (count : Fin 33) : Fin 5 :=
  ⟨(centeredMod 9 (((count : ℕ) : ℤ) - 16)).natAbs, by
    have hmem := centeredMod_mem_centeredInterval (q := 9) (by norm_num)
      (((count : ℕ) : ℤ) - 16)
    simp only [centeredInterval, Set.mem_Icc] at hmem
    have habs : |centeredMod 9 (((count : ℕ) : ℤ) - 16)| ≤ (4 : ℤ) :=
      (abs_le).2 hmem
    rw [Int.abs_eq_natAbs] at habs
    have hle : (centeredMod 9 (((count : ℕ) : ℤ) - 16)).natAbs ≤ 4 := by
      exact_mod_cast habs
    omega⟩

def rowClass (seed : SparseRowSeed 16) : Fin 5 :=
  rowClassOfTrueCount (trueCountOutcome seed)

def classEnergy (outcome : Fin 5) : ℕ := outcome ^ 2

def rowEnergy (seed : SparseRowSeed 16) : ℕ :=
  (centeredMod 9 (sparseAllOnesRowSum seed)).natAbs ^ 2

def rowWeights : Fin 5 → ℕ :=
  ![607812102, 1154294424, 999371554, 823843664, 709645552]

theorem rowEnergy_eq_classEnergy (seed : SparseRowSeed 16) :
    rowEnergy seed = classEnergy (rowClass seed) := by
  rw [rowEnergy, sparseAllOnesRowSum_eq_trueCount]
  rfl

theorem card_trueCountOutcome_fiber (count : Fin 33) :
    Fintype.card {seed : SparseRowSeed 16 // trueCountOutcome seed = count} =
      (32 : ℕ).choose count := by
  let e :
      {seed : SparseRowSeed 16 // trueCountOutcome seed = count} ≃
        {seed : SparseRowSeed 16 // sparseRowTrueCount seed = count} :=
    Equiv.subtypeEquiv (Equiv.refl _) fun _ => by
      constructor
      · intro h
        exact congrArg Fin.val h
      · intro h
        apply Fin.ext
        exact h
  rw [Fintype.card_congr e, card_sparseRowTrueCount_fiber]

set_option maxRecDepth 10000 in
theorem card_rowClass_fiber (outcome : Fin 5) :
    Fintype.card {seed : SparseRowSeed 16 // rowClass seed = outcome} =
      rowWeights outcome := by
  change Fintype.card
      {seed : SparseRowSeed 16 //
        rowClassOfTrueCount (trueCountOutcome seed) = outcome} = _
  rw [card_composite_fiber_eq_sum trueCountOutcome rowClassOfTrueCount outcome]
  simp_rw [card_trueCountOutcome_fiber]
  fin_cases outcome <;> decide +kernel

theorem classEnergy_values :
    (∀ outcome : Fin 5,
      classEnergy outcome = ![0, 1, 4, 9, 16] outcome) := by
  intro outcome
  fin_cases outcome <;> rfl

theorem rowDot_sparseMatrix_witness
    (seed : SparseSeed 256 16) (row : Fin 256) :
    rowDot (sparseMatrix seed) witness row =
      sparseAllOnesRowSum (seed row) := by
  simp [rowDot, sparseMatrix, sparseRow, witness, sparseAllOnesRowSum]

theorem modularProjectionSqNorm_sparseMatrix (seed : SparseSeed 256 16) :
    modularProjectionSqNorm 9 (sparseMatrix seed) witness =
      ∑ row, rowEnergy (seed row) := by
  apply Finset.sum_congr rfl
  intro row _
  rw [rowDot_sparseMatrix_witness]
  rfl

theorem failure_iff_strictEnergy (seed : SparseSeed 256 16) :
    L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29) 4 9 witness
        (sparseMatrix seed) ↔
      (∑ row, rowEnergy (seed row)) < 464 := by
  rw [L2ThresholdLowerFailure, modularProjectionSqNorm_sparseMatrix]
  norm_num [NonnegativeRatio.ofNat]

theorem card_strictEnergy :
    Fintype.card {seed : SparseSeed 256 16 //
        (∑ row, rowEnergy (seed row)) < 464} =
      strictWeightedCount rowWeights classEnergy 256 464 := by
  exact card_strictEnergy_eq_strictWeightedCount
    rowClass rowEnergy rowWeights classEnergy rowEnergy_eq_classEnergy
    card_rowClass_fiber 256 464

theorem probability_exact :
    eventProbability (sparseRademacherMatrix 256 16)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29) 4 9 witness) =
      (strictWeightedCount rowWeights classEnergy 256 464 : ℝ≥0∞) *
        (((2 ^ 32 : ℕ) ^ 256 : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [sparseRademacherMatrix_eq_map_uniformSeed]
  rw [eventProbability_map_congr
    (PMF.uniformOfFintype (SparseSeed 256 16)) sparseMatrix id
    (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29) 4 9 witness)
    (fun seed => (∑ row, rowEnergy (seed row)) < 464)
    (fun seed => by simpa using failure_iff_strictEnergy seed)]
  rw [PMF.map_id]
  rw [eventProbability_uniform_eq_card, card_strictEnergy,
    card_sparseSeed]

/-! ## Compact exact lower certificate

The certificate retains only class-count vectors with two energy-16 rows,
12--14 energy-9 rows, 45--55 energy-4 rows, and eight consecutive choices
of the energy-1 count.  All 264 retained vectors have total energy at most
463.  The remaining rows have energy zero.
-/

def certificateNumerator : ℕ :=
  ∑ n9 ∈ Finset.Icc 12 14,
    ∑ n4 ∈ Finset.Icc 45 55,
      let center := 431 - 9 * n9 - 4 * n4
      ∑ n1 ∈ Finset.Icc (center - 7) center,
        let n0 := 254 - n9 - n4 - n1
        (256 : ℕ).choose 2 * (254 : ℕ).choose n9 * (254 - n9).choose n4 *
          (254 - n9 - n4).choose n1 *
          709645552 ^ 2 * 823843664 ^ n9 * 999371554 ^ n4 *
          1154294424 ^ n1 * 607812102 ^ n0

def certificateCounts (n9 n4 n1 : ℕ) : Fin 5 → ℕ :=
  ![254 - n9 - n4 - n1, n1, n4, n9, 2]

def certificateVectors : Finset (Fin 5 → ℕ) :=
  (Finset.Icc 12 14).biUnion fun n9 =>
    (Finset.Icc 45 55).biUnion fun n4 =>
      let center := 431 - 9 * n9 - 4 * n4
      (Finset.Icc (center - 7) center).image fun n1 =>
        certificateCounts n9 n4 n1

def certificateMultinomialNumerator : ℕ :=
  ∑ counts ∈ certificateVectors,
    multinomialWeightedTerm rowWeights counts

set_option maxRecDepth 100000 in
theorem certificateNumerator_gt_two_pow_8064 :
    2 ^ 8064 < certificateNumerator := by
  rw [certificateNumerator]
  simp_rw [Nat.choose_eq_fast_choose]
  decide +kernel

set_option maxRecDepth 100000 in
theorem certificateMultinomialNumerator_gt_two_pow_8064 :
    2 ^ 8064 < certificateMultinomialNumerator := by
  decide +kernel

theorem certificateVectors_rows (counts : Fin 5 → ℕ)
    (hcounts : counts ∈ certificateVectors) :
    (∑ outcome, counts outcome) = 256 := by
  rw [certificateVectors] at hcounts
  simp only [Finset.mem_biUnion] at hcounts
  obtain ⟨n9, hn9, n4, hn4, hcounts⟩ := hcounts
  simp only [Finset.mem_image] at hcounts
  obtain ⟨n1, hn1, rfl⟩ := hcounts
  simp only [Finset.mem_Icc] at hn9 hn4 hn1
  simp [certificateCounts, Fin.sum_univ_succ]
  omega

theorem certificateVectors_energy (counts : Fin 5 → ℕ)
    (hcounts : counts ∈ certificateVectors) :
    (∑ outcome, counts outcome * classEnergy outcome) < 464 := by
  rw [certificateVectors] at hcounts
  simp only [Finset.mem_biUnion] at hcounts
  obtain ⟨n9, hn9, n4, hn4, hcounts⟩ := hcounts
  simp only [Finset.mem_image] at hcounts
  obtain ⟨n1, hn1, rfl⟩ := hcounts
  simp only [Finset.mem_Icc] at hn9 hn4 hn1
  simp [certificateCounts, classEnergy, Fin.sum_univ_succ]
  omega

theorem certificateMultinomialNumerator_le_strictWeightedCount :
    certificateMultinomialNumerator ≤
      strictWeightedCount rowWeights classEnergy 256 464 := by
  exact sum_multinomialWeightedTerm_le_strictWeightedCount
    rowWeights classEnergy 256 certificateVectors 464
      certificateVectors_rows certificateVectors_energy

theorem strictWeightedCount_gt_two_pow_8064 :
    2 ^ 8064 < strictWeightedCount rowWeights classEnergy 256 464 :=
  certificateMultinomialNumerator_gt_two_pow_8064.trans_le
    certificateMultinomialNumerator_le_strictWeightedCount

set_option maxRecDepth 100000 in
theorem probability_gt_failureTarget128 :
    eventProbability (sparseRademacherMatrix 256 16)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29) 4 9 witness) >
      failureTarget 128 := by
  rw [probability_exact]
  change
    (2 : ℝ≥0∞)⁻¹ ^ 128 <
      (strictWeightedCount rowWeights classEnergy 256 464 : ℝ≥0∞) *
        (((2 ^ 32 : ℕ) ^ 256 : ℕ) : ℝ≥0∞)⁻¹
  rw [← ENNReal.toReal_lt_toReal
    (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by norm_num)))
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.inv_ne_top.mpr (by positivity)))]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  field_simp
  have hcountReal : (2 : ℝ) ^ 8064 <
      strictWeightedCount rowWeights classEnergy 256 464 := by
    exact_mod_cast strictWeightedCount_gt_two_pow_8064
  calc
    (↑((2 ^ 32 : ℕ) ^ 256) : ℝ) =
        ((2 : ℝ) ^ 32) ^ 256 := by
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    _ = (2 : ℝ) ^ (32 * 256) := by rw [pow_mul]
    _ = (2 : ℝ) ^ (128 + 8064) := by norm_num
    _ = (2 : ℝ) ^ 128 * 2 ^ 8064 := by rw [pow_add]
    _ < 2 ^ 128 *
        (strictWeightedCount rowWeights classEnergy 256 464 : ℝ) :=
      mul_lt_mul_of_pos_left hcountReal (by positivity)

/-- The fixed witness is admissible for every exact rational modulus margin
at most `9/4`, and its strict floor-29 failure probability exceeds the
128-bit budget. -/
theorem admissible_family (margin : NonnegativeRatio)
    (hmargin : margin.LE nineFourths) :
    Odd 9 ∧
      CenteredInput 9 witness ∧
      0 < 4 ∧
      InputThresholdAtMostNorm 4 witness ∧
      InputThresholdWithinModulus margin 9 4 ∧
      eventProbability (sparseRademacherMatrix 256 16)
          (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29) 4 9 witness) >
        failureTarget 128 := by
  refine ⟨by norm_num, witness_centered, by norm_num, ?_, ?_,
    probability_gt_failureTarget128⟩
  · simp [InputThresholdAtMostNorm, witness_sqNorm]
  · simpa [NonnegativeRatio.LE, nineFourths,
      InputThresholdWithinModulus, Nat.mul_comm] using hmargin

/-- Squared floor `29` is impossible at 256 rows and a 128-bit budget for
every exact rational modulus margin at most `9/4`. -/
theorem bits128_false_of_le_nineFourths
    (margin : NonnegativeRatio) (hmargin : margin.LE nineFourths) :
    ¬ L2ThresholdLowerTailAt (parameters margin) (failureTarget 128) := by
  intro hclaimed
  have hadmissible := admissible_family margin hmargin
  have hbad := hclaimed 9 16 witness 4
    hadmissible.1 hadmissible.2.1 hadmissible.2.2.1
    hadmissible.2.2.2.1 hadmissible.2.2.2.2.1
  simp only [parameters,
    ProjectionDistribution.matrixPMF_balancedTernary] at hbad
  exact (not_lt_of_ge hadmissible.2.2.2.2.2.le) hbad

/-- Public specialization at the exact integer margin `2`. -/
theorem bits128_marginTwo_false :
    ¬ L2ThresholdLowerTailAt parametersTwo (failureTarget 128) := by
  exact bits128_false_of_le_nineFourths (NonnegativeRatio.ofNat 2)
    (by norm_num [NonnegativeRatio.LE, nineFourths, NonnegativeRatio.ofNat])

end CertifiedJL.Counterexamples.TernaryL2Rows256MarginTwo
