/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.Obstructions.L2Lower.Threshold76.Core
import CertifiedJL.Certificates.Families.Obstructions.L2Lower.Threshold76.CheckpointLink9
import CertifiedJL.Certificates.Families.Obstructions.L2Lower.Threshold76.CheckpointDigitSum
import CertifiedJL.Projection.Counterexamples.Shared.SparseAllOnesRow

/-!
# Verified 512-row threshold-floor-76 certificate

This module proves that the one-row table is the actual centered modular
squared-magnitude distribution of an 81-dimensional all-ones sparse row. It then connects one
compact kernel computation to the generic finite squared-norm soundness theorem.
-/

open scoped BigOperators

namespace CertifiedJL.ThresholdLower76

open FixedPointConvolution
open Probability.SparseAllOnes

def centeredMagnitudeOfCount (count : Fin 163) : ℕ :=
  (centeredMod 27 ((count : ℕ) - 81)).natAbs

theorem centeredMagnitudeOfCount_lt (count : Fin 163) :
    centeredMagnitudeOfCount count < 14 := by
  decide +kernel +revert

def rowClassOfCount (count : Fin 163) : Fin 14 :=
  ⟨centeredMagnitudeOfCount count, centeredMagnitudeOfCount_lt count⟩

def trueCountFin (seed : SparseRowSeed 81) : Fin 163 :=
  ⟨sparseRowTrueCount seed, by
    have hcard := Finset.card_le_univ
      (s := Probability.boolSupport (sparseRowSeedEquivBits 81 seed))
    simp only [sparseRowTrueCount]
    norm_num at hcard
    omega⟩

def rowClass (seed : SparseRowSeed 81) : Fin 14 :=
  rowClassOfCount (trueCountFin seed)

def rowResidueSquaredMagnitude (seed : SparseRowSeed 81) : ℕ :=
  (centeredMod 27 (sparseAllOnesRowSum seed)).natAbs ^ 2

theorem rowResidueSquaredMagnitude_eq_rowClass (seed : SparseRowSeed 81) :
    rowResidueSquaredMagnitude seed = (rowClass seed : ℕ) ^ 2 := by
  unfold rowResidueSquaredMagnitude rowClass rowClassOfCount centeredMagnitudeOfCount
  rw [sparseAllOnesRowSum_eq_trueCount]
  rfl

def trueCountFinFiberEquiv (count : Fin 163) :
    {seed : SparseRowSeed 81 // trueCountFin seed = count} ≃
      {seed : SparseRowSeed 81 // sparseRowTrueCount seed = count} :=
  Equiv.subtypeEquiv (Equiv.refl _) fun seed => by
    change trueCountFin seed = count ↔ sparseRowTrueCount seed = count.1
    constructor
    · intro h
      exact congrArg Fin.val h
    · intro h
      apply Fin.ext
      exact h

theorem card_trueCountFin_fiber (count : Fin 163) :
    Fintype.card {seed : SparseRowSeed 81 // trueCountFin seed = count} =
      Nat.choose 162 count := by
  rw [Fintype.card_congr (trueCountFinFiberEquiv count),
    card_sparseRowTrueCount_fiber]

def rowClassFiberEquiv (residue : Fin 14) :
    {seed : SparseRowSeed 81 // rowClass seed = residue} ≃
      (count : {count : Fin 163 // rowClassOfCount count = residue}) ×
        {seed : SparseRowSeed 81 // trueCountFin seed = count} :=
  (Equiv.sigmaSubtypeFiberEquivSubtype
      (f := trueCountFin)
      (p := fun seed => rowClass seed = residue)
      (q := fun count => rowClassOfCount count = residue)
      (fun _ => Iff.rfl)).symm

theorem rowClassCount_eq_sum (residue : Fin 14) :
    rowClassCount residue =
      ∑ count : {count : Fin 163 // rowClassOfCount count = residue},
        Nat.choose 162 count := by
  fin_cases residue <;> decide +kernel

theorem card_rowClass_fiber (residue : Fin 14) :
    Fintype.card {seed : SparseRowSeed 81 // rowClass seed = residue} =
      rowClassCount residue := by
  rw [Fintype.card_congr (rowClassFiberEquiv residue),
    Fintype.card_sigma]
  simp_rw [card_trueCountFin_fiber]
  exact (rowClassCount_eq_sum residue).symm

def rowSquaredMagnitudeFiberEquiv (energy : ℕ) :
    {seed : SparseRowSeed 81 // rowResidueSquaredMagnitude seed = energy} ≃
      (residue : {residue : Fin 14 // (residue : ℕ) ^ 2 = energy}) ×
        {seed : SparseRowSeed 81 // rowClass seed = residue} :=
  (Equiv.sigmaSubtypeFiberEquivSubtype
      (f := rowClass)
      (p := fun seed => rowResidueSquaredMagnitude seed = energy)
      (q := fun residue : Fin 14 => (residue : ℕ) ^ 2 = energy)
      (fun seed => by rw [rowResidueSquaredMagnitude_eq_rowClass])).symm

theorem statisticMultiplicity_rowResidueSquaredMagnitude (energy : ℕ) :
    statisticMultiplicity rowResidueSquaredMagnitude energy = rowMassAtSquaredNorm energy := by
  rw [statisticMultiplicity, Fintype.card_congr (rowSquaredMagnitudeFiberEquiv energy),
    Fintype.card_sigma]
  simp_rw [card_rowClass_fiber]
  rfl

def oneBlockEquiv (α : Type*) : Block α 1 ≃ α where
  toFun block := block 0
  invFun value := fun _ => value
  left_inv block := by
    funext i
    fin_cases i
    rfl
  right_inv _ := rfl

theorem blockStatisticSum_one (seed : Block (SparseRowSeed 81) 1) :
    rowResidueSquaredMagnitude ((oneBlockEquiv (SparseRowSeed 81)) seed) =
      blockStatisticSum rowResidueSquaredMagnitude seed := by
  simp [oneBlockEquiv, blockStatisticSum]

theorem statisticMultiplicity_blockStatisticSum_one (energy : ℕ) :
    statisticMultiplicity (@blockStatisticSum (SparseRowSeed 81) rowResidueSquaredMagnitude 1) energy =
      statisticMultiplicity rowResidueSquaredMagnitude energy :=
  statisticMultiplicity_congr (oneBlockEquiv (SparseRowSeed 81))
    blockStatisticSum_one energy

theorem state0_lowerApproximation :
    LowerApproximation cutoff rowDenominator scale
      (@blockStatisticSum (SparseRowSeed 81) rowResidueSquaredMagnitude 1) state0 := by
  constructor
  · unfold state0
    exact List.length_ofFn
  · intro energy henergy
    rw [getD_state0_of_lt henergy]
    rw [statisticMultiplicity_blockStatisticSum_one, statisticMultiplicity_rowResidueSquaredMagnitude]
    have hscaleFactor : 2 ^ (255 - 162) * rowDenominator = scale := by
      norm_num [rowDenominator, scale, pow_add]
    rw [mul_assoc, hscaleFactor]

theorem roundedState_lowerApproximation (stages : ℕ) :
    LowerApproximation cutoff (rowDenominator ^ (2 ^ stages)) scale
      (@blockStatisticSum (SparseRowSeed 81) rowResidueSquaredMagnitude (2 ^ stages))
      (roundedState stages) := by
  induction stages with
  | zero => simpa [roundedState] using state0_lowerApproximation
  | succ stages ih =>
      have hpow : 2 ^ (stages + 1) = 2 ^ stages + 2 ^ stages := by
        rw [pow_succ]
        omega
      rw [roundedState, hpow, pow_add]
      exact ih.squareBlockRounded scale_pos

theorem state0_sum : state0.sum = scale := by
  set_option maxRecDepth 100000 in
  decide +kernel

theorem roundedState_sum_le (stages : ℕ) :
    (roundedState stages).sum ≤ scale := by
  induction stages with
  | zero => simp [roundedState, state0_sum]
  | succ stages ih =>
      rw [roundedState]
      exact roundedConvolution_sum_le scale_pos _
        (roundedState_lowerApproximation stages).1 ih

theorem roundedState_entry_le (stages : ℕ) :
    ∀ x ∈ roundedState stages, x ≤ scale := by
  intro x hx
  exact (List.le_sum_of_mem hx).trans (roundedState_sum_le stages)

theorem scale_lt_packingBase : scale < packingBase := by
  set_option exponentiation.threshold 1000 in
  norm_num [scale, packingBase]

theorem packedState_eq_ofDigits (stages : ℕ) :
    packedState stages = Nat.ofDigits packingBase (roundedState stages) := by
  induction stages with
  | zero => rfl
  | succ stages ih =>
      change packedSquareStep cutoff packingBase scale (packedState stages) = _
      rw [ih, roundedState]
      apply packedSquareStep_ofDigits (Nat.zero_lt_of_lt packingBase_gt_one)
      · exact (roundedState_lowerApproximation stages).1
      · exact fullConvolution_digits_lt
          (roundedState_entry_le stages) (roundedState_entry_le stages)
          convolution_digits_fit

theorem packedState_digitSum (stages : ℕ) :
    packedDigitSum cutoff packingBase (packedState stages) =
      (roundedState stages).sum := by
  rw [packedState_eq_ofDigits]
  have hlength := (roundedState_lowerApproximation stages).1
  rw [← hlength]
  exact packedDigitSum_ofDigits (Nat.zero_lt_of_lt packingBase_gt_one) _
    (fun x hx => (roundedState_entry_le stages x hx).trans_lt scale_lt_packingBase)

/-- Kernel-checked checkpoint chain for nine packed squarings. -/
theorem packedState9_digitSum :
    packedDigitSum cutoff packingBase (packedState 9) = 9387937369855426309 := by
  rw [packedState9_eq_checkpoint]
  exact packedState9Checkpoint_digitSum

theorem roundedState9_sum :
    (roundedState 9).sum = 9387937369855426309 := by
  rw [← packedState_digitSum 9, packedState9_digitSum]

theorem roundedState9_sum_gt_target : 2 ^ 63 < (roundedState 9).sum := by
  rw [roundedState9_sum]
  norm_num

/-- Seeds in the certified strict lower-tail event. -/
@[ext]
structure FailureSeed where
  seed : Block (SparseRowSeed 81) 512
  failure : blockStatisticSum rowResidueSquaredMagnitude seed < cutoff
deriving Fintype

def failureSeedEquiv :
    {seed : Block (SparseRowSeed 81) 512 //
      blockStatisticSum rowResidueSquaredMagnitude seed < cutoff} ≃ FailureSeed where
  toFun seed := ⟨seed.1, seed.2⟩
  invFun seed := ⟨seed.seed, seed.failure⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem roundedState9_scaledMass_le_eventCard :
    (roundedState 9).sum * rowDenominator ^ 512 ≤
      Nat.card FailureSeed * scale :=
  by
    have h := (roundedState_lowerApproximation 9).sum_le_card_statistic_lt_mul_scale
    have hrows : 2 ^ 9 = 512 := by norm_num
    rw [hrows] at h
    rw [Fintype.card_eq_nat_card, Nat.card_congr failureSeedEquiv] at h
    exact h

theorem failureEventCard_scaled_gt :
    rowDenominator ^ 512 < Nat.card FailureSeed * 2 ^ 192 := by
  have hscale : scale = 2 ^ 63 * 2 ^ 192 := by
    unfold scale
    rw [show 255 = 63 + 192 by norm_num, pow_add]
  exact count_mul_pow_gt_of_scaled_lower
    (pow_pos (by norm_num) 63)
    (pow_pos (by norm_num [rowDenominator]) 512)
    roundedState9_sum_gt_target roundedState9_scaledMass_le_eventCard hscale

end CertifiedJL.ThresholdLower76
