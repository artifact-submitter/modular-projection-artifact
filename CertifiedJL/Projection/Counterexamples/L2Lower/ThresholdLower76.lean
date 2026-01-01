/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.Obstructions.L2Lower.Threshold76.Verified
import CertifiedJL.Model.Distributions.Entry
import CertifiedJL.Statements.L2.Lower

/-!
# The 512-row, 192-bit threshold-floor-76 counterexample

For modulus `27`, dimension `81`, public input threshold `9`, and the
all-ones vector, the strict lower-failure event at squared-norm floor `76` has
probability greater than `2⁻¹⁹²`.  The proof uses the compact exact counting
certificate in `Certificates.ThresholdLower76`.
-/

open scoped BigOperators ENNReal

namespace CertifiedJL

open Probability

namespace Counterexamples.ThresholdLower76.Internal

def witness : Fin 81 → ℤ := fun _ => 1

theorem witness_centered : CenteredInput 27 witness := by
  intro i
  norm_num [witness, centeredInterval]

theorem witness_sqNorm : sqNorm witness = 81 := by
  simp [sqNorm, witness]

theorem witness_rowDot (seed : SparseSeed 512 81) (row : Fin 512) :
    rowDot (sparseMatrix seed) witness row =
      Probability.SparseAllOnes.sparseAllOnesRowSum (seed row) := by
  unfold rowDot Probability.SparseAllOnes.sparseAllOnesRowSum
  apply Finset.sum_congr rfl
  intro coordinate _
  simp [sparseMatrix, sparseRow, witness]

theorem witness_modularProjectionSqNorm (seed : SparseSeed 512 81) :
    modularProjectionSqNorm 27 (sparseMatrix seed) witness =
      FixedPointConvolution.blockStatisticSum ThresholdLower76.rowResidueSquaredMagnitude seed := by
  unfold modularProjectionSqNorm FixedPointConvolution.blockStatisticSum
  apply Finset.sum_congr rfl
  intro row _
  rw [witness_rowDot]
  rfl

theorem failure_iff (seed : SparseSeed 512 81) :
    L2ThresholdLowerFailure (NonnegativeRatio.ofNat 76) 9 27 witness
        (sparseMatrix seed) ↔
      FixedPointConvolution.blockStatisticSum ThresholdLower76.rowResidueSquaredMagnitude seed <
        ThresholdLower76.cutoff := by
  rw [L2ThresholdLowerFailure, witness_modularProjectionSqNorm]
  norm_num [NonnegativeRatio.ofNat, ThresholdLower76.cutoff]

theorem sparseSeed_card :
    Fintype.card (SparseSeed 512 81) = ThresholdLower76.rowDenominator ^ 512 := by
  rw [Probability.SparseAllOnes.card_sparseSeed]
  norm_num [ThresholdLower76.rowDenominator]

set_option maxRecDepth 10000 in
theorem eventCard_scaled_gt :
    Nat.card ThresholdLower76.FailureSeed * 2 ^ 192 >
      ThresholdLower76.rowDenominator ^ 512 :=
  ThresholdLower76.failureEventCard_scaled_gt

theorem natRatio_gt {denominator numerator bits : ℕ}
    (hdenominator : 0 < denominator)
    (hscaled : denominator < 2 ^ bits * numerator) :
    (2 : ℝ≥0∞)⁻¹ ^ bits <
      (numerator : ℝ≥0∞) * (denominator : ℝ≥0∞)⁻¹ := by
  rw [← ENNReal.inv_pow]
  rw [show (numerator : ℝ≥0∞) * (denominator : ℝ≥0∞)⁻¹ =
    (numerator : ℝ≥0∞) / denominator by rfl]
  rw [ENNReal.lt_div_iff_mul_lt (by simp [hdenominator.ne']) (by simp)]
  rw [mul_comm, ← div_eq_mul_inv]
  rw [ENNReal.div_lt_iff (by simp) (by simp)]
  exact_mod_cast (by simpa only [mul_comm] using hscaled)

def embedFailureSeed : ThresholdLower76.FailureSeed →
    {seed : SparseSeed 512 81 //
      L2ThresholdLowerFailure (NonnegativeRatio.ofNat 76) 9 27 witness
        (sparseMatrix seed)} :=
  fun seed => ⟨seed.seed, (failure_iff seed.seed).mpr seed.failure⟩

theorem embedFailureSeed_injective : Function.Injective embedFailureSeed := by
  intro left right heq
  apply ThresholdLower76.FailureSeed.ext
  exact congrArg Subtype.val heq

theorem failureSeed_card_le :
    Nat.card ThresholdLower76.FailureSeed ≤
      Nat.card
        {seed : SparseSeed 512 81 //
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat 76) 9 27 witness
            (sparseMatrix seed)} :=
  Nat.card_le_card_of_injective embedFailureSeed embedFailureSeed_injective

theorem certifiedRatio_gt :
    failureTarget 192 <
      (Nat.card ThresholdLower76.FailureSeed : ℝ≥0∞) *
        (Fintype.card (SparseSeed 512 81) : ℝ≥0∞)⁻¹ := by
  rw [sparseSeed_card]
  unfold failureTarget
  exact natRatio_gt
    (pow_pos (by norm_num [ThresholdLower76.rowDenominator]) _)
    (by simpa only [mul_comm] using eventCard_scaled_gt)

theorem failureProbability_gt :
    eventProbability (sparseRademacherMatrix 512 81)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 76) 9 27 witness) >
      failureTarget 192 := by
  classical
  rw [sparseRademacherMatrix_eq_map_uniformSeed,
    eventProbability_map_uniform_eq_card]
  rw [Fintype.card_eq_nat_card (α :=
    {seed : SparseSeed 512 81 //
      L2ThresholdLowerFailure (NonnegativeRatio.ofNat 76) 9 27 witness
        (sparseMatrix seed)})]
  have hlower : failureTarget 192 <
      (Nat.card ThresholdLower76.FailureSeed : ℝ≥0∞) *
        (Fintype.card (SparseSeed 512 81) : ℝ≥0∞)⁻¹ :=
    certifiedRatio_gt
  have hprob :
      (Nat.card ThresholdLower76.FailureSeed : ℝ≥0∞) *
          (Fintype.card (SparseSeed 512 81) : ℝ≥0∞)⁻¹ ≤
        (Nat.card
          {seed : SparseSeed 512 81 //
            L2ThresholdLowerFailure (NonnegativeRatio.ofNat 76) 9 27 witness
              (sparseMatrix seed)} : ℝ≥0∞) *
          (Fintype.card (SparseSeed 512 81) : ℝ≥0∞)⁻¹ := by
    gcongr
    exact_mod_cast failureSeed_card_le
  exact hlower.trans_le hprob

end Counterexamples.ThresholdLower76.Internal

/-- Stable public name for the 81-dimensional all-ones witness. -/
def thresholdLower512Bits192Floor76Witness : Fin 81 → ℤ :=
  Counterexamples.ThresholdLower76.Internal.witness

/-- At the explicit admissible input `(q,d,b,w) = (27,81,9,1)`, squared norm
floor `76` fails with probability strictly greater than `2⁻¹⁹²`. -/
theorem thresholdLower512Bits192Floor76Counterexample :
    eventProbability (sparseRademacherMatrix 512 81)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 76) 9 27
          thresholdLower512Bits192Floor76Witness) >
      failureTarget 192 :=
  by
    simpa [thresholdLower512Bits192Floor76Witness] using
      Counterexamples.ThresholdLower76.Internal.failureProbability_gt

end CertifiedJL
