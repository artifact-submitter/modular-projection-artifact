/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Activity
import CertifiedJL.Statements.L2.Lower
import Mathlib.Tactic

/-!
# Security ceiling for balanced-ternary threshold lower tails

For a one-coordinate unit input, the distinguished coordinate is inactive in
every row with probability exactly `2⁻ʳᵒʷˢ`.  On that event the modular projection squared norm
is zero, so every positive squared-norm floor fails.  Consequently a strict
`rows`-bit threshold lower-tail bound is impossible with only `rows` rows.
-/

namespace CertifiedJL.Counterexamples.ThresholdSecurityCeiling

open Probability

def witness : Fin 1 → ℤ := fun _ => 1

theorem witness_centered : CenteredInput 3 witness := by
  intro i
  simp [witness, centeredInterval]

theorem witness_sqNorm : sqNorm witness = 1 := by
  simp [sqNorm, witness]

private theorem matrix_entry_eq_zero_of_activityCount_lt_one
    {rows : ℕ} (J : Fin rows → Fin 1 → ℤ)
    (hcount : (dominantActivityCount
      (matrixDominantActivity (0 : Fin 1) J) : ℕ) < 1) :
    ∀ row, J row 0 = 0 := by
  intro row
  by_contra hne
  have hmem : row ∈ boolSupport
      (matrixDominantActivity (0 : Fin 1) J) := by
    simp [boolSupport, matrixDominantActivity, hne]
  have hpositive : 0 < (boolSupport
      (matrixDominantActivity (0 : Fin 1) J)).card :=
    Finset.card_pos.mpr ⟨row, hmem⟩
  have hempty : boolSupport
      (matrixDominantActivity (0 : Fin 1) J) = ∅ := by
    simpa [dominantActivityCount] using hcount
  rw [hempty] at hpositive
  simp at hpositive

private theorem all_inactive_implies_failure
    {rows squaredNormFloor : ℕ} (hfloor : 0 < squaredNormFloor)
    (J : Fin rows → Fin 1 → ℤ)
    (hcount : (dominantActivityCount
      (matrixDominantActivity (0 : Fin 1) J) : ℕ) < 1) :
    L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
      1 3 witness J := by
  have hzero := matrix_entry_eq_zero_of_activityCount_lt_one J hcount
  have hcenteredZero : centeredMod 3 0 = 0 := by
    apply centeredMod_eq_self (by norm_num)
    norm_num [centeredInterval]
  simp [L2ThresholdLowerFailure, NonnegativeRatio.ofNat, modularProjectionSqNorm,
    rowDot, witness, hzero, hcenteredZero, hfloor]

theorem allInactive_probability_eq (rows : ℕ) :
    eventProbability (sparseRademacherMatrix rows 1)
        (fun J => (dominantActivityCount
          (matrixDominantActivity (0 : Fin 1) J) : ℕ) < 1) =
      failureTarget rows := by
  rw [sparse_dominantActivityCount_lt_probability_eq_at rows (0 : Fin 1) 1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    Nat.cast_one, zero_add, one_mul, failureTarget]
  rw [show ((2 ^ rows : ℕ) : ENNReal) = (2 : ENNReal) ^ rows by norm_cast]
  exact ENNReal.inv_pow

/-- No positive threshold squared-norm floor has a strict `rows`-bit lower-tail
bound for a balanced-ternary matrix with only `rows` rows. -/
theorem rowsBits_false (rows squaredNormFloor : ℕ) (hfloor : 0 < squaredNormFloor) :
    ¬ L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := rows
        squaredNormFloor := NonnegativeRatio.ofNat squaredNormFloor
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget rows) := by
  intro h
  have hbad := h 3 1 witness 1 (by norm_num) witness_centered (by norm_num)
    (by simp [InputThresholdAtMostNorm, witness_sqNorm])
    (by norm_num [InputThresholdWithinModulus, NonnegativeRatio.ofNat])
  simp only [ProjectionDistribution.matrixPMF_balancedTernary] at hbad
  have hlower : failureTarget rows ≤
      eventProbability (sparseRademacherMatrix rows 1)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
          1 3 witness) := by
    rw [← allInactive_probability_eq rows]
    exact eventProbability_mono (sparseRademacherMatrix rows 1)
      (all_inactive_implies_failure hfloor)
  exact (not_lt_of_ge hlower) hbad

end CertifiedJL.Counterexamples.ThresholdSecurityCeiling
