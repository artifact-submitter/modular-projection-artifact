/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Statements.LInf.Lower
import Mathlib.Tactic

/-!
# Integer margin-one obstruction for the ternary infinity threshold

At modulus three, nine unit coefficients have norm exactly three. Every
centered residue has magnitude at most one, which lies inside every rational
coordinate cap at least `1/3` at public threshold three. Thus every matrix
passes, for every row count.  The previous 256-row, `21/50` obstruction is
retained as a specialization.
-/

namespace CertifiedJL.Counterexamples.TernaryLInfThresholdMarginOne

def oneThird : NonnegativeRatio :=
  { numerator := 1, denominator := 3, denominator_pos := by decide }

def familyParameters (rows : ℕ) (coordinateCap : NonnegativeRatio) :
    LInfThresholdLowerParameters :=
  { distribution := .balancedTernary
    rows := rows
    coordinateCap := coordinateCap
    modulusMargin := NonnegativeRatio.ofNat 1 }

def parameters : LInfThresholdLowerParameters :=
  familyParameters 256
    { numerator := 21, denominator := 50, denominator_pos := by decide }

def witness : Fin 9 → ℤ := fun _ => 1

theorem witness_centered : CenteredInput 3 witness := by
  intro i
  simp [witness, centeredInterval]

theorem witness_sqNorm : sqNorm witness = 9 := by
  simp [sqNorm, witness]

theorem every_matrix_passes_of_oneThird_le
    {rows : ℕ} {coordinateCap : NonnegativeRatio}
    (hcap : oneThird.LE coordinateCap)
    (J : Fin rows → Fin 9 → ℤ) :
    LInfThresholdSmallProjection
      (familyParameters rows coordinateCap) 3 3 witness J := by
  change ∀ j : Fin rows,
    coordinateCap.denominator ^ 2 *
        (centeredMod 3 (rowDot J witness j)).natAbs ^ 2 ≤
      coordinateCap.numerator ^ 2 * 3 ^ 2
  intro j
  have hmem := centeredMod_mem_centeredInterval (q := 3) (by norm_num)
    (rowDot J witness j)
  simp only [centeredInterval, Set.mem_Icc] at hmem
  have habs : |centeredMod 3 (rowDot J witness j)| ≤ (1 : ℤ) :=
    (abs_le).2 hmem
  rw [Int.abs_eq_natAbs] at habs
  have hnat : (centeredMod 3 (rowDot J witness j)).natAbs ≤ 1 := by
    exact_mod_cast habs
  have hsq : (centeredMod 3 (rowDot J witness j)).natAbs ^ 2 ≤ 1 :=
    Nat.pow_le_pow_left hnat 2
  have hcapRaw : coordinateCap.denominator ≤
      coordinateCap.numerator * 3 := by
    simpa [oneThird, NonnegativeRatio.LE] using hcap
  have hcapSq : coordinateCap.denominator ^ 2 ≤
      coordinateCap.numerator ^ 2 * 3 ^ 2 := by
    simpa [mul_pow] using Nat.pow_le_pow_left hcapRaw 2
  calc
    coordinateCap.denominator ^ 2 *
        (centeredMod 3 (rowDot J witness j)).natAbs ^ 2 ≤
      coordinateCap.denominator ^ 2 * 1 :=
        Nat.mul_le_mul_left _ hsq
    _ ≤ coordinateCap.numerator ^ 2 * 3 ^ 2 := by simpa using hcapSq

theorem probability_eq_one_of_oneThird_le
    {rows : ℕ} {coordinateCap : NonnegativeRatio}
    (hcap : oneThird.LE coordinateCap) :
    eventProbability
        ((familyParameters rows coordinateCap).distribution.matrixPMF
          (familyParameters rows coordinateCap).rows 9)
        (LInfThresholdSmallProjection
          (familyParameters rows coordinateCap) 3 3 witness) = 1 := by
  rw [eventProbability_congr
    ((familyParameters rows coordinateCap).distribution.matrixPMF
      (familyParameters rows coordinateCap).rows 9)
    (event' := fun _ => True) (by
      intro J
      exact iff_true_intro (by
        simpa [familyParameters, ProjectionDistribution.matrixPMF_balancedTernary] using
          every_matrix_passes_of_oneThird_le hcap J))]
  simp [eventProbability]

/-- At every row count and every exact rational cap at least `1/3`, modulus
margin one is impossible for any target budget at most one. -/
theorem lowerTail_false_of_oneThird_le
    {rows : ℕ} {coordinateCap : NonnegativeRatio} {budget : ENNReal}
    (hcap : oneThird.LE coordinateCap) (hbudget : budget ≤ 1) :
    ¬ LInfThresholdLowerTailAt
      (familyParameters rows coordinateCap) budget := by
  intro h
  have hbad := h 3 9 witness 3 (by norm_num) witness_centered (by norm_num)
    (by simp [InputThresholdAtMostNorm, witness_sqNorm])
    (by norm_num [InputThresholdWithinModulus, familyParameters,
      NonnegativeRatio.ofNat])
  rw [probability_eq_one_of_oneThird_le hcap] at hbad
  exact (not_lt_of_ge hbudget) hbad

theorem every_matrix_passes (J : Fin 256 → Fin 9 → ℤ) :
    LInfThresholdSmallProjection parameters 3 3 witness J := by
  exact every_matrix_passes_of_oneThird_le (by
    norm_num [oneThird, NonnegativeRatio.LE]) J

theorem probability_eq_one :
    eventProbability (parameters.distribution.matrixPMF parameters.rows 9)
        (LInfThresholdSmallProjection parameters 3 3 witness) = 1 := by
  exact probability_eq_one_of_oneThird_le (by
    norm_num [oneThird, parameters, familyParameters, NonnegativeRatio.LE])

/-- The `21/50` threshold theorem is false at integer modulus margin one,
even with the 130-bit target replaced by any budget below one. -/
theorem bits130_false :
    ¬ LInfThresholdLowerTailAt parameters (failureTarget 130) := by
  apply lowerTail_false_of_oneThird_le
  · norm_num [oneThird, parameters, familyParameters, NonnegativeRatio.LE]
  · unfold failureTarget
    calc
      (2 : ENNReal)⁻¹ ^ 130 ≤ 1 ^ 130 := by gcongr <;> simp
      _ = 1 := by norm_num

end CertifiedJL.Counterexamples.TernaryLInfThresholdMarginOne
