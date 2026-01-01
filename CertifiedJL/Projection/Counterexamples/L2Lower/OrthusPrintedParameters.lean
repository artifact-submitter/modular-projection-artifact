/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.Counterexamples.LInf.SparseLInfTwoCoordinate
import CertifiedJL.Model.Modular.Centered
import CertifiedJL.Statements.LInf.Lower
import Mathlib.Tactic

/-!
# Complete parameter bridge for the printed Orthus infinity threshold

The existing finite counterexample counts the raw row event.  This module
connects it to the printed witness, threshold, modulus condition, centered
reduction, and exact rational coordinate cap.
-/

open scoped ENNReal

namespace CertifiedJL.Counterexamples.OrthusPrintedParameters

/-- The two-coordinate witness from the Orthus counterexample. -/
def witness : Fin 2 → ℤ := fun _ => 22

/-- Exact parameters of the printed 256-row, cap-`0.74`, margin-`91` claim. -/
def parameters : LInfThresholdLowerParameters :=
  { distribution := .balancedTernary
    rows := 256
    coordinateCap :=
      { numerator := 74, denominator := 100, denominator_pos := by decide }
    modulusMargin := NonnegativeRatio.ofNat 91 }

private theorem centered_rowDot_witness {q : ℕ} (hq : Odd q) (hqLower : 2821 ≤ q)
    (J : Fin 256 → Fin 2 → ℤ)
    (hentry : ∀ row i, |J row i| ≤ 1) (row : Fin 256) :
    centeredMod q (rowDot J witness row) = rowDot J witness row := by
  rw [centeredMod_eq_self hq]
  simp only [rowDot, witness, Fin.sum_univ_two]
  have h0 := hentry row 0
  have h1 := hentry row 1
  have h0' := (abs_le.mp h0)
  have h1' := (abs_le.mp h1)
  constructor <;> omega

private theorem sparse_entry_abs_le_one (seed : SparseSeed 256 2)
    (row : Fin 256) (i : Fin 2) :
    |sparseMatrix seed row i| ≤ 1 := by
  simp only [sparseMatrix, sparseRow]
  rcases h : seed row i with ⟨left, right⟩
  cases left <;> cases right <;> decide

private theorem printedEvent_sparseMatrix_iff {q : ℕ}
    (hq : Odd q) (hqLower : 2821 ≤ q) (seed : SparseSeed 256 2) :
    LInfThresholdSmallProjection parameters 31 q witness
        (sparseMatrix seed) ↔
      SparseLInfTwoCoordinatePass (sparseMatrix seed) := by
  simp only [LInfThresholdSmallProjection, parameters,
    SparseLInfTwoCoordinatePass, sparseLInfTwoCoordinateRowPass]
  apply forall_congr'
  intro row
  rw [centered_rowDot_witness hq hqLower
    (sparseMatrix seed) (sparse_entry_abs_le_one seed) row]
  simp only [rowDot, witness, sparseMatrix, sparseRow,
    Fin.sum_univ_two]
  rcases h0 : seed row 0 with ⟨a, b⟩
  rcases h1 : seed row 1 with ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [h0, h1, sparseBit]

private theorem printedProbability_exact (q : ℕ) (hq : Odd q)
    (hqLower : 2821 ≤ q) :
    eventProbability (sparseRademacherMatrix 256 2)
        (LInfThresholdSmallProjection parameters 31 q witness) =
      (14 : ℝ≥0∞) ^ 256 * ((16 : ℝ≥0∞) ^ 256)⁻¹ := by
  rw [sparseRademacherMatrix_eq_map_uniformSeed]
  rw [eventProbability_map_congr
    (PMF.uniformOfFintype (SparseSeed 256 2))
    sparseMatrix sparseMatrix
    (LInfThresholdSmallProjection parameters 31 q witness)
    SparseLInfTwoCoordinatePass
    (printedEvent_sparseMatrix_iff hq hqLower)]
  rw [← sparseRademacherMatrix_eq_map_uniformSeed]
  simpa [rowCount] using
    Counterexamples.SparseLInfTwoCoordinate.Internal.sparseLInfTwoCoordinateProbability_exact

/-- For every odd modulus at least `2821`, the printed witness satisfies all
input hypotheses.  Its cap-`0.74` event has exact probability
`(14/16)^256`, which is greater than `2⁻¹²⁸`. -/
theorem printedParameterBridge (q : ℕ) (hq : Odd q) (hqLower : 2821 ≤ q) :
    CenteredInput q witness ∧
      31 ^ 2 < sqNorm witness ∧
      31 ≤ q / 91 ∧
      InputThresholdWithinModulus (NonnegativeRatio.ofNat 91) q 31 ∧
      eventProbability (sparseRademacherMatrix 256 2)
          (LInfThresholdSmallProjection parameters 31 q witness) =
        (14 : ℝ≥0∞) ^ 256 * ((16 : ℝ≥0∞) ^ 256)⁻¹ ∧
      eventProbability (sparseRademacherMatrix 256 2)
          (LInfThresholdSmallProjection parameters 31 q witness) >
        failureTarget 128 := by
  refine ⟨?_, ?_, ?_, ?_, printedProbability_exact q hq hqLower, ?_⟩
  · intro i
    fin_cases i <;>
      simp only [witness, centeredInterval, Set.mem_Icc] <;> omega
  · norm_num [sqNorm, witness, Fin.sum_univ_two]
  · omega
  · norm_num [InputThresholdWithinModulus, NonnegativeRatio.ofNat]
    omega
  · rw [sparseRademacherMatrix_eq_map_uniformSeed]
    rw [eventProbability_map_congr
      (PMF.uniformOfFintype (SparseSeed 256 2))
      sparseMatrix sparseMatrix
      (LInfThresholdSmallProjection parameters 31 q witness)
      SparseLInfTwoCoordinatePass
      (printedEvent_sparseMatrix_iff hq hqLower)]
    rw [← sparseRademacherMatrix_eq_map_uniformSeed]
    simpa [rowCount, securityBits] using
      Counterexamples.SparseLInfTwoCoordinate.Internal.sparseLInfTwoCoordinateProbability_gt

end CertifiedJL.Counterexamples.OrthusPrintedParameters
