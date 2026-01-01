/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Modular.Centered
import CertifiedJL.Projection.Counterexamples.Shared.SparseAllOnesRow

/-!
# Generic geometry of flat sparse upper-tail witnesses

This module identifies the modular projection of an all-ones vector in
dimension `d`, with modulus `2 * d + 1`, with the corresponding vector of
sparse row sums.  The result is uniform in the row count and endpoint.
-/

open scoped BigOperators ENNReal

namespace CertifiedJL
open Probability
namespace Counterexamples.SparseUpper.FlatWitness

export Probability.SparseAllOnes
  (sparseRowSeedEquivBits sparseRowTrueCount sparseAllOnesRowSum
    sparseAllOnesRowSum_eq_trueCount)

/-- The all-ones witness in an arbitrary finite dimension. -/
@[nolint unusedArguments]
def vector (d : ℕ) : Fin d → ℤ := fun _ => 1

/-- The squared norm used for a vector of integer row sums. -/
def rowSqNorm {rows : ℕ} (z : Fin rows → ℤ) : ℕ :=
  ∑ j, (z j).natAbs ^ 2

@[simp] theorem sqNorm_vector (d : ℕ) : sqNorm (vector d) = d := by
  unfold sqNorm vector
  simp

theorem vector_ne_zero {d : ℕ} (hd : 0 < d) : vector d ≠ 0 := by
  intro hzero
  have hcoordinate := congrFun hzero (⟨0, hd⟩ : Fin d)
  simp [vector] at hcoordinate

theorem modulus_odd (d : ℕ) : Odd (2 * d + 1) := by
  exact ⟨d, by omega⟩

/-- A sparse row dotted with the flat witness is its integer row sum. -/
theorem rowDot_sparseMatrix_vector {rows d : ℕ}
    (seed : SparseSeed rows d) (j : Fin rows) :
    rowDot (sparseMatrix seed) (vector d) j =
      sparseAllOnesRowSum (seed j) := by
  unfold rowDot sparseMatrix sparseRow sparseAllOnesRowSum vector
  simp

/-- Every sparse all-ones row sum is centered modulo `2 * d + 1`. -/
theorem rowSum_mem_centeredInterval {rows d : ℕ}
    (seed : SparseSeed rows d) (j : Fin rows) :
    sparseAllOnesRowSum (seed j) ∈ centeredInterval (2 * d + 1) := by
  have hcount : sparseRowTrueCount (seed j) ≤ 2 * d := by
    change (boolSupport (sparseRowSeedEquivBits d (seed j))).card ≤ 2 * d
    simpa [Fintype.card_fin] using
      Finset.card_le_univ
        (s := boolSupport (sparseRowSeedEquivBits d (seed j)))
  rw [sparseAllOnesRowSum_eq_trueCount]
  simp only [centeredInterval, Set.mem_Icc]
  constructor <;> push_cast at hcount ⊢ <;> omega

@[simp] theorem centeredMod_rowSum {rows d : ℕ}
    (seed : SparseSeed rows d) (j : Fin rows) :
    centeredMod (2 * d + 1) (sparseAllOnesRowSum (seed j)) =
      sparseAllOnesRowSum (seed j) := by
  exact centeredMod_eq_self (modulus_odd d)
    (rowSum_mem_centeredInterval seed j)

/-- Modular projection of the flat witness is exactly the row-sum norm. -/
theorem modularProjectionSqNorm_sparseMatrix_vector {rows d : ℕ}
    (seed : SparseSeed rows d) :
    modularProjectionSqNorm (2 * d + 1) (sparseMatrix seed) (vector d) =
      rowSqNorm (fun j => sparseAllOnesRowSum (seed j)) := by
  unfold modularProjectionSqNorm rowSqNorm
  apply Finset.sum_congr rfl
  intro j _
  rw [rowDot_sparseMatrix_vector, centeredMod_rowSum]

/-- The matrix and row-sum upper-tail events agree for every sparse seed. -/
theorem matrixFailure_iff_rowFailure {rows d threshold : ℕ}
    (seed : SparseSeed rows d) :
    modularProjectionSqNorm (2 * d + 1) (sparseMatrix seed) (vector d) >
        threshold * sqNorm (vector d) ↔
      threshold * d < rowSqNorm (fun j => sparseAllOnesRowSum (seed j)) := by
  rw [modularProjectionSqNorm_sparseMatrix_vector, sqNorm_vector]

/--
Any product row-sum PMF represented as the image of the uniform sparse seed
has exactly the probability of the corresponding modular flat-witness event.
-/
theorem eventProbability_eq {rows d threshold : ℕ}
    (rowSumsPMF : PMF (Fin rows → ℤ))
    (hrowSumsPMF :
      rowSumsPMF =
        (PMF.uniformOfFintype (SparseSeed rows d)).map
          (fun seed j => sparseAllOnesRowSum (seed j))) :
    eventProbability (sparseRademacherMatrix rows d)
        (fun J =>
          modularProjectionSqNorm (2 * d + 1) J (vector d) >
            threshold * sqNorm (vector d)) =
      rowSumsPMF.toMeasure {z | threshold * d < rowSqNorm z} := by
  rw [sparseRademacherMatrix_eq_map_uniformSeed, hrowSumsPMF,
    ← eventProbability_eq_toMeasure]
  exact eventProbability_map_congr _ _ _ _ _ matrixFailure_iff_rowFailure

/-- A specialization wrapper which keeps a client's named modulus and witness
visible in its public statement. -/
theorem eventProbability_eq_of_specialization {rows d threshold q : ℕ}
    (w : Fin d → ℤ) (rowSumsPMF : PMF (Fin rows → ℤ))
    (hw : w = vector d) (hq : q = 2 * d + 1)
    (hrowSumsPMF :
      rowSumsPMF =
        (PMF.uniformOfFintype (SparseSeed rows d)).map
          (fun seed j => sparseAllOnesRowSum (seed j))) :
    eventProbability (sparseRademacherMatrix rows d)
        (fun J =>
          modularProjectionSqNorm q J w > threshold * sqNorm w) =
      rowSumsPMF.toMeasure {z | threshold * d < rowSqNorm z} := by
  subst w
  subst q
  exact eventProbability_eq rowSumsPMF hrowSumsPMF

/-- Package a strict probability bound as the standard finite witness triple. -/
theorem counterexample_of_probability_gt {rows d threshold bits : ℕ}
    (hd : 0 < d)
    (hprob :
      eventProbability (sparseRademacherMatrix rows d)
          (fun J =>
            modularProjectionSqNorm (2 * d + 1) J (vector d) >
              threshold * sqNorm (vector d)) >
        failureTarget bits) :
    Odd (2 * d + 1) ∧ vector d ≠ 0 ∧
      eventProbability (sparseRademacherMatrix rows d)
          (fun J =>
            modularProjectionSqNorm (2 * d + 1) J (vector d) >
              threshold * sqNorm (vector d)) >
        failureTarget bits := by
  exact ⟨modulus_odd d, vector_ne_zero hd, hprob⟩

/-- Package the standard witness triple while retaining named client constants. -/
theorem counterexample_of_specialization {rows d threshold bits q : ℕ}
    (w : Fin d → ℤ) (hw : w = vector d) (hq : q = 2 * d + 1)
    (hd : 0 < d)
    (hprob :
      eventProbability (sparseRademacherMatrix rows d)
          (fun J =>
            modularProjectionSqNorm q J w > threshold * sqNorm w) >
        failureTarget bits) :
    Odd q ∧ w ≠ 0 ∧
      eventProbability (sparseRademacherMatrix rows d)
          (fun J =>
            modularProjectionSqNorm q J w > threshold * sqNorm w) >
        failureTarget bits := by
  subst w
  subst q
  exact counterexample_of_probability_gt hd hprob

/-- A strict finite flat-witness failure refutes the corresponding uniform
balanced-ternary upper-tail bound. -/
theorem not_l2UpperTailAt_of_probability_gt
    {rows d threshold : ℕ} {budget : ENNReal}
    (q : ℕ) (w : Fin d → ℤ)
    (hprob :
      eventProbability (sparseRademacherMatrix rows d)
          (fun J =>
            modularProjectionSqNorm q J w > threshold * sqNorm w) >
        budget) :
    ¬ L2UpperTailAt
      { distribution := .balancedTernary
        rows := rows
        threshold := NonnegativeRatio.ofNat threshold }
      budget := by
  intro hclaimed
  have hbad := hclaimed q d w
  simp only [ProjectionDistribution.matrixPMF_balancedTernary] at hbad
  rw [eventProbability_congr
    (sparseRademacherMatrix rows d)
    (event' := fun J =>
      modularProjectionSqNorm q J w > threshold * sqNorm w)
    (by
      intro J
      exact L2UpperFailure_ofNat_iff threshold q w J)] at hbad
  exact (not_lt_of_ge hprob.le) hbad

end Counterexamples.SparseUpper.FlatWitness
end CertifiedJL
