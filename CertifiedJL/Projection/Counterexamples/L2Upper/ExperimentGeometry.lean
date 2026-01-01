/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.Counterexamples.L2Upper.QuantitativeBounds

-- See the corresponding note in `GaussianComparison`.
set_option Elab.async false

/-!
# Experiment geometry for the sparse upper-336 counterexample

This module identifies the all-ones witness's modular projection squared norm with the exact
sum of squared discrete row values used by the analytic comparison.
-/

open scoped BigOperators ENNReal

open MeasureTheory

namespace CertifiedJL
open Probability
namespace Counterexamples.SparseUpper.Internal

/-! ## Identification with the modular sparse-matrix experiment -/

/-- The local dimension is definitionally the headline witness dimension. -/
theorem dimension_eq_counterexampleDimension :
    dimension = counterexampleDimension := by
  rfl

/-- The headline all-ones witness. -/
abbrev allOnesVector : Fin counterexampleDimension → ℤ :=
  sparseUpperCounterexampleVector

/-- The local all-ones witness is the headline witness. -/
theorem allOnesVector_eq_counterexampleVector :
    allOnesVector = sparseUpperCounterexampleVector := by
  rfl

/-- The headline all-ones witness has squared norm exactly `dimension`. -/
theorem sqNorm_sparseUpperCounterexampleVector :
    sqNorm sparseUpperCounterexampleVector = dimension := by
  calc
    sqNorm sparseUpperCounterexampleVector =
        ∑ _ : Fin counterexampleDimension, 1 := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [sparseUpperCounterexampleVector,
        Int.natAbs_one, one_pow]
    _ = counterexampleDimension := by simp
    _ = dimension := by rfl

/-- The local all-ones witness has squared norm exactly `dimension`. -/
theorem sqNorm_allOnesVector :
    sqNorm allOnesVector = dimension := by
  unfold sqNorm
  calc
    (∑ i, (allOnesVector i).natAbs ^ 2) =
        ∑ _ : Fin dimension, 1 := by
      apply Finset.sum_congr rfl
      intro i _
      simp [allOnesVector, sparseUpperCounterexampleVector]
    _ = dimension := by simp

/-- A sparse matrix row dotted with the all-ones witness is its row sum. -/
theorem rowDot_sparseMatrix_counterexampleVector
    (seed : SparseSeed rowCount counterexampleDimension) (j : Fin rowCount) :
    rowDot (sparseMatrix seed) allOnesVector j =
      sparseAllOnesRowSum (seed j) := by
  unfold rowDot sparseMatrix sparseRow sparseAllOnesRowSum
  apply Finset.sum_congr rfl
  intro i _
  simp [allOnesVector, sparseUpperCounterexampleVector]

/-- Every possible all-ones row sum lies in the centered residue interval. -/
theorem sparseAllOnesRowSum_mem_centeredInterval
    (seed : SparseSeed rowCount counterexampleDimension) (j : Fin rowCount) :
    sparseAllOnesRowSum (seed j) ∈
      centeredInterval counterexampleModulus := by
  have hcount :
      sparseRowTrueCount (seed j) ≤ 2 * counterexampleDimension := by
    change
      (boolSupport
        (sparseRowSeedEquivBits counterexampleDimension (seed j))).card ≤
        2 * counterexampleDimension
    simpa [Fintype.card_fin] using
      Finset.card_le_univ
        (s := boolSupport
          (sparseRowSeedEquivBits counterexampleDimension (seed j)))
  have hhalf :
      counterexampleDimension ≤ counterexampleModulus / 2 := by
    norm_num [counterexampleDimension, counterexampleSide,
      counterexampleModulus]
  rw [sparseAllOnesRowSum_eq_trueCount]
  simp only [centeredInterval, Set.mem_Icc]
  constructor <;> push_cast at hcount hhalf ⊢ <;> omega

/-- Centered modular reduction is inactive on every witness row sum. -/
theorem centeredMod_sparseAllOnesRowSum
    (seed : SparseSeed rowCount counterexampleDimension) (j : Fin rowCount) :
    centeredMod counterexampleModulus
        (sparseAllOnesRowSum (seed j)) =
      sparseAllOnesRowSum (seed j) := by
  exact centeredMod_eq_self
    (by
      refine ⟨2_147_483_598, ?_⟩
      norm_num [counterexampleModulus])
    (sparseAllOnesRowSum_mem_centeredInterval seed j)

/-- The modular projection squared norm of the witness is exactly the sum of squared discrete row values. -/
theorem modularProjectionSqNorm_sparseMatrix_counterexampleVector
    (seed : SparseSeed rowCount counterexampleDimension) :
    modularProjectionSqNorm counterexampleModulus
        (sparseMatrix seed) allOnesVector =
      discreteSqNorm (fun j =>
        sparseAllOnesRowSum (seed j)) := by
  unfold modularProjectionSqNorm discreteSqNorm
  apply Finset.sum_congr rfl
  intro j _
  rw [rowDot_sparseMatrix_counterexampleVector,
    centeredMod_sparseAllOnesRowSum]

/-- The modular failure predicate, named to keep elaborator snapshots compact. -/
abbrev sparseUpperMatrixFailure
    (J : Fin rowCount → Fin counterexampleDimension → ℤ) : Prop :=
  modularProjectionSqNorm counterexampleModulus J allOnesVector >
    336 * sqNorm allOnesVector

/-- The corresponding discrete row-sum failure predicate. -/
abbrev sparseUpperRowSumFailure (z : Fin 256 → ℤ) : Prop :=
  336 * dimension < discreteSqNorm z

/-- The two named failure predicates agree on every sparse seed. -/
theorem sparseUpperFailure_iff
    (seed : SparseSeed rowCount counterexampleDimension) :
    sparseUpperMatrixFailure (sparseMatrix seed) ↔
      sparseUpperRowSumFailure
        (fun j => sparseAllOnesRowSum (seed j)) := by
  unfold sparseUpperMatrixFailure sparseUpperRowSumFailure
  rw [modularProjectionSqNorm_sparseMatrix_counterexampleVector,
    sqNorm_allOnesVector]

end Counterexamples.SparseUpper.Internal

end CertifiedJL
