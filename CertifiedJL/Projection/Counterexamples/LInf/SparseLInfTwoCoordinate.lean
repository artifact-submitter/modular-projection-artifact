/-
Copyright (c) 2026 Anonymous Author and Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author, Anonymous Author
-/

import CertifiedJL.Model.Distributions.Entry
import CertifiedJL.Probability.Finite.Counting
import CertifiedJL.Statements.L2.Upper.Rows256Bits128

/-!
# Two-coordinate sparse infinity-norm obstruction

This module formalizes the finite counting core of a two-coordinate sparse
infinity-norm obstruction. A sparse row passes exactly when two
independent sparse entries do not have the same nonzero sign.  Fourteen of
the sixteen equiprobable row seeds pass, so all 256 rows pass with probability
`(7 / 8) ^ 256`, which is strictly greater than `2 ^ (-128)`.
-/

open scoped ENNReal

namespace CertifiedJL

/-- The row event in the two-coordinate sparse infinity-norm obstruction. -/
def sparseLInfTwoCoordinateRowPass (row : Fin 2 → ℤ) : Prop :=
  |row 0 + row 1| ≤ 1

instance sparseLInfTwoCoordinateRowPassDecidable :
    DecidablePred sparseLInfTwoCoordinateRowPass := by
  intro row
  unfold sparseLInfTwoCoordinateRowPass
  infer_instance

/-- Every one of the 256 projected coordinates satisfies the coordinate cap. -/
def SparseLInfTwoCoordinatePass
    (J : Matrix (Fin rowCount) (Fin 2) ℤ) : Prop :=
  ∀ j, sparseLInfTwoCoordinateRowPass (J j)

instance sparseLInfTwoCoordinatePassDecidable :
    DecidablePred SparseLInfTwoCoordinatePass := by
  intro J
  unfold SparseLInfTwoCoordinatePass
  let : DecidablePred (fun j => sparseLInfTwoCoordinateRowPass (J j)) :=
    fun j => sparseLInfTwoCoordinateRowPassDecidable (J j)
  exact Fintype.decidableForallFintype

namespace Counterexamples.SparseLInfTwoCoordinate.Internal

/-- Fourteen of the sixteen uniform four-bit row seeds pass. -/
theorem sparseLInfTwoCoordinateRowPass_card :
    Fintype.card
        {seed : SparseRowSeed 2 //
          sparseLInfTwoCoordinateRowPass (sparseRow seed)} = 14 := by
  decide

/-- Separate a matrix seed satisfying the row event into satisfying row seeds. -/
def sparseLInfTwoCoordinateSeedEquiv (m : ℕ) :
    {seed : SparseSeed m 2 //
        ∀ j, sparseLInfTwoCoordinateRowPass (sparseRow (seed j))} ≃
      (Fin m →
        {seed : SparseRowSeed 2 //
          sparseLInfTwoCoordinateRowPass (sparseRow seed)}) where
  toFun seed j := ⟨seed.1 j, seed.2 j⟩
  invFun rows := ⟨fun j => (rows j).1, fun j => (rows j).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sparseLInfTwoCoordinateSeed_card (m : ℕ) :
    Fintype.card
        {seed : SparseSeed m 2 //
          ∀ j, sparseLInfTwoCoordinateRowPass (sparseRow (seed j))} =
      14 ^ m := by
  rw [Fintype.card_congr (sparseLInfTwoCoordinateSeedEquiv m),
    Fintype.card_fun, sparseLInfTwoCoordinateRowPass_card, Fintype.card_fin]

theorem sparseSeedTwo_card (m : ℕ) :
    Fintype.card (SparseSeed m 2) = 16 ^ m := by
  classical
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_prod]
  norm_num

set_option maxRecDepth 10000 in
theorem sparseLInfTwoCoordinateProbability_exact :
    eventProbability
        (sparseRademacherMatrix rowCount 2)
        SparseLInfTwoCoordinatePass =
      (14 : ℝ≥0∞) ^ rowCount * ((16 : ℝ≥0∞) ^ rowCount)⁻¹ := by
  rw [sparseRademacherMatrix_eq_map_uniformSeed]
  change
    eventProbability
        (PMF.map sparseMatrix
          (PMF.uniformOfFintype (SparseSeed rowCount 2)))
        (fun J => ∀ j, sparseLInfTwoCoordinateRowPass (J j)) = _
  rw [Probability.eventProbability_map_uniform_eq_card]
  change
    (Fintype.card
        {seed : SparseSeed rowCount 2 //
          ∀ j, sparseLInfTwoCoordinateRowPass (sparseRow (seed j))} : ℝ≥0∞) *
        (Fintype.card (SparseSeed rowCount 2) : ℝ≥0∞)⁻¹ = _
  rw [sparseLInfTwoCoordinateSeed_card, sparseSeedTwo_card]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 10000 in
theorem sparseLInfTwoCoordinateProbability_gt :
    eventProbability
        (sparseRademacherMatrix rowCount 2)
        SparseLInfTwoCoordinatePass >
      failureTarget securityBits := by
  rw [sparseLInfTwoCoordinateProbability_exact]
  change
    (2 : ℝ≥0∞)⁻¹ ^ 128 <
      (14 : ℝ≥0∞) ^ 256 * ((16 : ℝ≥0∞) ^ 256)⁻¹
  have hscaled :
      (16 : ℕ) ^ 256 < 2 ^ 128 * 14 ^ 256 := by
    norm_num
  rw [← ENNReal.toReal_lt_toReal (by simp) (by
    exact ENNReal.mul_ne_top (by simp) (by simp))]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_mul]
  field_simp
  exact_mod_cast hscaled

end Counterexamples.SparseLInfTwoCoordinate.Internal

end CertifiedJL
