/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Distributions.Entry
import CertifiedJL.Probability.Finite.Counting
import CertifiedJL.Probability.Product.RowTensorization
import CertifiedJL.Statements.LInf.Lower
import Mathlib.Tactic

/-!
# A finite 192-row obstruction at coordinate cap 0.34

For `q = 7`, public threshold `b = 3`, and
`w = (1,1,1,1,1,2)`, a row passes the `17/50` coordinate cap exactly when
its centered dot product has magnitude at most one.  Exactly `2116` of the
`4096` equiprobable sparse-row seeds pass.  Hence all 192 rows pass with
probability `(529/1024)^192`, which is strictly greater than `2^-183`.

This is an exact finite obstruction: the corresponding 183-bit theorem is
false.  It deliberately does not claim that the proved 129-bit theorem is
tight; the interval between 129 and 182 bits remains open.
-/

open scoped ENNReal

namespace CertifiedJL

namespace Counterexamples.TernaryLInfRows192Cap34

def parameters : LInfThresholdLowerParameters :=
  { distribution := .balancedTernary
    rows := 192
    coordinateCap :=
      { numerator := 17, denominator := 50, denominator_pos := by decide }
    modulusMargin := NonnegativeRatio.ofNat 2 }

def witness : Fin 6 → ℤ := fun i => if i = 5 then 2 else 1

def rowPass (row : Fin 6 → ℤ) : Prop :=
  50 ^ 2 * (centeredMod 7 (∑ i, row i * witness i)).natAbs ^ 2 ≤
    17 ^ 2 * 3 ^ 2

instance rowPassDecidable : DecidablePred rowPass := by
  intro row
  unfold rowPass
  infer_instance

theorem witness_centered : CenteredInput 7 witness := by
  intro i
  by_cases h : i = 5
  · subst i
    norm_num [witness, centeredInterval]
  · simp [witness, h, centeredInterval]

theorem witness_sqNorm : sqNorm witness = 9 := by
  decide

theorem row_event_eq (row : Fin 6 → ℤ) :
    rowPass row ↔
      50 ^ 2 * (centeredMod 7 (rowDot (fun _ : Fin 1 => row) witness 0)).natAbs ^ 2 ≤
        17 ^ 2 * 3 ^ 2 := by
  simp only [rowPass, rowDot]

set_option maxRecDepth 10000 in
theorem rowPass_card :
    Fintype.card {seed : SparseRowSeed 6 // rowPass (sparseRow seed)} = 2116 := by
  decide

theorem rowSeed_card : Fintype.card (SparseRowSeed 6) = 4096 := by
  classical
  rw [Fintype.card_fun, Fintype.card_prod]
  norm_num

theorem rowProbability_exact :
    eventProbability (sparseRademacherRow 6) rowPass =
      (529 : ℝ≥0∞) * (1024 : ℝ≥0∞)⁻¹ := by
  rw [sparseRademacherRow_eq_map_uniformRowSeed,
    Probability.eventProbability_map_uniform_eq_card, rowPass_card, rowSeed_card]
  rw [← ENNReal.toReal_eq_toReal_iff'
    (ENNReal.mul_ne_top (by norm_num)
      (ENNReal.inv_ne_top.mpr (by norm_num)))
    (ENNReal.mul_ne_top (by norm_num)
      (ENNReal.inv_ne_top.mpr (by norm_num)))]
  norm_num

theorem matrix_event_eq (J : Fin 192 → Fin 6 → ℤ) :
    LInfThresholdSmallProjection parameters 3 7 witness J ↔
      ∀ j, rowPass (J j) := by
  rfl

theorem probability_exact :
    eventProbability (sparseRademacherMatrix 192 6)
        (LInfThresholdSmallProjection parameters 3 7 witness) =
      ((529 : ℝ≥0∞) * (1024 : ℝ≥0∞)⁻¹) ^ 192 := by
  rw [eventProbability_congr
    (sparseRademacherMatrix 192 6)
    (event' := fun J => ∀ j, rowPass (J j)) matrix_event_eq]
  rw [sparseRademacherMatrix_eventProbability_allRows_eq_pow,
    rowProbability_exact]

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 10000 in
theorem probability_gt_failureTarget183 :
    eventProbability (sparseRademacherMatrix 192 6)
        (LInfThresholdSmallProjection parameters 3 7 witness) >
      failureTarget 183 := by
  rw [probability_exact]
  change
    (2 : ℝ≥0∞)⁻¹ ^ 183 <
      ((529 : ℝ≥0∞) * (1024 : ℝ≥0∞)⁻¹) ^ 192
  have hbase : (529 : ℝ≥0∞) * (1024 : ℝ≥0∞)⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num)
      (ENNReal.inv_ne_top.mpr (by norm_num))
  rw [← ENNReal.toReal_lt_toReal
    (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by norm_num)))
    (ENNReal.pow_ne_top hbase)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_mul]
  norm_num

/-- The 192-row `17/50` lower-tail theorem is false at 183 bits. -/
theorem bits183_false :
    ¬ LInfThresholdLowerTailAt parameters (failureTarget 183) := by
  intro h
  have hclaimed := h 7 6 witness 3 (by norm_num) witness_centered
    (by norm_num) (by simp [InputThresholdAtMostNorm, witness_sqNorm])
    (by norm_num [InputThresholdWithinModulus, parameters,
      NonnegativeRatio.ofNat])
  exact (not_lt_of_ge probability_gt_failureTarget183.le) hclaimed

end Counterexamples.TernaryLInfRows192Cap34

end CertifiedJL
