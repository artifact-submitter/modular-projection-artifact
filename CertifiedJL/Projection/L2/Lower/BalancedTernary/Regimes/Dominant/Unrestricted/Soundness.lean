/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Unrestricted.Analytic

/-!
# Probability bridge for dominant-coordinate bounds

This module turns bounds under each exact conditioned seed law into the pure
binomial average used by the public-threshold dominant cells. It contains no
certificate data or numeric checker assumptions.
-/

open scoped BigOperators

namespace CertifiedJL

/-- Exact real event averaging under the sparse-matrix PMF. -/
theorem sparseMatrix_eventProbability_toReal_eq_dominantAverage
    {m d : ℕ} (i : Fin d) (event : (Fin m → Fin d → ℤ) → Prop) :
    (eventProbability (sparseRademacherMatrix m d) event).toReal =
      ∑ activity : DominantActivity m,
        (Fintype.card (DominantActivity m) : ℝ)⁻¹ *
          (eventProbability (dominantConditionalMatrixPMF i activity)
            event).toReal := by
  rw [sparseRademacherMatrix_eq_map_uniformDominantView i]
  exact Probability.eventProbability_map_uniform_prod_toReal
    (fun activity conditional =>
      sparseMatrixOfDominantView i (activity, conditional)) event

/-- Regroup a function of the active count by its exact binomial fibers. -/
theorem sum_dominantActivityCount_at
    (rows : ℕ) (Q : Fin (rows + 1) → ℝ) :
    ∑ activity : DominantActivity rows, Q (dominantActivityCount activity) =
      ∑ k : Fin (rows + 1), (rows.choose (k : ℕ) : ℝ) * Q k := by
  rw [← Fintype.sum_fiberwise' dominantActivityCount Q]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_univ]
  rw [card_dominantActivityCount_fiber]

/-- Compatibility specialization of active-count regrouping at 256 rows. -/
theorem sum_dominantActivityCount (Q : Fin 257 → ℝ) :
    ∑ activity : DominantActivity 256, Q (dominantActivityCount activity) =
      ∑ k : Fin 257, ((256 : ℕ).choose (k : ℕ) : ℝ) * Q k :=
  sum_dominantActivityCount_at 256 Q

/-- Uniform activity averaging is exactly the corresponding binomial
average. -/
theorem dominantActivityAverage_eq_binomialAverage_at
    (rows : ℕ) (Q : Fin (rows + 1) → ℝ) :
    ∑ activity : DominantActivity rows,
        (Fintype.card (DominantActivity rows) : ℝ)⁻¹ *
          Q (dominantActivityCount activity) =
      dominantBinomialAverageAt rows Q := by
  rw [← Finset.mul_sum]
  rw [sum_dominantActivityCount_at]
  rw [dominantBinomialAverageAt]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  norm_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [div_eq_mul_inv]
  ring

/-- Compatibility specialization of uniform activity averaging at 256 rows. -/
theorem dominantActivityAverage_eq_binomialAverage (Q : Fin 257 → ℝ) :
    ∑ activity : DominantActivity 256,
        (Fintype.card (DominantActivity 256) : ℝ)⁻¹ *
          Q (dominantActivityCount activity) =
      dominantBinomialAverage Q := by
  simpa [dominantBinomialAverage, dominantBinomialAverageAt] using
    dominantActivityAverage_eq_binomialAverage_at 256 Q

/-- Conditional event bounds indexed by the active set imply their exact
binomial average under `sparseRademacherMatrix`. -/
theorem dominantEventProbability_le_binomialAverage_of_conditional_at
    {d : ℕ} (rows : ℕ) (i : Fin d)
    (event : (Fin rows → Fin d → ℤ) → Prop)
    (Q : Fin (rows + 1) → ℝ)
    (hconditional : ∀ activity : DominantActivity rows,
      (eventProbability (dominantConditionalMatrixPMF i activity)
        event).toReal ≤ Q (dominantActivityCount activity)) :
    (eventProbability (sparseRademacherMatrix rows d) event).toReal ≤
      dominantBinomialAverageAt rows Q := by
  rw [sparseMatrix_eventProbability_toReal_eq_dominantAverage i event]
  rw [← dominantActivityAverage_eq_binomialAverage_at rows Q]
  apply Finset.sum_le_sum
  intro activity _
  exact mul_le_mul_of_nonneg_left (hconditional activity) (by positivity)

end CertifiedJL
