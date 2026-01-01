/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Unrestricted.Conditioning

/-!
# Exact activity counting for balanced-ternary threshold lower tails

This module contains the row-count-generic distributional counting identity
used by protocol-threshold proofs. It does not expose the retired cap-relative
dominant-coordinate assembly.
-/

open scoped BigOperators ENNReal

namespace CertifiedJL

open Probability

/-- Exact count of `rows`-bit activity patterns below an arbitrary cutoff. -/
theorem card_dominantActivityCount_lt_at (rows cutoff : ℕ) :
    Fintype.card
        {activity : DominantActivity rows //
          (dominantActivityCount activity : ℕ) < cutoff} =
      ∑ k ∈ Finset.range cutoff, rows.choose k := by
  let e :
      {activity : DominantActivity rows //
          (dominantActivityCount activity : ℕ) < cutoff} ≃
        {activity : Fin rows → Bool //
          trueCountOn (fun _ : Fin rows => True) activity < cutoff} :=
    Equiv.subtypeEquiv (Equiv.refl _) fun activity => by
      simp [dominantActivityCount, trueCountOn, boolSupport]
  rw [Fintype.card_congr e, card_trueCountOn_lt]
  simp

/-- Compatibility specialization of exact activity counting at 256 rows. -/
theorem card_dominantActivityCount_lt (cutoff : ℕ) :
    Fintype.card
        {activity : DominantActivity 256 //
          (dominantActivityCount activity : ℕ) < cutoff} =
      ∑ k ∈ Finset.range cutoff, (256 : ℕ).choose k :=
  card_dominantActivityCount_lt_at 256 cutoff

/-- Exact probability of an activity count below an arbitrary cutoff and row
count. -/
theorem sparse_dominantActivityCount_lt_probability_eq_at
    {d : ℕ} (rows : ℕ) (i : Fin d) (cutoff : ℕ) :
    eventProbability (sparseRademacherMatrix rows d)
        (fun J =>
          (dominantActivityCount (matrixDominantActivity i J) : ℕ) < cutoff) =
      ((∑ k ∈ Finset.range cutoff, rows.choose k : ℕ) : ℝ≥0∞) *
        ((2 ^ rows : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [show
      eventProbability (sparseRademacherMatrix rows d)
          (fun J =>
            (dominantActivityCount (matrixDominantActivity i J) : ℕ) < cutoff) =
        eventProbability
          ((sparseRademacherMatrix rows d).map (matrixDominantActivity i))
          (fun activity =>
            (dominantActivityCount activity : ℕ) < cutoff) by
    unfold eventProbability
    rw [PMF.map_comp]
    rfl]
  rw [sparseRademacherMatrix_dominantActivity]
  rw [eventProbability_uniform_eq_card]
  rw [card_dominantActivityCount_lt_at]
  rw [show Fintype.card (DominantActivity rows) = 2 ^ rows by
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]]

/-- Compatibility specialization of the exact activity probability at 256
rows. -/
theorem sparse_dominantActivityCount_lt_probability_eq
    {d : ℕ} (i : Fin d) (cutoff : ℕ) :
    eventProbability (sparseRademacherMatrix 256 d)
        (fun J =>
          (dominantActivityCount (matrixDominantActivity i J) : ℕ) < cutoff) =
      ((∑ k ∈ Finset.range cutoff, (256 : ℕ).choose k : ℕ) : ℝ≥0∞) *
        ((2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ :=
  sparse_dominantActivityCount_lt_probability_eq_at 256 i cutoff

end CertifiedJL
