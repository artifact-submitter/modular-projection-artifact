/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Statements.LInf.Upper
import CertifiedJL.Statements.OneRow.Upper
import CertifiedJL.Statements.Shared.BudgetAllocation

/-!
# Matrix infinity upper tails from one-row bounds

This module combines contraction of centered modular representatives with a
finite union bound. It is independent of the analytic method used to prove the
coefficient-uniform one-row estimate.
-/

open scoped BigOperators ENNReal

namespace CertifiedJL

/-- An exact squared modular row failure implies the corresponding real
one-row upper failure before centered reduction. -/
theorem lInfUpperRowFailure_implies_oneRow
    (threshold : NonnegativeRatio) (q : ℕ) {d : ℕ}
    (w : Fin d → ℤ) (row : Fin d → ℤ)
    (hfailure :
      threshold.numerator ^ 2 * sqNorm w <
        threshold.denominator ^ 2 *
          (centeredMod q (∑ i, row i * w i)).natAbs ^ 2) :
    OneRowUpperFailure threshold.toReal (integerEuclideanVector w) row := by
  let z : ℤ := ∑ i, row i * w i
  have hden : (0 : ℝ) < threshold.denominator := by
    exact_mod_cast threshold.denominator_pos
  have hmodNat := centeredMod_natAbs_le q z
  have hmod :
      ((centeredMod q z).natAbs : ℝ) ≤ |(z : ℝ)| := by
    have hmod' :
        ((centeredMod q z).natAbs : ℝ) ≤ (z.natAbs : ℝ) := by
      exact_mod_cast hmodNat
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hmod'
  have hfailReal :
      (threshold.numerator : ℝ) ^ 2 * (sqNorm w : ℝ) <
        (threshold.denominator : ℝ) ^ 2 *
          ((centeredMod q z).natAbs : ℝ) ^ 2 := by
    exact_mod_cast hfailure
  have hnorm := norm_sq_integerEuclideanVector w
  unfold OneRowUpperFailure
  rw [euclideanRowDot_integerEuclideanVector]
  change |(z : ℝ)| > threshold.toReal * ‖integerEuclideanVector w‖
  by_contra hnot
  have hle :
      |(z : ℝ)| ≤ threshold.toReal * ‖integerEuclideanVector w‖ :=
    le_of_not_gt hnot
  have hscaled :
      (threshold.denominator : ℝ) * |(z : ℝ)| ≤
        threshold.numerator * ‖integerEuclideanVector w‖ := by
    rw [NonnegativeRatio.toReal] at hle
    have hrearrange :
        (threshold.numerator : ℝ) / threshold.denominator *
            ‖integerEuclideanVector w‖ =
          ((threshold.numerator : ℝ) *
            ‖integerEuclideanVector w‖) / threshold.denominator := by
      ring
    rw [hrearrange] at hle
    simpa only [mul_comm] using (le_div_iff₀ hden).mp hle
  have hdenNonneg : (0 : ℝ) ≤ threshold.denominator := hden.le
  have hmodNonneg :
      (0 : ℝ) ≤ ((centeredMod q z).natAbs : ℝ) := by positivity
  have habsNonneg : (0 : ℝ) ≤ |(z : ℝ)| := abs_nonneg _
  have hnormNonneg : (0 : ℝ) ≤ ‖integerEuclideanVector w‖ := norm_nonneg _
  have hnumNonneg : (0 : ℝ) ≤ threshold.numerator := by positivity
  have hscaledMod :
      (threshold.denominator : ℝ) *
          ((centeredMod q z).natAbs : ℝ) ≤
        threshold.numerator * ‖integerEuclideanVector w‖ :=
    (mul_le_mul_of_nonneg_left hmod hdenNonneg).trans hscaled
  have hsqscaled :=
    (sq_le_sq₀
      (mul_nonneg hdenNonneg hmodNonneg)
      (mul_nonneg hnumNonneg hnormNonneg)).mpr hscaledMod
  have hcontra :
      (threshold.denominator : ℝ) ^ 2 *
          ((centeredMod q z).natAbs : ℝ) ^ 2 ≤
        (threshold.numerator : ℝ) ^ 2 * (sqNorm w : ℝ) := by
    simpa only [mul_pow, hnorm] using hsqscaled
  exact (not_lt_of_ge hcontra) hfailReal

/-- A coefficient-uniform one-row theorem implies a modular matrix
infinity-norm upper theorem whenever the row allocations fit in the requested
total failure budget. -/
theorem LInfUpperTailAt.of_oneRow
    {distribution : ProjectionDistribution} {rows : ℕ} {threshold : NonnegativeRatio}
    {rowBudget totalBudget : ENNReal}
    (hrows : 0 < rows)
    (hone : OneRowUpperTailAt
      { distribution := distribution, threshold := threshold.toReal } rowBudget)
    (hbudget : rows • rowBudget ≤ totalBudget) :
    LInfUpperTailAt
      { distribution := distribution, rows := rows, coordinateThreshold := threshold }
      totalBudget := by
  intro q d w
  let _ : Nonempty (Fin rows) := Fin.pos_iff_nonempty.mp hrows
  unfold LInfUpperFailure
  apply eventProbability_iUnion_lt_of_budgetAllocation
    (p := distribution.matrixPMF rows d)
    (event := fun j J =>
      threshold.numerator ^ 2 * sqNorm w <
        threshold.denominator ^ 2 *
          (centeredMod q (rowDot J w j)).natAbs ^ 2)
    (allocation := fun _ => rowBudget)
    (total := totalBudget)
  · intro j
    calc
      eventProbability (distribution.matrixPMF rows d)
          (fun J => threshold.numerator ^ 2 * sqNorm w <
            threshold.denominator ^ 2 *
              (centeredMod q (rowDot J w j)).natAbs ^ 2) ≤
        eventProbability (distribution.matrixPMF rows d)
          (fun J => OneRowUpperFailure threshold.toReal
            (integerEuclideanVector w) (J j)) := by
          apply eventProbability_mono
          intro J hJ
          exact lInfUpperRowFailure_implies_oneRow threshold q w (J j) hJ
      _ = eventProbability (distribution.rowPMF d)
          (OneRowUpperFailure threshold.toReal
            (integerEuclideanVector w)) := by
          calc
            _ = eventProbability
                ((distribution.matrixPMF rows d).map (fun J => J j))
                (OneRowUpperFailure threshold.toReal
                  (integerEuclideanVector w)) := by
                unfold eventProbability
                rw [PMF.map_comp]
                rfl
            _ = _ := by rw [ProjectionDistribution.matrixPMF_rowMarginal]
      _ < rowBudget := hone d (integerEuclideanVector w)
  · simpa using hbudget

end CertifiedJL
