/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Projection.RowRestriction
import CertifiedJL.Statements.L2.Lower.Affine
import CertifiedJL.Statements.L2.Upper
import CertifiedJL.Statements.LInf.Lower.Affine
import CertifiedJL.Statements.LInf.Upper

/-!
# Tail-statement transports across row counts

Upper failures restrict to an initial row segment, so an upper-tail theorem at
more rows implies the same theorem at fewer rows.  Lower failures move in the
opposite direction: adding rows can only make the lower event smaller.  The
affine lower transports restrict the fixed shift together with the matrix.
-/

namespace CertifiedJL

private theorem sum_castLE_le_sum {smallRows largeRows : ℕ}
    (hrows : smallRows ≤ largeRows) (f : Fin largeRows → ℕ) :
    ∑ j : Fin smallRows, f (Fin.castLE hrows j) ≤ ∑ j : Fin largeRows, f j := by
  classical
  let e : Fin smallRows ↪ Fin largeRows :=
    ⟨Fin.castLE hrows, Fin.castLE_injective hrows⟩
  calc
    ∑ j : Fin smallRows, f (Fin.castLE hrows j) =
        ∑ j ∈ Finset.univ.map e, f j := by
      rw [Finset.sum_map]
      rfl
    _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin largeRows)), f j := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => Nat.zero_le _)
    _ = ∑ j : Fin largeRows, f j := by simp

/-- Restricting rows cannot increase modular projected squared norm. -/
theorem modularProjectionSqNorm_restrictRows_le {smallRows largeRows d q : ℕ}
    (hrows : smallRows ≤ largeRows) (J : Fin largeRows → Fin d → ℤ)
    (w : Fin d → ℤ) :
    modularProjectionSqNorm q (restrictRows hrows J) w ≤ modularProjectionSqNorm q J w := by
  unfold modularProjectionSqNorm
  simpa [restrictRows, rowDot] using sum_castLE_le_sum hrows
    (fun j => (centeredMod q (rowDot J w j)).natAbs ^ 2)

/-- Restricting both a matrix and its fixed row-wise shift cannot increase
affine modular projected squared norm. -/
theorem shiftedModularProjectionSqNorm_restrictRows_le {smallRows largeRows d q : ℕ}
    (hrows : smallRows ≤ largeRows) (shift : Fin largeRows → ℤ)
    (J : Fin largeRows → Fin d → ℤ) (w : Fin d → ℤ) :
    shiftedModularProjectionSqNorm q (restrictRows hrows shift)
        (restrictRows hrows J) w ≤
      shiftedModularProjectionSqNorm q shift J w := by
  unfold shiftedModularProjectionSqNorm
  simpa [restrictRows, rowDot] using sum_castLE_le_sum hrows
    (fun j => (centeredMod q (shift j + rowDot J w j)).natAbs ^ 2)

/-- An L2 upper-tail theorem at `largeRows` restricts to every smaller row
count with the same threshold and budget. -/
theorem L2UpperTailAt.restrict_rows
    {distribution : ProjectionDistribution} {smallRows largeRows : ℕ} {threshold : NonnegativeRatio}
    {budget : ENNReal} (hrows : smallRows ≤ largeRows)
    (h : L2UpperTailAt
      { distribution := distribution, rows := largeRows, threshold := threshold } budget) :
    L2UpperTailAt
      { distribution := distribution, rows := smallRows, threshold := threshold } budget := by
  intro q d w
  rw [eventProbability_matrixPMF_restrictRows distribution hrows]
  apply (eventProbability_mono _ fun J hJ => ?_).trans_lt (h q d w)
  unfold L2UpperFailure at hJ ⊢
  exact hJ.trans_le (Nat.mul_le_mul_left threshold.denominator
      (modularProjectionSqNorm_restrictRows_le hrows J w))

/-- Transport an L2 upper-tail theorem across all three monotone parameters.

The target may use fewer rows, a larger exact threshold, and a larger failure
budget.  This theorem is the certificate-free closure operation for a
certified upper endpoint. -/
theorem L2UpperTailAt.mono_parameters
    {distribution : ProjectionDistribution}
    {sourceRows targetRows : ℕ}
    {sourceThreshold targetThreshold : NonnegativeRatio}
    {sourceBudget targetBudget : ENNReal}
    (hrows : targetRows ≤ sourceRows)
    (hthreshold : sourceThreshold.LE targetThreshold)
    (hbudget : sourceBudget ≤ targetBudget)
    (h : L2UpperTailAt
      { distribution := distribution
        rows := sourceRows
        threshold := sourceThreshold }
      sourceBudget) :
    L2UpperTailAt
      { distribution := distribution
        rows := targetRows
        threshold := targetThreshold }
      targetBudget :=
  ((h.restrict_rows hrows).mono_threshold hthreshold).mono_budget hbudget

/-- An infinity-norm upper-tail theorem at `largeRows` restricts to every
smaller row count with the same coordinate threshold and budget. -/
theorem LInfUpperTailAt.restrict_rows
    {distribution : ProjectionDistribution} {smallRows largeRows : ℕ}
    {coordinateThreshold : NonnegativeRatio} {budget : ENNReal}
    (hrows : smallRows ≤ largeRows)
    (h : LInfUpperTailAt
      { distribution := distribution, rows := largeRows,
        coordinateThreshold := coordinateThreshold } budget) :
    LInfUpperTailAt
      { distribution := distribution, rows := smallRows,
        coordinateThreshold := coordinateThreshold } budget := by
  intro q d w
  rw [eventProbability_matrixPMF_restrictRows distribution hrows]
  apply (eventProbability_mono _ fun J hJ => ?_).trans_lt (h q d w)
  obtain ⟨j, hj⟩ := hJ
  exact ⟨Fin.castLE hrows j, hj⟩

/-- An L2 threshold-lower theorem extends to every larger row count with the
same floor, margin, and budget. -/
theorem L2ThresholdLowerTailAt.extend_rows
    {distribution : ProjectionDistribution} {smallRows largeRows : ℕ}
    {squaredNormFloor modulusMargin : NonnegativeRatio} {budget : ENNReal}
    (hrows : smallRows ≤ largeRows)
    (h : L2ThresholdLowerTailAt
      { distribution := distribution, rows := smallRows, squaredNormFloor := squaredNormFloor,
        modulusMargin := modulusMargin } budget) :
    L2ThresholdLowerTailAt
      { distribution := distribution, rows := largeRows, squaredNormFloor := squaredNormFloor,
        modulusMargin := modulusMargin } budget := by
  intro q d w inputThreshold hq hcentered hpositive hnorm hmodulus
  calc
    eventProbability (distribution.matrixPMF largeRows d)
        (L2ThresholdLowerFailure squaredNormFloor inputThreshold q w) ≤
      eventProbability (distribution.matrixPMF largeRows d)
        (fun J => L2ThresholdLowerFailure squaredNormFloor inputThreshold q w
          (restrictRows hrows J)) := by
      apply eventProbability_mono
      intro J hJ
      unfold L2ThresholdLowerFailure at hJ ⊢
      exact (Nat.mul_le_mul_left squaredNormFloor.denominator
        (modularProjectionSqNorm_restrictRows_le hrows J w)).trans_lt hJ
    _ = eventProbability (distribution.matrixPMF smallRows d)
        (L2ThresholdLowerFailure squaredNormFloor inputThreshold q w) :=
      (eventProbability_matrixPMF_restrictRows distribution hrows _).symm
    _ < budget :=
      h q d w inputThreshold hq hcentered hpositive hnorm hmodulus

/-- An affine L2 threshold-lower theorem extends to every larger row count. -/
theorem AffineL2ThresholdLowerTailAt.extend_rows
    {distribution : ProjectionDistribution} {smallRows largeRows : ℕ}
    {squaredNormFloor modulusMargin : NonnegativeRatio} {budget : ENNReal}
    (hrows : smallRows ≤ largeRows)
    (h : AffineL2ThresholdLowerTailAt
      { distribution := distribution, rows := smallRows, squaredNormFloor := squaredNormFloor,
        modulusMargin := modulusMargin } budget) :
    AffineL2ThresholdLowerTailAt
      { distribution := distribution, rows := largeRows, squaredNormFloor := squaredNormFloor,
        modulusMargin := modulusMargin } budget := by
  intro q d w inputThreshold shift hq hcentered hpositive hnorm hmodulus
  calc
    eventProbability (distribution.matrixPMF largeRows d)
        (AffineL2ThresholdLowerFailure squaredNormFloor inputThreshold q shift w) ≤
      eventProbability (distribution.matrixPMF largeRows d)
        (fun J => AffineL2ThresholdLowerFailure squaredNormFloor inputThreshold q
          (restrictRows hrows shift) w (restrictRows hrows J)) := by
      apply eventProbability_mono
      intro J hJ
      unfold AffineL2ThresholdLowerFailure at hJ ⊢
      exact (Nat.mul_le_mul_left squaredNormFloor.denominator
        (shiftedModularProjectionSqNorm_restrictRows_le hrows shift J w)).trans_lt hJ
    _ = eventProbability (distribution.matrixPMF smallRows d)
        (AffineL2ThresholdLowerFailure squaredNormFloor inputThreshold q
          (restrictRows hrows shift) w) :=
      (eventProbability_matrixPMF_restrictRows distribution hrows _).symm
    _ < budget := h q d w inputThreshold (restrictRows hrows shift)
      hq hcentered hpositive hnorm hmodulus

/-- A coordinatewise threshold-lower theorem extends to every larger row
count with the same cap, margin, and budget. -/
theorem LInfThresholdLowerTailAt.extend_rows
    {distribution : ProjectionDistribution} {smallRows largeRows : ℕ}
    {coordinateCap modulusMargin : NonnegativeRatio} {budget : ENNReal}
    (hrows : smallRows ≤ largeRows)
    (h : LInfThresholdLowerTailAt
      { distribution := distribution, rows := smallRows, coordinateCap := coordinateCap,
        modulusMargin := modulusMargin } budget) :
    LInfThresholdLowerTailAt
      { distribution := distribution, rows := largeRows, coordinateCap := coordinateCap,
        modulusMargin := modulusMargin } budget := by
  intro q d w inputThreshold hq hcentered hpositive hnorm hmodulus
  let smallParameters : LInfThresholdLowerParameters :=
    { distribution := distribution, rows := smallRows, coordinateCap := coordinateCap,
      modulusMargin := modulusMargin }
  let largeParameters : LInfThresholdLowerParameters :=
    { distribution := distribution, rows := largeRows, coordinateCap := coordinateCap,
      modulusMargin := modulusMargin }
  calc
    eventProbability (distribution.matrixPMF largeRows d)
        (LInfThresholdSmallProjection largeParameters inputThreshold q w) ≤
      eventProbability (distribution.matrixPMF largeRows d)
        (fun J => LInfThresholdSmallProjection smallParameters inputThreshold q w
          (restrictRows hrows J)) := by
      apply eventProbability_mono
      intro J hJ j
      exact hJ (Fin.castLE hrows j)
    _ = eventProbability (distribution.matrixPMF smallRows d)
        (LInfThresholdSmallProjection smallParameters inputThreshold q w) :=
      (eventProbability_matrixPMF_restrictRows distribution hrows _).symm
    _ < budget :=
      h q d w inputThreshold hq hcentered hpositive hnorm hmodulus

/-- An affine coordinatewise threshold-lower theorem extends to every larger
row count, with the fixed shift restricted in the source application. -/
theorem AffineLInfThresholdLowerTailAt.extend_rows
    {distribution : ProjectionDistribution} {smallRows largeRows : ℕ}
    {coordinateCap modulusMargin : NonnegativeRatio} {budget : ENNReal}
    (hrows : smallRows ≤ largeRows)
    (h : AffineLInfThresholdLowerTailAt
      { distribution := distribution, rows := smallRows, coordinateCap := coordinateCap,
        modulusMargin := modulusMargin } budget) :
    AffineLInfThresholdLowerTailAt
      { distribution := distribution, rows := largeRows, coordinateCap := coordinateCap,
        modulusMargin := modulusMargin } budget := by
  intro q d w inputThreshold shift hq hcentered hpositive hnorm hmodulus
  let smallParameters : LInfThresholdLowerParameters :=
    { distribution := distribution, rows := smallRows, coordinateCap := coordinateCap,
      modulusMargin := modulusMargin }
  let largeParameters : LInfThresholdLowerParameters :=
    { distribution := distribution, rows := largeRows, coordinateCap := coordinateCap,
      modulusMargin := modulusMargin }
  calc
    eventProbability (distribution.matrixPMF largeRows d)
        (AffineLInfThresholdSmallProjection largeParameters inputThreshold q
          shift w) ≤
      eventProbability (distribution.matrixPMF largeRows d)
        (fun J => AffineLInfThresholdSmallProjection smallParameters
          inputThreshold q (restrictRows hrows shift) w
          (restrictRows hrows J)) := by
      apply eventProbability_mono
      intro J hJ j
      exact hJ (Fin.castLE hrows j)
    _ = eventProbability (distribution.matrixPMF smallRows d)
        (AffineLInfThresholdSmallProjection smallParameters inputThreshold q
          (restrictRows hrows shift) w) :=
      (eventProbability_matrixPMF_restrictRows distribution hrows _).symm
    _ < budget := h q d w inputThreshold (restrictRows hrows shift)
      hq hcentered hpositive hnorm hmodulus

end CertifiedJL
