/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.ProviderCore
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.RetainedProvider128

/-! # Target-neutral retained dominant provider -/

open MeasureTheory

namespace CertifiedJL

/-- Event-level retained branch for arbitrary row count, squared-norm floor, and
high-activity budget. -/
theorem sparseThresholdDominantHighActivity_retained_of_geometry_at
    {rows squaredNormFloor : ℕ} {highBudget : ℝ}
    (geometry : CertificateContracts.SparseL2ThresholdDominantRetainedGeometry)
    (finalRatio : Real.exp
      ((23 / 10 : ℝ) * squaredNormFloor * (2500 / 2401)) *
        (53 / 100 : ℝ) ^ rows < highBudget)
    (hbudget : 0 < highBudget)
    {q d : ℕ} (w : Fin d → ℤ) (inputThreshold : ℕ) (i : Fin d)
    (hq : Odd q) (hinputThreshold : 0 < inputThreshold) (hi : w i ≠ 0)
    (hdominant : 49 * inputThreshold < 50 * (w i).natAbs)
    (hmax : ∀ j, (w j).natAbs ^ 2 ≤ (w i).natAbs ^ 2)
    (hresidual : (1 / 2 : ℝ) ≤ dominantResidualRatio w i)
    (hmodulus : 3 ≤ (q : ℝ) / (dominantAmplitude w i : ℝ)) :
    eventProbability (sparseRademacherMatrix rows d)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
              inputThreshold q w J ∧
            squaredNormFloor ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ)) <
      ENNReal.ofReal highBudget := by
  let A := dominantAmplitude w i
  let s : ℝ := (23 / 10) * (inputThreshold : ℝ) ^ 2 / (A : ℝ) ^ 2
  have hA : 0 < A := dominantAmplitude_pos hi
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  have hs : 0 < s := by dsimp [s]; positivity
  have hcoefficient : s / (inputThreshold : ℝ) ^ 2 =
      (23 / 10 : ℝ) / (A : ℝ) ^ 2 := by
    dsimp [s]
    field_simp
  have hrow := sparseThresholdDominant_retained_row_le_fiftythree_hundred_of_geometry
    geometry w i hq hi hmax hresidual hmodulus
  have hrowThreshold :
      ∫ row, Real.exp
          (-(s / (inputThreshold : ℝ) ^ 2) * sparseLowerRowKernel q w row)
          ∂(sparseRademacherRow d).toMeasure ≤ 53 / 100 := by
    simpa only [hcoefficient] using hrow
  have hdomReal : (49 : ℝ) * inputThreshold < 50 * A := by
    exact_mod_cast hdominant
  have hsq :
      (2401 : ℝ) * (inputThreshold : ℝ) ^ 2 < 2500 * (A : ℝ) ^ 2 := by
    have hproduct : 0 <
        (50 * (A : ℝ) - 49 * inputThreshold) *
          (50 * (A : ℝ) + 49 * inputThreshold) := by positivity
    nlinarith
  have hthresholdRatio :
      (inputThreshold : ℝ) ^ 2 / (A : ℝ) ^ 2 < 2500 / 2401 := by
    apply (div_lt_iff₀ (sq_pos_of_pos hAreal)).2
    nlinarith
  exact sparseThresholdDominantHighActivity_of_rowKernel_at
    rows squaredNormFloor w inputThreshold i (23 / 10) (53 / 100)
      (2500 / 2401) hbudget hinputThreshold hi (by norm_num)
      hthresholdRatio.le hrow (by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          finalRatio)

/-- Compatibility wrapper for the fixed-tilt replay structure. -/
theorem sparseThresholdDominantHighActivity_retained_of_replay_at
    {rows squaredNormFloor : ℕ} {highBudget : ℝ}
    (replay : CertificateContracts.SparseL2ThresholdDominantReplayAt
      rows squaredNormFloor highBudget)
    (hbudget : 0 < highBudget)
    {q d : ℕ} (w : Fin d → ℤ) (inputThreshold : ℕ) (i : Fin d)
    (hq : Odd q) (hinputThreshold : 0 < inputThreshold) (hi : w i ≠ 0)
    (hdominant : 49 * inputThreshold < 50 * (w i).natAbs)
    (hmax : ∀ j, (w j).natAbs ^ 2 ≤ (w i).natAbs ^ 2)
    (hresidual : (1 / 2 : ℝ) ≤ dominantResidualRatio w i)
    (hmodulus : 3 ≤ (q : ℝ) / (dominantAmplitude w i : ℝ)) :
    eventProbability (sparseRademacherMatrix rows d)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
              inputThreshold q w J ∧
            squaredNormFloor ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ)) <
      ENNReal.ofReal highBudget :=
  sparseThresholdDominantHighActivity_retained_of_geometry_at
    replay.retainedGeometry replay.retainedFinalRatio hbudget w inputThreshold i
      hq hinputThreshold hi hdominant hmax hresidual hmodulus

end CertifiedJL
