/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Activity
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Spec.ThresholdConfig
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.Fourier
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Lower

/-!
# Target-neutral threshold lower-tail assembly

This module combines the low-activity, dominant, near-dominant, and diffuse
branches for an arbitrary row count, squared-norm floor, bit target, and budget
split. It contains no target-specific certificate data.
-/

open scoped ENNReal
open MeasureTheory

namespace CertifiedJL

/-- Target-dependent high-activity contract for the dominant-coordinate
branch. -/
def SparseThresholdDominantHighActivityBoundAt
    (config : ThresholdTailConfig)
    (modulusMargin : NonnegativeRatio) : Prop :=
  ∀ (q d : ℕ) (w : Fin d → ℤ) (inputThreshold : ℕ) (i : Fin d),
    Odd q →
    CenteredInput q w →
    0 < inputThreshold →
    InputThresholdAtMostNorm inputThreshold w →
    InputThresholdWithinModulus modulusMargin q inputThreshold →
    49 * inputThreshold < 50 * (w i).natAbs →
    (∀ j, (w j).natAbs ^ 2 ≤ (w i).natAbs ^ 2) →
    eventProbability (sparseRademacherMatrix config.rows d)
        (fun J =>
            L2ThresholdLowerFailure
                (NonnegativeRatio.ofNat config.squaredNormFloor)
              inputThreshold q w J ∧
            config.squaredNormFloor ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ)) <
      config.highBudget

/-- Reusable frozen near-dominant one-row contract. -/
def SparseThresholdNearDominantRowBoundAt
    (modulusMargin : NonnegativeRatio) : Prop :=
  ∀ (q d : ℕ) (w : Fin d → ℤ) (inputThreshold : ℕ),
    Odd q →
    CenteredInput q w →
    0 < inputThreshold →
    InputThresholdAtMostNorm inputThreshold w →
    InputThresholdWithinModulus modulusMargin q inputThreshold →
    (∀ i, 50 * (w i).natAbs ≤ 49 * inputThreshold) →
    (∃ i, 3 * inputThreshold < 4 * (w i).natAbs) →
    ∫ row,
        Real.exp (-((23 / 10 : ℝ) / (inputThreshold : ℝ) ^ 2) *
          sparseLowerRowKernel q w row)
          ∂(sparseRademacherRow d).toMeasure ≤
      681 / 1250

/-- Target-selectable diffuse one-row contract. -/
def SparseThresholdDiffuseRowBoundWithAt
    (tilt rowCap : ℝ) (modulusMargin : NonnegativeRatio) : Prop :=
  ∀ (q d : ℕ) (w : Fin d → ℤ) (inputThreshold : ℕ),
    Odd q →
    CenteredInput q w →
    0 < inputThreshold →
    InputThresholdAtMostNorm inputThreshold w →
    InputThresholdWithinModulus modulusMargin q inputThreshold →
    (∀ i, 4 * (w i).natAbs ≤ 3 * inputThreshold) →
    ∫ row,
        Real.exp (-(tilt / (inputThreshold : ℝ) ^ 2) *
          sparseLowerRowKernel q w row)
          ∂(sparseRademacherRow d).toMeasure ≤
      rowCap

/-- Legacy frozen diffuse one-row contract. -/
def SparseThresholdDiffuseRowBoundAt
    (modulusMargin : NonnegativeRatio) : Prop :=
  SparseThresholdDiffuseRowBoundWithAt (33 / 10) (97 / 200) modulusMargin

set_option maxHeartbeats 800000 in
-- The nested three-event ENNReal union assembly is elaboration-intensive.
/-- Generic margin-three assembly from a low-activity count bound, a
high-activity dominant bound, the frozen near envelope, and a selected diffuse
envelope. -/
theorem sparseThresholdLowerTail_marginThree_of_analyticBoundsWithDiffuse
    (config : ThresholdTailConfig)
    (diffuseTilt diffuseRowCap : ℝ)
    (hdiffuseTilt : 0 < diffuseTilt)
    (hbudgets : config.BudgetsValid)
    (hactivity : ∀ {d : ℕ} (i : Fin d),
      eventProbability (sparseRademacherMatrix config.rows d)
          (fun J =>
            (dominantActivityCount (matrixDominantActivity i J) : ℕ) <
              config.squaredNormFloor) < config.lowBudget)
    (hdominant : SparseThresholdDominantHighActivityBoundAt config
      (NonnegativeRatio.ofNat 3))
    (hnear : SparseThresholdNearDominantRowBoundAt
      (NonnegativeRatio.ofNat 3))
    (hdiffuse : SparseThresholdDiffuseRowBoundWithAt diffuseTilt diffuseRowCap
      (NonnegativeRatio.ofNat 3))
    (hnearRatio : Real.exp (config.squaredNormFloor * (23 / 10 : ℝ)) *
      (681 / 1250 : ℝ) ^ config.rows < (2 : ℝ)⁻¹ ^ config.bits)
    (hdiffuseRatio : Real.exp (config.squaredNormFloor * diffuseTilt) *
      diffuseRowCap ^ config.rows < (2 : ℝ)⁻¹ ^ config.bits) :
    L2ThresholdLowerTailAt
      (config.parameters (NonnegativeRatio.ofNat 3)) config.target := by
  intro q d w inputThreshold hq hcentered hpositive hnorm hmodulus
  simp only [ThresholdTailConfig.parameters,
    ProjectionDistribution.matrixPMF_balancedTernary]
  by_cases hlarge : ∃ i, 49 * inputThreshold < 50 * (w i).natAbs
  · obtain ⟨i, -, hmax, hi⟩ :=
      exists_maximalSqCoordinate_above_threshold w inputThreshold hlarge
    let count : (Fin config.rows → Fin d → ℤ) → ℕ :=
      fun J => (dominantActivityCount (matrixDominantActivity i J) : ℕ)
    let failure : (Fin config.rows → Fin d → ℤ) → Prop :=
      L2ThresholdLowerFailure
        (NonnegativeRatio.ofNat config.squaredNormFloor) inputThreshold q w
    calc
      eventProbability (sparseRademacherMatrix config.rows d) failure ≤
          eventProbability (sparseRademacherMatrix config.rows d)
            (fun J => count J < config.squaredNormFloor ∨
              (failure J ∧ config.squaredNormFloor ≤ count J)) := by
        apply eventProbability_mono
        intro J hfailure
        by_cases hlow : count J < config.squaredNormFloor
        · exact Or.inl hlow
        · exact Or.inr ⟨hfailure, le_of_not_gt hlow⟩
      _ ≤ eventProbability (sparseRademacherMatrix config.rows d)
              (fun J => count J < config.squaredNormFloor) +
            eventProbability (sparseRademacherMatrix config.rows d)
              (fun J => failure J ∧ config.squaredNormFloor ≤ count J) :=
        eventProbability_or_le (sparseRademacherMatrix config.rows d)
          (fun J : Fin config.rows → Fin d → ℤ =>
            count J < config.squaredNormFloor)
          (fun J : Fin config.rows → Fin d → ℤ =>
            failure J ∧ config.squaredNormFloor ≤ count J)
      _ < config.lowBudget + config.highBudget := by
        apply ENNReal.add_lt_add
        · simpa only [count] using hactivity i
        · simpa only [count, failure] using
            hdominant q d w inputThreshold i hq hcentered hpositive
              hnorm hmodulus hi hmax
      _ ≤ config.target := hbudgets
  · have hnotLarge : ∀ i, 50 * (w i).natAbs ≤ 49 * inputThreshold :=
      fun i => le_of_not_gt (not_exists.mp hlarge i)
    by_cases hnearCoordinate : ∃ i, 3 * inputThreshold < 4 * (w i).natAbs
    · exact ternaryThresholdLowerTail_lt_failureTarget_of_rowKernel_at
        config.rows config.squaredNormFloor config.bits q d w inputThreshold
          (23 / 10) (681 / 1250) hpositive (by norm_num)
          (hnear q d w inputThreshold hq hcentered hpositive hnorm hmodulus
            hnotLarge hnearCoordinate)
          hnearRatio
    · exact ternaryThresholdLowerTail_lt_failureTarget_of_rowKernel_at
        config.rows config.squaredNormFloor config.bits q d w inputThreshold
          diffuseTilt diffuseRowCap hpositive hdiffuseTilt
          (hdiffuse q d w inputThreshold hq hcentered hpositive hnorm hmodulus
            (fun i => le_of_not_gt (not_exists.mp hnearCoordinate i)))
          hdiffuseRatio

set_option maxHeartbeats 800000 in
-- The compatibility wrapper elaborates the same intensive generic assembly.
/-- Backwards-compatible wrapper for the frozen `33/10`, `97/200` diffuse
envelope. -/
theorem sparseThresholdLowerTail_marginThree_of_analyticBounds
    (config : ThresholdTailConfig)
    (hbudgets : config.BudgetsValid)
    (hactivity : ∀ {d : ℕ} (i : Fin d),
      eventProbability (sparseRademacherMatrix config.rows d)
          (fun J =>
            (dominantActivityCount (matrixDominantActivity i J) : ℕ) <
              config.squaredNormFloor) < config.lowBudget)
    (hdominant : SparseThresholdDominantHighActivityBoundAt config
      (NonnegativeRatio.ofNat 3))
    (hnear : SparseThresholdNearDominantRowBoundAt
      (NonnegativeRatio.ofNat 3))
    (hdiffuse : SparseThresholdDiffuseRowBoundAt
      (NonnegativeRatio.ofNat 3))
    (hnearRatio : Real.exp (config.squaredNormFloor * (23 / 10 : ℝ)) *
      (681 / 1250 : ℝ) ^ config.rows < (2 : ℝ)⁻¹ ^ config.bits)
    (hdiffuseRatio : Real.exp (config.squaredNormFloor * (33 / 10 : ℝ)) *
      (97 / 200 : ℝ) ^ config.rows < (2 : ℝ)⁻¹ ^ config.bits) :
    L2ThresholdLowerTailAt
      (config.parameters (NonnegativeRatio.ofNat 3)) config.target := by
  exact sparseThresholdLowerTail_marginThree_of_analyticBoundsWithDiffuse
    config (33 / 10) (97 / 200) (by norm_num) hbudgets hactivity hdominant hnear
      hdiffuse hnearRatio hdiffuseRatio

end CertifiedJL
