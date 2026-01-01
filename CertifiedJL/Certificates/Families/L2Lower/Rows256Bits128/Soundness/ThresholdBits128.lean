/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Activity
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Assembly
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Spec.ThresholdBudget128
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.Fourier
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Lower
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Soundness.ThresholdRatios

/-!
# Direct margin-three balanced-ternary threshold assembly at 128 bits

This is the protocol-threshold statement: the public threshold is bounded by
the actual input norm, but the norm itself need not be bounded by the modulus.
The dominant activity prefix takes `13/200` of the 128-bit target, leaving
`187/200` for high activity.
-/

open scoped ENNReal
open MeasureTheory

namespace CertifiedJL

private theorem binomial256_prefix29_lt_threshold128LowActivityBudget_scaled :
    200 * (∑ k ∈ Finset.range 29, (256 : ℕ).choose k) * 2 ^ 128 <
      13 * 2 ^ 256 := by
  set_option maxRecDepth 10000 in
    decide +kernel

/-- Exact counting places `K < 29` below `13/200` of the 128-bit budget. -/
theorem sparse_dominantActivityCount_lt_29_probability_lt_threshold128Budget
    {d : ℕ} (i : Fin d) :
    eventProbability (sparseRademacherMatrix 256 d)
        (fun J =>
          (dominantActivityCount (matrixDominantActivity i J) : ℕ) < 29) <
      sparseThreshold128LowActivityBudget := by
  rw [sparse_dominantActivityCount_lt_probability_eq i 29]
  unfold sparseThreshold128LowActivityBudget failureTarget
  set_option maxRecDepth 10000 in
    rw [← ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)]
  repeat' rw [ENNReal.toReal_mul]
  repeat' rw [ENNReal.toReal_div]
  repeat' rw [ENNReal.toReal_pow]
  repeat' rw [ENNReal.toReal_inv]
  repeat' rw [ENNReal.toReal_natCast]
  repeat' rw [ENNReal.toReal_ofNat]
  field_simp
  set_option maxRecDepth 10000 in
    exact_mod_cast
      binomial256_prefix29_lt_threshold128LowActivityBudget_scaled

def SparseThresholdDominantHighActivity128BoundAt
    (modulusMargin : NonnegativeRatio) : Prop :=
  ∀ (q d : ℕ) (w : Fin d → ℤ) (inputThreshold : ℕ) (i : Fin d),
    Odd q →
    CenteredInput q w →
    0 < inputThreshold →
    InputThresholdAtMostNorm inputThreshold w →
    InputThresholdWithinModulus modulusMargin q inputThreshold →
    49 * inputThreshold < 50 * (w i).natAbs →
    (∀ j, (w j).natAbs ^ 2 ≤ (w i).natAbs ^ 2) →
    eventProbability (sparseRademacherMatrix 256 d)
        (fun J =>
            L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
              inputThreshold q w J ∧
            29 ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ)) <
      sparseThreshold128HighActivityBudget

def SparseThresholdNearDominantRow128BoundAt
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

def SparseThresholdDiffuseRow128BoundAt
    (modulusMargin : NonnegativeRatio) : Prop :=
  ∀ (q d : ℕ) (w : Fin d → ℤ) (inputThreshold : ℕ),
    Odd q →
    CenteredInput q w →
    0 < inputThreshold →
    InputThresholdAtMostNorm inputThreshold w →
    InputThresholdWithinModulus modulusMargin q inputThreshold →
    (∀ i, 4 * (w i).natAbs ≤ 3 * inputThreshold) →
    ∫ row,
        Real.exp (-((33 / 10 : ℝ) / (inputThreshold : ℝ) ^ 2) *
          sparseLowerRowKernel q w row)
          ∂(sparseRademacherRow d).toMeasure ≤
      97 / 200

set_option maxHeartbeats 800000 in
-- The nested three-event ENNReal union assembly is elaboration-intensive.
/-- Direct 128-bit margin-three assembly. No actual-norm cap is introduced. -/
theorem sparseThresholdLowerTail_marginThree_bits128_of_analyticBounds
    (hdominant :
      SparseThresholdDominantHighActivity128BoundAt
        (NonnegativeRatio.ofNat 3))
    (hnear :
      SparseThresholdNearDominantRow128BoundAt (NonnegativeRatio.ofNat 3))
    (hdiffuse :
      SparseThresholdDiffuseRow128BoundAt (NonnegativeRatio.ofNat 3)) :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 256
        squaredNormFloor := NonnegativeRatio.ofNat 29
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 128) := by
  let config : ThresholdTailConfig :=
    { rows := 256
      squaredNormFloor := 29
      bits := 128
      lowBudget := sparseThreshold128LowActivityBudget
      highBudget := sparseThreshold128HighActivityBudget }
  have hgeneric : L2ThresholdLowerTailAt
      (config.parameters (NonnegativeRatio.ofNat 3)) config.target := by
    apply sparseThresholdLowerTail_marginThree_of_analyticBounds config
    · exact sparseThreshold128Budgets_add.le
    · intro d i
      exact sparse_dominantActivityCount_lt_29_probability_lt_threshold128Budget i
    · intro q d w inputThreshold i hq hcentered hpositive hnorm hmodulus
        hi hmax
      exact hdominant q d w inputThreshold i hq hcentered hpositive hnorm
        hmodulus hi hmax
    · simpa [SparseThresholdNearDominantRowBoundAt,
        SparseThresholdNearDominantRow128BoundAt] using hnear
    · simpa [SparseThresholdDiffuseRowBoundAt,
        SparseThresholdDiffuseRowBoundWithAt,
        SparseThresholdDiffuseRow128BoundAt] using hdiffuse
    · simpa [config, mul_comm] using ThresholdNearDominantRatio128.finalRatio
    · simpa [config, mul_comm] using ThresholdDiffuseRatio.finalRatio128
  simpa [config, ThresholdTailConfig.parameters,
    ThresholdTailConfig.target] using hgeneric

end CertifiedJL
