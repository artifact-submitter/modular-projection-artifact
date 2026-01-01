/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Spec
import CertifiedJL.Certificates.Families.L2Lower.Rows192Bits128.Soundness.ThresholdBits192Bits128
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Diffuse.Provider128
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.Provider
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Near.Provider128

/-! # Exact assembly for 192 rows, squared-norm floor 12, and 128 bits -/

namespace CertifiedJL.CertificateAssembly

private noncomputable def highBudget : ℝ :=
  (((19 / (20 * 2 ^ 128) : ℚ) : ℝ))

private theorem highBudget_eq :
    highBudget = (19 / 20 : ℝ) * (2 : ℝ)⁻¹ ^ 128 := by
  unfold highBudget
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_pow]

private theorem highBudget_pos : 0 < highBudget := by
  unfold highBudget
  positivity

private theorem dominantReplay
    (direct : CertificateContracts.SparseL2ThresholdDominantDirectCover192Bits128)
    (capped : CertificateContracts.SparseL2ThresholdDominantCappedFourierCover192Bits128)
    (singleton : CertificateContracts.SparseL2ThresholdDominantSingletonFourierCover192Bits128)
    (retainedCoarse : CertificateContracts.SparseL2ThresholdDominantRetainedCoarse128)
    (retainedChord : CertificateContracts.SparseL2ThresholdDominantRetainedChord128)
    (retainedRatio : CertificateContracts.SparseL2ThresholdDominantFinalRatio192Bits128) :
    CertificateContracts.SparseL2ThresholdDominantTiltedReplayAt
      192 12 (7 / 2) (13 / 4) highBudget where
  singletonTiltPositive := by norm_num
  cappedTiltPositive := by norm_num
  directCover := by
    simpa [CertificateContracts.SparseL2ThresholdDominantDirectCover192Bits128,
      highBudget] using direct
  cappedFourierCover := by
    intro B r
    simpa [CertificateContracts.SparseL2ThresholdDominantCappedFourierCover192Bits128,
      highBudget] using @capped B r
  singletonFourierCover := by
    intro B r
    simpa [CertificateContracts.SparseL2ThresholdDominantSingletonFourierCover192Bits128,
      highBudget] using @singleton B r
  retainedGeometry := {
    coarseCentral := retainedCoarse.central
    conditionedTail := retainedCoarse.conditionedTail
    chordCentral := retainedChord
  }
  retainedFinalRatio := by
    simpa [CertificateContracts.SparseL2ThresholdDominantFinalRatio192Bits128,
      highBudget] using retainedRatio

private theorem nearReplay
    (nearCoarse : CertificateContracts.SparseL2ThresholdNearCoarseCover128)
    (nearEndpoints : CertificateContracts.SparseL2ThresholdNearEndpoints128)
    (nearCurvature : CertificateContracts.SparseL2ThresholdNearCurvature128) :
    CertificateContracts.SparseL2ThresholdNearReplay128 where
  coarseEnvelope := nearCoarse
  endpointFourFifths := nearEndpoints.fourFifths
  endpointSeventeenTwentieths := nearEndpoints.seventeenTwentieths
  endpointNineTenths := nearEndpoints.nineTenths
  endpointNineteenTwentieths := nearEndpoints.nineteenTwentieths
  endpointOne := nearEndpoints.one
  curvature := nearCurvature

/-- The fully kernel-checked 192/12/128 threshold-relative lower-tail
assembly. -/
theorem sparseL2ThresholdLower192Bits128 :
    CertificateContracts.SparseL2ThresholdDominantDirectCover192Bits128 →
    CertificateContracts.SparseL2ThresholdDominantCappedFourierCover192Bits128 →
    CertificateContracts.SparseL2ThresholdDominantSingletonFourierCover192Bits128 →
    CertificateContracts.SparseL2ThresholdDominantRetainedCoarse128 →
    CertificateContracts.SparseL2ThresholdDominantRetainedChord128 →
    CertificateContracts.SparseL2ThresholdDominantFinalRatio192Bits128 →
    CertificateContracts.SparseL2ThresholdNearCoarseCover128 →
    CertificateContracts.SparseL2ThresholdNearEndpoints128 →
    CertificateContracts.SparseL2ThresholdNearCurvature128 →
    CertificateContracts.SparseL2ThresholdNearFinalRatio192Bits128 →
    CertificateContracts.SparseL2ThresholdDiffuseLowScalar128 →
    CertificateContracts.SparseL2ThresholdDiffuseLowModularTail128 →
    CertificateContracts.SparseL2ThresholdDiffuseHighEndpoints128 →
    CertificateContracts.SparseL2ThresholdDiffuseFinalRatio192Bits128 →
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 192
        squaredNormFloor := NonnegativeRatio.ofNat 12
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 128) := by
  intro direct capped singleton retainedCoarse retainedChord retainedRatio
    nearCoarse nearEndpoints nearCurvature nearRatio
    diffuseScalar diffuseTail diffuseHigh diffuseRatio
  let config := Threshold192Bits128.config
  have hnear : SparseThresholdNearDominantRowBoundAt
      (NonnegativeRatio.ofNat 3) := by
    simpa [SparseThresholdNearDominantRowBoundAt,
      SparseThresholdNearDominantRow128BoundAt] using
      sparseThresholdNearDominantRow128Bound_marginThree_of_replay
        (nearReplay nearCoarse nearEndpoints nearCurvature)
  have hdiffuse : SparseThresholdDiffuseRowBoundAt
      (NonnegativeRatio.ofNat 3) := by
    simpa [SparseThresholdDiffuseRowBoundAt,
      SparseThresholdDiffuseRowBoundWithAt,
      SparseThresholdDiffuseRow128BoundAt] using
      sparseThresholdDiffuseRow128Bound_marginThree_of_replay
        diffuseScalar diffuseTail diffuseHigh
  have hgeneric : L2ThresholdLowerTailAt
      (config.parameters (NonnegativeRatio.ofNat 3)) config.target := by
    apply sparseThresholdLowerTail_marginThree_of_analyticBounds config
    · exact Threshold192Bits128.budgets_add.le
    · intro d i
      exact Threshold192Bits128.lowActivity i
    · exact sparseThresholdDominantHighActivity_of_tiltedReplay_at config
        (dominantReplay direct capped singleton retainedCoarse retainedChord retainedRatio)
        highBudget_pos (by
          simpa [config, Threshold192Bits128.config, highBudget_eq] using
            Threshold192Bits128.highBudget_real)
    · exact hnear
    · exact hdiffuse
    · simpa [CertificateContracts.SparseL2ThresholdNearFinalRatio192Bits128,
        config, Threshold192Bits128.config, inv_pow, mul_comm] using nearRatio
    · simpa [CertificateContracts.SparseL2ThresholdDiffuseFinalRatio192Bits128,
        config, Threshold192Bits128.config, inv_pow, mul_comm] using diffuseRatio
  simpa [config, Threshold192Bits128.config, ThresholdTailConfig.parameters,
    ThresholdTailConfig.target] using hgeneric

end CertifiedJL.CertificateAssembly
