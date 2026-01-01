/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Spec
import CertifiedJL.Certificates.Families.L2Lower.Rows512Floor73Bits193.Soundness.ThresholdBits512Floor73Bits193
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Diffuse.Floor73
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.Provider
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Near.Provider128

/-! # Exact assembly for 512 rows, squared-norm floor 73, and 193 bits -/

namespace CertifiedJL.CertificateAssembly

private noncomputable def highBudget : ℝ :=
  (((99999 / (100000 * 2 ^ 193) : ℚ) : ℝ))

private theorem highBudget_eq :
    highBudget = (99999 / 100000 : ℝ) * (2 : ℝ)⁻¹ ^ 193 := by
  unfold highBudget
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_pow]

private theorem highBudget_pos : 0 < highBudget := by
  unfold highBudget
  positivity

private theorem dominantReplay
    (direct : CertificateContracts.SparseL2ThresholdDominantDirectCover512Floor73Bits193)
    (capped : CertificateContracts.SparseL2ThresholdDominantCappedFourierCover512Floor73Bits193)
    (singleton : CertificateContracts.SparseL2ThresholdDominantSingletonFourierCover512Floor73Bits193)
    (retainedCoarse : CertificateContracts.SparseL2ThresholdDominantRetainedCoarse128)
    (retainedChord : CertificateContracts.SparseL2ThresholdDominantRetainedChord128)
    (retainedRatio : CertificateContracts.SparseL2ThresholdDominantFinalRatio512Floor73Bits193) :
    CertificateContracts.SparseL2ThresholdDominantReplayAt
      512 73 highBudget where
  directCover := by
    simpa [CertificateContracts.SparseL2ThresholdDominantDirectCover512Floor73Bits193,
      CertificateContracts.SparseL2ThresholdDominantDirectCoverAt,
      highBudget] using direct
  cappedFourierCover := by
    intro B r
    simpa [CertificateContracts.SparseL2ThresholdDominantCappedFourierCover512Floor73Bits193,
      CertificateContracts.SparseL2ThresholdDominantCappedFourierCoverAt,
      highBudget] using @capped B r
  singletonFourierCover := by
    intro B r
    simpa [CertificateContracts.SparseL2ThresholdDominantSingletonFourierCover512Floor73Bits193,
      CertificateContracts.SparseL2ThresholdDominantSingletonFourierCoverAt,
      highBudget] using @singleton B r
  retainedGeometry := {
    coarseCentral := retainedCoarse.central
    conditionedTail := retainedCoarse.conditionedTail
    chordCentral := retainedChord
  }
  retainedFinalRatio := by
    simpa [CertificateContracts.SparseL2ThresholdDominantFinalRatio512Floor73Bits193,
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

/-- The fully kernel-checked 512/73/193 threshold-relative lower-tail
assembly. -/
theorem sparseL2ThresholdLower512Floor73Bits193 :
    CertificateContracts.SparseL2ThresholdDominantDirectCover512Floor73Bits193 →
    CertificateContracts.SparseL2ThresholdDominantCappedFourierCover512Floor73Bits193 →
    CertificateContracts.SparseL2ThresholdDominantSingletonFourierCover512Floor73Bits193 →
    CertificateContracts.SparseL2ThresholdDominantRetainedCoarse128 →
    CertificateContracts.SparseL2ThresholdDominantRetainedChord128 →
    CertificateContracts.SparseL2ThresholdDominantFinalRatio512Floor73Bits193 →
    CertificateContracts.SparseL2ThresholdNearCoarseCover128 →
    CertificateContracts.SparseL2ThresholdNearEndpoints128 →
    CertificateContracts.SparseL2ThresholdNearCurvature128 →
    CertificateContracts.SparseL2ThresholdNearFinalRatio512Floor73Bits193 →
    CertificateContracts.SparseL2ThresholdDiffuseFloor73Endpoints →
    CertificateContracts.SparseL2ThresholdDiffuseFinalRatio512Floor73Bits193 →
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        squaredNormFloor := NonnegativeRatio.ofNat 73
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 193) := by
  intro direct capped singleton retainedCoarse retainedChord retainedRatio
    nearCoarse nearEndpoints nearCurvature nearRatio diffuseEndpoints diffuseRatio
  let config := Threshold512Floor73Bits193.config
  have hnear : SparseThresholdNearDominantRowBoundAt
      (NonnegativeRatio.ofNat 3) := by
    simpa [SparseThresholdNearDominantRowBoundAt,
      SparseThresholdNearDominantRow128BoundAt] using
      sparseThresholdNearDominantRow128Bound_marginThree_of_replay
        (nearReplay nearCoarse nearEndpoints nearCurvature)
  have hdiffuse : SparseThresholdDiffuseRowBoundWithAt
      (5 / 2) (539 / 1000) (NonnegativeRatio.ofNat 3) :=
    ThresholdDiffuseFloor73.rowBound_marginThree_of_replay diffuseEndpoints
  have hgeneric : L2ThresholdLowerTailAt
      (config.parameters (NonnegativeRatio.ofNat 3)) config.target := by
    apply sparseThresholdLowerTail_marginThree_of_analyticBoundsWithDiffuse
      config (5 / 2) (539 / 1000) (by norm_num)
    · exact Threshold512Floor73Bits193.budgets_add.le
    · intro d i
      exact Threshold512Floor73Bits193.lowActivity i
    · exact sparseThresholdDominantHighActivity_of_replay_at config
        (dominantReplay direct capped singleton retainedCoarse retainedChord retainedRatio)
        highBudget_pos (by
          simpa [config, Threshold512Floor73Bits193.config, highBudget_eq] using
            Threshold512Floor73Bits193.highBudget_real)
    · exact hnear
    · exact hdiffuse
    · simpa [CertificateContracts.SparseL2ThresholdNearFinalRatio512Floor73Bits193,
        config, Threshold512Floor73Bits193.config, inv_pow, mul_comm] using nearRatio
    · simpa [CertificateContracts.SparseL2ThresholdDiffuseFinalRatio512Floor73Bits193,
        config, Threshold512Floor73Bits193.config, inv_pow, mul_comm] using diffuseRatio
  simpa [config, Threshold512Floor73Bits193.config,
    ThresholdTailConfig.parameters, ThresholdTailConfig.target] using hgeneric

end CertifiedJL.CertificateAssembly
