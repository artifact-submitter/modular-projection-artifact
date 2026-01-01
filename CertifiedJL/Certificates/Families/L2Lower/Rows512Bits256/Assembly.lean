/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Spec
import CertifiedJL.Certificates.Families.L2Lower.Rows512Bits256.Soundness.ThresholdBits512Bits256
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Diffuse.Provider128
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.Provider
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Near.Provider128

/-! # Exact assembly for 512 rows, squared-norm floor 57, and 256 bits -/

namespace CertifiedJL.CertificateAssembly

private noncomputable def highBudget : ℝ :=
  (((24 / (25 * 2 ^ 256) : ℚ) : ℝ))

private theorem highBudget_eq :
    highBudget = (24 / 25 : ℝ) * (2 : ℝ)⁻¹ ^ 256 := by
  unfold highBudget
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_pow]

private theorem highBudget_pos : 0 < highBudget := by
  unfold highBudget
  positivity

private theorem dominantReplay
    (direct : CertificateContracts.SparseL2ThresholdDominantDirectCover512Bits256)
    (capped : CertificateContracts.SparseL2ThresholdDominantCappedFourierCover512Bits256)
    (singleton : CertificateContracts.SparseL2ThresholdDominantSingletonFourierCover512Bits256)
    (retainedCoarse : CertificateContracts.SparseL2ThresholdDominantRetainedCoarse128)
    (retainedChord : CertificateContracts.SparseL2ThresholdDominantRetainedChord128)
    (retainedRatio : CertificateContracts.SparseL2ThresholdDominantFinalRatio512Bits256) :
    CertificateContracts.SparseL2ThresholdDominantReplayAt
      512 57 highBudget where
  directCover := by
    simpa [CertificateContracts.SparseL2ThresholdDominantDirectCover512Bits256,
      CertificateContracts.SparseL2ThresholdDominantDirectCoverAt,
      highBudget] using direct
  cappedFourierCover := by
    intro B r
    simpa [CertificateContracts.SparseL2ThresholdDominantCappedFourierCover512Bits256,
      highBudget] using @capped B r
  singletonFourierCover := by
    intro B r
    simpa [CertificateContracts.SparseL2ThresholdDominantSingletonFourierCover512Bits256,
      highBudget] using @singleton B r
  retainedGeometry := {
    coarseCentral := retainedCoarse.central
    conditionedTail := retainedCoarse.conditionedTail
    chordCentral := retainedChord
  }
  retainedFinalRatio := by
    simpa [CertificateContracts.SparseL2ThresholdDominantFinalRatio512Bits256,
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

/-- The fully kernel-checked 512/57/256 threshold-relative lower-tail
assembly. -/
theorem sparseL2ThresholdLower512Bits256 :
    CertificateContracts.SparseL2ThresholdDominantDirectCover512Bits256 →
    CertificateContracts.SparseL2ThresholdDominantCappedFourierCover512Bits256 →
    CertificateContracts.SparseL2ThresholdDominantSingletonFourierCover512Bits256 →
    CertificateContracts.SparseL2ThresholdDominantRetainedCoarse128 →
    CertificateContracts.SparseL2ThresholdDominantRetainedChord128 →
    CertificateContracts.SparseL2ThresholdDominantFinalRatio512Bits256 →
    CertificateContracts.SparseL2ThresholdNearCoarseCover128 →
    CertificateContracts.SparseL2ThresholdNearEndpoints128 →
    CertificateContracts.SparseL2ThresholdNearCurvature128 →
    CertificateContracts.SparseL2ThresholdNearFinalRatio512Bits256 →
    CertificateContracts.SparseL2ThresholdDiffuseLowScalar128 →
    CertificateContracts.SparseL2ThresholdDiffuseLowModularTail128 →
    CertificateContracts.SparseL2ThresholdDiffuseHighEndpoints128 →
    CertificateContracts.SparseL2ThresholdDiffuseFinalRatio512Bits256 →
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        squaredNormFloor := NonnegativeRatio.ofNat 57
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 256) := by
  intro direct capped singleton retainedCoarse retainedChord retainedRatio
    nearCoarse nearEndpoints nearCurvature nearRatio
    diffuseScalar diffuseTail diffuseHigh diffuseRatio
  let config := Threshold512Bits256.config
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
    · exact Threshold512Bits256.budgets_add.le
    · intro d i
      exact Threshold512Bits256.lowActivity i
    · exact sparseThresholdDominantHighActivity_of_replay_at config
        (dominantReplay direct capped singleton retainedCoarse retainedChord retainedRatio)
        highBudget_pos (by
          simpa [config, Threshold512Bits256.config, highBudget_eq] using
            Threshold512Bits256.highBudget_real)
    · exact hnear
    · exact hdiffuse
    · simpa [CertificateContracts.SparseL2ThresholdNearFinalRatio512Bits256,
        config, Threshold512Bits256.config, inv_pow, mul_comm] using
        nearRatio
    · simpa [CertificateContracts.SparseL2ThresholdDiffuseFinalRatio512Bits256,
        config, Threshold512Bits256.config, inv_pow, mul_comm] using
        diffuseRatio
  simpa [config, Threshold512Bits256.config, ThresholdTailConfig.parameters,
    ThresholdTailConfig.target] using hgeneric

end CertifiedJL.CertificateAssembly
