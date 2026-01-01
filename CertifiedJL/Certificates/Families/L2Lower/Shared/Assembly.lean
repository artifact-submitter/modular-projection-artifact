/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Spec
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Diffuse.Provider128
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.Provider128
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Near.Provider128

/-! # Replay-free assembly for the threshold-relative lower tail -/

namespace CertifiedJL.CertificateAssembly

/-- Assemble the public-threshold lower-tail theorem from narrow replay
contracts. All analytic reductions and regime routing occur below this call. -/
theorem sparseL2ThresholdLower128
    (direct : CertificateContracts.SparseL2ThresholdDominantDirectCover128)
    (capped : CertificateContracts.SparseL2ThresholdDominantCappedFourierCover128)
    (singleton : CertificateContracts.SparseL2ThresholdDominantSingletonFourierCover128)
    (retainedCoarse : CertificateContracts.SparseL2ThresholdDominantRetainedCoarse128)
    (retainedChord : CertificateContracts.SparseL2ThresholdDominantRetainedChord128)
    (dominantRatio : CertificateContracts.SparseL2ThresholdDominantFinalRatio128)
    (nearCoarse : CertificateContracts.SparseL2ThresholdNearCoarseCover128)
    (nearEndpoints : CertificateContracts.SparseL2ThresholdNearEndpoints128)
    (nearCurvature : CertificateContracts.SparseL2ThresholdNearCurvature128)
    (diffuseScalar : CertificateContracts.SparseL2ThresholdDiffuseLowScalar128)
    (diffuseTail : CertificateContracts.SparseL2ThresholdDiffuseLowModularTail128)
    (diffuseHigh : CertificateContracts.SparseL2ThresholdDiffuseHighEndpoints128) :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 256
        squaredNormFloor := NonnegativeRatio.ofNat 29
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 128) :=
  let dominant : CertificateContracts.SparseL2ThresholdDominantReplay128 := {
    directCover := direct
    cappedFourierCover := capped
    singletonFourierCover := singleton
    retainedCoarseCentral := retainedCoarse.central
    retainedConditionedTail := retainedCoarse.conditionedTail
    retainedChordCentral := retainedChord
    retainedFinalRatio := dominantRatio
  }
  let near : CertificateContracts.SparseL2ThresholdNearReplay128 := {
    coarseEnvelope := nearCoarse
    endpointFourFifths := nearEndpoints.fourFifths
    endpointSeventeenTwentieths := nearEndpoints.seventeenTwentieths
    endpointNineTenths := nearEndpoints.nineTenths
    endpointNineteenTwentieths := nearEndpoints.nineteenTwentieths
    endpointOne := nearEndpoints.one
    curvature := nearCurvature
  }
  sparseThresholdLowerTail_marginThree_bits128_of_analyticBounds
    (sparseThresholdDominantHighActivity128_of_replay dominant)
    (sparseThresholdNearDominantRow128Bound_marginThree_of_replay near)
    (sparseThresholdDiffuseRow128Bound_marginThree_of_replay
      diffuseScalar diffuseTail diffuseHigh)

end CertifiedJL.CertificateAssembly
