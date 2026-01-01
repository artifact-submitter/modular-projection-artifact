/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.L2General
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Near.Provider128
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Diffuse.Provider128
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Diffuse.Floor73

/-! # Shared certificate assembly for general affine Euclidean lower tails

The verified and fast surfaces supply the same seven existing semantic
certificate contracts. The singleton analysis needs no certificate premise.
-/

namespace CertifiedJL.CertificateAssembly

/-- The three wrapped profile bounds used by the general affine assembly. -/
structure AffineL2WrappedProfiles : Prop where
  near : SparseThresholdNearWrappedRowBound
  diffuse33 : SparseThresholdDiffuseWrappedRowBoundAt (33 / 10) (97 / 200)
  diffuse25 : SparseThresholdDiffuseWrappedRowBoundAt (5 / 2) (539 / 1000)

/-- Existing near-profile certificates supply the wrapped retained-row bound. -/
theorem affineL2General_nearWrapped
    (coarse : CertificateContracts.SparseL2ThresholdNearCoarseCover128)
    (endpoints : CertificateContracts.SparseL2ThresholdNearEndpoints128)
    (curvature : CertificateContracts.SparseL2ThresholdNearCurvature128) :
    SparseThresholdNearWrappedRowBound := by
  let near : CertificateContracts.SparseL2ThresholdNearReplay128 := {
    coarseEnvelope := coarse
    endpointFourFifths := endpoints.fourFifths
    endpointSeventeenTwentieths := endpoints.seventeenTwentieths
    endpointNineTenths := endpoints.nineTenths
    endpointNineteenTwentieths := endpoints.nineteenTwentieths
    endpointOne := endpoints.one
    curvature := curvature
  }
  exact sparseThresholdNearDominantWrappedRow128Bound_marginThree_of_replay near

/-- Assemble the existing numerical inputs without replaying any certificate. -/
theorem affineL2General_profiles
    (nearCoarse : CertificateContracts.SparseL2ThresholdNearCoarseCover128)
    (nearEndpoints : CertificateContracts.SparseL2ThresholdNearEndpoints128)
    (nearCurvature : CertificateContracts.SparseL2ThresholdNearCurvature128)
    (diffuseScalar : CertificateContracts.SparseL2ThresholdDiffuseLowScalar128)
    (diffuseTail : CertificateContracts.SparseL2ThresholdDiffuseLowModularTail128)
    (diffuseHigh : CertificateContracts.SparseL2ThresholdDiffuseHighEndpoints128)
    (diffuseFloor73 : CertificateContracts.SparseL2ThresholdDiffuseFloor73Endpoints) :
    AffineL2WrappedProfiles where
  near := affineL2General_nearWrapped nearCoarse nearEndpoints nearCurvature
  diffuse33 := sparseThresholdDiffuseWrappedRowBound_marginThree_of_replay
    diffuseScalar diffuseTail diffuseHigh
  diffuse25 := ThresholdDiffuseFloor73.wrappedRowBound_marginThree_of_replay diffuseFloor73

end CertifiedJL.CertificateAssembly
