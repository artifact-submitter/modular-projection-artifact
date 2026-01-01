/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Spec
import CertifiedJL.Certificates.Families.L2Lower.Shared.Providers.DiffuseFloor73Verified
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.CappedFourierCover512Floor73Bits193
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover512Floor73Bits193
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.SingletonFourierCover512Floor73Bits193
import CertifiedJL.Certificates.Families.L2Lower.Rows512Floor73Bits193.Soundness.ThresholdRatios512Floor73Bits193

/-! # Kernel-verified providers for the 512/73/193 threshold endpoint -/

namespace CertifiedJL.CertificateProviders

theorem sparseL2ThresholdDominantDirectCover512Floor73Bits193_verified :
    CertificateContracts.SparseL2ThresholdDominantDirectCover512Floor73Bits193 := by
  simpa [CertificateContracts.SparseL2ThresholdDominantDirectCover512Floor73Bits193,
    CertificateContracts.SparseL2ThresholdDominantDirectCoverAt,
    SparseThresholdDominant.ConstantDirectCover512Floor73Bits193.budget]
    using SparseThresholdDominant.ConstantDirectCover512Floor73Bits193.exists_cover_cell

theorem sparseL2ThresholdDominantCappedFourierCover512Floor73Bits193_verified :
    CertificateContracts.SparseL2ThresholdDominantCappedFourierCover512Floor73Bits193 := by
  intro B r
  simpa [CertificateContracts.SparseL2ThresholdDominantCappedFourierCover512Floor73Bits193,
    CertificateContracts.SparseL2ThresholdDominantCappedFourierCoverAt,
    SparseThresholdDominant.CappedFourierNumeric128.z,
    SparseThresholdDominant.CappedFourierCover512Floor73Bits193.budget]
    using @SparseThresholdDominant.CappedFourierCover512Floor73Bits193.exists_cover_cell B r

theorem sparseL2ThresholdDominantSingletonFourierCover512Floor73Bits193_verified :
    CertificateContracts.SparseL2ThresholdDominantSingletonFourierCover512Floor73Bits193 := by
  intro B r
  simpa [CertificateContracts.SparseL2ThresholdDominantSingletonFourierCover512Floor73Bits193,
    CertificateContracts.SparseL2ThresholdDominantSingletonFourierCoverAt,
    SparseThresholdDominant.SingletonFourierNumeric128.z,
    SparseThresholdDominant.SingletonFourierCover512Floor73Bits193.budget]
    using @SparseThresholdDominant.SingletonFourierCover512Floor73Bits193.exists_cover_cell B r

theorem sparseL2ThresholdDominantFinalRatio512Floor73Bits193_verified :
    CertificateContracts.SparseL2ThresholdDominantFinalRatio512Floor73Bits193 := by
  simpa [CertificateContracts.SparseL2ThresholdDominantFinalRatio512Floor73Bits193]
    using ThresholdRatios512Floor73Bits193.retainedFinalRatio

theorem sparseL2ThresholdNearFinalRatio512Floor73Bits193_verified :
    CertificateContracts.SparseL2ThresholdNearFinalRatio512Floor73Bits193 := by
  simpa [CertificateContracts.SparseL2ThresholdNearFinalRatio512Floor73Bits193]
    using ThresholdRatios512Floor73Bits193.nearFinalRatio


theorem sparseL2ThresholdDiffuseFinalRatio512Floor73Bits193_verified :
    CertificateContracts.SparseL2ThresholdDiffuseFinalRatio512Floor73Bits193 := by
  simpa [CertificateContracts.SparseL2ThresholdDiffuseFinalRatio512Floor73Bits193]
    using ThresholdRatios512Floor73Bits193.diffuseFinalRatio

end CertifiedJL.CertificateProviders
