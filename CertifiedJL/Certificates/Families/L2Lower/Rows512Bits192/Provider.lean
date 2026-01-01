/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Spec
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.CappedFourierCover512Bits192
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover512Bits192
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.SingletonFourierCover512Bits192
import CertifiedJL.Certificates.Families.L2Lower.Rows512Bits192.Soundness.ThresholdRatios512Bits192

/-! # Kernel-verified providers for the 512/192 threshold endpoint -/

namespace CertifiedJL.CertificateProviders

theorem sparseL2ThresholdDominantDirectCover512Bits192_verified :
    CertificateContracts.SparseL2ThresholdDominantDirectCover512Bits192 := by
  simpa [CertificateContracts.SparseL2ThresholdDominantDirectCover512Bits192]
    using SparseThresholdDominant.ConstantDirectCover512Bits192.exists_cover_cell

theorem sparseL2ThresholdDominantCappedFourierCover512Bits192_verified :
    CertificateContracts.SparseL2ThresholdDominantCappedFourierCover512Bits192 := by
  intro B r
  simpa [CertificateContracts.SparseL2ThresholdDominantCappedFourierCover512Bits192,
    SparseThresholdDominant.CappedFourierNumeric128.z,
    SparseThresholdDominant.CappedFourierCover512Bits192.budget]
    using @SparseThresholdDominant.CappedFourierCover512Bits192.exists_cover_cell B r

theorem sparseL2ThresholdDominantSingletonFourierCover512Bits192_verified :
    CertificateContracts.SparseL2ThresholdDominantSingletonFourierCover512Bits192 := by
  intro B r
  simpa [CertificateContracts.SparseL2ThresholdDominantSingletonFourierCover512Bits192,
    SparseThresholdDominant.SingletonFourierNumeric128.z,
    SparseThresholdDominant.SingletonFourierCover512Bits192.budget]
    using @SparseThresholdDominant.SingletonFourierCover512Bits192.exists_cover_cell B r

theorem sparseL2ThresholdDominantFinalRatio512Bits192_verified :
    CertificateContracts.SparseL2ThresholdDominantFinalRatio512Bits192 := by
  simpa [CertificateContracts.SparseL2ThresholdDominantFinalRatio512Bits192]
    using ThresholdRatios512Bits192.retainedFinalRatio

theorem sparseL2ThresholdNearFinalRatio512Bits192_verified :
    CertificateContracts.SparseL2ThresholdNearFinalRatio512Bits192 := by
  simpa [CertificateContracts.SparseL2ThresholdNearFinalRatio512Bits192]
    using ThresholdRatios512Bits192.nearFinalRatio

theorem sparseL2ThresholdDiffuseFinalRatio512Bits192_verified :
    CertificateContracts.SparseL2ThresholdDiffuseFinalRatio512Bits192 := by
  simpa [CertificateContracts.SparseL2ThresholdDiffuseFinalRatio512Bits192]
    using ThresholdRatios512Bits192.diffuseFinalRatio

end CertifiedJL.CertificateProviders
