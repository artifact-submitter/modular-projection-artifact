/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Spec
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.CappedFourierCover384Bits192
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover384Bits192
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.SingletonFourierCover384Bits192
import CertifiedJL.Certificates.Families.L2Lower.Rows384Bits192.Soundness.ThresholdRatios384Bits192

/-! # Kernel-verified providers for the 384/43/192 threshold endpoint -/

namespace CertifiedJL.CertificateProviders

theorem sparseL2ThresholdDominantDirectCover384Bits192_verified :
    CertificateContracts.SparseL2ThresholdDominantDirectCover384Bits192 := by
  simpa [CertificateContracts.SparseL2ThresholdDominantDirectCover384Bits192]
    using SparseThresholdDominant.ConstantDirectCover384Bits192.exists_cover_cell

theorem sparseL2ThresholdDominantCappedFourierCover384Bits192_verified :
    CertificateContracts.SparseL2ThresholdDominantCappedFourierCover384Bits192 := by
  intro B r
  simpa [CertificateContracts.SparseL2ThresholdDominantCappedFourierCover384Bits192,
    SparseThresholdDominant.CappedFourierNumeric128.z,
    SparseThresholdDominant.CappedFourierCover384Bits192.budget]
    using @SparseThresholdDominant.CappedFourierCover384Bits192.exists_cover_cell B r

theorem sparseL2ThresholdDominantSingletonFourierCover384Bits192_verified :
    CertificateContracts.SparseL2ThresholdDominantSingletonFourierCover384Bits192 := by
  intro B r
  simpa [CertificateContracts.SparseL2ThresholdDominantSingletonFourierCover384Bits192,
    SparseThresholdDominant.SingletonFourierNumeric128.z,
    SparseThresholdDominant.SingletonFourierCover384Bits192.budget]
    using @SparseThresholdDominant.SingletonFourierCover384Bits192.exists_cover_cell B r

theorem sparseL2ThresholdDominantFinalRatio384Bits192_verified :
    CertificateContracts.SparseL2ThresholdDominantFinalRatio384Bits192 := by
  simpa [CertificateContracts.SparseL2ThresholdDominantFinalRatio384Bits192]
    using ThresholdRatios384Bits192.retainedFinalRatio

theorem sparseL2ThresholdNearFinalRatio384Bits192_verified :
    CertificateContracts.SparseL2ThresholdNearFinalRatio384Bits192 := by
  simpa [CertificateContracts.SparseL2ThresholdNearFinalRatio384Bits192]
    using ThresholdRatios384Bits192.nearFinalRatio

theorem sparseL2ThresholdDiffuseFinalRatio384Bits192_verified :
    CertificateContracts.SparseL2ThresholdDiffuseFinalRatio384Bits192 := by
  simpa [CertificateContracts.SparseL2ThresholdDiffuseFinalRatio384Bits192]
    using ThresholdRatios384Bits192.diffuseFinalRatio

end CertifiedJL.CertificateProviders
