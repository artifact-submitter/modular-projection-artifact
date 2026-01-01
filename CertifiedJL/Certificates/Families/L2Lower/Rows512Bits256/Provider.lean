/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Spec
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.CappedFourierCover512Bits256
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover512Bits256
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.SingletonFourierCover512Bits256
import CertifiedJL.Certificates.Families.L2Lower.Rows512Bits256.Soundness.ThresholdRatios512Bits256

/-! # Kernel-verified providers for the 512/256 threshold endpoint -/

namespace CertifiedJL.CertificateProviders

theorem sparseL2ThresholdDominantDirectCover512Bits256_verified :
    CertificateContracts.SparseL2ThresholdDominantDirectCover512Bits256 := by
  simpa [CertificateContracts.SparseL2ThresholdDominantDirectCover512Bits256,
    SparseThresholdDominant.ConstantDirectCover512Bits256.budget]
    using SparseThresholdDominant.ConstantDirectCover512Bits256.exists_cover_cell

theorem sparseL2ThresholdDominantCappedFourierCover512Bits256_verified :
    CertificateContracts.SparseL2ThresholdDominantCappedFourierCover512Bits256 := by
  intro B r
  simpa [CertificateContracts.SparseL2ThresholdDominantCappedFourierCover512Bits256,
    SparseThresholdDominant.CappedFourierNumeric128.z,
    SparseThresholdDominant.CappedFourierCover512Bits256.budget]
    using @SparseThresholdDominant.CappedFourierCover512Bits256.exists_cover_cell B r

theorem sparseL2ThresholdDominantSingletonFourierCover512Bits256_verified :
    CertificateContracts.SparseL2ThresholdDominantSingletonFourierCover512Bits256 := by
  intro B r
  simpa [CertificateContracts.SparseL2ThresholdDominantSingletonFourierCover512Bits256,
    SparseThresholdDominant.SingletonFourierNumeric128.z,
    SparseThresholdDominant.SingletonFourierCover512Bits256.budget]
    using @SparseThresholdDominant.SingletonFourierCover512Bits256.exists_cover_cell B r

theorem sparseL2ThresholdDominantFinalRatio512Bits256_verified :
    CertificateContracts.SparseL2ThresholdDominantFinalRatio512Bits256 := by
  simpa [CertificateContracts.SparseL2ThresholdDominantFinalRatio512Bits256]
    using ThresholdRatios512Bits256.retainedFinalRatio

theorem sparseL2ThresholdNearFinalRatio512Bits256_verified :
    CertificateContracts.SparseL2ThresholdNearFinalRatio512Bits256 := by
  simpa [CertificateContracts.SparseL2ThresholdNearFinalRatio512Bits256]
    using ThresholdRatios512Bits256.nearFinalRatio

theorem sparseL2ThresholdDiffuseFinalRatio512Bits256_verified :
    CertificateContracts.SparseL2ThresholdDiffuseFinalRatio512Bits256 := by
  simpa [CertificateContracts.SparseL2ThresholdDiffuseFinalRatio512Bits256]
    using ThresholdRatios512Bits256.diffuseFinalRatio

end CertifiedJL.CertificateProviders
