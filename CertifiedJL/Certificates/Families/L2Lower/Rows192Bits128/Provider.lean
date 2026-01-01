/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Spec
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover192Bits128
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.FourierCovers192Bits128
import CertifiedJL.Certificates.Families.L2Lower.Rows192Bits128.Soundness.ThresholdRatios192Bits128

/-! # Kernel-verified providers for the 192/12/128 threshold endpoint -/

namespace CertifiedJL.CertificateProviders

theorem sparseL2ThresholdDominantDirectCover192Bits128_verified :
    CertificateContracts.SparseL2ThresholdDominantDirectCover192Bits128 := by
  simpa [CertificateContracts.SparseL2ThresholdDominantDirectCover192Bits128,
    CertificateContracts.SparseL2ThresholdDominantDirectCoverAt,
    SparseThresholdDominant.ConstantDirectCover192Bits128.budget] using
    SparseThresholdDominant.ConstantDirectCover192Bits128.exists_cover_cell

theorem sparseL2ThresholdDominantCappedFourierCover192Bits128_verified :
    CertificateContracts.SparseL2ThresholdDominantCappedFourierCover192Bits128 := by
  intro B r hB2 hB3 hr
  obtain ⟨cell, _hmem, hLower, hUpper, hThreshold, hCellLower,
      hCellUpper, hbound⟩ :=
    SparseThresholdDominant.CappedFourierCover192Bits128.exists_cover_cell
      hB2 hB3 hr
  exact ⟨cell.lower, cell.upper, cell.thresholdUpper, hLower, hUpper,
    hThreshold, hCellLower, hCellUpper, (by
      simpa [SparseThresholdDominant.CappedFourierCover192Bits128.budget,
        SparseThresholdDominant.CappedFourierNumeric256Bits192.z] using hbound)⟩

theorem sparseL2ThresholdDominantSingletonFourierCover192Bits128_verified :
    CertificateContracts.SparseL2ThresholdDominantSingletonFourierCover192Bits128 := by
  intro B r hB2 hB5 hr
  obtain ⟨cell, _hmem, hLower, hUpper, hThreshold, hCellLower,
      hCellUpper, hbound⟩ :=
    SparseThresholdDominant.SingletonPhaseFourierCover192Bits128.exists_cover_cell
      hB2 hB5 hr
  exact ⟨cell.lower, cell.upper, cell.thresholdUpper, hLower, hUpper,
    hThreshold, hCellLower, hCellUpper, (by
      simpa [SparseThresholdDominant.SingletonPhaseFourierCover192Bits128.budget,
        SparseThresholdDominant.SingletonPhaseFourierNumeric256Bits192.z] using hbound)⟩

theorem sparseL2ThresholdDominantFinalRatio192Bits128_verified :
    CertificateContracts.SparseL2ThresholdDominantFinalRatio192Bits128 := by
  simpa [CertificateContracts.SparseL2ThresholdDominantFinalRatio192Bits128] using
    ThresholdRatios192Bits128.retainedFinalRatio

theorem sparseL2ThresholdNearFinalRatio192Bits128_verified :
    CertificateContracts.SparseL2ThresholdNearFinalRatio192Bits128 := by
  simpa [CertificateContracts.SparseL2ThresholdNearFinalRatio192Bits128] using
    ThresholdRatios192Bits128.nearFinalRatio

theorem sparseL2ThresholdDiffuseFinalRatio192Bits128_verified :
    CertificateContracts.SparseL2ThresholdDiffuseFinalRatio192Bits128 := by
  simpa [CertificateContracts.SparseL2ThresholdDiffuseFinalRatio192Bits128] using
    ThresholdRatios192Bits128.diffuseFinalRatio

end CertifiedJL.CertificateProviders
