/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Spec
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.CappedFourierCover256Bits192Selector
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover256Bits192
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.SingletonPhaseFourierCover256Bits192Selector
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits192.Soundness.ThresholdRatios256Bits192

/-! # Kernel-verified providers for the 256/9/192 threshold endpoint -/

namespace CertifiedJL.CertificateProviders

theorem sparseL2ThresholdDominantDirectCover256Bits192_verified :
    CertificateContracts.SparseL2ThresholdDominantDirectCover256Bits192 := by
  simpa [CertificateContracts.SparseL2ThresholdDominantDirectCover256Bits192,
    CertificateContracts.SparseL2ThresholdDominantDirectCoverAt]
    using SparseThresholdDominant.ConstantDirectCover256Bits192.exists_cover_cell

theorem sparseL2ThresholdDominantCappedFourierCover256Bits192_verified :
    CertificateContracts.SparseL2ThresholdDominantCappedFourierCover256Bits192 := by
  intro B r hB2 hB3 hr
  obtain ⟨cell, _hmem, hLower, hUpper, hThreshold, hcert⟩ :=
    SparseThresholdDominant.CappedFourierCover256Bits192.exists_certified_cell
      hB2 hB3 hr
  have hgeometry :=
    SparseThresholdDominant.CappedFourierNumeric256Bits192.certifiedCheck_geometry
      cell hcert
  exact ⟨cell.lower, cell.upper, cell.thresholdUpper, hLower, hUpper,
    hThreshold, hgeometry.1, hgeometry.2,
    (by
      simpa [SparseThresholdDominant.CappedFourierNumeric256Bits192.z] using
        SparseThresholdDominant.CappedFourierNumeric256Bits192.certifiedCheck_sound
          cell hcert)⟩

theorem sparseL2ThresholdDominantSingletonFourierCover256Bits192_verified :
    CertificateContracts.SparseL2ThresholdDominantSingletonFourierCover256Bits192 := by
  intro B r hB2 hB5 hr
  obtain ⟨cell, _hmem, hLower, hUpper, hThreshold, hcert⟩ :=
    SparseThresholdDominant.SingletonPhaseFourierCover256Bits192.exists_certified_cell
      hB2 hB5 hr
  have hgeometry :=
    SparseThresholdDominant.SingletonPhaseFourierNumeric256Bits192.certifiedCheck_geometry
      cell hcert
  exact ⟨cell.lower, cell.upper, cell.thresholdUpper, hLower, hUpper,
    hThreshold, hgeometry.1, hgeometry.2,
    (by
      simpa [SparseThresholdDominant.SingletonPhaseFourierNumeric256Bits192.z]
        using
          SparseThresholdDominant.SingletonPhaseFourierNumeric256Bits192.certifiedCheck_sound
            cell hcert)⟩

theorem sparseL2ThresholdDominantFinalRatio256Bits192_verified :
    CertificateContracts.SparseL2ThresholdDominantFinalRatio256Bits192 := by
  simpa [CertificateContracts.SparseL2ThresholdDominantFinalRatio256Bits192]
    using ThresholdRatios256Bits192.retainedFinalRatio

theorem sparseL2ThresholdNearFinalRatio256Bits192_verified :
    CertificateContracts.SparseL2ThresholdNearFinalRatio256Bits192 := by
  simpa [CertificateContracts.SparseL2ThresholdNearFinalRatio256Bits192]
    using ThresholdRatios256Bits192.nearFinalRatio

theorem sparseL2ThresholdDiffuseFinalRatio256Bits192_verified :
    CertificateContracts.SparseL2ThresholdDiffuseFinalRatio256Bits192 := by
  simpa [CertificateContracts.SparseL2ThresholdDiffuseFinalRatio256Bits192]
    using ThresholdRatios256Bits192.diffuseFinalRatio

end CertifiedJL.CertificateProviders
