/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Spec
import CertifiedJL.Certificates.Families.L2Lower.Shared.Providers.DiffuseVerified
import CertifiedJL.Certificates.Families.L2Lower.Shared.Providers.NearVerified
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.CappedFourierCover128Selector
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.ConstantDirectCover128Selector
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.SingletonFourierCover128Selector
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Dominant.Soundness.ThresholdDominantRetainedNumeric128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Dominant.Soundness.ThresholdDominantRetainedRatio128

/-! # Kernel-verified providers for the threshold-relative lower tail -/

namespace CertifiedJL.CertificateProviders

theorem sparseL2ThresholdDominantDirectCover128_verified :
    CertificateContracts.SparseL2ThresholdDominantDirectCover128 :=
  SparseThresholdDominant.ConstantDirectCover128Selector.exists_cover_cell

theorem sparseL2ThresholdDominantCappedFourierCover128_verified :
    CertificateContracts.SparseL2ThresholdDominantCappedFourierCover128 :=
  SparseThresholdDominant.CappedFourierCover128.exists_certified_cell

theorem sparseL2ThresholdDominantSingletonFourierCover128_verified :
    CertificateContracts.SparseL2ThresholdDominantSingletonFourierCover128 :=
  SparseThresholdDominant.SingletonFourierCover128.exists_certified_cell

theorem sparseL2ThresholdDominantRetainedCoarse128_verified :
    CertificateContracts.SparseL2ThresholdDominantRetainedCoarse128 where
  central := ThresholdDominantRetained128.Coarse.semanticCoarseCentral_lt
  conditionedTail := ThresholdDominantRetained128.Coarse.semanticConditionedTail_lt

theorem sparseL2ThresholdDominantRetainedChord128_verified :
    CertificateContracts.SparseL2ThresholdDominantRetainedChord128 :=
  ThresholdDominantRetained128.Chord.semanticChordCentral_lt

theorem sparseL2ThresholdDominantFinalRatio128_verified :
    CertificateContracts.SparseL2ThresholdDominantFinalRatio128 :=
  ThresholdDominantRetainedRatio128.finalRatio


end CertifiedJL.CertificateProviders
