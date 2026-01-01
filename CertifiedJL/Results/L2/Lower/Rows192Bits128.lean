/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows192Bits128.Assembly
import CertifiedJL.Certificates.Families.L2Lower.Rows192Bits128.Provider
import CertifiedJL.Certificates.Families.L2Lower.Shared.Providers.LowerVerified

/-! # Certified 192-row balanced-ternary modular tails -/

namespace CertifiedJL.Results.L2.Lower.Rows192Bits128

/-- Balanced-ternary strict threshold-relative L2 lower tail at squared-norm floor
`12`, under `b^2 ≤ ‖w‖₂^2` and `3 * b ≤ q`. -/
theorem ternaryL2ThresholdLower12 :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 192
        squaredNormFloor := NonnegativeRatio.ofNat 12
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 128) :=
  CertificateAssembly.sparseL2ThresholdLower192Bits128
    CertificateProviders.sparseL2ThresholdDominantDirectCover192Bits128_verified
    CertificateProviders.sparseL2ThresholdDominantCappedFourierCover192Bits128_verified
    CertificateProviders.sparseL2ThresholdDominantSingletonFourierCover192Bits128_verified
    CertificateProviders.sparseL2ThresholdDominantRetainedCoarse128_verified
    CertificateProviders.sparseL2ThresholdDominantRetainedChord128_verified
    CertificateProviders.sparseL2ThresholdDominantFinalRatio192Bits128_verified
    CertificateProviders.sparseL2ThresholdNearCoarseCover128_verified
    CertificateProviders.sparseL2ThresholdNearEndpoints128_verified
    CertificateProviders.sparseL2ThresholdNearCurvature128_verified
    CertificateProviders.sparseL2ThresholdNearFinalRatio192Bits128_verified
    CertificateProviders.sparseL2ThresholdDiffuseLowScalar128_verified
    CertificateProviders.sparseL2ThresholdDiffuseLowModularTail128_verified
    CertificateProviders.sparseL2ThresholdDiffuseHighEndpoints128_verified
    CertificateProviders.sparseL2ThresholdDiffuseFinalRatio192Bits128_verified

end CertifiedJL.Results.L2.Lower.Rows192Bits128
