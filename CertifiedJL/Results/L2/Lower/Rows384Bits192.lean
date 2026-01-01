/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows384Bits192.Assembly
import CertifiedJL.Certificates.Families.L2Lower.Rows384Bits192.Provider
import CertifiedJL.Certificates.Families.L2Lower.Shared.Providers.LowerVerified

/-! # Certified 384-row balanced-ternary modular tails at 192 bits -/

namespace CertifiedJL.Results.L2.Lower.Rows384Bits192

/-- Balanced-ternary strict threshold-relative L2 lower tail at squared-norm floor
`43`, under `b^2 ≤ ‖w‖₂^2` and `3 * b ≤ q`. -/
theorem ternaryL2ThresholdLower43 :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 384
        squaredNormFloor := NonnegativeRatio.ofNat 43
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 192) :=
  CertificateAssembly.sparseL2ThresholdLower384Bits192
    CertificateProviders.sparseL2ThresholdDominantDirectCover384Bits192_verified
    CertificateProviders.sparseL2ThresholdDominantCappedFourierCover384Bits192_verified
    CertificateProviders.sparseL2ThresholdDominantSingletonFourierCover384Bits192_verified
    CertificateProviders.sparseL2ThresholdDominantRetainedCoarse128_verified
    CertificateProviders.sparseL2ThresholdDominantRetainedChord128_verified
    CertificateProviders.sparseL2ThresholdDominantFinalRatio384Bits192_verified
    CertificateProviders.sparseL2ThresholdNearCoarseCover128_verified
    CertificateProviders.sparseL2ThresholdNearEndpoints128_verified
    CertificateProviders.sparseL2ThresholdNearCurvature128_verified
    CertificateProviders.sparseL2ThresholdNearFinalRatio384Bits192_verified
    CertificateProviders.sparseL2ThresholdDiffuseLowScalar128_verified
    CertificateProviders.sparseL2ThresholdDiffuseLowModularTail128_verified
    CertificateProviders.sparseL2ThresholdDiffuseHighEndpoints128_verified
    CertificateProviders.sparseL2ThresholdDiffuseFinalRatio384Bits192_verified

end CertifiedJL.Results.L2.Lower.Rows384Bits192
