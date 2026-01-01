/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits192.Assembly
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits192.Provider
import CertifiedJL.Certificates.Families.L2Lower.Shared.Providers.LowerVerified

/-! # Certified 256-row balanced-ternary modular tails at 192 bits -/

namespace CertifiedJL.Results.L2.Lower.Rows256Bits192

/-- Balanced-ternary strict threshold-relative L2 lower tail at squared-norm floor
`9`, under `b^2 ≤ ‖w‖₂^2` and `3 * b ≤ q`. -/
theorem ternaryL2ThresholdLower9 :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 256
        squaredNormFloor := NonnegativeRatio.ofNat 9
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 192) :=
  CertificateAssembly.sparseL2ThresholdLower256Bits192
    CertificateProviders.sparseL2ThresholdDominantDirectCover256Bits192_verified
    CertificateProviders.sparseL2ThresholdDominantCappedFourierCover256Bits192_verified
    CertificateProviders.sparseL2ThresholdDominantSingletonFourierCover256Bits192_verified
    CertificateProviders.sparseL2ThresholdDominantRetainedCoarse128_verified
    CertificateProviders.sparseL2ThresholdDominantRetainedChord128_verified
    CertificateProviders.sparseL2ThresholdDominantFinalRatio256Bits192_verified
    CertificateProviders.sparseL2ThresholdNearCoarseCover128_verified
    CertificateProviders.sparseL2ThresholdNearEndpoints128_verified
    CertificateProviders.sparseL2ThresholdNearCurvature128_verified
    CertificateProviders.sparseL2ThresholdNearFinalRatio256Bits192_verified
    CertificateProviders.sparseL2ThresholdDiffuseLowScalar128_verified
    CertificateProviders.sparseL2ThresholdDiffuseLowModularTail128_verified
    CertificateProviders.sparseL2ThresholdDiffuseHighEndpoints128_verified
    CertificateProviders.sparseL2ThresholdDiffuseFinalRatio256Bits192_verified

end CertifiedJL.Results.L2.Lower.Rows256Bits192
