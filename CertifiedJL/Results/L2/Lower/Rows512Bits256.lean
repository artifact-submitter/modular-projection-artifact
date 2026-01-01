/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows512Bits256.Assembly
import CertifiedJL.Certificates.Families.L2Lower.Rows512Bits256.Provider
import CertifiedJL.Certificates.Families.L2Lower.Shared.Providers.LowerVerified

/-! # Certified 512-row balanced-ternary L2 threshold tail at 256 bits -/

namespace CertifiedJL.Results.L2.Lower.Rows512Bits256

/-- Balanced-ternary strict threshold-relative L2 lower tail at squared-norm floor 57. -/
theorem ternaryL2ThresholdLower57 :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        squaredNormFloor := NonnegativeRatio.ofNat 57
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 256) :=
  CertificateAssembly.sparseL2ThresholdLower512Bits256
    CertificateProviders.sparseL2ThresholdDominantDirectCover512Bits256_verified
    CertificateProviders.sparseL2ThresholdDominantCappedFourierCover512Bits256_verified
    CertificateProviders.sparseL2ThresholdDominantSingletonFourierCover512Bits256_verified
    CertificateProviders.sparseL2ThresholdDominantRetainedCoarse128_verified
    CertificateProviders.sparseL2ThresholdDominantRetainedChord128_verified
    CertificateProviders.sparseL2ThresholdDominantFinalRatio512Bits256_verified
    CertificateProviders.sparseL2ThresholdNearCoarseCover128_verified
    CertificateProviders.sparseL2ThresholdNearEndpoints128_verified
    CertificateProviders.sparseL2ThresholdNearCurvature128_verified
    CertificateProviders.sparseL2ThresholdNearFinalRatio512Bits256_verified
    CertificateProviders.sparseL2ThresholdDiffuseLowScalar128_verified
    CertificateProviders.sparseL2ThresholdDiffuseLowModularTail128_verified
    CertificateProviders.sparseL2ThresholdDiffuseHighEndpoints128_verified
    CertificateProviders.sparseL2ThresholdDiffuseFinalRatio512Bits256_verified

end CertifiedJL.Results.L2.Lower.Rows512Bits256
