/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows512Floor73Bits193.Assembly
import CertifiedJL.Certificates.Families.L2Lower.Rows512Floor73Bits193.Provider
import CertifiedJL.Certificates.Families.L2Lower.Shared.Providers.LowerVerified

/-! # Certified 512-row balanced-ternary L2 threshold tail at 193 bits -/

namespace CertifiedJL.Results.L2.Lower.Rows512Bits193

/-- Balanced-ternary strict threshold-relative L2 lower tail at squared-norm floor 73. -/
theorem ternaryL2ThresholdLower73 :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        squaredNormFloor := NonnegativeRatio.ofNat 73
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 193) :=
  CertificateAssembly.sparseL2ThresholdLower512Floor73Bits193
    CertificateProviders.sparseL2ThresholdDominantDirectCover512Floor73Bits193_verified
    CertificateProviders.sparseL2ThresholdDominantCappedFourierCover512Floor73Bits193_verified
    CertificateProviders.sparseL2ThresholdDominantSingletonFourierCover512Floor73Bits193_verified
    CertificateProviders.sparseL2ThresholdDominantRetainedCoarse128_verified
    CertificateProviders.sparseL2ThresholdDominantRetainedChord128_verified
    CertificateProviders.sparseL2ThresholdDominantFinalRatio512Floor73Bits193_verified
    CertificateProviders.sparseL2ThresholdNearCoarseCover128_verified
    CertificateProviders.sparseL2ThresholdNearEndpoints128_verified
    CertificateProviders.sparseL2ThresholdNearCurvature128_verified
    CertificateProviders.sparseL2ThresholdNearFinalRatio512Floor73Bits193_verified
    CertificateProviders.sparseL2ThresholdDiffuseFloor73Endpoints_verified
    CertificateProviders.sparseL2ThresholdDiffuseFinalRatio512Floor73Bits193_verified

end CertifiedJL.Results.L2.Lower.Rows512Bits193
