/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows512Bits192.Assembly
import CertifiedJL.Certificates.Families.L2Lower.Rows512Bits192.Provider
import CertifiedJL.Certificates.Families.L2Lower.Shared.Providers.LowerVerified
import CertifiedJL.Results.L2.Lower.Rows512Bits193

/-! # Balanced-ternary L2 threshold specialization -/

namespace CertifiedJL.Results.L2.Lower.Rows512Bits192

/-- Balanced-ternary strict threshold-relative L2 lower tail at squared-norm floor 71. -/
theorem ternaryL2ThresholdLower71 :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        squaredNormFloor := NonnegativeRatio.ofNat 71
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 192) :=
  CertificateAssembly.sparseL2ThresholdLower512Bits192
    CertificateProviders.sparseL2ThresholdDominantDirectCover512Bits192_verified
    CertificateProviders.sparseL2ThresholdDominantCappedFourierCover512Bits192_verified
    CertificateProviders.sparseL2ThresholdDominantSingletonFourierCover512Bits192_verified
    CertificateProviders.sparseL2ThresholdDominantRetainedCoarse128_verified
    CertificateProviders.sparseL2ThresholdDominantRetainedChord128_verified
    CertificateProviders.sparseL2ThresholdDominantFinalRatio512Bits192_verified
    CertificateProviders.sparseL2ThresholdNearCoarseCover128_verified
    CertificateProviders.sparseL2ThresholdNearEndpoints128_verified
    CertificateProviders.sparseL2ThresholdNearCurvature128_verified
    CertificateProviders.sparseL2ThresholdNearFinalRatio512Bits192_verified
    CertificateProviders.sparseL2ThresholdDiffuseLowScalar128_verified
    CertificateProviders.sparseL2ThresholdDiffuseLowModularTail128_verified
    CertificateProviders.sparseL2ThresholdDiffuseHighEndpoints128_verified
    CertificateProviders.sparseL2ThresholdDiffuseFinalRatio512Bits192_verified

/-- The stronger 193-bit endpoint, weakened to the legacy 192-bit budget. -/
theorem ternaryL2ThresholdLower73 :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        squaredNormFloor := NonnegativeRatio.ofNat 73
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 192) := by
  apply Results.L2.Lower.Rows512Bits193.ternaryL2ThresholdLower73.mono_budget
  unfold failureTarget
  rw [pow_succ]
  exact mul_le_of_le_one_right (by positivity) (by norm_num)

end CertifiedJL.Results.L2.Lower.Rows512Bits192
