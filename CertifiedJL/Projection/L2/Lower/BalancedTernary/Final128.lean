/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Assembly
import CertifiedJL.Certificates.Families.L2Lower.Shared.Providers.LowerVerified

/-!
# Final balanced-ternary threshold-relative L2 lower tail at 128 bits

This module discharges the three analytic contracts in the exact 128-bit
probability-budget assembly.  The resulting theorem constrains the public
threshold by the modulus; it does not impose an upper bound on the actual
input norm.
-/

namespace CertifiedJL

/-- For 256 balanced-ternary rows, the modular squared norm falls below
`29 * b^2` with probability strictly less than `2^-128`, provided `b` is a
positive public lower bound on the input norm and `3 * b <= q`. -/
theorem ternaryThresholdLowerTail_marginThree_bits128 :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 256
        squaredNormFloor := NonnegativeRatio.ofNat 29
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 128) :=
  CertificateAssembly.sparseL2ThresholdLower128
    CertificateProviders.sparseL2ThresholdDominantDirectCover128_verified
    CertificateProviders.sparseL2ThresholdDominantCappedFourierCover128_verified
    CertificateProviders.sparseL2ThresholdDominantSingletonFourierCover128_verified
    CertificateProviders.sparseL2ThresholdDominantRetainedCoarse128_verified
    CertificateProviders.sparseL2ThresholdDominantRetainedChord128_verified
    CertificateProviders.sparseL2ThresholdDominantFinalRatio128_verified
    CertificateProviders.sparseL2ThresholdNearCoarseCover128_verified
    CertificateProviders.sparseL2ThresholdNearEndpoints128_verified
    CertificateProviders.sparseL2ThresholdNearCurvature128_verified
    CertificateProviders.sparseL2ThresholdDiffuseLowScalar128_verified
    CertificateProviders.sparseL2ThresholdDiffuseLowModularTail128_verified
    CertificateProviders.sparseL2ThresholdDiffuseHighEndpoints128_verified

end CertifiedJL
