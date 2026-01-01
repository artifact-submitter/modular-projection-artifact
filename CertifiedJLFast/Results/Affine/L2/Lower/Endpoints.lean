/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.Affine.Assembly.AffineEndpoints
import CertifiedJLFast.Assumptions.Families.L2Lower.Shared
import CertifiedJLFast.Results.Affine.LInf.Lower.Direct

/-! # Fast-provider mirror of the exact affine lower-tail endpoint family -/

namespace CertifiedJLFast.Results.Affine.L2.Lower.Endpoints

open CertifiedJL

private theorem profiles : CertificateAssembly.AffineL2WrappedProfiles :=
  CertificateAssembly.affineL2General_profiles
    Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed
    Assumptions.sparse_l2_threshold_near_endpoints128_assumed
    Assumptions.sparse_l2_threshold_near_curvature128_assumed
    Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed
    Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed
    Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed
    Assumptions.sparse_l2_threshold_diffuse_floor73_endpoints_assumed

private theorem l2 (e : AffineEndpointNumeric.L2EndpointData)
    (h : AffineEndpointNumeric.l2EndpointCheck e = true) :
    AffineEndpointNumeric.L2EndpointClaim e :=
  CertificateAssembly.affineL2Endpoint e profiles h

theorem ternaryAffineL2ThresholdLower192Floor11Bits128 :
    AffineL2ThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 192, squaredNormFloor := NonnegativeRatio.ofNat 11,
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget 128) :=
  l2 AffineEndpointNumeric.l2_192_11_128 AffineEndpointNumeric.l2_192_11_128_checked
theorem ternaryAffineL2ThresholdLower256Floor27Bits128 :
    AffineL2ThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 256, squaredNormFloor := NonnegativeRatio.ofNat 27,
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget 128) :=
  l2 AffineEndpointNumeric.l2_256_27_128 AffineEndpointNumeric.l2_256_27_128_checked
theorem ternaryAffineL2ThresholdLower256Floor9Bits194 :
    AffineL2ThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 256, squaredNormFloor := NonnegativeRatio.ofNat 9,
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget 194) :=
  l2 AffineEndpointNumeric.l2_256_9_194 AffineEndpointNumeric.l2_256_9_194_checked
theorem ternaryAffineL2ThresholdLower384Floor40Bits192 :
    AffineL2ThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 384, squaredNormFloor := NonnegativeRatio.ofNat 40,
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget 192) :=
  l2 AffineEndpointNumeric.l2_384_40_192 AffineEndpointNumeric.l2_384_40_192_checked
theorem ternaryAffineL2ThresholdLower512Floor73Bits193 :
    AffineL2ThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 512, squaredNormFloor := NonnegativeRatio.ofNat 73,
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget 193) :=
  l2 AffineEndpointNumeric.l2_512_73_193 AffineEndpointNumeric.l2_512_73_193_checked
theorem ternaryAffineL2ThresholdLower512Floor54Bits256 :
    AffineL2ThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 512, squaredNormFloor := NonnegativeRatio.ofNat 54,
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget 256) :=
  l2 AffineEndpointNumeric.l2_512_54_256 AffineEndpointNumeric.l2_512_54_256_checked
theorem ternaryAffineL2ThresholdLower195Floor12Bits128 :
    AffineL2ThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 195, squaredNormFloor := NonnegativeRatio.ofNat 12,
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget 128) :=
  l2 AffineEndpointNumeric.l2_195_12_128 AffineEndpointNumeric.l2_195_12_128_checked
theorem ternaryAffineL2ThresholdLower264Floor29Bits128 :
    AffineL2ThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 264, squaredNormFloor := NonnegativeRatio.ofNat 29,
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget 128) :=
  l2 AffineEndpointNumeric.l2_264_29_128 AffineEndpointNumeric.l2_264_29_128_checked
theorem ternaryAffineL2ThresholdLower394Floor43Bits192 :
    AffineL2ThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 394, squaredNormFloor := NonnegativeRatio.ofNat 43,
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget 192) :=
  l2 AffineEndpointNumeric.l2_394_43_192 AffineEndpointNumeric.l2_394_43_192_checked
theorem ternaryAffineL2ThresholdLower524Floor57Bits256 :
    AffineL2ThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 524, squaredNormFloor := NonnegativeRatio.ofNat 57,
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget 256) :=
  l2 AffineEndpointNumeric.l2_524_57_256 AffineEndpointNumeric.l2_524_57_256_checked

theorem allL2LowerBounds :
    AffineEndpointNumeric.L2EndpointClaim AffineEndpointNumeric.l2_192_11_128 ∧
    AffineEndpointNumeric.L2EndpointClaim AffineEndpointNumeric.l2_256_27_128 ∧
    AffineEndpointNumeric.L2EndpointClaim AffineEndpointNumeric.l2_256_9_194 ∧
    AffineEndpointNumeric.L2EndpointClaim AffineEndpointNumeric.l2_384_40_192 ∧
    AffineEndpointNumeric.L2EndpointClaim AffineEndpointNumeric.l2_512_73_193 ∧
    AffineEndpointNumeric.L2EndpointClaim AffineEndpointNumeric.l2_512_54_256 ∧
    AffineEndpointNumeric.L2EndpointClaim AffineEndpointNumeric.l2_195_12_128 ∧
    AffineEndpointNumeric.L2EndpointClaim AffineEndpointNumeric.l2_264_29_128 ∧
    AffineEndpointNumeric.L2EndpointClaim AffineEndpointNumeric.l2_394_43_192 ∧
    AffineEndpointNumeric.L2EndpointClaim AffineEndpointNumeric.l2_524_57_256 := by
  exact ⟨ternaryAffineL2ThresholdLower192Floor11Bits128,
    ternaryAffineL2ThresholdLower256Floor27Bits128,
    ternaryAffineL2ThresholdLower256Floor9Bits194,
    ternaryAffineL2ThresholdLower384Floor40Bits192,
    ternaryAffineL2ThresholdLower512Floor73Bits193,
    ternaryAffineL2ThresholdLower512Floor54Bits256,
    ternaryAffineL2ThresholdLower195Floor12Bits128,
    ternaryAffineL2ThresholdLower264Floor29Bits128,
    ternaryAffineL2ThresholdLower394Floor43Bits192,
    ternaryAffineL2ThresholdLower524Floor57Bits256⟩

end CertifiedJLFast.Results.Affine.L2.Lower.Endpoints
