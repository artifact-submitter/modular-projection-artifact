/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.Affine.Assembly.AffineEndpoints
import CertifiedJL.Certificates.Families.L2Lower.Shared.Providers.NearVerified
import CertifiedJL.Certificates.Families.L2Lower.Shared.Providers.DiffuseVerified
import CertifiedJL.Certificates.Families.L2Lower.Shared.Providers.DiffuseFloor73Verified
import CertifiedJL.Results.Affine.LInf.Lower.Direct

/-! # Exact affine lower-tail endpoint family at modulus margin three -/

namespace CertifiedJL.Results.Affine.LInf.Lower.Endpoints

open CertifiedJL

private theorem diffuse33 : SparseThresholdDiffuseWrappedRowBoundAt (33 / 10) (97 / 200) :=
  sparseThresholdDiffuseWrappedRowBound_marginThree_of_replay
    CertificateProviders.sparseL2ThresholdDiffuseLowScalar128_verified
    CertificateProviders.sparseL2ThresholdDiffuseLowModularTail128_verified
    CertificateProviders.sparseL2ThresholdDiffuseHighEndpoints128_verified

private theorem diffuse25 : SparseThresholdDiffuseWrappedRowBoundAt (5 / 2) (539 / 1000) :=
  ThresholdDiffuseFloor73.wrappedRowBound_marginThree_of_replay
    CertificateProviders.sparseL2ThresholdDiffuseFloor73Endpoints_verified

private theorem linf (e : AffineEndpointNumeric.LInfEndpointData)
    (hden : 0 < e.capDenominator)
    (hwrapped : SparseThresholdDiffuseWrappedRowBoundAt e.diffuseTilt e.diffuseCap)
    (ht : (0 : ℝ) < e.diffuseTilt) (hK : (0 : ℝ) ≤ e.diffuseCap)
    (h : AffineEndpointNumeric.lInfEndpointCheck e = true) :
    AffineEndpointNumeric.LInfEndpointClaim e hden :=
  CertificateAssembly.affineLInfEndpoint e hden hwrapped ht hK h

theorem ternaryAffineLInfThresholdLower192Cap279Over1000Bits129 :
    AffineLInfThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 192,
        coordinateCap := { numerator := 279, denominator := 1000, denominator_pos := by decide },
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget 129) :=
  linf AffineEndpointNumeric.lInf_192_279_1000_129 (by decide)
    (by simpa [AffineEndpointNumeric.lInf_192_279_1000_129] using diffuse33)
    (by norm_num) (by norm_num) AffineEndpointNumeric.lInf_192_279_1000_129_checked
theorem ternaryAffineLInfThresholdLower256Cap331Over1000Bits133 :
    AffineLInfThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 256,
        coordinateCap := { numerator := 331, denominator := 1000, denominator_pos := by decide },
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget 133) :=
  linf AffineEndpointNumeric.lInf_256_331_1000_133 (by decide)
    (by simpa [AffineEndpointNumeric.lInf_256_331_1000_133] using diffuse33)
    (by norm_num) (by norm_num) AffineEndpointNumeric.lInf_256_331_1000_133_checked
theorem ternaryAffineLInfThresholdLower384Cap331Over1000Bits200 :
    AffineLInfThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 384,
        coordinateCap := { numerator := 331, denominator := 1000, denominator_pos := by decide },
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget 200) :=
  linf AffineEndpointNumeric.lInf_384_331_1000_200 (by decide)
    (by simpa [AffineEndpointNumeric.lInf_384_331_1000_200] using diffuse33)
    (by norm_num) (by norm_num) AffineEndpointNumeric.lInf_384_331_1000_200_checked
theorem ternaryAffineLInfThresholdLower512Cap331Over1000Bits266 :
    AffineLInfThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 512,
        coordinateCap := { numerator := 331, denominator := 1000, denominator_pos := by decide },
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget 266) :=
  linf AffineEndpointNumeric.lInf_512_331_1000_266 (by decide)
    (by simpa [AffineEndpointNumeric.lInf_512_331_1000_266] using diffuse33)
    (by norm_num) (by norm_num) AffineEndpointNumeric.lInf_512_331_1000_266_checked
theorem ternaryAffineLInfThresholdLower512Cap46Over125Bits206 :
    AffineLInfThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 512,
        coordinateCap := { numerator := 46, denominator := 125, denominator_pos := by decide },
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget 206) :=
  linf AffineEndpointNumeric.lInf_512_46_125_206 (by decide)
    (by simpa [AffineEndpointNumeric.lInf_512_46_125_206] using diffuse25)
    (by norm_num) (by norm_num) AffineEndpointNumeric.lInf_512_46_125_206_checked
theorem ternaryAffineLInfThresholdLower256Cap9Over25Bits109 :
    AffineLInfThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 256,
        coordinateCap := { numerator := 9, denominator := 25, denominator_pos := by decide },
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget 109) :=
  linf AffineEndpointNumeric.lInf_256_9_25_109 (by decide)
    (by simpa [AffineEndpointNumeric.lInf_256_9_25_109] using diffuse33)
    (by norm_num) (by norm_num) AffineEndpointNumeric.lInf_256_9_25_109_checked
theorem ternaryAffineLInfThresholdLower462Cap9Over25Bits197 :
    AffineLInfThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 462,
        coordinateCap := { numerator := 9, denominator := 25, denominator_pos := by decide },
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget 197) :=
  linf AffineEndpointNumeric.lInf_462_9_25_197 (by decide)
    (by simpa [AffineEndpointNumeric.lInf_462_9_25_197] using diffuse33)
    (by norm_num) (by norm_num) AffineEndpointNumeric.lInf_462_9_25_197_checked

/-- The complete nine-member affine infinity endpoint family, including the
two previously published direct endpoints. -/
theorem allLInfLowerBounds :
    AffineEndpointNumeric.LInfEndpointClaim AffineEndpointNumeric.lInf_192_279_1000_129 (by decide) ∧
    AffineEndpointNumeric.LInfEndpointClaim AffineEndpointNumeric.lInf_256_6_25_197 (by decide) ∧
    AffineEndpointNumeric.LInfEndpointClaim AffineEndpointNumeric.lInf_256_331_1000_133 (by decide) ∧
    AffineEndpointNumeric.LInfEndpointClaim AffineEndpointNumeric.lInf_384_331_1000_200 (by decide) ∧
    AffineEndpointNumeric.LInfEndpointClaim AffineEndpointNumeric.lInf_512_331_1000_266 (by decide) ∧
    AffineEndpointNumeric.LInfEndpointClaim AffineEndpointNumeric.lInf_512_46_125_206 (by decide) ∧
    AffineEndpointNumeric.LInfEndpointClaim AffineEndpointNumeric.lInf_256_67_200_130 (by decide) ∧
    AffineEndpointNumeric.LInfEndpointClaim AffineEndpointNumeric.lInf_256_9_25_109 (by decide) ∧
    AffineEndpointNumeric.LInfEndpointClaim AffineEndpointNumeric.lInf_462_9_25_197 (by decide) := by
  exact ⟨ternaryAffineLInfThresholdLower192Cap279Over1000Bits129,
    Direct.ternaryAffineLInfThresholdLower256Cap6Over25Bits197,
    ternaryAffineLInfThresholdLower256Cap331Over1000Bits133,
    ternaryAffineLInfThresholdLower384Cap331Over1000Bits200,
    ternaryAffineLInfThresholdLower512Cap331Over1000Bits266,
    ternaryAffineLInfThresholdLower512Cap46Over125Bits206,
    Direct.ternaryAffineLInfThresholdLower256Cap67Over200Bits130,
    ternaryAffineLInfThresholdLower256Cap9Over25Bits109,
    ternaryAffineLInfThresholdLower462Cap9Over25Bits197⟩

end CertifiedJL.Results.Affine.LInf.Lower.Endpoints
