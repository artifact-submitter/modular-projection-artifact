/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.Affine.Assembly.RatioL2Endpoint
import CertifiedJL.Certificates.Families.L2Lower.Shared.Providers.NearVerified
import CertifiedJL.Certificates.Families.L2Lower.Shared.Providers.DiffuseVerified
import CertifiedJL.Certificates.Families.L2Lower.Shared.Providers.DiffuseFloor73Verified

/-! # Certified 256-row balanced-ternary lower frontier through 152 bits

All endpoints use singleton tilt `5/2`, the exact rational row cap
`545333/1000000`, and the shared diffuse profile at tilt `33/10` with cap
`97/200`. The stronger affine theorem is assembled first; each public result
then specializes its pre-sampled row shift to zero.
-/

namespace CertifiedJL.Results.L2.Lower.Rows256Bits152

open AffineRatioEndpointNumeric

private def endpoint (numerator denominator bits : ℕ) : L2EndpointData :=
  ⟨256, numerator, denominator, bits,
    5 / 2, 545333 / 1000000, 33 / 10, 97 / 200⟩

def floor79Over4Bits152 : L2EndpointData := endpoint 79 4 152
def floor20Bits151 : L2EndpointData := endpoint 20 1 151
def floor41Over2Bits150 : L2EndpointData := endpoint 41 2 150
def floor83Over4Bits149 : L2EndpointData := endpoint 83 4 149
def floor21Bits148 : L2EndpointData := endpoint 21 1 148
def floor85Over4Bits147 : L2EndpointData := endpoint 85 4 147
def floor43Over2Bits146 : L2EndpointData := endpoint 43 2 146
def floor87Over4Bits145 : L2EndpointData := endpoint 87 4 145
def floor22Bits144 : L2EndpointData := endpoint 22 1 144

/-- Machine-readable exact endpoint frontier, ordered by decreasing security
target and increasing squared-norm floor. -/
def frontier : List L2EndpointData :=
  [floor79Over4Bits152, floor20Bits151, floor41Over2Bits150,
    floor83Over4Bits149, floor21Bits148, floor85Over4Bits147,
    floor43Over2Bits146, floor87Over4Bits145, floor22Bits144]

set_option maxRecDepth 100000 in
/-- Every advertised endpoint passes the exact interval checker. -/
theorem frontier_all_checked : frontier.all endpointCheck = true := by
  decide +kernel

private theorem endpoint_checked {e : L2EndpointData} (hmem : e ∈ frontier) :
    endpointCheck e = true := by
  have hall := frontier_all_checked
  rw [List.all_eq_true] at hall
  exact hall e hmem

private theorem profiles : CertificateAssembly.AffineL2WrappedProfiles :=
  CertificateAssembly.affineL2General_profiles
    CertificateProviders.sparseL2ThresholdNearCoarseCover128_verified
    CertificateProviders.sparseL2ThresholdNearEndpoints128_verified
    CertificateProviders.sparseL2ThresholdNearCurvature128_verified
    CertificateProviders.sparseL2ThresholdDiffuseLowScalar128_verified
    CertificateProviders.sparseL2ThresholdDiffuseLowModularTail128_verified
    CertificateProviders.sparseL2ThresholdDiffuseHighEndpoints128_verified
    CertificateProviders.sparseL2ThresholdDiffuseFloor73Endpoints_verified

private theorem lower (e : L2EndpointData) (hden : 0 < e.floorDenominator)
    (hcheck : endpointCheck e = true) :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := e.rows
        squaredNormFloor := floorRatio e hden
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget e.bits) :=
  (CertificateAssembly.affineL2RatioEndpoint e hden profiles hcheck).to_unshifted

theorem ternaryL2ThresholdLower79Over4Bits152 :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 256
        squaredNormFloor := ⟨79, 4, by decide⟩
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 152) := by
  simpa [floor79Over4Bits152, endpoint, floorRatio] using
    lower floor79Over4Bits152 (by decide)
      (endpoint_checked (by simp [frontier]))

theorem ternaryL2ThresholdLower20Bits151 :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 256
        squaredNormFloor := NonnegativeRatio.ofNat 20
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 151) := by
  simpa [floor20Bits151, endpoint, floorRatio, NonnegativeRatio.ofNat] using
    lower floor20Bits151 (by decide)
      (endpoint_checked (by simp [frontier]))

theorem ternaryL2ThresholdLower41Over2Bits150 :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 256
        squaredNormFloor := ⟨41, 2, by decide⟩
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 150) := by
  simpa [floor41Over2Bits150, endpoint, floorRatio] using
    lower floor41Over2Bits150 (by decide)
      (endpoint_checked (by simp [frontier]))

theorem ternaryL2ThresholdLower83Over4Bits149 :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 256
        squaredNormFloor := ⟨83, 4, by decide⟩
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 149) := by
  simpa [floor83Over4Bits149, endpoint, floorRatio] using
    lower floor83Over4Bits149 (by decide)
      (endpoint_checked (by simp [frontier]))

theorem ternaryL2ThresholdLower21Bits148 :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 256
        squaredNormFloor := NonnegativeRatio.ofNat 21
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 148) := by
  simpa [floor21Bits148, endpoint, floorRatio, NonnegativeRatio.ofNat] using
    lower floor21Bits148 (by decide)
      (endpoint_checked (by simp [frontier]))

theorem ternaryL2ThresholdLower85Over4Bits147 :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 256
        squaredNormFloor := ⟨85, 4, by decide⟩
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 147) := by
  simpa [floor85Over4Bits147, endpoint, floorRatio] using
    lower floor85Over4Bits147 (by decide)
      (endpoint_checked (by simp [frontier]))

theorem ternaryL2ThresholdLower43Over2Bits146 :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 256
        squaredNormFloor := ⟨43, 2, by decide⟩
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 146) := by
  simpa [floor43Over2Bits146, endpoint, floorRatio] using
    lower floor43Over2Bits146 (by decide)
      (endpoint_checked (by simp [frontier]))

theorem ternaryL2ThresholdLower87Over4Bits145 :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 256
        squaredNormFloor := ⟨87, 4, by decide⟩
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 145) := by
  simpa [floor87Over4Bits145, endpoint, floorRatio] using
    lower floor87Over4Bits145 (by decide)
      (endpoint_checked (by simp [frontier]))

theorem ternaryL2ThresholdLower22Bits144 :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 256
        squaredNormFloor := NonnegativeRatio.ofNat 22
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 144) := by
  simpa [floor22Bits144, endpoint, floorRatio, NonnegativeRatio.ofNat] using
    lower floor22Bits144 (by decide)
      (endpoint_checked (by simp [frontier]))

end CertifiedJL.Results.L2.Lower.Rows256Bits152
