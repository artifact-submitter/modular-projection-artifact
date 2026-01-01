/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.Affine.Soundness.EndpointNumeric
import CertifiedJL.Certificates.Families.Affine.Spec.EndpointClaims
import CertifiedJL.Certificates.Families.Affine.Assembly.AffineL2General
import CertifiedJL.Projection.LInf.Lower.BalancedTernary.Affine

/-! # Certificate assembly for the exact affine endpoint inventory -/

namespace CertifiedJL.CertificateAssembly

/-- A checked L2 record and the seven shared wrapped-profile contracts assemble
to the exact public threshold statement. -/
theorem affineL2Endpoint (e : AffineEndpointNumeric.L2EndpointData)
    (profiles : AffineL2WrappedProfiles)
    (hcheck : AffineEndpointNumeric.l2EndpointCheck e = true) :
    AffineL2ThresholdLowerTailAt
      { distribution := .balancedTernary, rows := e.rows,
        squaredNormFloor := NonnegativeRatio.ofNat e.squaredNormFloor,
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget e.bits) := by
  have h := AffineEndpointNumeric.l2EndpointCheck_sound e hcheck
  apply ternaryAffineL2ThresholdLowerTailAt_of_finiteTilt_lt_failureTarget
    e.rows e.bits (NonnegativeRatio.ofNat e.squaredNormFloor) e.singletonTilt
      h.1 profiles.near profiles.diffuse33 profiles.diffuse25
  simpa [NonnegativeRatio.ofNat, NonnegativeRatio.toReal] using h.2

/-- A checked L-infinity record and the selected wrapped diffuse-row contract
assemble to the exact public threshold statement. -/
theorem affineLInfEndpoint (e : AffineEndpointNumeric.LInfEndpointData)
    (hden : 0 < e.capDenominator)
    (hwrapped : SparseThresholdDiffuseWrappedRowBoundAt e.diffuseTilt e.diffuseCap)
    (ht : (0 : ℝ) < e.diffuseTilt) (hK : (0 : ℝ) ≤ e.diffuseCap)
    (hcheck : AffineEndpointNumeric.lInfEndpointCheck e = true) :
    AffineLInfThresholdLowerTailAt
      { distribution := .balancedTernary, rows := e.rows,
        coordinateCap := AffineEndpointNumeric.lInfCoordinateCap e hden,
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget e.bits) := by
  have h := AffineEndpointNumeric.lInfEndpointCheck_sound e hcheck
  apply ternaryAffineLInfThresholdLowerTail_of_wrappedRowBound
    e.rows e.bits
      (AffineEndpointNumeric.lInfCoordinateCap e hden)
      e.diffuseTilt e.diffuseCap hwrapped h.2.1 ht hK h.2.2.1
  exact h.2.2.2

end CertifiedJL.CertificateAssembly
