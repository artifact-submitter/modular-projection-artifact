/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.Affine.Assembly.AffineEndpoints

/-! # Proof-only canaries for the exact affine endpoint inventory -/

open CertifiedJL

example : AffineEndpointNumeric.l2Endpoints.length = 10 := by decide
example : AffineEndpointNumeric.lInfEndpoints.length = 9 := by decide

example := AffineEndpointNumeric.l2Endpoints_coverage
example := AffineEndpointNumeric.lInfEndpoints_coverage
example := AffineEndpointNumeric.l2Endpoints_all_checked
example := AffineEndpointNumeric.lInfEndpoints_all_checked

example := AffineEndpointNumeric.l2EndpointCheck_sound
example := AffineEndpointNumeric.lInfEndpointCheck_sound
example := CertificateAssembly.affineL2Endpoint
example := CertificateAssembly.affineLInfEndpoint

-- The exact replacement endpoint uses 264 rows. No 256-row floor-29 claim is
-- silently introduced by the inventory.
example : (AffineEndpointNumeric.l2_264_29_128.rows,
    AffineEndpointNumeric.l2_264_29_128.squaredNormFloor,
    AffineEndpointNumeric.l2_264_29_128.bits) = (264, 29, 128) := by decide

-- The only L-infinity endpoint selecting the `5/2, 539/1000` provider.
example : (AffineEndpointNumeric.lInf_512_46_125_206.diffuseTilt,
    AffineEndpointNumeric.lInf_512_46_125_206.diffuseCap) =
      (5 / 2, 539 / 1000) := by
  norm_num [AffineEndpointNumeric.lInf_512_46_125_206]
