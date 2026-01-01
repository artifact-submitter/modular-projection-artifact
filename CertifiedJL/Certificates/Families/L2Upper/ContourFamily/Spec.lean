/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits192Threshold406
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256Bits152Threshold365
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256RescaledFrontier
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows384Bits192Threshold509
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows512Bits256Threshold681

/-! # Semantic contracts for the high-security upper-contour family -/

namespace CertifiedJL.CertificateContracts

open SparseUpperContourFamily

/-- The narrow finite certificate boundary shared by the parameterized
upper-contour family.  Analytic soundness remains outside this contract. -/
def SparseL2UpperContourEndpointChecks
    (parameters : Parameters) (lowBoxes : List ProfileBox)
    (highBox : HighProfileBox) : Prop :=
  allBoxesCheck parameters lowBoxes = true ∧
    highProfileCheck parameters highBox = true

/-- Exact endpoint checks for 192 rows, 128 bits, and threshold 287. -/
def SparseL2UpperContourRows192Bits128Threshold287 : Prop :=
  SparseL2UpperContourEndpointChecks
    SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters
    SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.profileBoxes
    SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.highProfile

/-- Exact endpoint checks for 256 rows, 192 bits, and threshold 406. -/
def SparseL2UpperContourRows256Bits192Threshold406 : Prop :=
  SparseL2UpperContourEndpointChecks
    SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters
    SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.profileBoxes
    SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.highProfile

/-- Exact endpoint checks for 256 rows, 152 bits, and threshold 365. -/
def SparseL2UpperContourRows256Bits152Threshold365 : Prop :=
  SparseL2UpperContourEndpointChecks
    SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters
    SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes
    SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.highProfile

/-- Exact endpoint checks for one member of the rescaled 256-row frontier. -/
def SparseL2UpperContourRows256RescaledEndpoint
    (endpoint : SparseUpperContourFamily.Instances.Rows256RescaledFrontier.Endpoint) : Prop :=
  SparseL2UpperContourEndpointChecks
    (SparseUpperContourFamily.Instances.Rows256RescaledFrontier.parameters endpoint)
    SparseUpperContourFamily.Instances.Rows256RescaledFrontier.profileBoxes
    SparseUpperContourFamily.Instances.Rows256RescaledFrontier.highProfile

/-- Exact endpoint checks for every certified rational 256-row frontier anchor. -/
def SparseL2UpperContourRows256RescaledFrontier : Prop :=
  ∀ endpoint ∈
      SparseUpperContourFamily.Instances.Rows256RescaledFrontier.certifiedEndpoints,
    SparseL2UpperContourRows256RescaledEndpoint endpoint

/-- Exact endpoint checks for 384 rows, 192 bits, and threshold 509. -/
def SparseL2UpperContourRows384Bits192Threshold509 : Prop :=
  SparseL2UpperContourEndpointChecks
    SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters
    SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes
    SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.highProfile

/-- Exact endpoint checks for 512 rows, 256 bits, and threshold 681. -/
def SparseL2UpperContourRows512Bits256Threshold681 : Prop :=
  SparseL2UpperContourEndpointChecks
    SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters
    SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.profileBoxes
    SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.highProfile

end CertifiedJL.CertificateContracts
