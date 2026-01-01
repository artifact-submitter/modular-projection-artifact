/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.Instances.Rows256Bits192Threshold406Soundness
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.Instances.Rows256Bits152Threshold365Soundness
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.Instances.Rows256RescaledFrontierSoundness
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.Instances.Rows192Bits128Threshold287Soundness
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.Instances.Rows384Bits192Threshold509Soundness
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.Instances.Rows512Bits256Threshold681Soundness

/-! # Shared assembly for high-security balanced-ternary upper contours -/

namespace CertifiedJL.CertificateAssembly

open SparseUpperContourFamily

/-- Combine narrow finite endpoint checks with separately proved analytic
soundness to obtain a public modular upper-tail theorem. -/
theorem l2UpperTailAt_of_sparseUpperContourEndpointChecks
    {parameters : Parameters} {lowBoxes : List ProfileBox}
    {highBox : HighProfileBox}
    (profileCover : ProfilePartitionCovers lowBoxes (highBox.profileMinimum : ℝ))
    (lowTargets : ∀ box ∈ lowBoxes, box.target ≤ 1)
    (highTarget : highBox.target ≤ 1)
    (lowSound : ∀ box ∈ lowBoxes, LowProfileBoxSound parameters box)
    (highSound : HighProfileBoxSound parameters highBox)
    (verified : CertificateContracts.SparseL2UpperContourEndpointChecks
      parameters lowBoxes highBox)
    (threshold : NonnegativeRatio)
    (hthreshold : threshold.toReal = (parameters.threshold : ℝ)) :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := parameters.rows
        threshold := threshold }
      (failureTarget parameters.securityBits) := by
  apply l2UpperTailAt_of_checkedCertificate
    { lowBoxes := lowBoxes
      highBox := highBox
      profileCover := profileCover
      lowTargets := lowTargets
      highTarget := highTarget
      lowChecks := verified.1
      highCheck := verified.2
      lowSound := lowSound
      highSound := highSound }
      threshold hthreshold

/-- The endpoint contract implies the 192-row, 128-bit threshold-287 result. -/
theorem ternaryL2Upper287
    (verified : CertificateContracts.SparseL2UpperContourRows192Bits128Threshold287) :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 192
        threshold := NonnegativeRatio.ofNat 287 }
      (failureTarget 128) := by
  simpa [CertificateContracts.SparseL2UpperContourRows192Bits128Threshold287,
    SparseUpperContourFamily.Instances.Rows192Bits128Threshold287.parameters,
    SparseUpperContourFamily.Instances.Rows192Bits128Threshold287Soundness.threshold,
    Parameters.rows, Parameters.securityBits] using
    l2UpperTailAt_of_sparseUpperContourEndpointChecks
      SparseUpperContourFamily.Instances.Rows192Bits128Threshold287Soundness.profileCover
      SparseUpperContourFamily.Instances.Rows192Bits128Threshold287Soundness.lowTargets
      SparseUpperContourFamily.Instances.Rows192Bits128Threshold287Soundness.highTarget
      SparseUpperContourFamily.Instances.Rows192Bits128Threshold287Soundness.lowSound
      SparseUpperContourFamily.Instances.Rows192Bits128Threshold287Soundness.highSound
      verified
      SparseUpperContourFamily.Instances.Rows192Bits128Threshold287Soundness.threshold
      SparseUpperContourFamily.Instances.Rows192Bits128Threshold287Soundness.threshold_eq

/-- The endpoint contract implies the 256-row, 192-bit threshold-406 result. -/
theorem ternaryL2Upper406
    (verified : CertificateContracts.SparseL2UpperContourRows256Bits192Threshold406) :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 256
        threshold := NonnegativeRatio.ofNat 406 }
      (failureTarget 192) := by
  simpa [CertificateContracts.SparseL2UpperContourRows256Bits192Threshold406,
    SparseUpperContourFamily.Instances.Rows256Bits192Threshold406.parameters,
    SparseUpperContourFamily.Instances.Rows256Bits192Threshold406Soundness.threshold,
    Parameters.rows, Parameters.securityBits] using
    l2UpperTailAt_of_sparseUpperContourEndpointChecks
      SparseUpperContourFamily.Instances.Rows256Bits192Threshold406Soundness.profileCover
      SparseUpperContourFamily.Instances.Rows256Bits192Threshold406Soundness.lowTargets
      SparseUpperContourFamily.Instances.Rows256Bits192Threshold406Soundness.highTarget
      SparseUpperContourFamily.Instances.Rows256Bits192Threshold406Soundness.lowSound
      SparseUpperContourFamily.Instances.Rows256Bits192Threshold406Soundness.highSound
      verified
      SparseUpperContourFamily.Instances.Rows256Bits192Threshold406Soundness.threshold
      SparseUpperContourFamily.Instances.Rows256Bits192Threshold406Soundness.threshold_eq

/-- The endpoint contract implies the 256-row, 152-bit threshold-365 result. -/
theorem ternaryL2Upper365
    (verified : CertificateContracts.SparseL2UpperContourRows256Bits152Threshold365) :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 256
        threshold := NonnegativeRatio.ofNat 365 }
      (failureTarget 152) := by
  simpa [CertificateContracts.SparseL2UpperContourRows256Bits152Threshold365,
    SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters,
    SparseUpperContourFamily.Instances.Rows256Bits152Threshold365Soundness.threshold,
    Parameters.rows, Parameters.securityBits] using
    l2UpperTailAt_of_sparseUpperContourEndpointChecks
      SparseUpperContourFamily.Instances.Rows256Bits152Threshold365Soundness.profileCover
      SparseUpperContourFamily.Instances.Rows256Bits152Threshold365Soundness.lowTargets
      SparseUpperContourFamily.Instances.Rows256Bits152Threshold365Soundness.highTarget
      SparseUpperContourFamily.Instances.Rows256Bits152Threshold365Soundness.lowSound
      SparseUpperContourFamily.Instances.Rows256Bits152Threshold365Soundness.highSound
      verified
      SparseUpperContourFamily.Instances.Rows256Bits152Threshold365Soundness.threshold
      SparseUpperContourFamily.Instances.Rows256Bits152Threshold365Soundness.threshold_eq

/-- Assemble one exact rational anchor from the rescaled 256-row frontier. -/
theorem ternaryL2UpperOfRows256RescaledEndpoint
    (endpoint : SparseUpperContourFamily.Instances.Rows256RescaledFrontier.Endpoint)
    (hthreshold : 338 ≤
      (SparseUpperContourFamily.Instances.Rows256RescaledFrontier.parameters endpoint).threshold)
    (verified : CertificateContracts.SparseL2UpperContourRows256RescaledEndpoint endpoint) :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 256
        threshold := endpoint.threshold }
      (failureTarget
        (SparseUpperContourFamily.Instances.Rows256RescaledFrontier.parameters endpoint).securityBits) := by
  let certificate : SparseUpperContourFamily.CheckedCertificate
      (SparseUpperContourFamily.Instances.Rows256RescaledFrontier.parameters endpoint) :=
    { lowBoxes := SparseUpperContourFamily.Instances.Rows256RescaledFrontier.profileBoxes
      highBox := SparseUpperContourFamily.Instances.Rows256RescaledFrontier.highProfile
      profileCover :=
        SparseUpperContourFamily.Instances.Rows256RescaledFrontierSoundness.profileCover
      lowTargets :=
        SparseUpperContourFamily.Instances.Rows256RescaledFrontierSoundness.lowTargets
      highTarget :=
        SparseUpperContourFamily.Instances.Rows256RescaledFrontierSoundness.highTarget
      lowChecks := verified.1
      highCheck := verified.2
      lowSound :=
        SparseUpperContourFamily.Instances.Rows256RescaledFrontierSoundness.lowSound
          endpoint hthreshold
      highSound :=
        SparseUpperContourFamily.Instances.Rows256RescaledFrontierSoundness.highSound
          endpoint (le_trans (by norm_num) hthreshold) }
  simpa [SparseUpperContourFamily.Instances.Rows256RescaledFrontier.rows_eq] using
    SparseUpperContourFamily.l2UpperTailAt_of_checkedCertificate
      certificate endpoint.threshold
      (SparseUpperContourFamily.Instances.Rows256RescaledFrontier.threshold_toReal endpoint)

/-- The endpoint contract implies the 384-row, 192-bit threshold-509 result. -/
theorem ternaryL2Upper509
    (verified : CertificateContracts.SparseL2UpperContourRows384Bits192Threshold509) :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 384
        threshold := NonnegativeRatio.ofNat 509 }
      (failureTarget 192) := by
  simpa [CertificateContracts.SparseL2UpperContourRows384Bits192Threshold509,
    SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters,
    SparseUpperContourFamily.Instances.Rows384Bits192Threshold509Soundness.threshold,
    Parameters.rows, Parameters.securityBits] using
    l2UpperTailAt_of_sparseUpperContourEndpointChecks
      SparseUpperContourFamily.Instances.Rows384Bits192Threshold509Soundness.profileCover
      SparseUpperContourFamily.Instances.Rows384Bits192Threshold509Soundness.lowTargets
      SparseUpperContourFamily.Instances.Rows384Bits192Threshold509Soundness.highTarget
      SparseUpperContourFamily.Instances.Rows384Bits192Threshold509Soundness.lowSound
      SparseUpperContourFamily.Instances.Rows384Bits192Threshold509Soundness.highSound
      verified
      SparseUpperContourFamily.Instances.Rows384Bits192Threshold509Soundness.threshold
      SparseUpperContourFamily.Instances.Rows384Bits192Threshold509Soundness.threshold_eq

/-- The endpoint contract implies the 512-row, 256-bit threshold-681 result. -/
theorem ternaryL2Upper681
    (verified : CertificateContracts.SparseL2UpperContourRows512Bits256Threshold681) :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 512
        threshold := NonnegativeRatio.ofNat 681 }
      (failureTarget 256) := by
  simpa [CertificateContracts.SparseL2UpperContourRows512Bits256Threshold681,
    SparseUpperContourFamily.Instances.Rows512Bits256Threshold681.parameters,
    SparseUpperContourFamily.Instances.Rows512Bits256Threshold681Soundness.threshold,
    Parameters.rows, Parameters.securityBits] using
    l2UpperTailAt_of_sparseUpperContourEndpointChecks
      SparseUpperContourFamily.Instances.Rows512Bits256Threshold681Soundness.profileCover
      SparseUpperContourFamily.Instances.Rows512Bits256Threshold681Soundness.lowTargets
      SparseUpperContourFamily.Instances.Rows512Bits256Threshold681Soundness.highTarget
      SparseUpperContourFamily.Instances.Rows512Bits256Threshold681Soundness.lowSound
      SparseUpperContourFamily.Instances.Rows512Bits256Threshold681Soundness.highSound
      verified
      SparseUpperContourFamily.Instances.Rows512Bits256Threshold681Soundness.threshold
      SparseUpperContourFamily.Instances.Rows512Bits256Threshold681Soundness.threshold_eq

end CertifiedJL.CertificateAssembly
