/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.Soundness
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.Instances.Rows384Bits192Threshold509Soundness
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509.Verified

/-! Checked numeric and analytic assembly for one upper-contour instance. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509.Certificate

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

def checkedCertificate : CheckedCertificate CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters where
  lowBoxes := CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.profileBoxes
  highBox := CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.highProfile
  profileCover := CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509Soundness.profileCover
  lowTargets := CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509Soundness.lowTargets
  highTarget := CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509Soundness.highTarget
  lowChecks := CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509.Verified.allBoxesCheck_eq_true
  highCheck := CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509.Verified.highProfileCheck_eq_true
  lowSound := CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509Soundness.lowSound
  highSound := CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509Soundness.highSound

theorem normalizedUpperTail :
    NormalizedUpperTailAt CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters :=
  normalizedUpperTail_of_checkedCertificate checkedCertificate

theorem l2UpperTail :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := (CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters).rows
        threshold := CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509Soundness.threshold }
      (failureTarget (CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509.parameters).securityBits) :=
  l2UpperTailAt_of_checkedCertificate checkedCertificate
    CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509Soundness.threshold CertifiedJL.SparseUpperContourFamily.Instances.Rows384Bits192Threshold509Soundness.threshold_eq

end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows384Bits192Threshold509.Certificate
