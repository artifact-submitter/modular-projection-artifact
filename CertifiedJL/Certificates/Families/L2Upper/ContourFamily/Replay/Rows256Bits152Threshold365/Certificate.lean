/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.Soundness
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.Instances.Rows256Bits152Threshold365Soundness
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365.Verified

/-! Checked numeric and analytic assembly for one upper-contour instance. -/

namespace CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365.Certificate

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

def checkedCertificate : CheckedCertificate CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters where
  lowBoxes := CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.profileBoxes
  highBox := CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.highProfile
  profileCover := CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365Soundness.profileCover
  lowTargets := CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365Soundness.lowTargets
  highTarget := CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365Soundness.highTarget
  lowChecks := CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365.Verified.allBoxesCheck_eq_true
  highCheck := CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365.Verified.highProfileCheck_eq_true
  lowSound := CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365Soundness.lowSound
  highSound := CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365Soundness.highSound

theorem normalizedUpperTail :
    NormalizedUpperTailAt CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters :=
  normalizedUpperTail_of_checkedCertificate checkedCertificate

theorem l2UpperTail :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := (CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters).rows
        threshold := CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365Soundness.threshold }
      (failureTarget (CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365.parameters).securityBits) :=
  l2UpperTailAt_of_checkedCertificate checkedCertificate
    CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365Soundness.threshold CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365Soundness.threshold_eq

end CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Replay.Rows256Bits152Threshold365.Certificate
