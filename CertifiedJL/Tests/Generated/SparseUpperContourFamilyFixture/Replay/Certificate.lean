/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.Soundness
import CertifiedJL.Tests.SparseUpperContourFamilyFixtureSoundness
import CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.Verified

/-! Checked numeric and analytic assembly for one upper-contour instance. -/

namespace CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.Certificate

open CertifiedJL.SparseUpperContourFamily

set_option linter.style.longLine false

def checkedCertificate : CheckedCertificate CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters where
  lowBoxes := CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes
  highBox := CertifiedJL.Tests.SparseUpperContourFamilyFixture.highProfile
  profileCover := CertifiedJL.Tests.SparseUpperContourFamilyFixtureSoundness.profileCover
  lowTargets := CertifiedJL.Tests.SparseUpperContourFamilyFixtureSoundness.lowTargets
  highTarget := CertifiedJL.Tests.SparseUpperContourFamilyFixtureSoundness.highTarget
  lowChecks := CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.Verified.allBoxesCheck_eq_true
  highCheck := CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.Verified.highProfileCheck_eq_true
  lowSound := CertifiedJL.Tests.SparseUpperContourFamilyFixtureSoundness.lowSound
  highSound := CertifiedJL.Tests.SparseUpperContourFamilyFixtureSoundness.highSound

theorem normalizedUpperTail :
    NormalizedUpperTailAt CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters :=
  normalizedUpperTail_of_checkedCertificate checkedCertificate

theorem l2UpperTail :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := (CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters).rows
        threshold := CertifiedJL.Tests.SparseUpperContourFamilyFixtureSoundness.threshold }
      (failureTarget (CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters).securityBits) :=
  l2UpperTailAt_of_checkedCertificate checkedCertificate
    CertifiedJL.Tests.SparseUpperContourFamilyFixtureSoundness.threshold CertifiedJL.Tests.SparseUpperContourFamilyFixtureSoundness.threshold_eq

end CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.Certificate
