/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Assembly
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Instances.Rows384Bits192.Provider

/-! # Certified 384-row balanced-ternary modular tails at 192 bits -/

namespace CertifiedJL.Results.L2.Upper.Rows384Bits192

/-- Balanced-ternary modular `L₂` upper tail at threshold `509`. -/
theorem ternaryL2Upper509 :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 384
        threshold := NonnegativeRatio.ofNat 509 }
      (failureTarget 192) :=
  CertificateAssembly.ternaryL2Upper509
    CertificateProviders.sparseL2UpperContourRows384Bits192Threshold509_verified

end CertifiedJL.Results.L2.Upper.Rows384Bits192
