/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Assembly
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Instances.Rows256Bits192.Provider

/-! # Certified 256-row balanced-ternary modular tails at 192 bits -/

namespace CertifiedJL.Results.L2.Upper.Rows256Bits192

/-- Balanced-ternary modular `L₂` upper tail at threshold `406`. -/
theorem ternaryL2Upper406 :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 256
        threshold := NonnegativeRatio.ofNat 406 }
      (failureTarget 192) :=
  CertificateAssembly.ternaryL2Upper406
    CertificateProviders.sparseL2UpperContourRows256Bits192Threshold406_verified

end CertifiedJL.Results.L2.Upper.Rows256Bits192
