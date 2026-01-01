/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Assembly
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Instances.Rows256Bits152.Provider

/-! # Certified 256-row balanced-ternary modular tails at 152 bits -/

namespace CertifiedJL.Results.L2.Upper.Rows256Bits152

/-- Balanced-ternary modular `L₂` upper tail at threshold `365`. -/
theorem ternaryL2Upper365 :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 256
        threshold := NonnegativeRatio.ofNat 365 }
      (failureTarget 152) :=
  CertificateAssembly.ternaryL2Upper365
    CertificateProviders.sparseL2UpperContourRows256Bits152Threshold365_verified

end CertifiedJL.Results.L2.Upper.Rows256Bits152
