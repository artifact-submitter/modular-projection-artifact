/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Assembly
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Instances.Rows192Bits128.Provider

/-! # Certified 192-row balanced-ternary modular tails -/

namespace CertifiedJL.Results.L2.Upper.Rows192Bits128

/-- Balanced-ternary modular `L₂` upper tail at threshold `287`. -/
theorem ternaryL2Upper287 :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 192
        threshold := NonnegativeRatio.ofNat 287 }
      (failureTarget 128) :=
  CertificateAssembly.ternaryL2Upper287
    CertificateProviders.sparseL2UpperContourRows192Bits128Threshold287_verified

end CertifiedJL.Results.L2.Upper.Rows192Bits128
