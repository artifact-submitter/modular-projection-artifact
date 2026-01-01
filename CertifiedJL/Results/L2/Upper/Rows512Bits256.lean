/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Assembly
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Instances.Rows512Bits256.Provider

/-! # Certified 512-row balanced-ternary modular tails at 256 bits -/

namespace CertifiedJL.Results.L2.Upper.Rows512Bits256

/-- Balanced-ternary modular `L₂` upper tail at threshold `681`. -/
theorem ternaryL2Upper681 :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 512
        threshold := NonnegativeRatio.ofNat 681 }
      (failureTarget 256) :=
  CertificateAssembly.ternaryL2Upper681
    CertificateProviders.sparseL2UpperContourRows512Bits256Threshold681_verified

end CertifiedJL.Results.L2.Upper.Rows512Bits256
