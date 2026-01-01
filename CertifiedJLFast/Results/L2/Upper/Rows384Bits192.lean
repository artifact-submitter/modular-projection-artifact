/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Assembly
import CertifiedJLFast.Assumptions.Families.L2Upper.ContourFamily

/-! # Assumption-backed 384-row result specializations -/

namespace CertifiedJLFast.Results.L2.Upper.Rows384Bits192

/-- Assumption-backed balanced-ternary modular `L₂` upper tail at threshold `509`. -/
theorem ternaryL2Upper509 :
    CertifiedJL.L2UpperTailAt
      { distribution := .balancedTernary
        rows := 384
        threshold := CertifiedJL.NonnegativeRatio.ofNat 509 }
      (CertifiedJL.failureTarget 192) :=
  CertifiedJL.CertificateAssembly.ternaryL2Upper509
    Assumptions.sparse_l2_upper_contour_rows384_bits192_threshold509_assumed

end CertifiedJLFast.Results.L2.Upper.Rows384Bits192
