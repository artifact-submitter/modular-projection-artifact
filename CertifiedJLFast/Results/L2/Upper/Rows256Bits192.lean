/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Assembly
import CertifiedJLFast.Assumptions.Families.L2Upper.ContourFamily

/-! # Assumption-backed 256-row, 192-bit specializations -/

namespace CertifiedJLFast.Results.L2.Upper.Rows256Bits192

/-- Assumption-backed balanced-ternary modular `L₂` upper tail at threshold `406`. -/
theorem ternaryL2Upper406 :
    CertifiedJL.L2UpperTailAt
      { distribution := .balancedTernary
        rows := 256
        threshold := CertifiedJL.NonnegativeRatio.ofNat 406 }
      (CertifiedJL.failureTarget 192) :=
  CertifiedJL.CertificateAssembly.ternaryL2Upper406
    Assumptions.sparse_l2_upper_contour_rows256_bits192_threshold406_assumed

end CertifiedJLFast.Results.L2.Upper.Rows256Bits192
