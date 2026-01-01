/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Assembly
import CertifiedJLFast.Assumptions.Families.L2Upper.ContourFamily

/-! # Assumption-backed 192-row specializations -/

namespace CertifiedJLFast.Results.L2.Upper.Rows192Bits128

open scoped ENNReal

/-- Assumption-backed balanced-ternary modular `L₂` upper tail at threshold `287`. -/
theorem ternaryL2Upper287 :
    CertifiedJL.L2UpperTailAt
      { distribution := .balancedTernary
        rows := 192
        threshold := CertifiedJL.NonnegativeRatio.ofNat 287 }
      (CertifiedJL.failureTarget 128) :=
  CertifiedJL.CertificateAssembly.ternaryL2Upper287
    Assumptions.sparse_l2_upper_contour_rows192_bits128_threshold287_assumed

end CertifiedJLFast.Results.L2.Upper.Rows192Bits128
