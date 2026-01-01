/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Assembly
import CertifiedJLFast.Assumptions.Families.L2Upper.ContourFamily

/-! # Assumption-backed 512-row, 256-bit upper specialization -/

namespace CertifiedJLFast.Results.L2.Upper.Rows512Bits256

/-- Assumption-backed balanced-ternary modular `L₂` upper tail at threshold `681`. -/
theorem ternaryL2Upper681 :
    CertifiedJL.L2UpperTailAt
      { distribution := .balancedTernary
        rows := 512
        threshold := CertifiedJL.NonnegativeRatio.ofNat 681 }
      (CertifiedJL.failureTarget 256) :=
  CertifiedJL.CertificateAssembly.ternaryL2Upper681
    Assumptions.sparse_l2_upper_contour_rows512_bits256_threshold681_assumed

end CertifiedJLFast.Results.L2.Upper.Rows512Bits256
