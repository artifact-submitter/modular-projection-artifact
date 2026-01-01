/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJLFast.Results.LInf.Lower.TwoDecimal

/-! # Assumption-backed 192-row specializations -/

namespace CertifiedJLFast.Results.LInf.Lower.Rows192Bits128

open scoped ENNReal

/-- Assumption-backed `17/50` threshold-relative `L∞` lower tail at 129 bits. -/
theorem ternaryLInfThresholdLower17Over50 :
    CertifiedJL.LInfThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 192
        coordinateCap :=
          { numerator := 17, denominator := 50, denominator_pos := by decide }
        modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 2 }
      (CertifiedJL.failureTarget 129) :=
  CertifiedJLFast.Results.LInf.Lower.TwoDecimal.lower17Over50Rows192Bits129

end CertifiedJLFast.Results.LInf.Lower.Rows192Bits128
