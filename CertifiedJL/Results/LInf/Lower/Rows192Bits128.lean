/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Results.LInf.Lower.TwoDecimal

/-! # Certified 192-row balanced-ternary modular tails -/

namespace CertifiedJL.Results.LInf.Lower.Rows192Bits128

/-- Balanced-ternary strict threshold-relative `L∞` lower tail at coordinate
cap `0.34`, proved at 129 bits under `b² ≤ ‖w‖₂²` and `2b ≤ q`. -/
theorem ternaryLInfThresholdLower17Over50 :
    LInfThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 192
        coordinateCap :=
          { numerator := 17, denominator := 50, denominator_pos := by decide }
        modulusMargin := NonnegativeRatio.ofNat 2 }
      (failureTarget 129) :=
  CertifiedJL.Results.LInf.Lower.TwoDecimal.lower17Over50Rows192Bits129

end CertifiedJL.Results.LInf.Lower.Rows192Bits128
