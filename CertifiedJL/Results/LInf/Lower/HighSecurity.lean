/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Results.LInf.Lower.TwoDecimal

/-! # Aggregate high-security modular infinity-norm results -/

namespace CertifiedJL.Results.LInf.Lower.HighSecurity

/-- The sharp two-decimal threshold-relative infinity lower-tail frontier. -/
theorem allThresholdLowerBounds :
    LInfThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 256
          coordinateCap :=
            { numerator := 6, denominator := 25, denominator_pos := by decide }
          modulusMargin := NonnegativeRatio.ofNat 2 }
        (failureTarget 197) ∧
      LInfThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 256
          coordinateCap :=
            { numerator := 21, denominator := 50, denominator_pos := by decide }
          modulusMargin := NonnegativeRatio.ofNat 2 }
        (failureTarget 133) ∧
      LInfThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 384
          coordinateCap :=
            { numerator := 21, denominator := 50, denominator_pos := by decide }
          modulusMargin := NonnegativeRatio.ofNat 2 }
        (failureTarget 200) ∧
      LInfThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 512
          coordinateCap :=
            { numerator := 47, denominator := 100, denominator_pos := by decide }
          modulusMargin := NonnegativeRatio.ofNat 2 }
        (failureTarget 206) ∧
      LInfThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 512
          coordinateCap :=
            { numerator := 21, denominator := 50, denominator_pos := by decide }
          modulusMargin := NonnegativeRatio.ofNat 2 }
        (failureTarget 266) := by
  exact ⟨CertifiedJL.Results.LInf.Lower.TwoDecimal.lower6Over25Rows256Bits197,
    CertifiedJL.Results.LInf.Lower.TwoDecimal.lower21Over50Rows256Bits133,
    CertifiedJL.Results.LInf.Lower.TwoDecimal.lower21Over50Rows384Bits200,
    CertifiedJL.Results.LInf.Lower.TwoDecimal.lower47Over100Rows512Bits206,
    CertifiedJL.Results.LInf.Lower.TwoDecimal.lower21Over50Rows512Bits266⟩

end CertifiedJL.Results.LInf.Lower.HighSecurity
