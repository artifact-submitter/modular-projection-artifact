/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Results.LInf.Upper.Rows256
import CertifiedJL.Results.LInf.Upper.Rows256Bits192
import CertifiedJL.Results.LInf.Upper.Rows384Bits192
import CertifiedJL.Results.LInf.Upper.Rows512Bits192
import CertifiedJL.Results.LInf.Upper.Rows512Bits256

/-! # Aggregate high-security modular infinity-norm results -/

namespace CertifiedJL.Results.LInf.Upper.HighSecurity

/-- The strongest certified modular infinity upper-tail specializations in
the application grid. The first cell uses the certificate-sharp one-row
theorem; the remaining cells use exact equal-share elementary bounds. -/
theorem allUpperBounds :
    LInfUpperTailAt
        { distribution := .balancedTernary
          rows := 256
          coordinateThreshold :=
            { numerator := 39, denominator := 4, denominator_pos := by decide } }
        (failureTarget 133) ∧
      LInfUpperTailAt
        { distribution := .balancedTernary
          rows := 256
          coordinateThreshold :=
            { numerator := 1181, denominator := 100,
              denominator_pos := by decide } }
        (failureTarget 192) ∧
      LInfUpperTailAt
        { distribution := .balancedTernary
          rows := 384
          coordinateThreshold :=
            { numerator := 1183, denominator := 100,
              denominator_pos := by decide } }
        (failureTarget 192) ∧
      LInfUpperTailAt
        { distribution := .balancedTernary
          rows := 512
          coordinateThreshold :=
            { numerator := 1184, denominator := 100,
              denominator_pos := by decide } }
        (failureTarget 192) ∧
      LInfUpperTailAt
        { distribution := .balancedTernary
          rows := 512
          coordinateThreshold :=
            { numerator := 1358, denominator := 100,
              denominator_pos := by decide } }
        (failureTarget 256) := by
  exact ⟨Rows256.ternaryLInfUpper39Over4Bits133,
    Rows256Bits192.ternaryLInfUpper1181Over100,
    Rows384Bits192.ternaryLInfUpper1183Over100,
    Rows512Bits192.ternaryLInfUpper1184Over100,
    Rows512Bits256.ternaryLInfUpper1358Over100⟩

end CertifiedJL.Results.LInf.Upper.HighSecurity
