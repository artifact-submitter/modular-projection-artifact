/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Results.L2.Lower.Rows192Bits128
import CertifiedJL.Results.L2.Upper.Rows192Bits128
import CertifiedJL.Results.LInf.Lower.Rows192Bits128
import CertifiedJL.Results.LInf.Upper.Rows192Bits128
/-! # Certified 192-row balanced-ternary modular tails -/

namespace CertifiedJL.Results.Composites.Rows192Bits128

/-- The complete certified 192-row parameter set. -/
theorem allBounds :
    L2ThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 192
          squaredNormFloor := NonnegativeRatio.ofNat 12
          modulusMargin := NonnegativeRatio.ofNat 3 }
        (failureTarget 128) ∧
      L2UpperTailAt
        { distribution := .balancedTernary
          rows := 192
          threshold := NonnegativeRatio.ofNat 287 }
        (failureTarget 128) ∧
      LInfThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 192
          coordinateCap :=
            { numerator := 17, denominator := 50, denominator_pos := by decide }
          modulusMargin := NonnegativeRatio.ofNat 2 }
        (failureTarget 129) ∧
      LInfUpperTailAt
        { distribution := .balancedTernary
          rows := 192
          coordinateThreshold :=
            { numerator := 487, denominator := 50, denominator_pos := by decide } }
        (failureTarget 128) :=
  ⟨CertifiedJL.Results.L2.Lower.Rows192Bits128.ternaryL2ThresholdLower12,
    CertifiedJL.Results.L2.Upper.Rows192Bits128.ternaryL2Upper287,
    CertifiedJL.Results.LInf.Lower.Rows192Bits128.ternaryLInfThresholdLower17Over50,
    CertifiedJL.Results.LInf.Upper.Rows192Bits128.ternaryLInfUpper487Over50⟩

end CertifiedJL.Results.Composites.Rows192Bits128
