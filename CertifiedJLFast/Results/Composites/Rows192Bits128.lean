/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJLFast.Results.L2.Lower.Rows192Bits128
import CertifiedJLFast.Results.L2.Upper.Rows192Bits128
import CertifiedJLFast.Results.LInf.Lower.Rows192Bits128
import CertifiedJLFast.Results.LInf.Upper.Rows192Bits128
/-! # Assumption-backed 192-row specializations -/

namespace CertifiedJLFast.Results.Composites.Rows192Bits128

open scoped ENNReal

/-- The complete assumption-backed 192-row parameter set. -/
theorem allBounds :
    CertifiedJL.L2ThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 192
          squaredNormFloor := CertifiedJL.NonnegativeRatio.ofNat 12
          modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 3 }
        (CertifiedJL.failureTarget 128) ∧
      CertifiedJL.L2UpperTailAt
        { distribution := .balancedTernary
          rows := 192
          threshold := CertifiedJL.NonnegativeRatio.ofNat 287 }
        (CertifiedJL.failureTarget 128) ∧
      CertifiedJL.LInfThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 192
          coordinateCap :=
            { numerator := 17, denominator := 50, denominator_pos := by decide }
          modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 2 }
        (CertifiedJL.failureTarget 129) ∧
      CertifiedJL.LInfUpperTailAt
        { distribution := .balancedTernary
          rows := 192
          coordinateThreshold :=
            { numerator := 487, denominator := 50, denominator_pos := by decide } }
        (CertifiedJL.failureTarget 128) :=
  ⟨CertifiedJLFast.Results.L2.Lower.Rows192Bits128.ternaryL2ThresholdLower12,
    CertifiedJLFast.Results.L2.Upper.Rows192Bits128.ternaryL2Upper287,
    CertifiedJLFast.Results.LInf.Lower.Rows192Bits128.ternaryLInfThresholdLower17Over50,
    CertifiedJLFast.Results.LInf.Upper.Rows192Bits128.ternaryLInfUpper487Over50⟩

end CertifiedJLFast.Results.Composites.Rows192Bits128
