/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Results.L2.Lower.Rows256Bits192
import CertifiedJL.Results.L2.Lower.Rows384Bits192
import CertifiedJL.Results.L2.Lower.Rows512Bits192
import CertifiedJL.Results.L2.Lower.Rows512Bits193
import CertifiedJL.Results.L2.Lower.Rows512Bits256

/-! # Aggregate high-security threshold-relative Euclidean lower tails -/

namespace CertifiedJL.Results.L2.Lower.HighSecurity

/-- The original three kernel-checked high-security threshold-relative
lower-tail specializations. This type is preserved for API compatibility. -/
theorem allLowerBounds :
    L2ThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 384
          squaredNormFloor := NonnegativeRatio.ofNat 43
          modulusMargin := NonnegativeRatio.ofNat 3 }
        (failureTarget 192) ∧
      L2ThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 512
          squaredNormFloor := NonnegativeRatio.ofNat 71
          modulusMargin := NonnegativeRatio.ofNat 3 }
        (failureTarget 192) ∧
      L2ThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 512
          squaredNormFloor := NonnegativeRatio.ofNat 57
          modulusMargin := NonnegativeRatio.ofNat 3 }
        (failureTarget 256) := by
  exact ⟨Rows384Bits192.ternaryL2ThresholdLower43,
    Rows512Bits192.ternaryL2ThresholdLower71,
    Rows512Bits256.ternaryL2ThresholdLower57⟩

/-- All four kernel-checked high-security threshold-relative lower-tail
specializations, including the compact 256-row, 192-bit endpoint. -/
theorem allLowerBoundsIncluding256 :
    L2ThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 256
          squaredNormFloor := NonnegativeRatio.ofNat 9
          modulusMargin := NonnegativeRatio.ofNat 3 }
        (failureTarget 192) ∧
      L2ThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 384
          squaredNormFloor := NonnegativeRatio.ofNat 43
          modulusMargin := NonnegativeRatio.ofNat 3 }
        (failureTarget 192) ∧
      L2ThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 512
          squaredNormFloor := NonnegativeRatio.ofNat 71
          modulusMargin := NonnegativeRatio.ofNat 3 }
        (failureTarget 192) ∧
      L2ThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 512
          squaredNormFloor := NonnegativeRatio.ofNat 57
          modulusMargin := NonnegativeRatio.ofNat 3 }
        (failureTarget 256) :=
  ⟨Rows256Bits192.ternaryL2ThresholdLower9, allLowerBounds⟩

/-- The five strongest high-security public specializations, including the
192-bit corollary of the 512-row floor-73 result proved at 193 bits. -/
theorem allLowerBoundsIncludingFloor73 :
    L2ThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 256
          squaredNormFloor := NonnegativeRatio.ofNat 9
          modulusMargin := NonnegativeRatio.ofNat 3 }
        (failureTarget 192) ∧
      L2ThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 384
          squaredNormFloor := NonnegativeRatio.ofNat 43
          modulusMargin := NonnegativeRatio.ofNat 3 }
        (failureTarget 192) ∧
      L2ThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 512
          squaredNormFloor := NonnegativeRatio.ofNat 73
          modulusMargin := NonnegativeRatio.ofNat 3 }
        (failureTarget 192) ∧
      L2ThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 512
          squaredNormFloor := NonnegativeRatio.ofNat 73
          modulusMargin := NonnegativeRatio.ofNat 3 }
        (failureTarget 193) ∧
      L2ThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 512
          squaredNormFloor := NonnegativeRatio.ofNat 57
          modulusMargin := NonnegativeRatio.ofNat 3 }
        (failureTarget 256) :=
  ⟨Rows256Bits192.ternaryL2ThresholdLower9,
    Rows384Bits192.ternaryL2ThresholdLower43,
    Rows512Bits192.ternaryL2ThresholdLower73,
    Rows512Bits193.ternaryL2ThresholdLower73,
    Rows512Bits256.ternaryL2ThresholdLower57⟩

end CertifiedJL.Results.L2.Lower.HighSecurity
