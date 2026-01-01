/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Results.L2.Lower.Rows256Bits128
import CertifiedJL.Results.L2.Upper.Rows256Bits128
/-!
# Certified 256-row balanced-ternary modular tails at 128 bits

The named theorems in this module are the complete production modular
squared-Euclidean result surface at 256 rows and failure budget `2⁻¹²⁸`.
Each matrix entry is `-1`, `0`, or `1` with probabilities `1/4`, `1/2`,
and `1/4`.
-/

namespace CertifiedJL.Results.Composites.L2Rows256Bits128

/-- The threshold-relative lower and unrestricted upper 256-row, 128-bit
Euclidean bounds. -/
theorem allL2Bounds :
    L2ThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 256
          squaredNormFloor := NonnegativeRatio.ofNat 29
          modulusMargin := NonnegativeRatio.ofNat 3 }
        (failureTarget 128) ∧
      L2UpperTailAt
        { distribution := .balancedTernary
          rows := 256
          threshold := NonnegativeRatio.ofNat 338 }
        (failureTarget 128) :=
  ⟨CertifiedJL.Results.L2.Lower.Rows256Bits128.ternaryL2ThresholdLower29,
    CertifiedJL.Results.L2.Upper.Rows256Bits128.ternaryL2Upper338⟩

end CertifiedJL.Results.Composites.L2Rows256Bits128
