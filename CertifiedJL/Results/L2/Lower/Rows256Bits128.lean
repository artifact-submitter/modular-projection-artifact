/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Final128

/-!
# Certified 256-row balanced-ternary modular tails at 128 bits

The named theorems in this module are the complete production modular
squared-Euclidean result surface at 256 rows and failure budget `2⁻¹²⁸`.
Each matrix entry is `-1`, `0`, or `1` with probabilities `1/4`, `1/2`,
and `1/4`.
-/

namespace CertifiedJL.Results.L2.Lower.Rows256Bits128

/-- Balanced-ternary strict threshold-relative lower tail at squared-norm floor
`29`, for a positive public threshold `b` satisfying `b^2 <= sqNorm w` and
`3 * b <= q`.  The actual vector norm is otherwise unrestricted. -/
theorem ternaryL2ThresholdLower29 :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 256
        squaredNormFloor := NonnegativeRatio.ofNat 29
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 128) :=
  ternaryThresholdLowerTail_marginThree_bits128

end CertifiedJL.Results.L2.Lower.Rows256Bits128
