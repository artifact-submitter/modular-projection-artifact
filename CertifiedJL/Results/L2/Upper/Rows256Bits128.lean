/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.TheoremAssembly

/-!
# Certified 256-row balanced-ternary modular tails at 128 bits

The named theorems in this module are the complete production modular
squared-Euclidean result surface at 256 rows and failure budget `2⁻¹²⁸`.
Each matrix entry is `-1`, `0`, or `1` with probabilities `1/4`, `1/2`,
and `1/4`.
-/

namespace CertifiedJL.Results.L2.Upper.Rows256Bits128

/-- Balanced-ternary strict upper tail at threshold `338`, with no input-norm
restriction. -/
theorem ternaryL2Upper338 :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 256
        threshold := NonnegativeRatio.ofNat 338 }
      (failureTarget 128) := by
  intro q d w
  simp only [ProjectionDistribution.matrixPMF_balancedTernary]
  rw [eventProbability_congr (sparseRademacherMatrix 256 d)
    (event' := SparseUpperFailure q w) (by
      intro J
      simp [L2UpperFailure, SparseUpperFailure, NonnegativeRatio.ofNat,
        sparseUpperThreshold])]
  exact sparseUpper128_assembly q d w

end CertifiedJL.Results.L2.Upper.Rows256Bits128
