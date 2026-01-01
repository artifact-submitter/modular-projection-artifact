/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Soundness.TargetNumeric

/-! # Small exact endgame for the first affine infinity lower tails -/

namespace CertifiedJL.AffineLInfNumeric

open SparseThresholdDominant.TargetNumeric

/-- The diffuse row cap closes the original affine pilot with 130 bits. -/
theorem cap67Over200_ratio :
    (Real.exp ((33 / 10 : ℝ) * (67 / 200) ^ 2) * (97 / 200)) ^ 256 <
      (1 / 2 : ℝ) ^ 130 := by
  have h := certifiedCheckAt_sound 256 256 (33 / 10) ((67 / 200) ^ 2)
    (97 / 200) ((1 / 2) ^ 130) (97 / 200) (by norm_num) (by norm_num)
    (by decide +kernel)
  rw [mul_pow, ← Real.exp_nat_mul]
  convert h using 1 <;> norm_num <;> ring

/-- The diffuse row cap retains 197 bits at coordinate cap `6/25`. -/
theorem cap6Over25_ratio :
    (Real.exp ((33 / 10 : ℝ) * (6 / 25) ^ 2) * (97 / 200)) ^ 256 <
      (1 / 2 : ℝ) ^ 197 := by
  have h := certifiedCheckAt_sound 256 256 (33 / 10) ((6 / 25) ^ 2)
    (97 / 200) ((1 / 2) ^ 197) (97 / 200) (by norm_num) (by norm_num)
    (by decide +kernel)
  rw [mul_pow, ← Real.exp_nat_mul]
  convert h using 1 <;> norm_num <;> ring

end CertifiedJL.AffineLInfNumeric
