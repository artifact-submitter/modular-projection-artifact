/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows512Bits192.Assembly
import CertifiedJLFast.Assumptions.Families.L2Lower.Shared
import CertifiedJLFast.Results.L2.Lower.Rows512Bits193

/-! # Balanced-ternary L2 threshold specialization -/

namespace CertifiedJLFast.Results.L2.Lower.Rows512Bits192

/-- Balanced-ternary strict threshold-relative lower tail at squared-norm floor 71. -/
theorem ternaryL2ThresholdLower71 :
    CertifiedJL.L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        squaredNormFloor := CertifiedJL.NonnegativeRatio.ofNat 71
        modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 3 }
      (CertifiedJL.failureTarget 192) :=
  CertifiedJL.CertificateAssembly.sparseL2ThresholdLower512Bits192
    Assumptions.sparse_l2_threshold_dominant_direct_cover512_bits192_assumed
    Assumptions.sparse_l2_threshold_dominant_capped_fourier_cover512_bits192_assumed
    Assumptions.sparse_l2_threshold_dominant_singleton_fourier_cover512_bits192_assumed
    Assumptions.sparse_l2_threshold_dominant_retained_coarse128_assumed
    Assumptions.sparse_l2_threshold_dominant_retained_chord128_assumed
    Assumptions.sparse_l2_threshold_dominant_final_ratio512_bits192_assumed
    Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed
    Assumptions.sparse_l2_threshold_near_endpoints128_assumed
    Assumptions.sparse_l2_threshold_near_curvature128_assumed
    Assumptions.sparse_l2_threshold_near_final_ratio512_bits192_assumed
    Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed
    Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed
    Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed
    Assumptions.sparse_l2_threshold_diffuse_final_ratio512_bits192_assumed

/-- The stronger 193-bit endpoint, weakened to the legacy 192-bit budget. -/
theorem ternaryL2ThresholdLower73 :
    CertifiedJL.L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        squaredNormFloor := CertifiedJL.NonnegativeRatio.ofNat 73
        modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 3 }
      (CertifiedJL.failureTarget 192) := by
  apply Results.L2.Lower.Rows512Bits193.ternaryL2ThresholdLower73.mono_budget
  unfold CertifiedJL.failureTarget
  rw [pow_succ]
  exact mul_le_of_le_one_right (by positivity) (by norm_num)

end CertifiedJLFast.Results.L2.Lower.Rows512Bits192
