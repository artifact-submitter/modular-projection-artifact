/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows384Bits192.Assembly
import CertifiedJLFast.Assumptions.Families.L2Lower.Shared

/-! # Assumption-backed 384-row result specializations -/

namespace CertifiedJLFast.Results.L2.Lower.Rows384Bits192

/-- Balanced-ternary strict threshold-relative lower tail at squared-norm floor
`43`, with only the cataloged numerical boundaries assumed. -/
theorem ternaryL2ThresholdLower43 :
    CertifiedJL.L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 384
        squaredNormFloor := CertifiedJL.NonnegativeRatio.ofNat 43
        modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 3 }
      (CertifiedJL.failureTarget 192) :=
  CertifiedJL.CertificateAssembly.sparseL2ThresholdLower384Bits192
    Assumptions.sparse_l2_threshold_dominant_direct_cover384_bits192_assumed
    Assumptions.sparse_l2_threshold_dominant_capped_fourier_cover384_bits192_assumed
    Assumptions.sparse_l2_threshold_dominant_singleton_fourier_cover384_bits192_assumed
    Assumptions.sparse_l2_threshold_dominant_retained_coarse128_assumed
    Assumptions.sparse_l2_threshold_dominant_retained_chord128_assumed
    Assumptions.sparse_l2_threshold_dominant_final_ratio384_bits192_assumed
    Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed
    Assumptions.sparse_l2_threshold_near_endpoints128_assumed
    Assumptions.sparse_l2_threshold_near_curvature128_assumed
    Assumptions.sparse_l2_threshold_near_final_ratio384_bits192_assumed
    Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed
    Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed
    Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed
    Assumptions.sparse_l2_threshold_diffuse_final_ratio384_bits192_assumed

end CertifiedJLFast.Results.L2.Lower.Rows384Bits192
