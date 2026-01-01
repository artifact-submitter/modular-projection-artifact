/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows192Bits128.Assembly
import CertifiedJLFast.Assumptions.Families.L2Lower.Shared

/-! # Assumption-backed 192-row specializations -/

namespace CertifiedJLFast.Results.L2.Lower.Rows192Bits128

open scoped ENNReal

/-- Assumption-backed balanced-ternary threshold-relative `L₂` lower tail at
squared-norm floor `12`. -/
theorem ternaryL2ThresholdLower12 :
    CertifiedJL.L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 192
        squaredNormFloor := CertifiedJL.NonnegativeRatio.ofNat 12
        modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 3 }
      (CertifiedJL.failureTarget 128) :=
  CertifiedJL.CertificateAssembly.sparseL2ThresholdLower192Bits128
    Assumptions.sparse_l2_threshold_dominant_direct_cover192_bits128_assumed
    Assumptions.sparse_l2_threshold_dominant_capped_fourier_cover192_bits128_assumed
    Assumptions.sparse_l2_threshold_dominant_singleton_fourier_cover192_bits128_assumed
    Assumptions.sparse_l2_threshold_dominant_retained_coarse128_assumed
    Assumptions.sparse_l2_threshold_dominant_retained_chord128_assumed
    Assumptions.sparse_l2_threshold_dominant_final_ratio192_bits128_assumed
    Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed
    Assumptions.sparse_l2_threshold_near_endpoints128_assumed
    Assumptions.sparse_l2_threshold_near_curvature128_assumed
    Assumptions.sparse_l2_threshold_near_final_ratio192_bits128_assumed
    Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed
    Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed
    Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed
    Assumptions.sparse_l2_threshold_diffuse_final_ratio192_bits128_assumed

end CertifiedJLFast.Results.L2.Lower.Rows192Bits128
