/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows512Floor73Bits193.Assembly
import CertifiedJLFast.Assumptions.Families.L2Lower.Shared

/-! # Assumption-backed 512-row threshold endpoint at 193 bits -/

namespace CertifiedJLFast.Results.L2.Lower.Rows512Bits193

/-- Balanced-ternary strict threshold-relative L2 lower tail at squared-norm floor 73. -/
theorem ternaryL2ThresholdLower73 :
    CertifiedJL.L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        squaredNormFloor := CertifiedJL.NonnegativeRatio.ofNat 73
        modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 3 }
      (CertifiedJL.failureTarget 193) :=
  CertifiedJL.CertificateAssembly.sparseL2ThresholdLower512Floor73Bits193
    Assumptions.sparse_l2_threshold_dominant_direct_cover512_floor73_bits193_assumed
    Assumptions.sparse_l2_threshold_dominant_capped_fourier_cover512_floor73_bits193_assumed
    Assumptions.sparse_l2_threshold_dominant_singleton_fourier_cover512_floor73_bits193_assumed
    Assumptions.sparse_l2_threshold_dominant_retained_coarse128_assumed
    Assumptions.sparse_l2_threshold_dominant_retained_chord128_assumed
    Assumptions.sparse_l2_threshold_dominant_final_ratio512_floor73_bits193_assumed
    Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed
    Assumptions.sparse_l2_threshold_near_endpoints128_assumed
    Assumptions.sparse_l2_threshold_near_curvature128_assumed
    Assumptions.sparse_l2_threshold_near_final_ratio512_floor73_bits193_assumed
    Assumptions.sparse_l2_threshold_diffuse_floor73_endpoints_assumed
    Assumptions.sparse_l2_threshold_diffuse_final_ratio512_floor73_bits193_assumed

end CertifiedJLFast.Results.L2.Lower.Rows512Bits193
