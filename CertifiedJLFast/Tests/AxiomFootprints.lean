/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJLFast.Results.L2.Lower.Rows192Bits128
import CertifiedJLFast.Results.L2.Upper.Rows192Bits128
import CertifiedJLFast.Results.LInf.Lower.Rows192Bits128
import CertifiedJLFast.Results.LInf.Upper.Rows192Bits128
import CertifiedJLFast.Results.Composites.Rows192Bits128
import CertifiedJLFast.Results.L2.Lower.Rows256Bits128
import CertifiedJLFast.Results.L2.Upper.Rows256Bits128
import CertifiedJLFast.Results.LInf.Upper.Rows256Bits128
import CertifiedJLFast.Results.Composites.L2Rows256Bits128
import CertifiedJLFast.Results.L2.Lower.Rows256Bits192
import CertifiedJLFast.Results.L2.Upper.Rows256Bits192
import CertifiedJLFast.Results.L2.Lower.Rows384Bits192
import CertifiedJLFast.Results.L2.Upper.Rows384Bits192
import CertifiedJLFast.Results.L2.Upper.Rows512Bits192
import CertifiedJLFast.Results.L2.Upper.Rows512Bits256
import CertifiedJLFast.Results.L2.Lower.Rows512Bits192
import CertifiedJLFast.Results.L2.Lower.Rows512Bits193
import CertifiedJLFast.Results.L2.Lower.Rows512Bits256
import CertifiedJLFast.Results.LInf.Lower.TwoDecimal
import CertifiedJLFast.Results.Affine.LInf.Lower.Direct
import CertifiedJLFast.Results.Affine.L2.Lower.General
import CertifiedJLFast.Results.Affine.L2.Lower.Endpoints
import CertifiedJLFast.Results.Affine.LInf.Lower.Endpoints
import CertifiedJLFast.Results.Affine.L2.Upper
import CertifiedJLFast.Results.Affine.LInf.Upper
import CertifiedJLFast.Results.Affine.LInf.Lower.MarginTwo
import CertifiedJLFast.Results.Transports.Rows

/-! # Exact assumption footprints of fast results -/

open Lean in
run_cmd
  let standard : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checks : Array (Name × Array Name) := #[
    (``CertifiedJLFast.Results.Transports.Rows.ternaryL2Upper195Threshold338Bits128, #[``CertifiedJLFast.Assumptions.sparse_l2_upper_hybrid_assumed]),
    (``CertifiedJLFast.Results.Transports.Rows.ternaryAffineL2Upper195Threshold338Bits128, #[``CertifiedJLFast.Assumptions.sparse_l2_upper_hybrid_assumed]),
    (``CertifiedJLFast.Results.Transports.Rows.ternaryL2Upper264Threshold509Bits128, #[``CertifiedJLFast.Assumptions.sparse_l2_upper_contour_rows384_bits192_threshold509_assumed]),
    (``CertifiedJLFast.Results.Transports.Rows.ternaryAffineL2Upper264Threshold509Bits128, #[``CertifiedJLFast.Assumptions.sparse_l2_upper_contour_rows384_bits192_threshold509_assumed]),
    (``CertifiedJLFast.Results.Transports.Rows.ternaryL2Upper394Threshold607Bits192, #[``CertifiedJLFast.Assumptions.sparse_l2_upper_contour_512_bits192_assumed]),
    (``CertifiedJLFast.Results.Transports.Rows.ternaryAffineL2Upper394Threshold607Bits192, #[``CertifiedJLFast.Assumptions.sparse_l2_upper_contour_512_bits192_assumed]),
    (``CertifiedJLFast.Results.Transports.Rows.ternaryLInfUpper462Cap1358Over100Bits197, #[]),
    (``CertifiedJLFast.Results.Transports.Rows.ternaryAffineLInfUpper462Cap1358Over100Bits197, #[]),
    (``CertifiedJLFast.Results.Affine.L2.Lower.General.ternaryAffineL2LowerTail_toReal_le_finiteTilt, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_curvature128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_floor73_endpoints_assumed]),
    (``CertifiedJLFast.Results.Affine.L2.Lower.General.ternaryAffineL2LowerTail_toReal_le_general, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_curvature128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_floor73_endpoints_assumed]),
    (``CertifiedJLFast.Results.Affine.L2.Lower.General.ternaryAffineL2LowerTail_toReal_le_general_of_ratio, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_curvature128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_floor73_endpoints_assumed]),
    (``CertifiedJLFast.Results.Affine.L2.Lower.General.ternaryAffineL2ThresholdLowerTailAt_of_generalBound_lt_failureTarget, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_curvature128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_floor73_endpoints_assumed]),
    (``CertifiedJLFast.Results.Affine.L2.Lower.General.ternaryAffineL2ThresholdLowerTailAt_of_finiteTilt_lt_failureTarget, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_curvature128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_floor73_endpoints_assumed]),
    (``CertifiedJLFast.Results.Affine.LInf.Lower.Direct.ternaryAffineLInfThresholdLower256Cap67Over200Bits130, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed]),
    (``CertifiedJLFast.Results.Affine.LInf.Lower.Direct.ternaryAffineLInfThresholdLower256Cap6Over25Bits197, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed]),
    (``CertifiedJLFast.Results.LInf.Upper.Rows256Bits128.ternaryLInfUpper39Over4Bits133, #[
      ``CertifiedJLFast.Assumptions.moderate_grid_assumed,
      ``CertifiedJLFast.Assumptions.sparse_one_row_envelope_assumed]),
    (``CertifiedJLFast.Results.LInf.Upper.Rows256Bits128.ternaryLInfUpper39Over4, #[
      ``CertifiedJLFast.Assumptions.moderate_grid_assumed,
      ``CertifiedJLFast.Assumptions.sparse_one_row_envelope_assumed]),
    (``CertifiedJLFast.Results.L2.Lower.Rows192Bits128.ternaryL2ThresholdLower12, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_direct_cover192_bits128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_capped_fourier_cover192_bits128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_singleton_fourier_cover192_bits128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_retained_coarse128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_retained_chord128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_final_ratio192_bits128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_curvature128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_final_ratio192_bits128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_final_ratio192_bits128_assumed]),
    (``CertifiedJLFast.Results.L2.Upper.Rows192Bits128.ternaryL2Upper287, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_upper_contour_rows192_bits128_threshold287_assumed]),
    (``CertifiedJLFast.Results.LInf.Lower.Rows192Bits128.ternaryLInfThresholdLower17Over50, #[
      ``CertifiedJLFast.Assumptions.ternary_linf_cap34_central_assumed,
      ``CertifiedJLFast.Assumptions.ternary_linf_cap34_diffuse_assumed]),
    (``CertifiedJLFast.Results.LInf.Upper.Rows192Bits128.ternaryLInfUpper487Over50, #[]),
    (``CertifiedJLFast.Results.Composites.Rows192Bits128.allBounds, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_direct_cover192_bits128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_capped_fourier_cover192_bits128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_singleton_fourier_cover192_bits128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_retained_coarse128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_retained_chord128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_final_ratio192_bits128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_curvature128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_final_ratio192_bits128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_final_ratio192_bits128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_upper_contour_rows192_bits128_threshold287_assumed,
      ``CertifiedJLFast.Assumptions.ternary_linf_cap34_central_assumed,
      ``CertifiedJLFast.Assumptions.ternary_linf_cap34_diffuse_assumed]),
    (``CertifiedJLFast.Results.LInf.Lower.TwoDecimal.lower17Over50Rows192Bits129, #[
      ``CertifiedJLFast.Assumptions.ternary_linf_cap34_central_assumed,
      ``CertifiedJLFast.Assumptions.ternary_linf_cap34_diffuse_assumed]),
    (``CertifiedJLFast.Results.L2.Upper.Rows256Bits128.ternaryL2Upper338, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_upper_hybrid_assumed]),
    (``CertifiedJLFast.Results.L2.Lower.Rows256Bits128.ternaryL2ThresholdLower29, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_direct_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_capped_fourier_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_singleton_fourier_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_retained_coarse128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_retained_chord128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_final_ratio128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_curvature128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed]),
    (``CertifiedJLFast.Results.LInf.Lower.TwoDecimal.lower6Over25Rows256Bits197, #[
      ``CertifiedJLFast.Assumptions.ternary_linf_cap24_central_assumed,
      ``CertifiedJLFast.Assumptions.ternary_linf_cap24_diffuse_assumed]),
    -- The headline 133-bit repair consumes both generated majorant boundaries;
    -- the degree-seven 130-bit fallback has a different proof dependency path.
    (``CertifiedJLFast.Results.LInf.Lower.TwoDecimal.lower21Over50Rows256Bits133, #[
      ``CertifiedJLFast.Assumptions.ternary_linf_cap42_central_assumed,
      ``CertifiedJLFast.Assumptions.ternary_linf_cap42_diffuse_assumed]),
    (``CertifiedJLFast.Results.LInf.Lower.TwoDecimal.lower21Over50Rows384Bits200, #[
      ``CertifiedJLFast.Assumptions.ternary_linf_cap42_central_assumed,
      ``CertifiedJLFast.Assumptions.ternary_linf_cap42_diffuse_assumed]),
    (``CertifiedJLFast.Results.LInf.Lower.TwoDecimal.lower21Over50Rows512Bits266, #[
      ``CertifiedJLFast.Assumptions.ternary_linf_cap42_central_assumed,
      ``CertifiedJLFast.Assumptions.ternary_linf_cap42_diffuse_assumed]),
    (``CertifiedJLFast.Results.LInf.Lower.TwoDecimal.lower47Over100Rows512Bits206, #[
      ``CertifiedJLFast.Assumptions.ternary_linf_cap47_central_assumed,
      ``CertifiedJLFast.Assumptions.ternary_linf_cap47_diffuse_assumed]),
    (``CertifiedJLFast.Results.L2.Lower.Rows256Bits192.ternaryL2ThresholdLower9, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_direct_cover256_bits192_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_capped_fourier_cover256_bits192_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_singleton_fourier_cover256_bits192_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_retained_coarse128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_retained_chord128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_final_ratio256_bits192_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_curvature128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_final_ratio256_bits192_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_final_ratio256_bits192_assumed]),
    (``CertifiedJLFast.Results.L2.Lower.Rows384Bits192.ternaryL2ThresholdLower43, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_direct_cover384_bits192_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_capped_fourier_cover384_bits192_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_singleton_fourier_cover384_bits192_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_retained_coarse128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_retained_chord128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_final_ratio384_bits192_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_curvature128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_final_ratio384_bits192_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_final_ratio384_bits192_assumed]),
    (``CertifiedJLFast.Results.L2.Upper.Rows512Bits192.ternaryL2Upper607, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_upper_contour_512_bits192_assumed]),
    (``CertifiedJLFast.Results.L2.Upper.Rows256Bits192.ternaryL2Upper406, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_upper_contour_rows256_bits192_threshold406_assumed]),
    (``CertifiedJLFast.Results.L2.Upper.Rows384Bits192.ternaryL2Upper509, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_upper_contour_rows384_bits192_threshold509_assumed]),
    (``CertifiedJLFast.Results.L2.Upper.Rows512Bits256.ternaryL2Upper681, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_upper_contour_rows512_bits256_threshold681_assumed]),
    (``CertifiedJLFast.Results.L2.Lower.Rows512Bits192.ternaryL2ThresholdLower71, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_direct_cover512_bits192_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_capped_fourier_cover512_bits192_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_singleton_fourier_cover512_bits192_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_retained_coarse128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_retained_chord128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_final_ratio512_bits192_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_curvature128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_final_ratio512_bits192_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_final_ratio512_bits192_assumed]),
    (``CertifiedJLFast.Results.L2.Lower.Rows512Bits193.ternaryL2ThresholdLower73, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_direct_cover512_floor73_bits193_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_capped_fourier_cover512_floor73_bits193_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_singleton_fourier_cover512_floor73_bits193_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_retained_coarse128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_retained_chord128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_final_ratio512_floor73_bits193_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_curvature128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_final_ratio512_floor73_bits193_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_floor73_endpoints_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_final_ratio512_floor73_bits193_assumed]),
    (``CertifiedJLFast.Results.L2.Lower.Rows512Bits192.ternaryL2ThresholdLower73, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_direct_cover512_floor73_bits193_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_capped_fourier_cover512_floor73_bits193_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_singleton_fourier_cover512_floor73_bits193_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_retained_coarse128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_retained_chord128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_final_ratio512_floor73_bits193_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_curvature128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_final_ratio512_floor73_bits193_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_floor73_endpoints_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_final_ratio512_floor73_bits193_assumed]),
    (``CertifiedJLFast.Results.L2.Lower.Rows512Bits256.ternaryL2ThresholdLower57, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_direct_cover512_bits256_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_capped_fourier_cover512_bits256_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_singleton_fourier_cover512_bits256_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_retained_coarse128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_retained_chord128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_dominant_final_ratio512_bits256_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_curvature128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_final_ratio512_bits256_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_final_ratio512_bits256_assumed]),
    (``CertifiedJLFast.Results.Affine.L2.Lower.Endpoints.ternaryAffineL2ThresholdLower192Floor11Bits128, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_curvature128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_floor73_endpoints_assumed]),
    (``CertifiedJLFast.Results.Affine.L2.Lower.Endpoints.ternaryAffineL2ThresholdLower256Floor27Bits128, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_curvature128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_floor73_endpoints_assumed]),
    (``CertifiedJLFast.Results.Affine.L2.Lower.Endpoints.ternaryAffineL2ThresholdLower256Floor9Bits194, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_curvature128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_floor73_endpoints_assumed]),
    (``CertifiedJLFast.Results.Affine.L2.Lower.Endpoints.ternaryAffineL2ThresholdLower384Floor40Bits192, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_curvature128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_floor73_endpoints_assumed]),
    (``CertifiedJLFast.Results.Affine.L2.Lower.Endpoints.ternaryAffineL2ThresholdLower512Floor73Bits193, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_curvature128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_floor73_endpoints_assumed]),
    (``CertifiedJLFast.Results.Affine.L2.Lower.Endpoints.ternaryAffineL2ThresholdLower512Floor54Bits256, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_curvature128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_floor73_endpoints_assumed]),
    (``CertifiedJLFast.Results.Affine.L2.Lower.Endpoints.ternaryAffineL2ThresholdLower195Floor12Bits128, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_curvature128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_floor73_endpoints_assumed]),
    (``CertifiedJLFast.Results.Affine.L2.Lower.Endpoints.ternaryAffineL2ThresholdLower264Floor29Bits128, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_curvature128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_floor73_endpoints_assumed]),
    (``CertifiedJLFast.Results.Affine.L2.Lower.Endpoints.ternaryAffineL2ThresholdLower394Floor43Bits192, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_curvature128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_floor73_endpoints_assumed]),
    (``CertifiedJLFast.Results.Affine.L2.Lower.Endpoints.ternaryAffineL2ThresholdLower524Floor57Bits256, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_curvature128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_floor73_endpoints_assumed]),
    (``CertifiedJLFast.Results.Affine.LInf.Lower.Endpoints.ternaryAffineLInfThresholdLower192Cap279Over1000Bits129, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed]),
    (``CertifiedJLFast.Results.Affine.LInf.Lower.Endpoints.ternaryAffineLInfThresholdLower256Cap331Over1000Bits133, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed]),
    (``CertifiedJLFast.Results.Affine.LInf.Lower.Endpoints.ternaryAffineLInfThresholdLower384Cap331Over1000Bits200, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed]),
    (``CertifiedJLFast.Results.Affine.LInf.Lower.Endpoints.ternaryAffineLInfThresholdLower512Cap331Over1000Bits266, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed]),
    (``CertifiedJLFast.Results.Affine.LInf.Lower.Endpoints.ternaryAffineLInfThresholdLower512Cap46Over125Bits206, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_floor73_endpoints_assumed]),
    (``CertifiedJLFast.Results.Affine.LInf.Lower.Endpoints.ternaryAffineLInfThresholdLower256Cap9Over25Bits109, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed]),
    (``CertifiedJLFast.Results.Affine.LInf.Lower.Endpoints.ternaryAffineLInfThresholdLower462Cap9Over25Bits197, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed]),
    (``CertifiedJLFast.Results.Affine.L2.Lower.Endpoints.allL2LowerBounds, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_coarse_cover128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_near_curvature128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_floor73_endpoints_assumed]),
    (``CertifiedJLFast.Results.Affine.LInf.Lower.Endpoints.allLInfLowerBounds, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_floor73_endpoints_assumed]),
    (``CertifiedJLFast.Results.Affine.L2.Upper.ternaryAffineL2Upper192Threshold287Bits128, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_upper_contour_rows192_bits128_threshold287_assumed]),
    (``CertifiedJLFast.Results.Affine.LInf.Upper.ternaryAffineLInfUpper192Cap487Over50Bits128, #[]),
    (``CertifiedJLFast.Results.Affine.L2.Upper.ternaryAffineL2Upper256Threshold338Bits128, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_upper_hybrid_assumed]),
    (``CertifiedJLFast.Results.Affine.L2.Upper.ternaryAffineL2Upper512Threshold607Bits192, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_upper_contour_512_bits192_assumed]),
    (``CertifiedJLFast.Results.Affine.LInf.Upper.ternaryAffineLInfUpper256Cap39Over4Bits133, #[
      ``CertifiedJLFast.Assumptions.moderate_grid_assumed,
      ``CertifiedJLFast.Assumptions.sparse_one_row_envelope_assumed]),
    (``CertifiedJLFast.Results.Affine.LInf.Upper.ternaryAffineLInfUpper256Cap1181Over100Bits192, #[]),
    (``CertifiedJLFast.Results.Affine.LInf.Upper.ternaryAffineLInfUpper384Cap1183Over100Bits192, #[]),
    (``CertifiedJLFast.Results.Affine.LInf.Upper.ternaryAffineLInfUpper512Cap1184Over100Bits192, #[]),
    (``CertifiedJLFast.Results.Affine.LInf.Upper.ternaryAffineLInfUpper512Cap1358Over100Bits256, #[]),
    (``CertifiedJLFast.Results.Affine.L2.Upper.ternaryAffineL2Upper256Threshold406Bits192, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_upper_contour_rows256_bits192_threshold406_assumed]),
    (``CertifiedJLFast.Results.Affine.L2.Upper.ternaryAffineL2Upper384Threshold509Bits192, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_upper_contour_rows384_bits192_threshold509_assumed]),
    (``CertifiedJLFast.Results.Affine.L2.Upper.ternaryAffineL2Upper512Threshold681Bits256, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_upper_contour_rows512_bits256_threshold681_assumed]),
    (``CertifiedJLFast.Results.Affine.LInf.Lower.MarginTwo.ternaryAffineLInfThresholdLower192Cap93Over500Margin2Bits129, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed]),
    (``CertifiedJLFast.Results.Affine.LInf.Lower.MarginTwo.ternaryAffineLInfThresholdLower256Cap4Over25Margin2Bits197, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed]),
    (``CertifiedJLFast.Results.Affine.LInf.Lower.MarginTwo.ternaryAffineLInfThresholdLower256Cap331Over1500Margin2Bits133, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed]),
    (``CertifiedJLFast.Results.Affine.LInf.Lower.MarginTwo.ternaryAffineLInfThresholdLower384Cap331Over1500Margin2Bits200, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed]),
    (``CertifiedJLFast.Results.Affine.LInf.Lower.MarginTwo.ternaryAffineLInfThresholdLower512Cap331Over1500Margin2Bits266, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed]),
    (``CertifiedJLFast.Results.Affine.LInf.Lower.MarginTwo.ternaryAffineLInfThresholdLower512Cap92Over375Margin2Bits206, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_floor73_endpoints_assumed]),
    (``CertifiedJLFast.Results.Affine.LInf.Lower.MarginTwo.ternaryAffineLInfThresholdLower256Cap67Over300Margin2Bits130, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed]),
    (``CertifiedJLFast.Results.Affine.LInf.Lower.MarginTwo.ternaryAffineLInfThresholdLower256Cap6Over25Margin2Bits109, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed]),
    (``CertifiedJLFast.Results.Affine.LInf.Lower.MarginTwo.ternaryAffineLInfThresholdLower462Cap6Over25Margin2Bits197, #[
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed,
      ``CertifiedJLFast.Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed])]
  for (target, project) in checks do
    let expected := standard ++ project
    let axioms ← Lean.collectAxioms target
    unless axioms.size == expected.size && axioms.all expected.contains &&
        expected.all axioms.contains do
      throwError "unexpected fast-result axiom footprint for {target}: {axioms}"
