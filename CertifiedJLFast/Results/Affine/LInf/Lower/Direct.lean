/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.Affine.Assembly.AffineLInf
import CertifiedJLFast.Assumptions.Families.L2Lower.Shared

/-! # Direct affine infinity-norm lower tails at modulus margin three -/

namespace CertifiedJLFast.Results.Affine.LInf.Lower.Direct

open CertifiedJL

/-- Arbitrary row-wise shifts fixed before sampling the balanced-ternary matrix. -/
theorem ternaryAffineLInfThresholdLower256Cap67Over200Bits130 :
    AffineLInfThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 256,
        coordinateCap := { numerator := 67, denominator := 200, denominator_pos := by decide },
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget 130) :=
  CertificateAssembly.affineLInfCap67Over200
    Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed
    Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed
    Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed

/-- Arbitrary row-wise shifts fixed before sampling the balanced-ternary matrix. -/
theorem ternaryAffineLInfThresholdLower256Cap6Over25Bits197 :
    AffineLInfThresholdLowerTailAt
      { distribution := .balancedTernary, rows := 256,
        coordinateCap := { numerator := 6, denominator := 25, denominator_pos := by decide },
        modulusMargin := NonnegativeRatio.ofNat 3 } (failureTarget 197) :=
  CertificateAssembly.affineLInfCap6Over25
    Assumptions.sparse_l2_threshold_diffuse_low_scalar128_assumed
    Assumptions.sparse_l2_threshold_diffuse_low_modular_tail128_assumed
    Assumptions.sparse_l2_threshold_diffuse_high_endpoints128_assumed

end CertifiedJLFast.Results.Affine.LInf.Lower.Direct
