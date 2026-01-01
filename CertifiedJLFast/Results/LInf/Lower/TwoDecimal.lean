/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.LInf.Lower.BalancedTernary.FortySevenHundredthsTwoDecimal
import CertifiedJL.Projection.LInf.Lower.BalancedTernary.SixTwentyFifthsTwoDecimal
import CertifiedJL.Projection.LInf.Lower.BalancedTernary.SeventeenFiftiethsTwoDecimal
import CertifiedJL.Projection.LInf.Lower.BalancedTernary.TwentyOneFiftiethTwoDecimal
import CertifiedJLFast.Assumptions.Families.LInfLower.TwoDecimal

/-! # Fast assembly of the two-decimal ternary infinity lower tails -/

namespace CertifiedJLFast.Results.LInf.Lower.TwoDecimal

open Assumptions

open CertifiedJL.TernaryLInfThresholdLower6Over25TwoDecimal in
theorem lower6Over25Rows256Bits197 :
    CertifiedJL.LInfThresholdLowerTailAt
      (parametersAt 256)
      (CertifiedJL.failureTarget 197) :=
  ternaryLInfThresholdLower6Over25_rows256_bits197_of_certificates
      ternary_linf_cap24_central_assumed ternary_linf_cap24_diffuse_assumed

open CertifiedJL.TernaryLInfThresholdLower17Over50TwoDecimal in
theorem lower17Over50Rows192Bits129 :
    CertifiedJL.LInfThresholdLowerTailAt
      (parametersAt 192)
      (CertifiedJL.failureTarget 129) :=
  ternaryLInfThresholdLower17Over50_rows192_bits129_of_certificates
      ternary_linf_cap34_central_assumed ternary_linf_cap34_diffuse_assumed

open CertifiedJL.TernaryLInfThresholdLower21Over50TwoDecimal in
theorem lower21Over50Rows256Bits133 :
    CertifiedJL.LInfThresholdLowerTailAt
      (parametersAt 256)
      (CertifiedJL.failureTarget 133) :=
  ternaryLInfThresholdLower21Over50_rows256_bits133_of_certificates
      ternary_linf_cap42_central_assumed ternary_linf_cap42_diffuse_assumed

open CertifiedJL.TernaryLInfThresholdLower21Over50TwoDecimal in
theorem lower21Over50Rows384Bits200 :
    CertifiedJL.LInfThresholdLowerTailAt
      (parametersAt 384)
      (CertifiedJL.failureTarget 200) :=
  ternaryLInfThresholdLower21Over50_rows384_bits200_of_certificates
      ternary_linf_cap42_central_assumed ternary_linf_cap42_diffuse_assumed

open CertifiedJL.TernaryLInfThresholdLower21Over50TwoDecimal in
theorem lower21Over50Rows512Bits266 :
    CertifiedJL.LInfThresholdLowerTailAt
      (parametersAt 512)
      (CertifiedJL.failureTarget 266) :=
  ternaryLInfThresholdLower21Over50_rows512_bits266_of_certificates
      ternary_linf_cap42_central_assumed ternary_linf_cap42_diffuse_assumed

open CertifiedJL.TernaryLInfThresholdLower47Over100TwoDecimal in
theorem lower47Over100Rows512Bits206 :
    CertifiedJL.LInfThresholdLowerTailAt
      (parametersAt 512)
      (CertifiedJL.failureTarget 206) :=
  ternaryLInfThresholdLower47Over100_rows512_bits206_of_certificates
      ternary_linf_cap47_central_assumed ternary_linf_cap47_diffuse_assumed

end CertifiedJLFast.Results.LInf.Lower.TwoDecimal
