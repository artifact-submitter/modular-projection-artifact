/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.LInfLower.TwoDecimal.Provider
import CertifiedJL.Projection.LInf.Lower.BalancedTernary.FortySevenHundredthsTwoDecimal
import CertifiedJL.Projection.LInf.Lower.BalancedTernary.SeventeenFiftiethsTwoDecimal
import CertifiedJL.Projection.LInf.Lower.BalancedTernary.SixTwentyFifthsTwoDecimal
import CertifiedJL.Projection.LInf.Lower.BalancedTernary.TwentyOneFiftiethTwoDecimal

/-! # Sharp two-decimal balanced-ternary modular infinity lower tails -/

namespace CertifiedJL.Results.LInf.Lower.TwoDecimal

open CertificateProviders

open CertifiedJL.TernaryLInfThresholdLower21Over50TwoDecimal in
/-- Under the public threshold hypotheses, one balanced-ternary row passes the
`21/50` centered coordinate cap with probability strictly below
`13939/20000`.  This is the certificate-free paper-facing form of the uniform
row lemma used by the 133-, 200-, and 266-bit matrix theorems. -/
theorem rowPass21Over50_lt_13939Over20000
    {q d inputThreshold : ℕ} (w : Fin d → ℤ) (_hq : Odd q)
    (hcentered : CenteredInput q w) (hpositive : 0 < inputThreshold)
    (hnorm : inputThreshold ^ 2 ≤ sqNorm w)
    (hmargin : 2 * inputThreshold ≤ q) :
    (eventProbability (sparseRademacherRow d)
      (RowPass q inputThreshold w)).toReal < 13939 / 20000 := by
  exact row_probability_toReal_lt w
    ternaryLInfCap42Central_verified ternaryLInfCap42Diffuse_verified
    hpositive hcentered hnorm hmargin

open CertifiedJL.TernaryLInfThresholdLower6Over25TwoDecimal in
theorem lower6Over25Rows256Bits197 :
    LInfThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 256
        coordinateCap :=
          { numerator := 6, denominator := 25, denominator_pos := by decide }
        modulusMargin := NonnegativeRatio.ofNat 2 }
      (failureTarget 197) := by
  simpa [parametersAt] using
    ternaryLInfThresholdLower6Over25_rows256_bits197_of_certificates
        ternaryLInfCap24Central_verified ternaryLInfCap24Diffuse_verified

open CertifiedJL.TernaryLInfThresholdLower17Over50TwoDecimal in
theorem lower17Over50Rows192Bits129 :
    LInfThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 192
        coordinateCap :=
          { numerator := 17, denominator := 50, denominator_pos := by decide }
        modulusMargin := NonnegativeRatio.ofNat 2 }
      (failureTarget 129) := by
  simpa [parametersAt] using
    ternaryLInfThresholdLower17Over50_rows192_bits129_of_certificates
      ternaryLInfCap34Central_verified ternaryLInfCap34Diffuse_verified

open CertifiedJL.TernaryLInfThresholdLower21Over50TwoDecimal in
theorem lower21Over50Rows256Bits133 :
    LInfThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 256
        coordinateCap :=
          { numerator := 21, denominator := 50, denominator_pos := by decide }
        modulusMargin := NonnegativeRatio.ofNat 2 }
      (failureTarget 133) := by
  simpa [parametersAt] using
    ternaryLInfThresholdLower21Over50_rows256_bits133_of_certificates
        ternaryLInfCap42Central_verified ternaryLInfCap42Diffuse_verified

open CertifiedJL.TernaryLInfThresholdLower21Over50TwoDecimal in
theorem lower21Over50Rows384Bits200 :
    LInfThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 384
        coordinateCap :=
          { numerator := 21, denominator := 50, denominator_pos := by decide }
        modulusMargin := NonnegativeRatio.ofNat 2 }
      (failureTarget 200) := by
  simpa [parametersAt] using
    ternaryLInfThresholdLower21Over50_rows384_bits200_of_certificates
        ternaryLInfCap42Central_verified ternaryLInfCap42Diffuse_verified

open CertifiedJL.TernaryLInfThresholdLower21Over50TwoDecimal in
theorem lower21Over50Rows512Bits266 :
    LInfThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        coordinateCap :=
          { numerator := 21, denominator := 50, denominator_pos := by decide }
        modulusMargin := NonnegativeRatio.ofNat 2 }
      (failureTarget 266) := by
  simpa [parametersAt] using
    ternaryLInfThresholdLower21Over50_rows512_bits266_of_certificates
        ternaryLInfCap42Central_verified ternaryLInfCap42Diffuse_verified

open CertifiedJL.TernaryLInfThresholdLower47Over100TwoDecimal in
theorem lower47Over100Rows512Bits206 :
    LInfThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        coordinateCap :=
          { numerator := 47, denominator := 100, denominator_pos := by decide }
        modulusMargin := NonnegativeRatio.ofNat 2 }
      (failureTarget 206) := by
  simpa [parametersAt] using
    ternaryLInfThresholdLower47Over100_rows512_bits206_of_certificates
        ternaryLInfCap47Central_verified ternaryLInfCap47Diffuse_verified

end CertifiedJL.Results.LInf.Lower.TwoDecimal
