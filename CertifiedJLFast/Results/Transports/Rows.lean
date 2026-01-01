/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJLFast.Results.L2.Upper.Rows256Bits128
import CertifiedJLFast.Results.L2.Upper.Rows384Bits192
import CertifiedJLFast.Results.L2.Upper.Rows512Bits192
import CertifiedJLFast.Results.L2.Upper.Rows512Bits256
import CertifiedJLFast.Results.LInf.Upper.Rows256Bits128
import CertifiedJL.Projection.LInf.Upper.Elementary
import CertifiedJL.Statements.Transport.Upper
import CertifiedJL.Statements.Transport.ParameterMonotonicity
import CertifiedJL.Statements.Transport.Rows

/-!
# Upper-tail endpoints derived by row restriction

These results use no new numerical certificate.  Each is an exact row marginal
of an existing upper-tail theorem, followed where necessary by a monotone
failure-budget relaxation.
-/

namespace CertifiedJLFast.Results.Transports.Rows

open CertifiedJL

/-- The 256-row threshold-338 theorem restricted to 195 rows. -/
theorem ternaryL2Upper195Threshold338Bits128 :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 195
        threshold := NonnegativeRatio.ofNat 338 }
      (failureTarget 128) :=
  CertifiedJLFast.Results.L2.Upper.Rows256Bits128.ternaryL2Upper338.restrict_rows (by omega)

/-- The 384-row threshold-509 theorem restricted to 264 rows and relaxed from
192-bit to 128-bit failure. -/
theorem ternaryL2Upper264Threshold509Bits128 :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 264
        threshold := NonnegativeRatio.ofNat 509 }
      (failureTarget 128) :=
  (CertifiedJLFast.Results.L2.Upper.Rows384Bits192.ternaryL2Upper509.restrict_rows (by omega)).mono_budget
    (failureTarget_antitone (by omega))

/-- The 512-row threshold-607 theorem restricted to 394 rows. -/
theorem ternaryL2Upper394Threshold607Bits192 :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 394
        threshold := NonnegativeRatio.ofNat 607 }
      (failureTarget 192) :=
  CertifiedJLFast.Results.L2.Upper.Rows512Bits192.ternaryL2Upper607.restrict_rows (by omega)

/-- The 512-row coordinate-threshold theorem restricted to 462 rows and
relaxed from 256-bit to 197-bit failure. -/
theorem ternaryLInfUpper462Cap1358Over100Bits197 :
    LInfUpperTailAt
      { distribution := .balancedTernary
        rows := 462
        coordinateThreshold :=
          { numerator := 1358, denominator := 100,
            denominator_pos := by decide } }
      (failureTarget 197) :=
  by
  have h : LInfUpperTailAt
      { distribution := .balancedTernary, rows := 512,
        coordinateThreshold :=
          { numerator := 1358, denominator := 100, denominator_pos := by decide } }
      (failureTarget 256) := by
    apply TernaryLInfUpperElementary.matrixUpperTailAt_of_two_mul_exp_neg_sq_lt
      (by decide) _ (by unfold failureTarget; finiteness)
    simpa [NonnegativeRatio.toReal] using
      TernaryLInfUpperElementary.two_mul_exp_neg_1358_over_100_sq_lt
  exact (h.restrict_rows (by omega)).mono_budget (failureTarget_antitone (by omega))

/-- The row-restricted upper bound with an arbitrary fixed centered shift. -/
theorem ternaryAffineL2Upper195Threshold338Bits128 :
    AffineL2UpperTailAt
      { distribution := .balancedTernary, rows := 195,
        threshold := NonnegativeRatio.ofNat 338 }
      (failureTarget 128) :=
  ternaryL2Upper195Threshold338Bits128.to_affine

/-- The row-restricted upper bound with an arbitrary fixed centered shift. -/
theorem ternaryAffineL2Upper264Threshold509Bits128 :
    AffineL2UpperTailAt
      { distribution := .balancedTernary, rows := 264,
        threshold := NonnegativeRatio.ofNat 509 }
      (failureTarget 128) :=
  ternaryL2Upper264Threshold509Bits128.to_affine

/-- The row-restricted upper bound with an arbitrary fixed centered shift. -/
theorem ternaryAffineL2Upper394Threshold607Bits192 :
    AffineL2UpperTailAt
      { distribution := .balancedTernary, rows := 394,
        threshold := NonnegativeRatio.ofNat 607 }
      (failureTarget 192) :=
  ternaryL2Upper394Threshold607Bits192.to_affine

/-- The row-restricted upper bound with an arbitrary fixed centered shift. -/
theorem ternaryAffineLInfUpper462Cap1358Over100Bits197 :
    AffineLInfUpperTailAt
      { distribution := .balancedTernary, rows := 462,
        coordinateThreshold :=
          { numerator := 1358, denominator := 100, denominator_pos := by decide } }
      (failureTarget 197) :=
  ternaryLInfUpper462Cap1358Over100Bits197.to_affine

end CertifiedJLFast.Results.Transports.Rows
