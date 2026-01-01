/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Results.L2.Upper.Rows256Bits128
import CertifiedJL.Results.L2.Upper.Rows384Bits192
import CertifiedJL.Results.L2.Upper.Rows512Bits192
import CertifiedJL.Results.LInf.Upper.Rows512Bits256
import CertifiedJL.Statements.Transport.Upper
import CertifiedJL.Statements.Transport.ParameterMonotonicity
import CertifiedJL.Statements.Transport.Rows

/-!
# Upper-tail endpoints derived by row restriction

These results use no new numerical certificate.  Each is an exact row marginal
of an existing upper-tail theorem, followed where necessary by a monotone
failure-budget relaxation.
-/

namespace CertifiedJL.Results.Transports.Rows

/-- The 256-row threshold-338 theorem restricted to 195 rows. -/
theorem ternaryL2Upper195Threshold338Bits128 :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 195
        threshold := NonnegativeRatio.ofNat 338 }
      (failureTarget 128) :=
  CertifiedJL.Results.L2.Upper.Rows256Bits128.ternaryL2Upper338.restrict_rows (by omega)

/-- The 384-row threshold-509 theorem restricted to 264 rows and relaxed from
192-bit to 128-bit failure. -/
theorem ternaryL2Upper264Threshold509Bits128 :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 264
        threshold := NonnegativeRatio.ofNat 509 }
      (failureTarget 128) :=
  (CertifiedJL.Results.L2.Upper.Rows384Bits192.ternaryL2Upper509.restrict_rows (by omega)).mono_budget
    (failureTarget_antitone (by omega))

/-- The 512-row threshold-607 theorem restricted to 394 rows. -/
theorem ternaryL2Upper394Threshold607Bits192 :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 394
        threshold := NonnegativeRatio.ofNat 607 }
      (failureTarget 192) :=
  CertifiedJL.Results.L2.Upper.Rows512Bits192.ternaryL2Upper607.restrict_rows (by omega)

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
  (CertifiedJL.Results.LInf.Upper.Rows512Bits256.ternaryLInfUpper1358Over100.restrict_rows
    (by omega)).mono_budget (failureTarget_antitone (by omega))

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

/-- All eight row-restricted upper endpoints stated together for the paper contract. -/
theorem allRowRestrictedUpperEndpoints :
    (L2UpperTailAt
      { distribution := .balancedTernary
        rows := 195
        threshold := NonnegativeRatio.ofNat 338 }
      (failureTarget 128)) ∧
    (L2UpperTailAt
      { distribution := .balancedTernary
        rows := 264
        threshold := NonnegativeRatio.ofNat 509 }
      (failureTarget 128)) ∧
    (L2UpperTailAt
      { distribution := .balancedTernary
        rows := 394
        threshold := NonnegativeRatio.ofNat 607 }
      (failureTarget 192)) ∧
    (LInfUpperTailAt
      { distribution := .balancedTernary
        rows := 462
        coordinateThreshold :=
          { numerator := 1358, denominator := 100,
            denominator_pos := by decide } }
      (failureTarget 197)) ∧
    (AffineL2UpperTailAt
      { distribution := .balancedTernary, rows := 195,
        threshold := NonnegativeRatio.ofNat 338 }
      (failureTarget 128)) ∧
    (AffineL2UpperTailAt
      { distribution := .balancedTernary, rows := 264,
        threshold := NonnegativeRatio.ofNat 509 }
      (failureTarget 128)) ∧
    (AffineL2UpperTailAt
      { distribution := .balancedTernary, rows := 394,
        threshold := NonnegativeRatio.ofNat 607 }
      (failureTarget 192)) ∧
    (AffineLInfUpperTailAt
      { distribution := .balancedTernary, rows := 462,
        coordinateThreshold :=
          { numerator := 1358, denominator := 100, denominator_pos := by decide } }
      (failureTarget 197)) :=
  ⟨ternaryL2Upper195Threshold338Bits128,
    ternaryL2Upper264Threshold509Bits128,
    ternaryL2Upper394Threshold607Bits192,
    ternaryLInfUpper462Cap1358Over100Bits197,
    ternaryAffineL2Upper195Threshold338Bits128,
    ternaryAffineL2Upper264Threshold509Bits128,
    ternaryAffineL2Upper394Threshold607Bits192,
    ternaryAffineLInfUpper462Cap1358Over100Bits197⟩

end CertifiedJL.Results.Transports.Rows
