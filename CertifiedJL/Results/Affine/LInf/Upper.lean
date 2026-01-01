/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Statements.Transport.Upper
import CertifiedJL.Results.LInf.Upper.Rows192Bits128
import CertifiedJL.Results.LInf.Upper.Rows256
import CertifiedJL.Results.LInf.Upper.Rows256Bits192
import CertifiedJL.Results.LInf.Upper.Rows384Bits192
import CertifiedJL.Results.LInf.Upper.Rows512Bits192
import CertifiedJL.Results.LInf.Upper.Rows512Bits256

/-! # Affine upper endpoints and margin-two lower endpoints -/

namespace CertifiedJL.Results.Affine.LInf.Upper

open CertifiedJL

/-- The unchanged 192-row upper endpoint plus the exact centered-shift norm. -/
theorem ternaryAffineLInfUpper192Cap487Over50Bits128 :
    AffineLInfUpperTailAt
      { distribution := .balancedTernary, rows := 192,
        coordinateThreshold := { numerator := 487, denominator := 50, denominator_pos := by decide } }
      (failureTarget 128) :=
  CertifiedJL.Results.LInf.Upper.Rows192Bits128.ternaryLInfUpper487Over50.to_affine

/-- The unchanged 256-row upper endpoint plus the exact centered-shift norm. -/
theorem ternaryAffineLInfUpper256Cap39Over4Bits133 :
    AffineLInfUpperTailAt
      { distribution := .balancedTernary, rows := 256,
        coordinateThreshold := { numerator := 39, denominator := 4, denominator_pos := by decide } }
      (failureTarget 133) :=
  CertifiedJL.Results.LInf.Upper.Rows256.ternaryLInfUpper39Over4Bits133.to_affine

/-- The unchanged 256-row upper endpoint plus the exact centered-shift norm. -/
theorem ternaryAffineLInfUpper256Cap1181Over100Bits192 :
    AffineLInfUpperTailAt
      { distribution := .balancedTernary, rows := 256,
        coordinateThreshold := { numerator := 1181, denominator := 100, denominator_pos := by decide } }
      (failureTarget 192) :=
  CertifiedJL.Results.LInf.Upper.Rows256Bits192.ternaryLInfUpper1181Over100.to_affine

/-- The unchanged 384-row upper endpoint plus the exact centered-shift norm. -/
theorem ternaryAffineLInfUpper384Cap1183Over100Bits192 :
    AffineLInfUpperTailAt
      { distribution := .balancedTernary, rows := 384,
        coordinateThreshold := { numerator := 1183, denominator := 100, denominator_pos := by decide } }
      (failureTarget 192) :=
  CertifiedJL.Results.LInf.Upper.Rows384Bits192.ternaryLInfUpper1183Over100.to_affine

/-- The unchanged 512-row upper endpoint plus the exact centered-shift norm. -/
theorem ternaryAffineLInfUpper512Cap1184Over100Bits192 :
    AffineLInfUpperTailAt
      { distribution := .balancedTernary, rows := 512,
        coordinateThreshold := { numerator := 1184, denominator := 100, denominator_pos := by decide } }
      (failureTarget 192) :=
  CertifiedJL.Results.LInf.Upper.Rows512Bits192.ternaryLInfUpper1184Over100.to_affine

/-- The unchanged 512-row upper endpoint plus the exact centered-shift norm. -/
theorem ternaryAffineLInfUpper512Cap1358Over100Bits256 :
    AffineLInfUpperTailAt
      { distribution := .balancedTernary, rows := 512,
        coordinateThreshold := { numerator := 1358, denominator := 100, denominator_pos := by decide } }
      (failureTarget 256) :=
  CertifiedJL.Results.LInf.Upper.Rows512Bits256.ternaryLInfUpper1358Over100.to_affine

end CertifiedJL.Results.Affine.LInf.Upper
