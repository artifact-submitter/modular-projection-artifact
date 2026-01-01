/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Statements.Transport.Upper
import CertifiedJL.Results.L2.Upper.Rows192Bits128
import CertifiedJL.Results.L2.Upper.Rows256Bits128
import CertifiedJL.Results.L2.Upper.Rows256Bits192
import CertifiedJL.Results.L2.Upper.Rows384Bits192
import CertifiedJL.Results.L2.Upper.Rows512Bits192
import CertifiedJL.Results.L2.Upper.Rows512Bits256

/-! # Affine upper endpoints and margin-two lower endpoints -/

namespace CertifiedJL.Results.Affine.L2.Upper

open CertifiedJL

/-- The unchanged 192-row upper endpoint plus the exact centered-shift norm. -/
theorem ternaryAffineL2Upper192Threshold287Bits128 :
    AffineL2UpperTailAt
      { distribution := .balancedTernary, rows := 192,
        threshold := NonnegativeRatio.ofNat 287 }
      (failureTarget 128) :=
  CertifiedJL.Results.L2.Upper.Rows192Bits128.ternaryL2Upper287.to_affine

/-- The unchanged 256-row upper endpoint plus the exact centered-shift norm. -/
theorem ternaryAffineL2Upper256Threshold338Bits128 :
    AffineL2UpperTailAt
      { distribution := .balancedTernary, rows := 256,
        threshold := NonnegativeRatio.ofNat 338 }
      (failureTarget 128) :=
  CertifiedJL.Results.L2.Upper.Rows256Bits128.ternaryL2Upper338.to_affine

/-- The unchanged 512-row upper endpoint plus the exact centered-shift norm. -/
theorem ternaryAffineL2Upper512Threshold607Bits192 :
    AffineL2UpperTailAt
      { distribution := .balancedTernary, rows := 512,
        threshold := NonnegativeRatio.ofNat 607 }
      (failureTarget 192) :=
  CertifiedJL.Results.L2.Upper.Rows512Bits192.ternaryL2Upper607.to_affine

/-- The unchanged 256-row upper endpoint plus the exact centered-shift norm. -/
theorem ternaryAffineL2Upper256Threshold406Bits192 :
    AffineL2UpperTailAt
      { distribution := .balancedTernary, rows := 256,
        threshold := NonnegativeRatio.ofNat 406 }
      (failureTarget 192) :=
  CertifiedJL.Results.L2.Upper.Rows256Bits192.ternaryL2Upper406.to_affine

/-- The unchanged 384-row upper endpoint plus the exact centered-shift norm. -/
theorem ternaryAffineL2Upper384Threshold509Bits192 :
    AffineL2UpperTailAt
      { distribution := .balancedTernary, rows := 384,
        threshold := NonnegativeRatio.ofNat 509 }
      (failureTarget 192) :=
  CertifiedJL.Results.L2.Upper.Rows384Bits192.ternaryL2Upper509.to_affine

/-- The unchanged 512-row upper endpoint plus the exact centered-shift norm. -/
theorem ternaryAffineL2Upper512Threshold681Bits256 :
    AffineL2UpperTailAt
      { distribution := .balancedTernary, rows := 512,
        threshold := NonnegativeRatio.ofNat 681 }
      (failureTarget 256) :=
  CertifiedJL.Results.L2.Upper.Rows512Bits256.ternaryL2Upper681.to_affine

end CertifiedJL.Results.Affine.L2.Upper
