/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJLFast.Results.Transports.Rows
import CertifiedJLFast.Results.Affine.L2.Lower.Endpoints
import CertifiedJLFast.Results.Affine.L2.Upper
import CertifiedJLFast.Results.Affine.LInf.Lower.Endpoints
import CertifiedJLFast.Results.Affine.LInf.Lower.MarginTwo
import CertifiedJLFast.Results.Affine.LInf.Upper
import CertifiedJLFast.Results.Affine.LInf.Lower.Direct
import CertifiedJLFast.Results.Affine.L2.Lower.General
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
import CertifiedJL.Obstructions.Lightweight

/-!
# Assumption-backed fast theorem assembly

This separate library replaces only cataloged finite certificate replays by
named assumptions.  All statement, analytic, soundness, routing, and theorem
assembly code remains kernel checked.  It is never imported by `CertifiedJL`.
-/
