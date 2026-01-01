/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Results.Transports.Rows
import CertifiedJL.Results.Affine.L2.Lower.Endpoints
import CertifiedJL.Results.Affine.LInf.Lower.Endpoints
import CertifiedJL.Results.Affine.L2.Upper
import CertifiedJL.Results.Affine.LInf.Upper
import CertifiedJL.Results.Affine.LInf.Lower.MarginTwo
import CertifiedJL.Results.Affine.LInf.Lower.Direct
import CertifiedJL.Results.Affine.L2.Lower.General
import CertifiedJL.Results.LInf.Lower.HighSecurity
import CertifiedJL.Results.LInf.Upper.HighSecurity
import CertifiedJL.Results.L2.Lower.HighSecurity
import CertifiedJL.Results.L2.Lower.Rows192Bits128
import CertifiedJL.Results.L2.Upper.Rows192Bits128
import CertifiedJL.Results.LInf.Lower.Rows192Bits128
import CertifiedJL.Results.LInf.Upper.Rows192Bits128
import CertifiedJL.Results.Composites.Rows192Bits128
import CertifiedJL.Results.L2.Lower.Rows256Bits128
import CertifiedJL.Results.L2.Upper.Rows256Bits128
import CertifiedJL.Results.L2.Upper.Rows256Frontier
import CertifiedJL.Results.Composites.L2Rows256Bits128
import CertifiedJL.Results.L2.Lower.Rows256Bits152
import CertifiedJL.Results.L2.Lower.Rows256Bits192
import CertifiedJL.Results.L2.Upper.Rows256Bits192
import CertifiedJL.Results.LInf.Upper.Rows256Bits192
import CertifiedJL.Results.L2.Lower.Rows384Bits192
import CertifiedJL.Results.L2.Upper.Rows384Bits192
import CertifiedJL.Results.LInf.Upper.Rows384Bits192
import CertifiedJL.Results.L2.Upper.Rows512Bits192
import CertifiedJL.Results.LInf.Upper.Rows512Bits192
import CertifiedJL.Results.L2.Lower.Rows512Bits192
import CertifiedJL.Results.L2.Lower.Rows512Bits193
import CertifiedJL.Results.L2.Upper.Rows512Bits256
import CertifiedJL.Results.LInf.Upper.Rows512Bits256
import CertifiedJL.Results.L2.Lower.Rows512Bits256
import CertifiedJL.Results.LInf.Lower.TwoDecimal

/-!
# Kernel-checked result surface

This umbrella contains unconditional certified probability results. It does
not import application-specific or assumption-explicit reductions.

For a result's mathematical content, follow this short path:

* a theorem in this `Results` hierarchy;
* the named proposition in `CertifiedJL.Statements.L2.Lower`,
  `CertifiedJL.Statements.L2.Upper`, `CertifiedJL.Statements.LInf.Lower`, or
  `CertifiedJL.Statements.LInf.Upper`;
* the probability event and projected-norm formula in `CertifiedJL.Model`.

The four principal 256-row results are:

* `Results.L2.Lower.Rows256Bits128.ternaryL2ThresholdLower29`, an instance of
  the Euclidean lower-tail schema in `Statements.L2.Lower`;
* `Results.L2.Upper.Rows256Bits128.ternaryL2Upper338`, an instance of the
  Euclidean upper-tail schema in `Statements.L2.Upper`;
* `Results.LInf.Lower.TwoDecimal.lower21Over50Rows256Bits133`, an instance of
  the coordinatewise lower-tail schema in `Statements.LInf.Lower`;
* `Results.LInf.Upper.Rows256.ternaryLInfUpper39Over4Bits133`, an instance of
  the coordinatewise upper-tail schema in `Statements.LInf.Upper`.

For the fixed-shift comparison, see
`Results.Affine.L2.Lower.Endpoints.ternaryAffineL2ThresholdLower256Floor27Bits128`:
it has the same 256-row, 128-bit budget as the unshifted floor-29 result, with
the shift fixed before the random projection is sampled.
-/
