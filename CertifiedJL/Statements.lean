/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Statements.L2.Lower
import CertifiedJL.Statements.L2.Lower.Affine
import CertifiedJL.Statements.L2.Upper
import CertifiedJL.Statements.L2.Upper.Rows256Bits128
import CertifiedJL.Statements.LInf.Lower
import CertifiedJL.Statements.LInf.Lower.Affine
import CertifiedJL.Statements.LInf.Upper
import CertifiedJL.Statements.OneRow.Endpoint975
import CertifiedJL.Statements.OneRow.Upper
import CertifiedJL.Statements.Shared.BudgetAllocation
import CertifiedJL.Statements.Shared.ExactRatio
import CertifiedJL.Statements.Shared.Input
import CertifiedJL.Statements.Transport.LInfToL2
import CertifiedJL.Statements.Transport.ParameterMonotonicity
import CertifiedJL.Statements.Transport.Rows
import CertifiedJL.Statements.Transport.Scaling
import CertifiedJL.Statements.Transport.Upper
import CertifiedJL.Model.ProjectionDistribution

/-!
# Parameterized probability statements

This umbrella exposes every reusable mathematical proposition schema without
importing a concrete certificate, counterexample, or protocol adapter. Protocol
composition remains available through the opt-in `CertifiedJL.Protocol`
umbrella.
-/
