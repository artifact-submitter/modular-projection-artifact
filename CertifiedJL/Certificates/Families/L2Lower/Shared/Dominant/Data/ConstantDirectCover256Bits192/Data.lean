/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantDirectCover256And384Bits192Caps

/-!
# Target data for the 256-row, floor-9 direct dominant cover

The inherited cover geometry and tilts are unchanged. The old six-decimal caps
are sufficient for 185 of 188 cells. Cells 8, 14, and 15 use tighter rational
roundings of the same dyadic interval evaluator. The exact interval endpoints
can be reproduced by evaluating Numeric.inactiveRow and Numeric.activeRow at
the corresponding cell's decoded geometry and tilt, then reading upperRat.

For cells 8, 14, and 15 respectively, the evaluated decimal pairs are
approximately (1.000122031, 0.018592844), (1.000113844, 0.012776012), and
(0.996189783, 0.018537881). The caps below round each component upward.
Every rounding and final binomial comparison is rechecked in the kernel.
-/

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover256Bits192

open ConstantNumeric
open ConstantDirectCover256And384Bits192Caps

def budget : ℚ := 99 / (100 * 2 ^ 192)

abbrev certificate8 := ConstantDirectCover256And384Bits192Caps.certificate8
abbrev certificate14 := ConstantDirectCover256And384Bits192Caps.certificate14
abbrev certificate15 := ConstantDirectCover256And384Bits192Caps.certificate15
abbrev targetCertificate :=
  ConstantDirectCover256And384Bits192Caps.targetCertificate

def targetCheck (entry : Entry) : Bool :=
  localCertifiedCheckFor 256 9 entry.cell (targetCertificate entry) budget

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover256Bits192
