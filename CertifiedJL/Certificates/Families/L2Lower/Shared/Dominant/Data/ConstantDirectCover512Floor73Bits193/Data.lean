/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

/-! # Shared data for the 512-row, floor-73, 193-bit direct-cover replay -/

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover512Floor73Bits193

open ConstantNumeric

def budget : ℚ := 99999 / (100000 * 2 ^ 193)

def targetCheck (entry : Entry) : Bool :=
  localCertifiedCheckFor 512 73 entry.cell entry.certificate budget

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover512Floor73Bits193
