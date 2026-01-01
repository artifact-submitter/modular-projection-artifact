/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData

/-! # Target data for the 512-row, floor-71 direct dominant cover -/

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover512Bits192

open ConstantNumeric

def budget : ℚ := 99 / (100 * 2 ^ 192)

def targetCheck (entry : Entry) : Bool :=
  localCertifiedCheckFor 512 71 entry.cell entry.certificate budget

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover512Bits192
