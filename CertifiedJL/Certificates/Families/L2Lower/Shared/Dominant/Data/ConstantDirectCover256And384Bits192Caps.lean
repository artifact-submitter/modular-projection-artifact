/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantDirectCover128.Shard02
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantDirectCover128.Shard03

/-! # Shared tightened row caps for the 256/192 and 384/192 direct covers -/

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover256And384Bits192Caps

open ConstantNumeric

def certificate8 : Certificate where
  inactiveUpper := 10002 / 10000
  activeUpper := 187 / 10000
  growthUpper := 0

def certificate14 : Certificate where
  inactiveUpper := 10002 / 10000
  activeUpper := 128 / 10000
  growthUpper := 0

def certificate15 : Certificate where
  inactiveUpper := 9962 / 10000
  activeUpper := 186 / 10000
  growthUpper := 0

/-- The two targets use exactly the same three tightened row caps. -/
def targetCertificate (entry : Entry) : Certificate :=
  if entry.cell = ConstantDirectCover128Shard02.cell8 then certificate8
  else if entry.cell = ConstantDirectCover128Shard03.cell14 then certificate14
  else if entry.cell = ConstantDirectCover128Shard03.cell15 then certificate15
  else entry.certificate

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover256And384Bits192Caps
