/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantDirectCover128.Shard23

/-!
# Target data for the 192-row, floor-12 direct dominant cover

The inherited selector geometry works unchanged except for cell 95, whose
target-dependent tilt is changed from 13/5 to 19/5. Its row caps are the
exact upper endpoints of the reflected interval evaluator.
-/

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover192Bits128

open ConstantNumeric
open SparseThresholdDominant.Numeric

def budget : ℚ := 19 / (20 * 2 ^ 128)

def targetCell95 : Cell :=
  { ConstantDirectCover128Shard23.cell95 with z := 19 / 5 }

def targetCertificate95 : Certificate where
  inactiveUpper :=
    (inactiveRow targetCell95.decode targetCell95.z).upperRat
  activeUpper :=
    (activeRow targetCell95.decode targetCell95.z).upperRat
  growthUpper := 0

def retargetCell (cell : Cell) : Cell :=
  if cell = ConstantDirectCover128Shard23.cell95 then targetCell95 else cell

def retargetCertificate (entry : Entry) : Certificate :=
  if entry.cell = ConstantDirectCover128Shard23.cell95 then
    targetCertificate95
  else entry.certificate

def retargetEntry (entry : Entry) : Entry :=
  ⟨retargetCell entry.cell, retargetCertificate entry⟩

def targetCheck (entry : Entry) : Bool :=
  localCertifiedCheckFor 192 12 (retargetEntry entry).cell
    (retargetEntry entry).certificate budget

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover192Bits128
