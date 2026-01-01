/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantDirectCover128.Shard02
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantDirectCover128.Shard03

/-!
# Target data for the 512-row, floor-57 direct dominant cover

The inherited selector geometry is unchanged except that its tiny cell 14 is
split at residual ratio 1/1024. Cell 8 uses tilt 4 instead of 81/20. Exact
reflected interval endpoints replace rounded row caps for this target.
-/

namespace CertifiedJL.SparseThresholdDominant.ConstantDirectCover512Bits256

open ConstantNumeric
open SparseThresholdDominant.Numeric

def budget : ℚ := 24 / (25 * 2 ^ 256)

def cell8Target : Cell :=
  { ConstantDirectCover128Shard02.cell8 with z := 4 }

def cell14A : Cell :=
  { ConstantDirectCover128Shard03.cell14 with upper := 1 / 1024 }

def cell14B : Cell :=
  { ConstantDirectCover128Shard03.cell14 with lower := 1 / 1024 }

def targetCellA (cell : Cell) : Cell :=
  if cell = ConstantDirectCover128Shard02.cell8 then cell8Target
  else if cell = ConstantDirectCover128Shard03.cell14 then cell14A
  else cell

def exactCertificate (cell : Cell) : Certificate where
  inactiveUpper := max 0 (inactiveRow cell.decode cell.z).upperRat
  activeUpper := max 0 (activeRow cell.decode cell.z).upperRat
  growthUpper := 0

def targetCheckA (entry : Entry) : Bool :=
  let cell := targetCellA entry.cell
  localCertifiedCheckFor 512 57 cell (exactCertificate cell) budget

end CertifiedJL.SparseThresholdDominant.ConstantDirectCover512Bits256
