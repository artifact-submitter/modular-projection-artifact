/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Soundness.ThresholdNearChordSoundness128

/-! # Structural partitions for power-chord certificates -/

namespace CertifiedJL
namespace ThresholdNearChord128

inductive Plan where
  | leaf
  | splitX (left right : Plan)
  | splitA (left right : Plan)
  | splitY (left right : Plan)
deriving DecidableEq, Repr

def xMid (cell : Cell) : ℚ := (cell.xLower + cell.xUpper) / 2
def aMid (cell : Cell) : ℚ := (cell.aLower + cell.aUpper) / 2
def yMid (cell : Cell) : ℚ := (cell.yLower + cell.yUpper) / 2

def leftX (cell : Cell) : Cell := { cell with xUpper := xMid cell }
def rightX (cell : Cell) : Cell := { cell with xLower := xMid cell }
def leftA (cell : Cell) : Cell := { cell with aUpper := aMid cell }
def rightA (cell : Cell) : Cell := { cell with aLower := aMid cell }
def leftY (cell : Cell) : Cell := { cell with yUpper := yMid cell }
def rightY (cell : Cell) : Cell := { cell with yLower := yMid cell }

end ThresholdNearChord128
end CertifiedJL
