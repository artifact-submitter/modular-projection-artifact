/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Data.ThresholdNearCoarseNumeric128

/-! # Executable subdivision plans for the coarse near-band checker

Search is an untrusted proposal operation. Production replay checks supplied
plans; structural coverage is proved separately in the soundness layer.
-/

namespace CertifiedJL.ThresholdNearCoarse128

/-- A binary subdivision plan.  Each split bisects exactly one coordinate of
the current rational cell, so coverage is structural rather than inferred
from a flat collection of sampled rectangles. -/
inductive Plan where
  | leaf
  | splitX (left right : Plan)
  | splitA (left right : Plan)
deriving DecidableEq, Repr

def xMid (cell : Cell) : ℚ := (cell.xLower + cell.xUpper) / 2
def aMid (cell : Cell) : ℚ := (cell.aLower + cell.aUpper) / 2

def leftX (cell : Cell) : Cell :=
  { cell with xUpper := xMid cell }

def rightX (cell : Cell) : Cell :=
  { cell with xLower := xMid cell }

def leftA (cell : Cell) : Cell :=
  { cell with aUpper := aMid cell }

def rightA (cell : Cell) : Cell :=
  { cell with aLower := aMid cell }

/-- Every leaf must pass the sound local checker. -/
def planCheck : Cell → Plan → Bool
  | cell, .leaf => certifiedCheck cell
  | cell, .splitX left right =>
      planCheck (leftX cell) left && planCheck (rightX cell) right
  | cell, .splitA left right =>
      planCheck (leftA cell) left && planCheck (rightA cell) right

/-- Construct a bounded adaptive dyadic cover, alternating the split
coordinate.  Already certified rectangles stop immediately. -/
def adaptiveRefine : ℕ → Bool → Cell → Plan
  | 0, _, _ => .leaf
  | depth + 1, splitXNext, cell =>
      if certifiedCheck cell then
        .leaf
      else if splitXNext then
        .splitX (adaptiveRefine depth false (leftX cell))
          (adaptiveRefine depth false (rightX cell))
      else
        .splitA (adaptiveRefine depth true (leftA cell))
          (adaptiveRefine depth true (rightA cell))

end CertifiedJL.ThresholdNearCoarse128

