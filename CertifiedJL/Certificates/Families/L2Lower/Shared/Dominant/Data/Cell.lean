/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib.Data.Rat.Defs

/-! Rational input schema for threshold dominant certificates. -/

namespace CertifiedJL

/-- A residual-ratio cell with an independent public-threshold-ratio cap at a
specified row count. -/
structure ThresholdDominantCellRowBoundsAt (rows : ℕ) where
  lower : ℚ
  upper : ℚ
  thresholdUpper : ℚ
  modulusLower : ℚ
  z : Fin (rows + 1) → ℚ

/-- Compatibility specialization of threshold dominant cells at 256 rows. -/
abbrev ThresholdDominantCellRowBounds :=
  ThresholdDominantCellRowBoundsAt 256

namespace ThresholdDominantCellRowBoundsAt

def Valid {rows : ℕ} (cell : ThresholdDominantCellRowBoundsAt rows) : Prop :=
  0 ≤ cell.lower ∧ cell.lower ≤ cell.upper ∧
    0 ≤ cell.thresholdUpper ∧ 1 < cell.modulusLower ∧
      ∀ k, 0 ≤ cell.z k

end ThresholdDominantCellRowBoundsAt

namespace ThresholdDominantCellRowBounds

def Valid (cell : ThresholdDominantCellRowBounds) : Prop :=
  ThresholdDominantCellRowBoundsAt.Valid cell

end ThresholdDominantCellRowBounds

end CertifiedJL
