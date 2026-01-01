/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib.Data.ENNReal.Basic

/-!
# Exact nonnegative ratios

Natural numerators and positive natural denominators keep modular event
thresholds in exact integer arithmetic.
-/

namespace CertifiedJL

/-- A nonnegative rational represented by a natural numerator and a positive
natural denominator. -/
structure NonnegativeRatio where
  numerator : ℕ
  denominator : ℕ
  denominator_pos : 0 < denominator
deriving DecidableEq, Repr

namespace NonnegativeRatio

/-- Embed a natural number as an exact ratio. -/
def ofNat (n : ℕ) : NonnegativeRatio where
  numerator := n
  denominator := 1
  denominator_pos := by decide

/-- The ratio `numerator / denominator` in the reals. -/
noncomputable def toReal (ratio : NonnegativeRatio) : ℝ :=
  (ratio.numerator : ℝ) / ratio.denominator

/-- The ratio `numerator / denominator` in the extended nonnegative reals. -/
noncomputable def toENNReal (ratio : NonnegativeRatio) : ENNReal :=
  (ratio.numerator : ENNReal) / ratio.denominator

/-- Exact cross-multiplied comparison of two nonnegative ratios. -/
def LE (left right : NonnegativeRatio) : Prop :=
  left.numerator * right.denominator ≤
    right.numerator * left.denominator

/-- Exact comparison of the squares of two nonnegative ratios. -/
def SquaredLE (left right : NonnegativeRatio) : Prop :=
  left.numerator ^ 2 * right.denominator ^ 2 ≤
    right.numerator ^ 2 * left.denominator ^ 2

end NonnegativeRatio
end CertifiedJL
