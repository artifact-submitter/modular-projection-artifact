/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Statements.OneRow.Upper

/-!
# The coefficient-uniform one-row endpoint at 9.75

This module fixes the exact strict event and 141-bit proposition for the
balanced-ternary one-row endpoint.
-/

namespace CertifiedJL

/-- The security exponent in the coefficient-uniform sparse one-row bound. -/
def sparseOneRowSecurityBits : ℕ := 141
/-- Strict failure event in the coefficient-uniform sparse one-row bound. -/
def SparseOneRow975Event {d : ℕ} (w : EuclideanSpace ℝ (Fin d))
    (row : Fin d → ℤ) : Prop :=
  |euclideanRowDot row w| > (39 / 4 : ℝ) * ‖w‖

/--
The coefficient-uniform sparse one-row proposition.

The statement includes the zero vector and dimension zero: in both cases the
strict failure event is empty, so separate nonzero and positive-dimension
hypotheses would be logically superfluous.
-/
def SparseOneRow975Statement : Prop :=
  ∀ (d : ℕ) (w : EuclideanSpace ℝ (Fin d)),
    eventProbability (sparseRademacherRow d) (SparseOneRow975Event w) <
      failureTarget sparseOneRowSecurityBits

end CertifiedJL
