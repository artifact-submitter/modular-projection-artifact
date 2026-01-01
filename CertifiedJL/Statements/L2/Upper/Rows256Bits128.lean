/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Statements.L2.Upper

/-!
# The 256-row, 128-bit balanced-ternary upper contract

This module fixes the exact constants and strict event used by the original
256-row upper result. Defining the proposition does not prove it.
-/

namespace CertifiedJL

/-- The security exponent in the target failure probability `2⁻¹²⁸`. -/
def securityBits : ℕ := 128

/-- The canonical number of independent projection rows. -/
def rowCount : ℕ := 256

/-- The strict sparse upper-failure threshold. -/
def sparseUpperThreshold : ℕ := 338
/-- Strict sparse upper-failure event. -/
def SparseUpperFailure (q : ℕ) {m d : ℕ}
    (w : Fin d → ℤ) (J : Matrix (Fin m) (Fin d) ℤ) : Prop :=
  modularProjectionSqNorm q J w > sparseUpperThreshold * sqNorm w

/-! ## Headline theorem propositions -/

/-- The paper's sharp 256-row sparse upper-tail proposition. -/
def SparseUpper128Statement : Prop :=
  ∀ (q d : ℕ) (w : Fin d → ℤ),
    eventProbability (sparseRademacherMatrix rowCount d)
      (SparseUpperFailure q w) < failureTarget securityBits

end CertifiedJL
