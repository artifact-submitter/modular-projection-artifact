/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Statements.L2.Upper.Rows256Bits128
import CertifiedJL.Statements.OneRow.Endpoint975

/-!
# Main-theorem notation canaries

These direct definitional tests pin the reader-facing balanced-ternary law names
and the VCVio-style probability notation used by the main theorem files.
-/

open scoped BigOperators

namespace CertifiedJL.Tests.MainTheoremNotation

local notation "Pr[" event " | " distribution "]" =>
  eventProbability distribution event

example (d : ℕ) (event : (Fin d → ℤ) → Prop) :
    Pr[event | sparseRademacherRow d] =
      eventProbability
        (uniformPiMap (fun _ : Fin d => sparseBit)) event := rfl

example (m d : ℕ) (event : (Fin m → Fin d → ℤ) → Prop) :
    Pr[event | sparseRademacherMatrix m d] =
      eventProbability
        (uniformPiMap (fun _ : Fin m => @sparseRow d)) event := rfl

example (q m d : ℕ) (J : Fin m → Fin d → ℤ) (w : Fin d → ℤ) :
    modularProjectionSqNorm q J w =
      ∑ j, (centeredMod q (∑ i, J j i * w i)).natAbs ^ 2 := rfl

example (d : ℕ) (w : Fin d → ℤ) :
    sqNorm w = ∑ i, (w i).natAbs ^ 2 := rfl

/-! The following canaries check the exact conversion from the internal
statement contracts to the literal reader-facing theorem types. -/

example (h : SparseOneRow975Statement) :
    ∀ (d : ℕ) (w : EuclideanSpace ℝ (Fin d)),
      Pr[(fun row =>
        |∑ i, (row i : ℝ) * w i| > (39 / 4 : ℝ) * ‖w‖) |
        sparseRademacherRow d] <
      (2 : ENNReal)⁻¹ ^ 141 := by
  intro d w
  rw [eventProbability_congr (sparseRademacherRow d)
    (event' := SparseOneRow975Event w) (by intro row; rfl)]
  simpa [failureTarget, sparseOneRowSecurityBits] using h d w

example (h : SparseUpper128Statement) :
    ∀ (q d : ℕ) (w : Fin d → ℤ),
      Pr[(fun J =>
        (∑ j,
          (centeredMod q (∑ i, J j i * w i)).natAbs ^ 2) >
            338 * ∑ i, (w i).natAbs ^ 2) |
        sparseRademacherMatrix 256 d] <
      (2 : ENNReal)⁻¹ ^ 128 := by
  intro q d w
  rw [eventProbability_congr (sparseRademacherMatrix 256 d)
    (event' := SparseUpperFailure q w) (by intro J; rfl)]
  simpa [rowCount, failureTarget, securityBits] using h q d w

end CertifiedJL.Tests.MainTheoremNotation
