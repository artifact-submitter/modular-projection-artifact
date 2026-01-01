/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Modular.Projection
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr

/-!
# Squared norms for integer projections

The headline theorems use natural-number squared norms. This module relates
that representation to ordinary integer and real sums of squares and proves
that centered modular reduction contracts the projected squared norm.
-/

open scoped BigOperators

namespace CertifiedJL

/-- The natural squared Euclidean norm of an integer source vector:
`∑ i, (w i).natAbs ^ 2`. -/
def sqNorm {d : ℕ} (w : Fin d → ℤ) : ℕ :=
  ∑ i, (w i).natAbs ^ 2

/-- The natural squared norm vanishes exactly on the zero vector. -/
@[simp]
theorem sqNorm_eq_zero_iff {d : ℕ} (w : Fin d → ℤ) :
    sqNorm w = 0 ↔ w = 0 := by
  simp [sqNorm, funext_iff]

/-- A nonzero integer vector has positive natural squared norm. -/
theorem sqNorm_pos_iff {d : ℕ} (w : Fin d → ℤ) :
    0 < sqNorm w ↔ w ≠ 0 := by
  rw [Nat.pos_iff_ne_zero, ne_eq, sqNorm_eq_zero_iff]

/-- Casting the natural squared norm to `ℤ` gives the usual sum of squares. -/
theorem intCast_sqNorm {d : ℕ} (w : Fin d → ℤ) :
    (sqNorm w : ℤ) = ∑ i, w i ^ 2 := by
  simp [sqNorm, sq_abs]

/-- Casting the natural squared norm to `ℝ` gives the usual sum of squares. -/
theorem realCast_sqNorm {d : ℕ} (w : Fin d → ℤ) :
    (sqNorm w : ℝ) = ∑ i, (w i : ℝ) ^ 2 := by
  exact_mod_cast intCast_sqNorm w

/--
Casting the modular projected squared norm to `ℤ` gives the sum of squared centered residues.
-/
theorem intCast_modularProjectionSqNorm {q m d : ℕ}
    (J : Matrix (Fin m) (Fin d) ℤ) (w : Fin d → ℤ) :
    (modularProjectionSqNorm q J w : ℤ) =
      ∑ j, centeredMod q (rowDot J w j) ^ 2 := by
  simp [modularProjectionSqNorm, sq_abs]

/--
Casting the modular projected squared norm to `ℝ` gives the real sum of squared centered residues.
-/
theorem realCast_modularProjectionSqNorm {q m d : ℕ}
    (J : Matrix (Fin m) (Fin d) ℤ) (w : Fin d → ℤ) :
    (modularProjectionSqNorm q J w : ℝ) =
      ∑ j, (centeredMod q (rowDot J w j) : ℝ) ^ 2 := by
  exact_mod_cast intCast_modularProjectionSqNorm J w

/-- Casting the shifted modular projected squared norm to `ℤ` gives the sum of squared centered
affine residues. -/
theorem intCast_shiftedModularProjectionSqNorm {q m d : ℕ} (shift : Fin m → ℤ)
    (J : Matrix (Fin m) (Fin d) ℤ) (w : Fin d → ℤ) :
    (shiftedModularProjectionSqNorm q shift J w : ℤ) =
      ∑ j, centeredMod q (shift j + rowDot J w j) ^ 2 := by
  simp [shiftedModularProjectionSqNorm, sq_abs]

/-- Casting the shifted modular projected squared norm to `ℝ` gives the corresponding real sum
of squares. -/
theorem realCast_shiftedModularProjectionSqNorm {q m d : ℕ} (shift : Fin m → ℤ)
    (J : Matrix (Fin m) (Fin d) ℤ) (w : Fin d → ℤ) :
    (shiftedModularProjectionSqNorm q shift J w : ℝ) =
      ∑ j, (centeredMod q (shift j + rowDot J w j) : ℝ) ^ 2 := by
  exact_mod_cast intCast_shiftedModularProjectionSqNorm shift J w

/-- Centered modular reduction contracts the squared norm of every projected vector. -/
theorem modularProjectionSqNorm_le_projectionSqNorm {q m d : ℕ}
    (J : Matrix (Fin m) (Fin d) ℤ) (w : Fin d → ℤ) :
    modularProjectionSqNorm q J w ≤ projectionSqNorm J w := by
  apply Finset.sum_le_sum
  intro j _
  gcongr
  exact centeredMod_natAbs_le q (rowDot J w j)

/-- The unreduced projected squared norm is the sum of the integer row-dot-product squares. -/
theorem intCast_projectionSqNorm {m d : ℕ}
    (J : Matrix (Fin m) (Fin d) ℤ) (w : Fin d → ℤ) :
    (projectionSqNorm J w : ℤ) = ∑ j, rowDot J w j ^ 2 := by
  simp [projectionSqNorm, sq_abs]

/-- Casting the unreduced projected squared norm to `ℝ` gives the usual sum of squares. -/
theorem realCast_projectionSqNorm {m d : ℕ}
    (J : Matrix (Fin m) (Fin d) ℤ) (w : Fin d → ℤ) :
    (projectionSqNorm J w : ℝ) = ∑ j, (rowDot J w j : ℝ) ^ 2 := by
  exact_mod_cast intCast_projectionSqNorm J w

/-- The modular projected squared norm is bounded by the real squared norm of
the unreduced projection. -/
theorem realCast_modularProjectionSqNorm_le {q m d : ℕ}
    (J : Matrix (Fin m) (Fin d) ℤ) (w : Fin d → ℤ) :
    (modularProjectionSqNorm q J w : ℝ) ≤ ∑ j, (rowDot J w j : ℝ) ^ 2 := by
  calc
    (modularProjectionSqNorm q J w : ℝ) ≤ projectionSqNorm J w := by
      exact_mod_cast modularProjectionSqNorm_le_projectionSqNorm J w
    _ = ∑ j, (rowDot J w j : ℝ) ^ 2 := realCast_projectionSqNorm J w

end CertifiedJL
