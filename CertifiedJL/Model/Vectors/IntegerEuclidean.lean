/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Vectors.Real
import CertifiedJL.Model.Vectors.SquaredNorm

/-!
# Integer vectors with their Euclidean norm

This neutral bridge casts integer coefficient vectors into Euclidean space
and relates the resulting norm and row dot product to the integer models.
-/

open scoped BigOperators

namespace CertifiedJL

/-- The real Euclidean vector obtained by casting integer coordinates. -/
def integerEuclideanVector {d : ℕ} (w : Fin d → ℤ) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i ↦ (w i : ℝ)

/-- Casting an integer vector preserves its squared Euclidean norm. -/
theorem norm_sq_integerEuclideanVector {d : ℕ} (w : Fin d → ℤ) :
    ‖integerEuclideanVector w‖ ^ 2 = (sqNorm w : ℝ) := by
  rw [PiLp.norm_sq_eq_of_L2]
  simpa [integerEuclideanVector, Real.norm_eq_abs] using (realCast_sqNorm w).symm

/-- Integer and Euclidean row dot products agree after casting. -/
theorem euclideanRowDot_integerEuclideanVector {d : ℕ}
    (row : Fin d → ℤ) (w : Fin d → ℤ) :
    euclideanRowDot row (integerEuclideanVector w) =
      ((∑ i, row i * w i : ℤ) : ℝ) := by
  simp [euclideanRowDot, realRowDot, integerEuclideanVector]

end CertifiedJL
