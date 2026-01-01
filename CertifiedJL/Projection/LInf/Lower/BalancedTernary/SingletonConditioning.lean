/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Distributions.BalancedTernary.SeedPartition

/-!
# Singleton-coordinate conditioning for sparse rows

This module contains the endpoint-independent finite conditioning machinery
for isolating one coordinate of a sparse Rademacher row.
-/

namespace CertifiedJL

/-- The coordinate mask selecting exactly `i`. -/
def singletonCoordinateMask {d : ℕ} (i : Fin d) (j : Fin d) : Prop :=
  j = i

instance singletonCoordinateMask_decidablePred {d : ℕ} (i : Fin d) :
    DecidablePred (singletonCoordinateMask i) := fun j => decEq j i

/-- A seed on a singleton coordinate mask is exactly one sparse-entry seed. -/
def sparseRowSingletonSeedEquiv {d : ℕ} (i : Fin d) :
    SparseRowSeedPart (singletonCoordinateMask i) ≃ Bool × Bool where
  toFun selected := selected ⟨i, rfl⟩
  invFun bits := fun _ => bits
  left_inv selected := by
    funext j
    rw [show j = ⟨i, rfl⟩ by exact Subtype.ext j.2]
  right_inv _ := rfl

/-- Uniform singleton-coordinate seeds map to the uniform two-bit law. -/
theorem map_uniformSparseRowSingletonSeed (d : ℕ) (i : Fin d) :
    (PMF.uniformOfFintype
      (SparseRowSeedPart (singletonCoordinateMask i))).map
        (sparseRowSingletonSeedEquiv i) =
      PMF.uniformOfFintype (Bool × Bool) :=
  map_uniformOfFintype_equiv (sparseRowSingletonSeedEquiv i)

/-- The selected singleton contributes exactly its sparse atom times `w i`. -/
theorem sparseRowSeedPartDot_singleton
    {d : ℕ} (i : Fin d)
    (selected : SparseRowSeedPart (singletonCoordinateMask i))
    (w : Fin d → ℤ) :
    sparseRowSeedPartDot (singletonCoordinateMask i) selected w =
      sparseBit (sparseRowSingletonSeedEquiv i selected) * w i := by
  classical
  unfold sparseRowSeedPartDot sparseRowSingletonSeedEquiv
  let : Unique {j : Fin d // singletonCoordinateMask i j} := {
    default := ⟨i, rfl⟩
    uniq := fun j => Subtype.ext j.2 }
  rw [Fintype.sum_unique]
  rfl

/-- Split a sparse row dot product into one selected coordinate and its complement. -/
theorem sparseRow_join_singleton_dot
    {d : ℕ} (i : Fin d)
    (selected : SparseRowSeedPart (singletonCoordinateMask i))
    (other : SparseRowSeedCompl (singletonCoordinateMask i))
    (w : Fin d → ℤ) :
    (∑ j, sparseRow
        (joinSparseRowSeed (singletonCoordinateMask i) selected other) j * w j) =
      sparseRowSeedComplDot (singletonCoordinateMask i) other w +
        sparseBit (sparseRowSingletonSeedEquiv i selected) * w i := by
  rw [sparseRow_join_dot_eq_add, sparseRowSeedPartDot_singleton]
  ring

end CertifiedJL
