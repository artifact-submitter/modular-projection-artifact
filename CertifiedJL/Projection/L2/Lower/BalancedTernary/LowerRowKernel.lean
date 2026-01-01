/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Vectors.SquaredNorm

/-!
# Sparse lower-tail row kernel

This module names the row kernel shared by the threshold-relative lower-tail
proofs. It deliberately contains no actual-norm lower-tail statement.
-/

open scoped BigOperators

namespace CertifiedJL

/-- The real row kernel associated with centered modular reduction. -/
def sparseLowerRowKernel
    (q : ℕ) {d : ℕ} (w : Fin d → ℤ) (row : Fin d → ℤ) : ℝ :=
  (centeredMod q (∑ i, row i * w i) : ℝ) ^ 2

@[simp]
theorem sparseLowerRowKernel_apply
    (q : ℕ) {d : ℕ} (w : Fin d → ℤ) (row : Fin d → ℤ) :
    sparseLowerRowKernel q w row =
      (centeredMod q (∑ i, row i * w i) : ℝ) ^ 2 :=
  rfl

/-- The row kernel after adding a fixed integer shift before centered modular
reduction. -/
def affineSparseLowerRowKernel
    (q : ℕ) (shift : ℤ) {d : ℕ} (w : Fin d → ℤ)
    (row : Fin d → ℤ) : ℝ :=
  (centeredMod q (shift + ∑ i, row i * w i) : ℝ) ^ 2

@[simp]
theorem affineSparseLowerRowKernel_apply
    (q : ℕ) (shift : ℤ) {d : ℕ} (w : Fin d → ℤ)
    (row : Fin d → ℤ) :
    affineSparseLowerRowKernel q shift w row =
      (centeredMod q (shift + ∑ i, row i * w i) : ℝ) ^ 2 :=
  rfl

@[simp]
theorem affineSparseLowerRowKernel_zero
    (q : ℕ) {d : ℕ} (w : Fin d → ℤ) (row : Fin d → ℤ) :
    affineSparseLowerRowKernel q 0 w row = sparseLowerRowKernel q w row := by
  simp [affineSparseLowerRowKernel, sparseLowerRowKernel]

end CertifiedJL
