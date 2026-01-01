/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Distributions.Signs
import CertifiedJL.Probability.Finite.Experiment

/-!
# Balanced-ternary projection distribution

A balanced-ternary entry is `-1`, `0`, or `1` with probabilities `1/4`,
`1/2`, and `1/4`. Two independent bits provide an exact finite seed model.
Rows and matrices use independent seeds at every coordinate.
-/

namespace CertifiedJL

/-- Two independent bits for each entry of a balanced-ternary row. -/
abbrev SparseRowSeed (d : ℕ) := Fin d → Bool × Bool

/-- Two independent bits for each entry of a balanced-ternary matrix. -/
abbrev SparseSeed (rows d : ℕ) := Fin rows → Fin d → Bool × Bool

/-- Interpret two bits as a balanced-ternary entry. Equal bits produce `±1`;
different bits produce `0`. -/
def sparseBit : Bool × Bool → ℤ
  | (false, false) => -1
  | (true, true) => 1
  | _ => 0

/-- A balanced-ternary entry is the integer average of its two signs. -/
theorem sparseBit_eq_average (b : Bool × Bool) :
    2 * sparseBit b = signBit b.1 + signBit b.2 := by
  rcases b with ⟨b₁, b₂⟩
  cases b₁ <;> cases b₂ <;> decide

/-- Interpret a balanced-ternary row seed as an integer row. -/
def sparseRow {d : ℕ} (seed : SparseRowSeed d) : Fin d → ℤ :=
  fun i => sparseBit (seed i)

/-- Interpret a balanced-ternary matrix seed as an integer matrix. -/
def sparseMatrix {rows d : ℕ} (seed : SparseSeed rows d) :
    Fin rows → Fin d → ℤ :=
  fun j => sparseRow (seed j)

/-- The balanced-ternary entry PMF, with masses `1/4`, `1/2`, and `1/4`
at `-1`, `0`, and `1`. -/
noncomputable def sparseEntryPMF : PMF ℤ :=
  (PMF.uniformOfFintype (Bool × Bool)).map sparseBit

/-- The PMF of one row of independent balanced-ternary entries. -/
noncomputable def sparseRademacherRow (d : ℕ) : PMF (Fin d → ℤ) :=
  uniformPiMap (fun _ : Fin d => sparseBit)

/-- The PMF of a matrix of mutually independent balanced-ternary entries. -/
noncomputable def sparseRademacherMatrix (rows d : ℕ) :
    PMF (Fin rows → Fin d → ℤ) :=
  uniformPiMap (fun _ : Fin rows => @sparseRow d)

end CertifiedJL
