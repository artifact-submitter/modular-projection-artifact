/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Distributions.Entry
import CertifiedJL.Model.ProjectionDistribution
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.FunProp

/-!
# Restricting a balanced-ternary matrix to an initial set of rows

A matrix with fewer balanced-ternary rows is the exact marginal of a matrix
with more rows.  This file records that distributional identity and the
corresponding event-probability transport once, independently of any tail
event.
-/

open MeasureTheory ProbabilityTheory

namespace CertifiedJL

/-- Restrict a matrix or row-indexed vector to its first `smallRows` rows. -/
def restrictRows {smallRows largeRows : ℕ} (hrows : smallRows ≤ largeRows)
    {C : Type*} (x : Fin largeRows → C) : Fin smallRows → C :=
  fun j => x (Fin.castLE hrows j)

@[simp]
theorem restrictRows_apply {smallRows largeRows : ℕ}
    (hrows : smallRows ≤ largeRows) {C : Type*} (x : Fin largeRows → C)
    (j : Fin smallRows) :
    restrictRows hrows x j = x (Fin.castLE hrows j) :=
  rfl

/-- Restricting a balanced-ternary matrix to an initial row segment gives the
balanced-ternary matrix distribution at the smaller row count. -/
theorem sparseRademacherMatrix_map_restrictRows
    {smallRows largeRows d : ℕ} (hrows : smallRows ≤ largeRows) :
    (sparseRademacherMatrix largeRows d).map (restrictRows hrows) =
      sparseRademacherMatrix smallRows d := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (p := sparseRademacherMatrix largeRows d)
    (f := restrictRows hrows) (by fun_prop)]
  rw [sparseRademacherMatrix_toMeasure smallRows d]
  have hindep :
      iIndepFun
        (fun j : Fin smallRows =>
          fun J : Fin largeRows → Fin d → ℤ => J (Fin.castLE hrows j))
        (sparseRademacherMatrix largeRows d).toMeasure :=
    (sparseRademacherMatrix_iIndepRows largeRows d).precomp
      (Fin.castLE_injective hrows)
  calc
    (sparseRademacherMatrix largeRows d).toMeasure.map
        (restrictRows hrows) =
      Measure.pi (fun j : Fin smallRows =>
        (sparseRademacherMatrix largeRows d).toMeasure.map
          (fun J => J (Fin.castLE hrows j))) := by
        change (sparseRademacherMatrix largeRows d).toMeasure.map
            (fun J j => J (Fin.castLE hrows j)) = _
        simpa using hindep.map_fun_eq_pi_map
          (fun _ => (measurable_pi_apply _).aemeasurable)
    _ = Measure.pi
        (fun _ : Fin smallRows => (sparseRademacherRow d).toMeasure) := by
      congr 1
      funext j
      rw [PMF.toMeasure_map (p := sparseRademacherMatrix largeRows d)
        (f := fun J => J (Fin.castLE hrows j)) (by fun_prop)]
      rw [sparseRademacherMatrix_rowMarginal]

/-- The row-restriction marginal for the public row-distribution interface. -/
theorem ProjectionDistribution.matrixPMF_map_restrictRows
    (distribution : ProjectionDistribution) {smallRows largeRows d : ℕ}
    (hrows : smallRows ≤ largeRows) :
    (distribution.matrixPMF largeRows d).map (restrictRows hrows) =
      distribution.matrixPMF smallRows d := by
  cases distribution
  exact sparseRademacherMatrix_map_restrictRows hrows

/-- Pull an event on a smaller matrix back to a larger matrix through exact
row restriction. -/
theorem eventProbability_matrixPMF_restrictRows
    (distribution : ProjectionDistribution) {smallRows largeRows d : ℕ}
    (hrows : smallRows ≤ largeRows)
    (event : (Fin smallRows → Fin d → ℤ) → Prop) :
    eventProbability (distribution.matrixPMF smallRows d) event =
      eventProbability (distribution.matrixPMF largeRows d)
        (fun J => event (restrictRows hrows J)) := by
  rw [← distribution.matrixPMF_map_restrictRows hrows]
  unfold eventProbability
  rw [PMF.map_comp]
  rfl

end CertifiedJL
