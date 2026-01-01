/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Distributions.BalancedTernary.Duplication
import CertifiedJL.Statements.OneRow.Endpoint975

/-!
# The coefficient-uniform sparse one-row theorem

This module isolates the normalized one-sided Rademacher theorem that carries
the analytic content of the `9.75` result, and proves the exact reduction from
that theorem to the public sparse-row statement.
-/

open scoped BigOperators ENNReal

namespace CertifiedJL

/--
The normalized one-sided Rademacher theorem needed by the sparse one-row
result. The final proof below must discharge this proposition, rather than
assuming it as an axiom.
-/
def NormalizedRademacher975UpperStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (a : ι → ℝ),
    (∑ i, a i ^ 2) = 1 →
    eventProbability (rademacherPMF ι)
        (fun seed =>
          sparseOneRowRademacherThreshold < rademacherSum a seed) <
      failureTarget 142

/--
The exact sparse-row theorem follows from the normalized one-sided
Rademacher theorem. This theorem closes all modeling, normalization,
strict-event, symmetry, and zero-vector obligations.
-/
theorem sparseOneRow975_of_normalizedRademacherUpper
    (hupper : NormalizedRademacher975UpperStatement) :
    SparseOneRow975Statement := by
  intro d w
  by_cases hw : w = 0
  · subst w
    have hempty :
        SparseOneRow975Event (0 : EuclideanSpace ℝ (Fin d)) =
          (fun _ : Fin d → ℤ => False) := by
      funext row
      apply propext
      simp [SparseOneRow975Event]
    rw [hempty, eventProbability_false]
    unfold failureTarget sparseOneRowSecurityBits
    rw [pos_iff_ne_zero]
    exact pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by norm_num))
  · rw [show
        eventProbability (sparseRademacherRow d) (SparseOneRow975Event w) =
          eventProbability (rademacherPMF (Fin d × Fin 2))
            (fun bits =>
              |rademacherSum (normalizedDuplicatedCoefficient w) bits| >
                sparseOneRowRademacherThreshold) by
        exact sparseOneRow975_probability_eq_rademacher w hw]
    apply rademacherSum_abs_tail_lt
    simpa [sparseOneRowSecurityBits] using
      hupper (Fin d × Fin 2) (normalizedDuplicatedCoefficient w)
        (sum_sq_normalizedDuplicatedCoefficient w hw)

end CertifiedJL
