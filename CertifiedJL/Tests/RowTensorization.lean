/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Product.RowTensorization
import Mathlib.Tactic

/-!
# Row tensorization mutation canaries

These canaries pin the empty product, the single-row orientation, and a
nontrivial two-row probability.  The last example rejects multiplication by
the row count, using the wrong marginal, or omitting a row.
-/

open scoped ENNReal

namespace CertifiedJL

example {α : Type} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) {event event' : α → Prop}
    (h : ∀ x, event x → event' x) :
    eventProbability p event ≤ eventProbability p event' :=
  eventProbability_mono p h

/-- The finite-union API retains the existential event and sum orientation. -/
example {ι α : Type} [Fintype ι] [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (event : ι → α → Prop) :
    eventProbability p (fun x => ∃ i, event i x) ≤
      ∑ i, eventProbability p (event i) :=
  eventProbability_exists_le_sum p event

/-- A two-event cover of `Bool` exercises a genuinely non-singleton union. -/
example :
    eventProbability (PMF.uniformOfFintype Bool)
        (fun b => ∃ i : Fin 2, (i = 0 ∧ b = false) ∨ (i = 1 ∧ b = true)) ≤
      ∑ i : Fin 2, eventProbability (PMF.uniformOfFintype Bool)
        (fun b => (i = 0 ∧ b = false) ∨ (i = 1 ∧ b = true)) :=
  eventProbability_exists_le_sum _ _

/-- Main-row tensorization and the exceptional-row union have distinct costs. -/
example (m d : ℕ) (main exceptional : (Fin d → ℤ) → Prop) :
    eventProbability (sparseRademacherMatrix m d)
        (fun J => ∀ j, main (J j) ∨ exceptional (J j)) ≤
      eventProbability (sparseRademacherRow d) main ^ m +
        m • eventProbability (sparseRademacherRow d) exceptional :=
  sparseRademacherMatrix_eventProbability_allRows_or_le_pow_add
    m d main exceptional

/-- A row-dependent exceedance event uses the exact complement product. -/
example (m d : ℕ) (event : Fin m → (Fin d → ℤ) → Prop) :
    eventProbability (sparseRademacherMatrix m d)
        (fun J => ∃ j, event j (J j)) =
      1 - ∏ j, (1 - eventProbability (sparseRademacherRow d) (event j)) :=
  sparseRademacherMatrix_eventProbability_someRow_eq_one_sub_prod m d event

/-- No row can witness an exceedance in the empty matrix. -/
example (d : ℕ) (event : (Fin d → ℤ) → Prop) :
    eventProbability (sparseRademacherMatrix 0 d)
        (fun J => ∃ j, event (J j)) = 0 := by
  rw [sparseRademacherMatrix_eventProbability_someRow_eq_one_sub_pow]
  simp

/-- An always-false row event remains impossible after tensorization. -/
example (m d : ℕ) :
    eventProbability (sparseRademacherMatrix m d)
        (fun _J => ∃ _j : Fin m, False) = 0 := by
  rw [sparseRademacherMatrix_eventProbability_someRow_eq_one_sub_pow
    (event := fun _ => False)]
  simp only [eventProbability_false, tsub_zero, one_pow, tsub_self]

/-- With at least one row, an always-true row event occurs surely. -/
example (m d : ℕ) :
    eventProbability (sparseRademacherMatrix (m + 1) d)
        (fun _J => ∃ _j : Fin (m + 1), True) = 1 := by
  rw [sparseRademacherMatrix_eventProbability_someRow_eq_one_sub_pow
    (event := fun _ => True)]
  have htrue : eventProbability (sparseRademacherRow d)
      (fun _ => True) = 1 := by
    rw [eventProbability_eq_toMeasure]
    simp
  rw [htrue]
  simp

/-- An event holds vacuously in every row of the empty matrix. -/
example (d : ℕ) (event : (Fin d → ℤ) → Prop) :
    eventProbability (sparseRademacherMatrix 0 d)
        (fun J => ∀ j, event (J j)) = 1 := by
  rw [sparseRademacherMatrix_eventProbability_allRows_eq_pow]
  simp

/-- Tensorization at one row preserves the one-row probability exactly. -/
example (d : ℕ) (event : (Fin d → ℤ) → Prop) :
    eventProbability (sparseRademacherMatrix 1 d)
        (fun J => ∀ j, event (J j)) =
      eventProbability (sparseRademacherRow d) event := by
  rw [sparseRademacherMatrix_eventProbability_allRows_eq_pow]
  simp

private theorem oneCoordinateZeroProbability :
    eventProbability (sparseRademacherRow 1)
        (fun row => row 0 = 0) = (2 : ℝ≥0∞)⁻¹ := by
  calc
    eventProbability (sparseRademacherRow 1)
        (fun row => row 0 = 0) =
        eventProbability
          ((sparseRademacherRow 1).map (fun row => row 0))
          (fun z => z = 0) := by
      unfold eventProbability
      rw [PMF.map_comp]
      simp [Function.comp_def]
    _ = eventProbability sparseEntryPMF (fun z => z = 0) := by
      rw [sparseRademacherRow_marginal 0]
    _ = (2 : ℝ≥0∞)⁻¹ := by
      rw [eventProbability_eq_toMeasure]
      have hset : {z : ℤ | z = 0} = {0} := by
        ext z
        simp
      rw [hset, PMF.toMeasure_apply_singleton _ _
        (measurableSet_singleton (0 : ℤ))]
      exact sparseEntryPMF_zero

/-- Two independent zero-entry events have probability `1/4`, not `1/2`. -/
example :
    eventProbability (sparseRademacherMatrix 2 1)
        (fun J => ∀ j, J j 0 = 0) = (4 : ℝ≥0∞)⁻¹ := by
  calc
    eventProbability (sparseRademacherMatrix 2 1)
        (fun J => ∀ j, J j 0 = 0) =
        eventProbability (sparseRademacherRow 1)
          (fun row => row 0 = 0) ^ 2 :=
      sparseRademacherMatrix_eventProbability_allRows_eq_pow
        2 1 (fun row => row 0 = 0)
    _ = (4 : ℝ≥0∞)⁻¹ := by
      rw [oneCoordinateZeroProbability]
      rw [pow_two, ← ENNReal.mul_inv (by norm_num) (by norm_num)]
      norm_num

#print axioms CertifiedJL.eventProbability_iIndepFun_forall_eq_prod
#print axioms CertifiedJL.eventProbability_iIndepFun_exists_eq_one_sub_prod
#print axioms CertifiedJL.eventProbability_compl_eq_one_sub
#print axioms CertifiedJL.eventProbability_mono
#print axioms CertifiedJL.eventProbability_exists_le_sum
#print axioms CertifiedJL.eventProbability_forall_or_le
#print axioms CertifiedJL.sparseRademacherMatrix_eventProbability_allRows_eq_pow
#print axioms CertifiedJL.sparseRademacherMatrix_eventProbability_someRow_eq_one_sub_prod
#print axioms CertifiedJL.sparseRademacherMatrix_eventProbability_someRow_eq_one_sub_pow
#print axioms CertifiedJL.sparseRademacherMatrix_eventProbability_allRows_le_pow
#print axioms CertifiedJL.sparseRademacherMatrix_eventProbability_allRows_or_le_pow_add

end CertifiedJL
