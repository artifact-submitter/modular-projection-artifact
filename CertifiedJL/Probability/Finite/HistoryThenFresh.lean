/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Finite.Experiment
import CertifiedJL.Probability.Product.RowTensorization

/-!
# A prior history followed by a fresh matrix sample

This module defines an explicit two-stage PMF: first sample a history, then
sample a matrix from the distribution prescribed for that history. It proves
generic averaging and event-composition lemmas. An application must separately
show that its concrete experiment has this factorization.
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace CertifiedJL

universe u v

/-- Dependent outcome of a history followed by a fresh matrix sample. -/
abbrev FreshMatrixOutcome (History : Type u) (rows : ℕ)
    (dimension : History → ℕ) :=
  Σ h : History, Fin rows → Fin (dimension h) → ℤ

/-- Sample a history and then, conditionally on it, a fresh matrix. -/
noncomputable def historyThenFreshMatrix
    {History : Type u} [Countable History] (rows : ℕ)
    (dimension : History → ℕ) (history : PMF History)
    (fresh : (h : History) → PMF (Fin rows → Fin (dimension h) → ℤ)) :
    PMF (FreshMatrixOutcome History rows dimension) :=
  history.bind fun h => (fresh h).map fun J => ⟨h, J⟩

/-- The joint event probability is the history-weighted average of the fresh
conditional event probabilities. -/
theorem eventProbability_historyThenFreshMatrix_eq
    {History : Type u} [Countable History]
    (rows : ℕ) (dimension : History → ℕ) (history : PMF History)
    (fresh : (h : History) → PMF (Fin rows → Fin (dimension h) → ℤ))
    (event : (h : History) → (Fin rows → Fin (dimension h) → ℤ) → Prop) :
    eventProbability (historyThenFreshMatrix rows dimension history fresh)
        (fun x => event x.1 x.2) =
      ∑' h, history h * eventProbability (fresh h) (event h) := by
  unfold eventProbability historyThenFreshMatrix
  rw [PMF.map_bind, PMF.bind_apply]
  apply tsum_congr
  intro h
  rw [PMF.map_comp]
  rfl

/-- A uniform conditional bound survives averaging over an arbitrary prior
history PMF. The statement uses the explicit `bind` above; it does not derive
fresh independence by conditioning an unrelated experiment. The non-strict
conclusion avoids inventing strict headroom. -/
theorem eventProbability_historyThenFreshMatrix_le
    {History : Type u} [Countable History]
    (rows : ℕ) (dimension : History → ℕ) (history : PMF History)
    (fresh : (h : History) → PMF (Fin rows → Fin (dimension h) → ℤ))
    (event : (h : History) → (Fin rows → Fin (dimension h) → ℤ) → Prop)
    (δ : ENNReal)
    (hpoint : ∀ h, eventProbability (fresh h) (event h) ≤ δ) :
    eventProbability (historyThenFreshMatrix rows dimension history fresh)
        (fun x => event x.1 x.2) ≤ δ := by
  rw [eventProbability_historyThenFreshMatrix_eq]
  calc
    (∑' h, history h * eventProbability (fresh h) (event h)) ≤
        ∑' h, history h * δ := by
      exact ENNReal.tsum_le_tsum fun h =>
        mul_le_mul_of_nonneg_left (hpoint h) bot_le
    _ = δ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
/-- A predicate depending only on history has the same probability before
and after the fresh sample. -/
theorem eventProbability_historyThenFreshMatrix_historyEvent
    {History : Type u} [Countable History]
    (rows : ℕ) (dimension : History → ℕ) (history : PMF History)
    (fresh : (h : History) → PMF (Fin rows → Fin (dimension h) → ℤ))
    (event : History → Prop) :
    eventProbability (historyThenFreshMatrix rows dimension history fresh)
      (fun x => event x.1) = eventProbability history event := by
  classical
  rw [eventProbability_historyThenFreshMatrix_eq
    (event := fun h _ => event h)]
  unfold eventProbability
  rw [PMF.map_apply]
  apply tsum_congr
  intro h
  by_cases he : event h <;> simp [he, PMF.map_apply, PMF.tsum_coe]
/-- Generic separately-accounted invalid-history composition. -/
theorem eventProbability_history_bad_le_add_invalid
    {History : Type u} [Countable History]
    (rows : ℕ) (dimension : History → ℕ) (history : PMF History)
    (fresh : (h : History) → PMF (Fin rows → Fin (dimension h) → ℤ))
    (valid bad : History → Prop)
    (accepted : (h : History) →
      (Fin rows → Fin (dimension h) → ℤ) → Prop)
    (budget invalidBudget : ENNReal)
    (hjoint : eventProbability
      (historyThenFreshMatrix rows dimension history fresh)
      (fun x => valid x.1 ∧ bad x.1 ∧ accepted x.1 x.2) ≤ budget)
    (hinvalid : eventProbability history (fun h => ¬ valid h) ≤ invalidBudget) :
    eventProbability (historyThenFreshMatrix rows dimension history fresh)
      (fun x => bad x.1 ∧ accepted x.1 x.2) ≤ budget + invalidBudget := by
  letI : MeasurableSpace (FreshMatrixOutcome History rows dimension) := ⊤
  letI : MeasurableSingletonClass
      (FreshMatrixOutcome History rows dimension) :=
    ⟨fun _ => MeasurableSet.of_discrete⟩
  let joint := historyThenFreshMatrix rows dimension history fresh
  calc
    eventProbability joint (fun x => bad x.1 ∧ accepted x.1 x.2) ≤
      eventProbability joint (fun x => valid x.1 ∧ bad x.1 ∧ accepted x.1 x.2) +
        eventProbability joint (fun x => ¬ valid x.1) := by
      apply (eventProbability_mono joint ?_).trans
        (eventProbability_or_le joint _ _)
      intro x hx
      by_cases hv : valid x.1
      · exact Or.inl ⟨hv, hx⟩
      · exact Or.inr hv
    _ ≤ budget + invalidBudget := by
      apply add_le_add hjoint
      dsimp [joint]
      exact (eventProbability_historyThenFreshMatrix_historyEvent rows
        dimension history fresh (fun h => ¬ valid h)).trans_le hinvalid
/-- Finite-call union composition for fresh-matrix bad events. -/
theorem eventProbability_finiteCall_le_sum
    {Call : Type u} [Fintype Call]
    {Ω : Type v} [Countable Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω]
    (experiment : PMF Ω) (bad : Call → Ω → Prop) (budget : Call → ENNReal)
    (hcall : ∀ i, eventProbability experiment (bad i) ≤ budget i) :
    eventProbability experiment (fun ω => ∃ i, bad i ω) ≤ ∑ i, budget i := by
  exact (eventProbability_exists_le_sum experiment bad).trans
    (Finset.sum_le_sum fun i _ => hcall i)

end CertifiedJL
