/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Finite.Conditioning

/-!
# Lower bounds through finite conditioning

The existing conditioning API is oriented toward row-event upper bounds.
Endpoint anti-concentration needs the dual direction: lower bounds on every
fiber, or varying lower bounds averaged across the finite outer seed.
-/

open scoped BigOperators

namespace CertifiedJL.Probability

/-- Fiberwise lower bounds imply their uniform-average lower bound. -/
theorem eventProbability_map_uniform_prod_toReal_ge_average
    {α β γ : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β]
    (f : α → β → γ) (event : γ → Prop) (bound : α → ℝ)
    (hbound : ∀ a, bound a ≤
      (eventProbability
        ((PMF.uniformOfFintype β).map (f a)) event).toReal) :
    (∑ a : α, (Fintype.card α : ℝ)⁻¹ * bound a) ≤
      (eventProbability
        ((PMF.uniformOfFintype (α × β)).map fun x => f x.1 x.2)
        event).toReal := by
  rw [eventProbability_map_uniform_prod_toReal f event]
  apply Finset.sum_le_sum
  intro a _
  exact mul_le_mul_of_nonneg_left (hbound a) (by positivity)

/-- A common lower bound on every fiber bounds the full product event. -/
theorem eventProbability_map_uniform_prod_toReal_ge
    {α β γ : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β]
    (f : α → β → γ) (event : γ → Prop) (c : ℝ)
    (hbound : ∀ a, c ≤
      (eventProbability
        ((PMF.uniformOfFintype β).map (f a)) event).toReal) :
    c ≤ (eventProbability
      ((PMF.uniformOfFintype (α × β)).map fun x => f x.1 x.2)
      event).toReal := by
  have h := eventProbability_map_uniform_prod_toReal_ge_average
    f event (fun _ => c) hbound
  convert h using 1
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

end CertifiedJL.Probability
