/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Finite.Counting

/-!
# Fiber bounds for finite uniform products

This module turns pointwise bounds on the fibers of a finite uniform product
into unconditional probability bounds. It is independent of sparse rows and
serves as the probability-layer owner for finite conditioning arguments.
-/

open scoped BigOperators ENNReal

namespace CertifiedJL.Probability

/-- Fiber bounds imply a bound by their uniform average. -/
theorem eventProbability_map_uniform_prod_toReal_le_average
    {α β γ : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β]
    (f : α → β → γ) (event : γ → Prop) (bound : α → ℝ)
    (hbound : ∀ a,
      (eventProbability
        ((PMF.uniformOfFintype β).map (f a)) event).toReal ≤ bound a) :
    (eventProbability
        ((PMF.uniformOfFintype (α × β)).map fun x => f x.1 x.2)
        event).toReal ≤
      ∑ a : α, (Fintype.card α : ℝ)⁻¹ * bound a := by
  rw [eventProbability_map_uniform_prod_toReal f event]
  apply Finset.sum_le_sum
  intro a _
  exact mul_le_mul_of_nonneg_left (hbound a) (by positivity)

/-- A common upper bound on every fiber bounds the unconditional event. -/
theorem eventProbability_map_uniform_prod_toReal_le
    {α β γ : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β]
    (f : α → β → γ) (event : γ → Prop) (c : ℝ)
    (hbound : ∀ a,
      (eventProbability
        ((PMF.uniformOfFintype β).map (f a)) event).toReal ≤ c) :
    (eventProbability
        ((PMF.uniformOfFintype (α × β)).map fun x => f x.1 x.2)
        event).toReal ≤ c := by
  refine (eventProbability_map_uniform_prod_toReal_le_average
    f event (fun _ => c) hbound).trans_eq ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_univ]
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

end CertifiedJL.Probability
