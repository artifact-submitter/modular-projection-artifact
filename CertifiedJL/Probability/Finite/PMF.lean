/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Finite.UniformPiBridge

/-!
# Elementary bounds for finite PMFs

This module collects measure-theoretic bridges that are independent of any
particular row distribution or tail event.
-/

open scoped ENNReal
open MeasureTheory

namespace CertifiedJL

/-- A pointwise majorant of an event indicator bounds its probability. -/
theorem finitePMF_eventProbability_toReal_le_integral
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω]
    (p : PMF Ω) (event : Ω → Prop) [DecidablePred event] (F : Ω → ℝ)
    (hpoint : ∀ ω, (if event ω then (1 : ℝ) else 0) ≤ F ω) :
    (eventProbability p event).toReal ≤ ∫ ω, F ω ∂p.toMeasure := by
  classical
  rw [eventProbability_toReal_eq_sum, finitePMF_integral_eq_sum]
  simp only [smul_eq_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases he : event ω
  · simp only [if_pos he]
    have hp := hpoint ω
    rw [if_pos he] at hp
    simpa using mul_le_mul_of_nonneg_left hp (p ω).toReal_nonneg
  · simp only [if_neg he]
    have hp := hpoint ω
    rw [if_neg he] at hp
    have hm : (p ω).toReal * 0 ≤ (p ω).toReal * F ω :=
      mul_le_mul_of_nonneg_left hp (p ω).toReal_nonneg
    simpa using hm

/-- Convert a finite-event bound on `ENNReal.toReal` back to `ENNReal`. -/
theorem finitePMF_eventProbability_le_of_toReal_le
    {Ω : Type*} (p : PMF Ω) (event : Ω → Prop) {c : ℝ≥0∞}
    (hc : c ≠ ∞)
    (h : (eventProbability p event).toReal ≤ c.toReal) :
    eventProbability p event ≤ c := by
  exact (ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _) hc).mp h

end CertifiedJL
