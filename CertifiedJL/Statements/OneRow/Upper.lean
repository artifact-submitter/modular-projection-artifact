/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Vectors.Real
import CertifiedJL.Model.ProjectionDistribution
import CertifiedJL.Probability.Finite.Experiment
import CertifiedJL.Probability.Finite.FailureBudget

/-!
# Coefficient-uniform one-row upper tails

The schema includes dimension zero and the zero vector.  Strictness makes the
failure event empty in both cases.
-/

namespace CertifiedJL

/-- Parameters of a coefficient-uniform one-row upper-tail statement. -/
structure OneRowUpperParameters where
  /-- Distribution used to sample the projection row. -/
  distribution : ProjectionDistribution
  /-- Scalar multiple of the source-vector norm in the strict event. -/
  threshold : ℝ

/-- The strict scalar upper-failure event for one projection row. -/
def OneRowUpperFailure (threshold : ℝ) {d : ℕ}
    (w : EuclideanSpace ℝ (Fin d)) (row : Fin d → ℤ) : Prop :=
  |euclideanRowDot row w| > threshold * ‖w‖

/-- A coefficient-uniform one-row upper-tail bound at an arbitrary budget. -/
def OneRowUpperTailAt
    (parameters : OneRowUpperParameters) (budget : ENNReal) : Prop :=
  -- Fix the source dimension and real source vector.
  ∀ (d : ℕ) (w : EuclideanSpace ℝ (Fin d)),
    -- Then sample one row; strict scalar overflow must have probability below
    -- `budget`, uniformly over every coefficient vector.
    eventProbability (parameters.distribution.rowPMF d)
      (OneRowUpperFailure parameters.threshold w) < budget

/-- A one-row bound remains valid under a larger failure budget. -/
theorem OneRowUpperTailAt.mono_budget
    {parameters : OneRowUpperParameters} {budget budget' : ENNReal}
    (h : OneRowUpperTailAt parameters budget) (hbudget : budget ≤ budget') :
    OneRowUpperTailAt parameters budget' := by
  intro d w
  exact (h d w).trans_le hbudget

/-- Increasing the scalar threshold shrinks the strict one-row failure
event. -/
theorem OneRowUpperFailure.antitone_threshold
    {lower upper : ℝ} (hthreshold : lower ≤ upper) {d : ℕ}
    {w : EuclideanSpace ℝ (Fin d)} {row : Fin d → ℤ}
    (h : OneRowUpperFailure upper w row) :
    OneRowUpperFailure lower w row := by
  exact (mul_le_mul_of_nonneg_right hthreshold (norm_nonneg w)).trans_lt h

/-- A one-row upper-tail theorem at a smaller threshold implies the theorem
at every larger threshold. -/
theorem OneRowUpperTailAt.mono_threshold
    {distribution : ProjectionDistribution} {lower upper : ℝ} {budget : ENNReal}
    (hthreshold : lower ≤ upper)
    (h : OneRowUpperTailAt { distribution := distribution, threshold := lower } budget) :
    OneRowUpperTailAt { distribution := distribution, threshold := upper } budget := by
  intro d w
  let _ : MeasurableSpace (Fin d → ℤ) := ⊤
  exact (eventProbability_mono (p := distribution.rowPMF d)
      (fun _ hfailure ↦
        OneRowUpperFailure.antitone_threshold hthreshold hfailure)).trans_lt
    (h d w)

end CertifiedJL
