/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.ProjectionDistribution
import CertifiedJL.Model.Vectors.SquaredNorm
import CertifiedJL.Probability.Finite.Experiment
import CertifiedJL.Probability.Finite.FailureBudget
import CertifiedJL.Statements.Shared.ExactRatio

/-!
# Modular squared-norm upper tails

These schemas compare the squared norm of a whole modular projection with an
exact rational multiple of the source-vector squared norm.
-/

namespace CertifiedJL

/-- Constants selecting a modular squared-norm upper tail. Constructing this
record proves no probability bound. -/
structure L2UpperParameters where
  /-- Distribution used to sample the projection matrix. -/
  distribution : ProjectionDistribution
  /-- Number of coordinates in the projected vector. -/
  rows : ℕ
  /-- Exact rational multiplier of the source-vector squared norm. -/
  threshold : NonnegativeRatio
deriving DecidableEq, Repr

/-- Exact strict upper-failure event

`threshold.numerator * sqNorm w <`
`threshold.denominator * modularProjectionSqNorm q J w`.

Thus the modular projected squared norm strictly exceeds the configured
rational multiple of the source-vector squared norm. -/
def L2UpperFailure (threshold : NonnegativeRatio) (q : ℕ) {rows d : ℕ}
    (w : Fin d → ℤ) (J : Fin rows → Fin d → ℤ) : Prop :=
  threshold.numerator * sqNorm w <
    threshold.denominator * modularProjectionSqNorm q J w

/-- Integer thresholds recover the direct strict projected squared-norm comparison. -/
@[simp]
theorem L2UpperFailure_ofNat_iff (threshold q : ℕ) {rows d : ℕ}
    (w : Fin d → ℤ) (J : Fin rows → Fin d → ℤ) :
    L2UpperFailure (NonnegativeRatio.ofNat threshold) q w J ↔
      modularProjectionSqNorm q J w > threshold * sqNorm w := by
  simp [L2UpperFailure, NonnegativeRatio.ofNat]
/-- Uniform modular squared-norm upper tail. For every modulus, dimension, and
integer source vector, the probability of the strict upper-failure event under
the configured matrix distribution is below `budget`. -/
def L2UpperTailAt (parameters : L2UpperParameters) (budget : ENNReal) : Prop :=
  -- Fix a modulus, source dimension, and integer source vector.
  ∀ (q d : ℕ) (w : Fin d → ℤ),
    -- Then sample `J`; strict squared-norm overflow must have probability
    -- below `budget` for every fixed source vector.
    eventProbability (parameters.distribution.matrixPMF parameters.rows d)
      (L2UpperFailure parameters.threshold q w) < budget

/-- An upper-tail bound remains valid under a larger failure budget. -/
theorem L2UpperTailAt.mono_budget
    {parameters : L2UpperParameters} {budget budget' : ENNReal}
    (h : L2UpperTailAt parameters budget) (hbudget : budget ≤ budget') :
    L2UpperTailAt parameters budget' := by
  intro q d w
  exact (h q d w).trans_le hbudget
/-- Increasing the threshold shrinks a strict upper-failure event. -/
theorem L2UpperFailure.antitone_threshold
    {lower upper : NonnegativeRatio} (hthreshold : lower.LE upper)
    {q rows d : ℕ} {w : Fin d → ℤ} {J : Fin rows → Fin d → ℤ}
    (h : L2UpperFailure upper q w J) :
    L2UpperFailure lower q w J := by
  have hscaled := Nat.mul_lt_mul_of_pos_left h lower.denominator_pos
  have hratio := Nat.mul_le_mul_right (sqNorm w) hthreshold
  exact Nat.lt_of_mul_lt_mul_left (calc
    upper.denominator * (lower.numerator * sqNorm w) =
        (lower.numerator * upper.denominator) * sqNorm w := by ac_rfl
    _ ≤ (upper.numerator * lower.denominator) * sqNorm w := hratio
    _ = lower.denominator * (upper.numerator * sqNorm w) := by ac_rfl
    _ < lower.denominator *
          (upper.denominator * modularProjectionSqNorm q J w) := hscaled
    _ = upper.denominator *
          (lower.denominator * modularProjectionSqNorm q J w) := by ac_rfl)

/-- An upper-tail theorem at a smaller threshold implies the theorem at a
larger threshold. -/
theorem L2UpperTailAt.mono_threshold
    {distribution : ProjectionDistribution} {rows : ℕ} {lower upper : NonnegativeRatio}
    {budget : ENNReal} (hthreshold : lower.LE upper)
    (h : L2UpperTailAt
      { distribution := distribution, rows := rows, threshold := lower } budget) :
    L2UpperTailAt
      { distribution := distribution, rows := rows, threshold := upper } budget := by
  intro q d w
  let _ : MeasurableSpace (Fin rows → Fin d → ℤ) := ⊤
  exact (eventProbability_mono (p := distribution.matrixPMF rows d)
      (fun _ hfailure =>
        L2UpperFailure.antitone_threshold hthreshold hfailure)).trans_lt
    (h q d w)

end CertifiedJL
