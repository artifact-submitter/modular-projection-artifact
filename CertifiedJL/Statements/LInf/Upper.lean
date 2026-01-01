/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.ProjectionDistribution
import CertifiedJL.Model.Vectors.IntegerEuclidean
import CertifiedJL.Probability.Finite.Experiment
import CertifiedJL.Probability.Finite.FailureBudget
import CertifiedJL.Statements.Shared.ExactRatio

/-!
# Modular infinity-norm upper tails

These schemas bound the strict event that one modular projection coordinate is
too large relative to the source-vector norm.
-/

namespace CertifiedJL

/-- Constants selecting a modular infinity-norm upper tail. Constructing this
record proves no probability bound. -/
structure LInfUpperParameters where
  /-- Distribution used to sample the projection matrix. -/
  distribution : ProjectionDistribution
  /-- Number of coordinates in the projected vector. -/
  rows : ℕ
  /-- Exact rational multiplier of the source-vector Euclidean norm. -/
  coordinateThreshold : NonnegativeRatio
deriving DecidableEq, Repr
/-- Some centered projected coordinate strictly exceeds an exact rational
multiple of the input Euclidean norm. Squared cross multiplication keeps the
modular event in `ℕ`. -/
def LInfUpperFailure (parameters : LInfUpperParameters) (q : ℕ)
    {d : ℕ} (w : Fin d → ℤ)
    (J : Fin parameters.rows → Fin d → ℤ) : Prop :=
  ∃ j,
    parameters.coordinateThreshold.numerator ^ 2 * sqNorm w <
      parameters.coordinateThreshold.denominator ^ 2 *
        (centeredMod q (rowDot J w j)).natAbs ^ 2
/-- Uniform modular infinity-norm upper tail. The probability that some
projected coordinate strictly exceeds the configured multiple of `‖w‖₂` is
below `budget`. Centered reduction is a contraction, so no source-norm to
modulus condition is required. -/
def LInfUpperTailAt (parameters : LInfUpperParameters) (budget : ENNReal) : Prop :=
  -- Fix a modulus, source dimension, and integer source vector.
  ∀ (q d : ℕ) (w : Fin d → ℤ),
    -- Then sample `J`; the event that some coordinate strictly exceeds the
    -- configured cap must have probability below `budget`.
    eventProbability (parameters.distribution.matrixPMF parameters.rows d)
      (LInfUpperFailure parameters q w) < budget

/-- A modular infinity-norm upper-tail bound remains valid under a larger
failure budget. -/
theorem LInfUpperTailAt.mono_budget
    {parameters : LInfUpperParameters} {budget budget' : ENNReal}
    (h : LInfUpperTailAt parameters budget) (hbudget : budget ≤ budget') :
    LInfUpperTailAt parameters budget' := by
  intro q d w
  exact (h q d w).trans_le hbudget

end CertifiedJL
