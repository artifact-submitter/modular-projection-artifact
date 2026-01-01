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
import CertifiedJL.Statements.Shared.Input

/-!
# Public-threshold modular squared-norm lower tails

These schemas bound the probability that an input whose norm exceeds a public
threshold has a modular projection whose squared norm is too small.
-/

namespace CertifiedJL

/-- Constants selecting a public-threshold modular squared-norm lower tail.

`squaredNormFloor` multiplies the square of the public input threshold.
`modulusMargin` constrains that threshold rather than the possibly much larger
norm of the source vector. Constructing this record proves no tail bound. -/
structure L2ThresholdLowerParameters where
  /-- Distribution used to sample the projection matrix. -/
  distribution : ProjectionDistribution
  /-- Number of coordinates in the projected vector. -/
  rows : ℕ
  /-- Exact rational multiplier of `inputThreshold ^ 2`. -/
  squaredNormFloor : NonnegativeRatio
  /-- Exact rational multiplier in the modulus condition. -/
  modulusMargin : NonnegativeRatio
deriving DecidableEq, Repr

/-- Exact strict public-threshold lower-failure event

`squaredNormFloor.denominator * modularProjectionSqNorm q J w <`
`squaredNormFloor.numerator * inputThreshold ^ 2`.

The right side uses the public threshold rather than `sqNorm w`. Cross
multiplication keeps the rational comparison exact in `ℕ`. -/
def L2ThresholdLowerFailure (squaredNormFloor : NonnegativeRatio)
    (inputThreshold q : ℕ) {rows d : ℕ} (w : Fin d → ℤ)
    (J : Fin rows → Fin d → ℤ) : Prop :=
  squaredNormFloor.denominator * modularProjectionSqNorm q J w <
    squaredNormFloor.numerator * inputThreshold ^ 2
/-- Uniform public-threshold modular squared-norm lower tail.

For every odd modulus `q`, centered source vector `w`, and positive public
threshold `inputThreshold` satisfying `inputThreshold ^ 2 ≤ sqNorm w` and the
configured modulus margin, the probability over a sampled matrix `J` of
`L2ThresholdLowerFailure` is strictly below `budget`.

There is no upper bound on `sqNorm w`; only the public threshold is constrained
by the modulus margin. All inputs precede the matrix probability, so the
statement is pointwise in a fixed input rather than simultaneous over inputs. -/
def L2ThresholdLowerTailAt (parameters : L2ThresholdLowerParameters)
    (budget : ENNReal) : Prop :=
  -- Choose the modulus, source dimension, source vector, and public threshold.
  ∀ (q d : ℕ) (w : Fin d → ℤ) (inputThreshold : ℕ),
    -- Odd `q` gives a positive modulus with no tie at `±q/2`.
    Odd q →
    -- Each source coefficient is the centered representative modulo `q`.
    CenteredInput q w →
    -- The public threshold is nonzero.
    0 < inputThreshold →
    -- Its square is a lower bound for the source-vector squared norm.
    InputThresholdAtMostNorm inputThreshold w →
    -- Exact margin condition `M * inputThreshold ≤ q`, represented by cross
    -- multiplication; the full source norm need not fit the modulus.
    InputThresholdWithinModulus parameters.modulusMargin q inputThreshold →
    -- Sample `J` after fixing the preceding data; the strict bad-event
    -- probability must lie below the requested budget.
    eventProbability (parameters.distribution.matrixPMF parameters.rows d)
      (L2ThresholdLowerFailure parameters.squaredNormFloor inputThreshold q w) < budget

/-- A protocol-facing lower-tail bound remains valid under a larger failure
budget. -/
theorem L2ThresholdLowerTailAt.mono_budget
    {parameters : L2ThresholdLowerParameters} {budget budget' : ENNReal}
    (h : L2ThresholdLowerTailAt parameters budget)
    (hbudget : budget ≤ budget') :
    L2ThresholdLowerTailAt parameters budget' := by
  intro q d w inputThreshold hq hcentered hpositive hnorm hmodulus
  exact (h q d w inputThreshold hq hcentered hpositive hnorm hmodulus).trans_le hbudget

end CertifiedJL
