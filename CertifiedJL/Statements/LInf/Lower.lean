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
import CertifiedJL.Statements.Shared.Input

/-!
# Public-threshold modular infinity-norm lower tails

These schemas bound the closed event that every modular projection coordinate
is small relative to a public threshold.
-/

namespace CertifiedJL

/-- Constants selecting a public-threshold modular infinity-norm lower tail.
Constructing this record proves no probability bound. -/
structure LInfThresholdLowerParameters where
  /-- Distribution used to sample the projection matrix. -/
  distribution : ProjectionDistribution
  /-- Number of coordinates in the projected vector. -/
  rows : ℕ
  /-- Exact rational multiplier of the public input threshold. -/
  coordinateCap : NonnegativeRatio
  /-- Exact rational multiplier in the modulus condition. -/
  modulusMargin : NonnegativeRatio
deriving DecidableEq, Repr

/-- Closed small-projection event: every centered modular output coordinate is
at most `coordinateCap * inputThreshold`. Squaring and cross multiplication
keep the comparison exact in `ℕ`. -/
def LInfThresholdSmallProjection
    (parameters : LInfThresholdLowerParameters) (inputThreshold q : ℕ)
    {d : ℕ} (w : Fin d → ℤ)
    (J : Fin parameters.rows → Fin d → ℤ) : Prop :=
  ∀ j,
    parameters.coordinateCap.denominator ^ 2 *
        (centeredMod q (rowDot J w j)).natAbs ^ 2 ≤
      parameters.coordinateCap.numerator ^ 2 * inputThreshold ^ 2
/-- Uniform public-threshold modular infinity-norm lower tail.

Under the odd-modulus, centered-input, positive-threshold, lower-norm, and
modulus-margin premises displayed below, the probability that every projected
coordinate satisfies the closed cap is strictly below `budget`. The actual
source-vector norm may be arbitrarily larger than `inputThreshold`. -/
def LInfThresholdLowerTailAt (parameters : LInfThresholdLowerParameters)
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
    -- Sample `J` after fixing the preceding data; the closed coordinate-cap
    -- event must have probability strictly below `budget`.
    eventProbability (parameters.distribution.matrixPMF parameters.rows d)
      (LInfThresholdSmallProjection parameters inputThreshold q w) < budget

/-- A protocol-facing infinity-norm lower-tail bound remains valid under a
larger failure budget. -/
theorem LInfThresholdLowerTailAt.mono_budget
    {parameters : LInfThresholdLowerParameters} {budget budget' : ENNReal}
    (h : LInfThresholdLowerTailAt parameters budget)
    (hbudget : budget ≤ budget') :
    LInfThresholdLowerTailAt parameters budget' := by
  intro q d w inputThreshold hq hcentered hpositive hnorm hmodulus
  exact (h q d w inputThreshold hq hcentered hpositive hnorm hmodulus).trans_le
    hbudget

end CertifiedJL
