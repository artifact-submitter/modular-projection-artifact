/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Modular.Projection
import CertifiedJL.Statements.LInf.Lower

/-!
# Shifted modular infinity-norm lower tails

The row-wise integer shift is arbitrary and is quantified before the
probability over the freshly sampled projection matrix.
-/

namespace CertifiedJL

/-- Closed shifted coordinate-cap event. Every coordinate of
`centeredMod q (shift + Jw)` is at most the configured exact rational multiple
of the public input threshold, expressed by squared cross multiplication. -/
def AffineLInfThresholdSmallProjection
    (parameters : LInfThresholdLowerParameters) (inputThreshold q : ℕ)
    {d : ℕ} (shift : Fin parameters.rows → ℤ) (w : Fin d → ℤ)
    (J : Fin parameters.rows → Fin d → ℤ) : Prop :=
  ∀ j,
    parameters.coordinateCap.denominator ^ 2 *
        (centeredMod q (shift j + rowDot J w j)).natAbs ^ 2 ≤
      parameters.coordinateCap.numerator ^ 2 * inputThreshold ^ 2

/-- Shifted infinity-norm sibling of `AffineL2ThresholdLowerTailAt`.

The shift is arbitrary but fixed before the fresh matrix `J` is sampled. The
probability that every shifted output coordinate lies in the closed cap is
strictly below `budget`. History-selected shifts require the separate explicit
two-stage protocol adapter. -/
def AffineLInfThresholdLowerTailAt
    (parameters : LInfThresholdLowerParameters) (budget : ENNReal) : Prop :=
  -- Choose the modulus, source data, public threshold, and arbitrary shift.
  ∀ (q d : ℕ) (w : Fin d → ℤ) (inputThreshold : ℕ)
      (shift : Fin parameters.rows → ℤ),
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
    -- Sample `J` after the shift is fixed; the closed shifted cap event must
    -- have probability strictly below `budget`.
    eventProbability (parameters.distribution.matrixPMF parameters.rows d)
      (AffineLInfThresholdSmallProjection parameters inputThreshold q shift w) <
        budget

@[simp]
theorem affineLInfThresholdSmallProjection_zeroShift
    (parameters : LInfThresholdLowerParameters) (inputThreshold q : ℕ)
    {d : ℕ} (w : Fin d → ℤ)
    (J : Fin parameters.rows → Fin d → ℤ) :
    AffineLInfThresholdSmallProjection parameters inputThreshold q
        (fun _ => 0) w J ↔
      LInfThresholdSmallProjection parameters inputThreshold q w J := by
  simp [AffineLInfThresholdSmallProjection, LInfThresholdSmallProjection]

/-- An affine infinity-norm lower-tail bound remains valid under a larger
failure budget. -/
theorem AffineLInfThresholdLowerTailAt.mono_budget
    {parameters : LInfThresholdLowerParameters} {budget budget' : ENNReal}
    (h : AffineLInfThresholdLowerTailAt parameters budget)
    (hbudget : budget ≤ budget') :
    AffineLInfThresholdLowerTailAt parameters budget' := by
  intro q d w inputThreshold shift hq hcentered hpositive hnorm hmodulus
  exact (h q d w inputThreshold shift hq hcentered hpositive hnorm
    hmodulus).trans_le hbudget

/-- The affine infinity-norm theorem specializes to the unshifted theorem. -/
theorem AffineLInfThresholdLowerTailAt.to_unshifted
    {parameters : LInfThresholdLowerParameters} {budget : ENNReal}
    (h : AffineLInfThresholdLowerTailAt parameters budget) :
    LInfThresholdLowerTailAt parameters budget := by
  intro q d w inputThreshold hq hcentered hpositive hnorm hmodulus
  rw [eventProbability_congr (parameters.distribution.matrixPMF parameters.rows d)
    (event' := AffineLInfThresholdSmallProjection parameters inputThreshold q
      (fun _ => 0) w)
    (fun J => (affineLInfThresholdSmallProjection_zeroShift parameters
      inputThreshold q w J).symm)]
  exact h q d w inputThreshold (fun _ => 0) hq hcentered hpositive hnorm
    hmodulus

end CertifiedJL
