/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Modular.Projection
import CertifiedJL.Statements.L2.Lower

/-!
# Shifted modular squared-norm lower tails

The row-wise integer shift is arbitrary and is quantified before the
probability over the freshly sampled projection matrix.
-/

namespace CertifiedJL

/-- Exact strict shifted modular lower-failure event

`squaredNormFloor.denominator *`
`shiftedModularProjectionSqNorm q shift J w <`
`squaredNormFloor.numerator * inputThreshold ^ 2`.

No size, centeredness, or distribution condition is imposed on `shift`. -/
def AffineL2ThresholdLowerFailure (squaredNormFloor : NonnegativeRatio)
    (inputThreshold q : ℕ) {rows d : ℕ} (shift : Fin rows → ℤ)
    (w : Fin d → ℤ) (J : Fin rows → Fin d → ℤ) : Prop :=
  squaredNormFloor.denominator * shiftedModularProjectionSqNorm q shift J w <
    squaredNormFloor.numerator * inputThreshold ^ 2

/-- Uniform shifted modular squared-norm lower tail.

For every admissible modulus, source vector, public threshold, and row-wise
integer shift, the probability over a fresh sampled matrix `J` of the strict
lower-failure event is below `budget`. The quantifier order fixes `shift`
before `J` is sampled. The property contains no history object; protocol
adapters separately model a history followed by the prescribed fresh matrix
distribution. A shift depending on this same `J` would state a different and
generally false claim. -/
def AffineL2ThresholdLowerTailAt (parameters : L2ThresholdLowerParameters)
    (budget : ENNReal) : Prop :=
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
    -- Sample `J` after the shift is fixed; the strict shifted bad event must
    -- have probability below `budget`.
    eventProbability (parameters.distribution.matrixPMF parameters.rows d)
      (AffineL2ThresholdLowerFailure parameters.squaredNormFloor
        inputThreshold q shift w) < budget

@[simp]
theorem affineL2ThresholdLowerFailure_zeroShift
    (squaredNormFloor : NonnegativeRatio) (inputThreshold q : ℕ)
    {rows d : ℕ} (w : Fin d → ℤ) (J : Fin rows → Fin d → ℤ) :
    AffineL2ThresholdLowerFailure squaredNormFloor inputThreshold q
        (fun _ => 0) w J ↔
      L2ThresholdLowerFailure squaredNormFloor inputThreshold q w J := by
  simp only [AffineL2ThresholdLowerFailure, L2ThresholdLowerFailure,
    shiftedModularProjectionSqNorm, modularProjectionSqNorm, zero_add]

/-- An affine squared-Euclidean lower-tail bound remains valid under a larger
failure budget. -/
theorem AffineL2ThresholdLowerTailAt.mono_budget
    {parameters : L2ThresholdLowerParameters} {budget budget' : ENNReal}
    (h : AffineL2ThresholdLowerTailAt parameters budget)
    (hbudget : budget ≤ budget') :
    AffineL2ThresholdLowerTailAt parameters budget' := by
  intro q d w inputThreshold shift hq hcentered hpositive hnorm hmodulus
  exact (h q d w inputThreshold shift hq hcentered hpositive hnorm
    hmodulus).trans_le hbudget

/-- The affine squared-Euclidean theorem specializes to the unshifted
theorem. -/
theorem AffineL2ThresholdLowerTailAt.to_unshifted
    {parameters : L2ThresholdLowerParameters} {budget : ENNReal}
    (h : AffineL2ThresholdLowerTailAt parameters budget) :
    L2ThresholdLowerTailAt parameters budget := by
  intro q d w inputThreshold hq hcentered hpositive hnorm hmodulus
  rw [eventProbability_congr (parameters.distribution.matrixPMF parameters.rows d)
    (event' := AffineL2ThresholdLowerFailure parameters.squaredNormFloor
      inputThreshold q (fun _ => 0) w)
    (fun J => (affineL2ThresholdLowerFailure_zeroShift
      parameters.squaredNormFloor inputThreshold q w J).symm)]
  exact h q d w inputThreshold (fun _ => 0) hq hcentered hpositive hnorm
    hmodulus

end CertifiedJL
