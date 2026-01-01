/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Modular.AffineTransport
import CertifiedJL.Statements.L2.Lower.Affine
import CertifiedJL.Statements.LInf.Lower.Affine
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Scaling transports for shifted lower tails

Exact integer scaling moves the maintained lower-tail statements between
modulus margins without rounding probability thresholds.
-/

namespace CertifiedJL

/-- Multiply a nonnegative ratio by `2/3`. -/
def NonnegativeRatio.twoThirds (r : NonnegativeRatio) : NonnegativeRatio where
  numerator := 2 * r.numerator
  denominator := 3 * r.denominator
  denominator_pos := Nat.mul_pos (by decide) r.denominator_pos

/-- Multiply a nonnegative ratio by `4/9`.  This is the squared-norm
counterpart of `twoThirds`. -/
def NonnegativeRatio.fourNinths (r : NonnegativeRatio) : NonnegativeRatio where
  numerator := 4 * r.numerator
  denominator := 9 * r.denominator
  denominator_pos := Nat.mul_pos (by decide) r.denominator_pos

/-- The scaled source coordinate-cap event is exactly its two-thirds target
event. -/
theorem affineLInfThresholdSmallProjection_scale_three_iff
    (parameters : LInfThresholdLowerParameters) (q inputThreshold : ℕ)
    {d : ℕ} (shift : Fin parameters.rows → ℤ) (w : Fin d → ℤ)
    (J : Fin parameters.rows → Fin d → ℤ) (hq : Odd q) :
    AffineLInfThresholdSmallProjection parameters (2 * inputThreshold) (3 * q)
        (fun j => 3 * shift j) (fun i => 3 * w i) J ↔
      AffineLInfThresholdSmallProjection
        { parameters with coordinateCap := parameters.coordinateCap.twoThirds }
        inputThreshold q shift w J := by
  constructor <;> intro h j
  · have hj := h j
    have hrow : rowDot J (fun i => 3 * w i) j = 3 * rowDot J w j := by
      simpa using rowDot_natCast_mul 3 J w j
    rw [hrow, ← mul_add, centeredMod_three_mul q hq,
      Int.natAbs_mul] at hj
    norm_num at hj
    simp only [NonnegativeRatio.twoThirds]
    ring_nf at hj ⊢
    exact hj
  · have hj := h j
    have hrow : rowDot J (fun i => 3 * w i) j = 3 * rowDot J w j := by
      simpa using rowDot_natCast_mul 3 J w j
    rw [hrow, ← mul_add, centeredMod_three_mul q hq,
      Int.natAbs_mul]
    norm_num
    simp only [NonnegativeRatio.twoThirds] at hj
    ring_nf at hj ⊢
    exact hj

/-- Exact margin-three to margin-two lower-tail transport.  More generally,
both the coordinate cap and the modulus margin are multiplied by `2/3`. -/
theorem AffineLInfThresholdLowerTailAt.twoThirds
    {parameters : LInfThresholdLowerParameters} {budget : ENNReal}
    (h : AffineLInfThresholdLowerTailAt parameters budget) :
    AffineLInfThresholdLowerTailAt
      { parameters with
        coordinateCap := parameters.coordinateCap.twoThirds
        modulusMargin := parameters.modulusMargin.twoThirds } budget := by
  intro q d w inputThreshold shift hq hcentered hpositive hnorm hmodulus
  have hodd3 : Odd 3 := ⟨1, rfl⟩
  have hq3 : Odd (3 * q) := hodd3.mul hq
  have hcentered3 : CenteredInput (3 * q) (fun i => 3 * w i) := by
    simpa using hcentered.odd_mul 3 hodd3 hq
  have hpositive2 : 0 < 2 * inputThreshold := Nat.mul_pos (by decide) hpositive
  have hnorm2 : InputThresholdAtMostNorm (2 * inputThreshold)
      (fun i => 3 * w i) := by
    unfold InputThresholdAtMostNorm at hnorm ⊢
    rw [show sqNorm (fun i => 3 * w i) = 3 ^ 2 * sqNorm w by
      simpa using sqNorm_natCast_mul 3 w]
    nlinarith
  have hmodulus3 : InputThresholdWithinModulus parameters.modulusMargin
      (3 * q) (2 * inputThreshold) := by
    unfold InputThresholdWithinModulus at hmodulus ⊢
    change 2 * parameters.modulusMargin.numerator * inputThreshold ≤
      3 * parameters.modulusMargin.denominator * q at hmodulus
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmodulus
  calc
    eventProbability (parameters.distribution.matrixPMF parameters.rows d)
        (AffineLInfThresholdSmallProjection
          { parameters with
            coordinateCap := parameters.coordinateCap.twoThirds
            modulusMargin := parameters.modulusMargin.twoThirds }
          inputThreshold q shift w) =
      eventProbability (parameters.distribution.matrixPMF parameters.rows d)
        (AffineLInfThresholdSmallProjection parameters (2 * inputThreshold)
          (3 * q) (fun j => 3 * shift j) (fun i => 3 * w i)) :=
      eventProbability_congr _ fun J =>
        (affineLInfThresholdSmallProjection_scale_three_iff parameters q
          inputThreshold shift w J hq).symm
    _ < budget := h (3 * q) d (fun i => 3 * w i) (2 * inputThreshold)
      (fun j => 3 * shift j) hq3 hcentered3 hpositive2 hnorm2 hmodulus3

/-- Scaling modulus, threshold, input, and shift by `(3, 2, 3, 3)` turns an
affine L2 lower-failure event at floor `L` into the event at floor `4L/9`. -/
theorem affineL2ThresholdLowerFailure_scale_three_iff
    (squaredNormFloor : NonnegativeRatio) (q inputThreshold : ℕ)
    {rows d : ℕ} (shift : Fin rows → ℤ) (w : Fin d → ℤ)
    (J : Fin rows → Fin d → ℤ) (hq : Odd q) :
    AffineL2ThresholdLowerFailure squaredNormFloor (2 * inputThreshold) (3 * q)
        (fun j => 3 * shift j) (fun i => 3 * w i) J ↔
      AffineL2ThresholdLowerFailure squaredNormFloor.fourNinths inputThreshold q
        shift w J := by
  unfold AffineL2ThresholdLowerFailure
  rw [show shiftedModularProjectionSqNorm (3 * q) (fun j => 3 * shift j) J
      (fun i => 3 * w i) = 3 ^ 2 * shiftedModularProjectionSqNorm q shift J w by
    simpa using shiftedModularProjectionSqNorm_odd_mul 3 q (by exact ⟨1, rfl⟩) hq shift J w]
  simp only [NonnegativeRatio.fourNinths]
  ring_nf

/-- Exact margin-three to margin-two affine L2 transport.  The modulus margin
is multiplied by `2/3`, while the squared-norm floor is multiplied by
`4/9`; the failure budget is unchanged. -/
theorem AffineL2ThresholdLowerTailAt.fourNinths
    {parameters : L2ThresholdLowerParameters} {budget : ENNReal}
    (h : AffineL2ThresholdLowerTailAt parameters budget) :
    AffineL2ThresholdLowerTailAt
      { parameters with
        squaredNormFloor := parameters.squaredNormFloor.fourNinths
        modulusMargin := parameters.modulusMargin.twoThirds } budget := by
  intro q d w inputThreshold shift hq hcentered hpositive hnorm hmodulus
  have hodd3 : Odd 3 := ⟨1, rfl⟩
  have hq3 : Odd (3 * q) := hodd3.mul hq
  have hcentered3 : CenteredInput (3 * q) (fun i => 3 * w i) := by
    simpa using hcentered.odd_mul 3 hodd3 hq
  have hpositive2 : 0 < 2 * inputThreshold := Nat.mul_pos (by decide) hpositive
  have hnorm2 : InputThresholdAtMostNorm (2 * inputThreshold)
      (fun i => 3 * w i) := by
    unfold InputThresholdAtMostNorm at hnorm ⊢
    rw [show sqNorm (fun i => 3 * w i) = 3 ^ 2 * sqNorm w by
      simpa using sqNorm_natCast_mul 3 w]
    nlinarith
  have hmodulus3 : InputThresholdWithinModulus parameters.modulusMargin
      (3 * q) (2 * inputThreshold) := by
    unfold InputThresholdWithinModulus at hmodulus ⊢
    change 2 * parameters.modulusMargin.numerator * inputThreshold ≤
      3 * parameters.modulusMargin.denominator * q at hmodulus
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmodulus
  calc
    eventProbability (parameters.distribution.matrixPMF parameters.rows d)
        (AffineL2ThresholdLowerFailure parameters.squaredNormFloor.fourNinths
          inputThreshold q shift w) =
      eventProbability (parameters.distribution.matrixPMF parameters.rows d)
        (AffineL2ThresholdLowerFailure parameters.squaredNormFloor
          (2 * inputThreshold) (3 * q) (fun j => 3 * shift j)
          (fun i => 3 * w i)) :=
      eventProbability_congr _ fun J =>
        (affineL2ThresholdLowerFailure_scale_three_iff parameters.squaredNormFloor q
          inputThreshold shift w J hq).symm
    _ < budget := h (3 * q) d (fun i => 3 * w i) (2 * inputThreshold)
      (fun j => 3 * shift j) hq3 hcentered3 hpositive2 hnorm2 hmodulus3


end CertifiedJL
