/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Statements.L2.Lower.Affine
import CertifiedJL.Statements.LInf.Lower.Affine

/-!
# From coordinate caps to projected squared-norm floors

Exact arithmetic converts a closed coordinate cap into a strict squared-norm
lower-failure event when the constants leave strict headroom.
-/

namespace CertifiedJL

/-- Exact arithmetic condition under which a coordinate cap forces the
corresponding squared-norm failure event. -/
def LInfCapFitsL2SquaredNormFloor (rows : ℕ) (coordinateCap squaredNormFloor :
    NonnegativeRatio) : Prop :=
  squaredNormFloor.denominator * rows * coordinateCap.numerator ^ 2 <
    squaredNormFloor.numerator * coordinateCap.denominator ^ 2

/-- A positive-threshold affine coordinate cap is contained in the matching
strict affine squared-norm failure event. -/
theorem affineLInfThresholdSmallProjection_implies_l2Failure
    (parameters : LInfThresholdLowerParameters)
    (squaredNormFloor : NonnegativeRatio) (inputThreshold q : ℕ)
    {d : ℕ} (shift : Fin parameters.rows → ℤ) (w : Fin d → ℤ)
    (J : Fin parameters.rows → Fin d → ℤ)
    (hpositive : 0 < inputThreshold)
    (hfit : LInfCapFitsL2SquaredNormFloor parameters.rows
      parameters.coordinateCap squaredNormFloor)
    (hsmall : AffineLInfThresholdSmallProjection parameters inputThreshold q
      shift w J) :
    AffineL2ThresholdLowerFailure squaredNormFloor inputThreshold q shift w J := by
  let cap := parameters.coordinateCap
  have hsum : cap.denominator ^ 2 * shiftedModularProjectionSqNorm q shift J w ≤
      parameters.rows * (cap.numerator ^ 2 * inputThreshold ^ 2) := by
    change cap.denominator ^ 2 *
      (∑ j, (centeredMod q (shift j + rowDot J w j)).natAbs ^ 2) ≤ _
    rw [Finset.mul_sum]
    calc
      ∑ j, cap.denominator ^ 2 *
          (centeredMod q (shift j + rowDot J w j)).natAbs ^ 2 ≤
          ∑ _j : Fin parameters.rows,
            cap.numerator ^ 2 * inputThreshold ^ 2 := by
        exact Finset.sum_le_sum fun j _ => hsmall j
      _ = parameters.rows * (cap.numerator ^ 2 * inputThreshold ^ 2) := by
        simp [Finset.sum_const, Fintype.card_fin]
  have hthresholdSq : 0 < inputThreshold ^ 2 := pow_pos hpositive _
  have hscaled :
      cap.denominator ^ 2 *
          (squaredNormFloor.denominator * shiftedModularProjectionSqNorm q shift J w) <
        cap.denominator ^ 2 *
          (squaredNormFloor.numerator * inputThreshold ^ 2) := by
    calc
      cap.denominator ^ 2 *
          (squaredNormFloor.denominator * shiftedModularProjectionSqNorm q shift J w) =
          squaredNormFloor.denominator *
            (cap.denominator ^ 2 * shiftedModularProjectionSqNorm q shift J w) := by
        ac_rfl
      _ ≤ squaredNormFloor.denominator *
          (parameters.rows * (cap.numerator ^ 2 * inputThreshold ^ 2)) :=
        Nat.mul_le_mul_left _ hsum
      _ = (squaredNormFloor.denominator * parameters.rows * cap.numerator ^ 2) *
          inputThreshold ^ 2 := by ring
      _ < (squaredNormFloor.numerator * cap.denominator ^ 2) *
          inputThreshold ^ 2 :=
        Nat.mul_lt_mul_of_pos_right hfit hthresholdSq
      _ = cap.denominator ^ 2 *
          (squaredNormFloor.numerator * inputThreshold ^ 2) := by ring
  exact Nat.lt_of_mul_lt_mul_left hscaled

/-- An affine squared-norm lower tail implies the affine coordinate-cap
lower tail whenever their exact constants fit. -/
theorem affineLInfThresholdLowerTailAt_of_affineL2
    (distribution : ProjectionDistribution) (rows : ℕ)
    (coordinateCap squaredNormFloor modulusMargin : NonnegativeRatio)
    (budget : ENNReal)
    (hfit : LInfCapFitsL2SquaredNormFloor rows coordinateCap squaredNormFloor)
    (hl2 : AffineL2ThresholdLowerTailAt
      { distribution := distribution, rows := rows, squaredNormFloor := squaredNormFloor,
        modulusMargin := modulusMargin } budget) :
    AffineLInfThresholdLowerTailAt
      { distribution := distribution, rows := rows, coordinateCap := coordinateCap,
        modulusMargin := modulusMargin } budget := by
  intro q d w inputThreshold shift hq hcentered hpositive hnorm hmodulus
  let lInfParameters : LInfThresholdLowerParameters :=
    { distribution := distribution, rows := rows, coordinateCap := coordinateCap,
      modulusMargin := modulusMargin }
  calc
    eventProbability (distribution.matrixPMF rows d)
        (AffineLInfThresholdSmallProjection lInfParameters inputThreshold q
          shift w) ≤
        eventProbability (distribution.matrixPMF rows d)
          (AffineL2ThresholdLowerFailure squaredNormFloor inputThreshold q
            shift w) := by
      apply eventProbability_mono
      intro J hsmall
      exact affineLInfThresholdSmallProjection_implies_l2Failure
        lInfParameters squaredNormFloor inputThreshold q shift w J hpositive hfit
          hsmall
    _ < budget :=
      hl2 q d w inputThreshold shift hq hcentered hpositive hnorm hmodulus

/-- The exact Akita-facing constants have `0.2704 b²` of deterministic
squared-norm slack: `256 * (67/200)^2 = 28.7296 < 29`. -/
theorem rows256_cap67div200_fits_squaredNormFloor29 :
    LInfCapFitsL2SquaredNormFloor 256
      { numerator := 67, denominator := 200, denominator_pos := by decide }
      (NonnegativeRatio.ofNat 29) := by
  norm_num [LInfCapFitsL2SquaredNormFloor, NonnegativeRatio.ofNat]

end CertifiedJL
