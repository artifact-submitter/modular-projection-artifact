/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Statements.L2.Lower.Affine
import CertifiedJL.Statements.LInf.Lower.Affine
import CertifiedJL.Statements.Transport.Upper

/-!
# Monotonicity of exact projection parameters

These lemmas transport the public tail schemas across exact rational floors,
coordinate caps, modulus margins, upper thresholds, and security budgets.
They do not introduce numerical estimates.
-/

namespace CertifiedJL

namespace NonnegativeRatio

/-- An exact comparison of nonnegative ratios implies the corresponding
comparison after squaring. -/
theorem LE.squaredLE {lower upper : NonnegativeRatio}
    (h : lower.LE upper) : lower.SquaredLE upper := by
  unfold LE at h
  unfold SquaredLE
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
    Nat.pow_le_pow_left h 2

private theorem lowerFailure_mono
    {lower upper : NonnegativeRatio} (h : lower.LE upper)
    {squaredNorm thresholdSq : ℕ}
    (hfailure : lower.denominator * squaredNorm < lower.numerator * thresholdSq) :
    upper.denominator * squaredNorm < upper.numerator * thresholdSq := by
  have hscaled := Nat.mul_lt_mul_of_pos_left hfailure upper.denominator_pos
  have hratio := Nat.mul_le_mul_right thresholdSq h
  exact Nat.lt_of_mul_lt_mul_left (calc
    lower.denominator * (upper.denominator * squaredNorm) =
        upper.denominator * (lower.denominator * squaredNorm) := by ac_rfl
    _ < upper.denominator * (lower.numerator * thresholdSq) := hscaled
    _ = (lower.numerator * upper.denominator) * thresholdSq := by ac_rfl
    _ ≤ (upper.numerator * lower.denominator) * thresholdSq := hratio
    _ = lower.denominator * (upper.numerator * thresholdSq) := by ac_rfl)

private theorem lowerClosed_mono
    {lower upper : NonnegativeRatio} (h : lower.SquaredLE upper)
    {value thresholdSq : ℕ}
    (hsmall : lower.denominator ^ 2 * value ≤
      lower.numerator ^ 2 * thresholdSq) :
    upper.denominator ^ 2 * value ≤
      upper.numerator ^ 2 * thresholdSq := by
  have hscaled := Nat.mul_le_mul_left (upper.denominator ^ 2) hsmall
  have hratio := Nat.mul_le_mul_right thresholdSq h
  exact Nat.le_of_mul_le_mul_left (calc
      lower.denominator ^ 2 * (upper.denominator ^ 2 * value) =
          upper.denominator ^ 2 * (lower.denominator ^ 2 * value) := by ac_rfl
      _ ≤ upper.denominator ^ 2 * (lower.numerator ^ 2 * thresholdSq) := hscaled
      _ = (lower.numerator ^ 2 * upper.denominator ^ 2) * thresholdSq := by ac_rfl
      _ ≤ (upper.numerator ^ 2 * lower.denominator ^ 2) * thresholdSq := hratio
      _ = lower.denominator ^ 2 *
          (upper.numerator ^ 2 * thresholdSq) := by ac_rfl)
    (Nat.pow_pos lower.denominator_pos)

end NonnegativeRatio

/-- A stronger modulus margin implies every weaker exact rational margin. -/
theorem InputThresholdWithinModulus.antitone_margin
    {weaker stronger : NonnegativeRatio} (hmargin : weaker.LE stronger)
    {q inputThreshold : ℕ}
    (h : InputThresholdWithinModulus stronger q inputThreshold) :
    InputThresholdWithinModulus weaker q inputThreshold := by
  unfold InputThresholdWithinModulus at h ⊢
  have hratio := Nat.mul_le_mul_right inputThreshold hmargin
  have hscaled := Nat.mul_le_mul_left weaker.denominator h
  apply Nat.le_of_mul_le_mul_left _ stronger.denominator_pos
  calc
    stronger.denominator * (weaker.numerator * inputThreshold) =
        (weaker.numerator * stronger.denominator) * inputThreshold := by ac_rfl
    _ ≤ (stronger.numerator * weaker.denominator) * inputThreshold := hratio
    _ = weaker.denominator * (stronger.numerator * inputThreshold) := by ac_rfl
    _ ≤ weaker.denominator * (stronger.denominator * q) := hscaled
    _ = stronger.denominator * (weaker.denominator * q) := by ac_rfl

/-- Raising the exact squared-norm floor enlarges the strict lower-failure event. -/
theorem L2ThresholdLowerFailure.mono_squaredNormFloor
    {lower upper : NonnegativeRatio} (hfloor : lower.LE upper)
    {inputThreshold q rows d : ℕ} {w : Fin d → ℤ}
    {J : Fin rows → Fin d → ℤ}
    (h : L2ThresholdLowerFailure lower inputThreshold q w J) :
    L2ThresholdLowerFailure upper inputThreshold q w J :=
  NonnegativeRatio.lowerFailure_mono hfloor h

/-- A lower-tail theorem remains valid after decreasing its exact squared-norm
floor. -/
theorem L2ThresholdLowerTailAt.mono_squaredNormFloor
    {parameters : L2ThresholdLowerParameters} {budget : ENNReal}
    {squaredNormFloor : NonnegativeRatio}
    (hfloor : squaredNormFloor.LE parameters.squaredNormFloor)
    (h : L2ThresholdLowerTailAt parameters budget) :
    L2ThresholdLowerTailAt
      { parameters with squaredNormFloor := squaredNormFloor } budget := by
  intro q d w inputThreshold hq hcentered hpositive hnorm hmodulus
  apply (eventProbability_mono _ fun J hJ =>
    L2ThresholdLowerFailure.mono_squaredNormFloor hfloor hJ).trans_lt
  exact h q d w inputThreshold hq hcentered hpositive hnorm hmodulus

/-- An affine lower-tail theorem remains valid after decreasing its exact
squared-norm floor. -/
theorem AffineL2ThresholdLowerTailAt.mono_squaredNormFloor
    {parameters : L2ThresholdLowerParameters} {budget : ENNReal}
    {squaredNormFloor : NonnegativeRatio}
    (hfloor : squaredNormFloor.LE parameters.squaredNormFloor)
    (h : AffineL2ThresholdLowerTailAt parameters budget) :
    AffineL2ThresholdLowerTailAt
      { parameters with squaredNormFloor := squaredNormFloor } budget := by
  intro q d w inputThreshold shift hq hcentered hpositive hnorm hmodulus
  apply (eventProbability_mono _ fun J hJ =>
    NonnegativeRatio.lowerFailure_mono hfloor hJ).trans_lt
  exact h q d w inputThreshold shift hq hcentered hpositive hnorm hmodulus

/-- A lower-tail theorem at a weaker modulus condition remains valid when the
statement assumes a stronger margin. -/
theorem L2ThresholdLowerTailAt.mono_modulusMargin
    {parameters : L2ThresholdLowerParameters} {budget : ENNReal}
    {modulusMargin : NonnegativeRatio}
    (hmargin : parameters.modulusMargin.LE modulusMargin)
    (h : L2ThresholdLowerTailAt parameters budget) :
    L2ThresholdLowerTailAt
      { parameters with modulusMargin := modulusMargin } budget := by
  intro q d w inputThreshold hq hcentered hpositive hnorm hmodulus
  exact h q d w inputThreshold hq hcentered hpositive hnorm
    (hmodulus.antitone_margin hmargin)

/-- Affine version of exact modulus-margin strengthening. -/
theorem AffineL2ThresholdLowerTailAt.mono_modulusMargin
    {parameters : L2ThresholdLowerParameters} {budget : ENNReal}
    {modulusMargin : NonnegativeRatio}
    (hmargin : parameters.modulusMargin.LE modulusMargin)
    (h : AffineL2ThresholdLowerTailAt parameters budget) :
    AffineL2ThresholdLowerTailAt
      { parameters with modulusMargin := modulusMargin } budget := by
  intro q d w inputThreshold shift hq hcentered hpositive hnorm hmodulus
  exact h q d w inputThreshold shift hq hcentered hpositive hnorm
    (hmodulus.antitone_margin hmargin)

/-- Enlarging an exact coordinate cap enlarges the closed lower event. -/
theorem LInfThresholdSmallProjection.mono_coordinateCap
    {parameters : LInfThresholdLowerParameters} {coordinateCap : NonnegativeRatio}
    (hcap : parameters.coordinateCap.SquaredLE coordinateCap)
    {inputThreshold q d : ℕ} {w : Fin d → ℤ}
    {J : Fin parameters.rows → Fin d → ℤ}
    (h : LInfThresholdSmallProjection parameters inputThreshold q w J) :
    LInfThresholdSmallProjection
      { parameters with coordinateCap := coordinateCap }
      inputThreshold q w J := by
  intro j
  exact NonnegativeRatio.lowerClosed_mono hcap (h j)

/-- A coordinatewise lower-tail theorem remains valid after decreasing its
exact cap. -/
theorem LInfThresholdLowerTailAt.mono_coordinateCap
    {parameters : LInfThresholdLowerParameters} {budget : ENNReal}
    {coordinateCap : NonnegativeRatio}
    (hcap : coordinateCap.SquaredLE parameters.coordinateCap)
    (h : LInfThresholdLowerTailAt parameters budget) :
    LInfThresholdLowerTailAt
      { parameters with coordinateCap := coordinateCap } budget := by
  intro q d w inputThreshold hq hcentered hpositive hnorm hmodulus
  apply (eventProbability_mono _ fun J hJ =>
    LInfThresholdSmallProjection.mono_coordinateCap hcap hJ).trans_lt
  exact h q d w inputThreshold hq hcentered hpositive hnorm hmodulus

/-- Affine coordinate-cap event monotonicity. -/
theorem AffineLInfThresholdSmallProjection.mono_coordinateCap
    {parameters : LInfThresholdLowerParameters} {coordinateCap : NonnegativeRatio}
    (hcap : parameters.coordinateCap.SquaredLE coordinateCap)
    {inputThreshold q d : ℕ} {shift : Fin parameters.rows → ℤ}
    {w : Fin d → ℤ} {J : Fin parameters.rows → Fin d → ℤ}
    (h : AffineLInfThresholdSmallProjection parameters inputThreshold q shift w J) :
    AffineLInfThresholdSmallProjection
      { parameters with coordinateCap := coordinateCap }
      inputThreshold q shift w J := by
  intro j
  exact NonnegativeRatio.lowerClosed_mono hcap (h j)

/-- An affine coordinatewise lower-tail theorem remains valid after decreasing
its exact cap. -/
theorem AffineLInfThresholdLowerTailAt.mono_coordinateCap
    {parameters : LInfThresholdLowerParameters} {budget : ENNReal}
    {coordinateCap : NonnegativeRatio}
    (hcap : coordinateCap.SquaredLE parameters.coordinateCap)
    (h : AffineLInfThresholdLowerTailAt parameters budget) :
    AffineLInfThresholdLowerTailAt
      { parameters with coordinateCap := coordinateCap } budget := by
  intro q d w inputThreshold shift hq hcentered hpositive hnorm hmodulus
  apply (eventProbability_mono _ fun J hJ =>
    AffineLInfThresholdSmallProjection.mono_coordinateCap hcap hJ).trans_lt
  exact h q d w inputThreshold shift hq hcentered hpositive hnorm hmodulus

/-- Coordinatewise lower-tail modulus-margin strengthening. -/
theorem LInfThresholdLowerTailAt.mono_modulusMargin
    {parameters : LInfThresholdLowerParameters} {budget : ENNReal}
    {modulusMargin : NonnegativeRatio}
    (hmargin : parameters.modulusMargin.LE modulusMargin)
    (h : LInfThresholdLowerTailAt parameters budget) :
    LInfThresholdLowerTailAt
      { parameters with modulusMargin := modulusMargin } budget := by
  intro q d w inputThreshold hq hcentered hpositive hnorm hmodulus
  exact h q d w inputThreshold hq hcentered hpositive hnorm
    (hmodulus.antitone_margin hmargin)

/-- Affine coordinatewise lower-tail modulus-margin strengthening. -/
theorem AffineLInfThresholdLowerTailAt.mono_modulusMargin
    {parameters : LInfThresholdLowerParameters} {budget : ENNReal}
    {modulusMargin : NonnegativeRatio}
    (hmargin : parameters.modulusMargin.LE modulusMargin)
    (h : AffineLInfThresholdLowerTailAt parameters budget) :
    AffineLInfThresholdLowerTailAt
      { parameters with modulusMargin := modulusMargin } budget := by
  intro q d w inputThreshold shift hq hcentered hpositive hnorm hmodulus
  exact h q d w inputThreshold shift hq hcentered hpositive hnorm
    (hmodulus.antitone_margin hmargin)

/-- Increasing an exact coordinate threshold shrinks the infinity-norm upper
failure event. -/
theorem LInfUpperFailure.antitone_coordinateThreshold
    {parameters : LInfUpperParameters} {coordinateThreshold : NonnegativeRatio}
    (hthreshold : parameters.coordinateThreshold.SquaredLE coordinateThreshold)
    {q d : ℕ} {w : Fin d → ℤ}
    {J : Fin parameters.rows → Fin d → ℤ}
    (h : LInfUpperFailure
      { parameters with coordinateThreshold := coordinateThreshold } q w J) :
    LInfUpperFailure parameters q w J := by
  obtain ⟨j, hj⟩ := h
  refine ⟨j, ?_⟩
  simp only at hj
  have hscaled := Nat.mul_lt_mul_of_pos_left hj
    (Nat.pow_pos (n := 2) parameters.coordinateThreshold.denominator_pos)
  have hratio := Nat.mul_le_mul_right (sqNorm w) hthreshold
  exact Nat.lt_of_mul_lt_mul_left (calc
    coordinateThreshold.denominator ^ 2 *
        (parameters.coordinateThreshold.numerator ^ 2 * sqNorm w) =
      (parameters.coordinateThreshold.numerator ^ 2 *
        coordinateThreshold.denominator ^ 2) * sqNorm w := by ac_rfl
    _ ≤ (coordinateThreshold.numerator ^ 2 *
        parameters.coordinateThreshold.denominator ^ 2) * sqNorm w := hratio
    _ = parameters.coordinateThreshold.denominator ^ 2 *
        (coordinateThreshold.numerator ^ 2 * sqNorm w) := by ac_rfl
    _ < parameters.coordinateThreshold.denominator ^ 2 *
        (coordinateThreshold.denominator ^ 2 *
          (centeredMod q (rowDot J w j)).natAbs ^ 2) := hscaled
    _ = coordinateThreshold.denominator ^ 2 *
        (parameters.coordinateThreshold.denominator ^ 2 *
          (centeredMod q (rowDot J w j)).natAbs ^ 2) := by
            simp only [mul_left_comm])

/-- An infinity-norm upper-tail theorem at a smaller exact threshold implies
the theorem at every larger exact threshold. -/
theorem LInfUpperTailAt.mono_coordinateThreshold
    {parameters : LInfUpperParameters} {budget : ENNReal}
    {coordinateThreshold : NonnegativeRatio}
    (hthreshold : parameters.coordinateThreshold.SquaredLE coordinateThreshold)
    (h : LInfUpperTailAt parameters budget) :
    LInfUpperTailAt
      { parameters with coordinateThreshold := coordinateThreshold } budget := by
  intro q d w
  apply (eventProbability_mono _ fun J hJ =>
    LInfUpperFailure.antitone_coordinateThreshold hthreshold hJ).trans_lt
  exact h q d w

/-- Affine L2 upper tails remain valid under a larger failure budget. -/
theorem AffineL2UpperTailAt.mono_budget
    {parameters : L2UpperParameters} {budget budget' : ENNReal}
    (h : AffineL2UpperTailAt parameters budget) (hbudget : budget ≤ budget') :
    AffineL2UpperTailAt parameters budget' := by
  intro q d w shift
  exact (h q d w shift).trans_le hbudget

/-- Affine infinity-norm upper tails remain valid under a larger failure
budget. -/
theorem AffineLInfUpperTailAt.mono_budget
    {parameters : LInfUpperParameters} {budget budget' : ENNReal}
    (h : AffineLInfUpperTailAt parameters budget) (hbudget : budget ≤ budget') :
    AffineLInfUpperTailAt parameters budget' := by
  intro q d w shift
  exact (h q d w shift).trans_le hbudget

/-- More security bits give a weakly smaller exact failure target. -/
theorem failureTarget_antitone {bits bits' : ℕ} (hbits : bits ≤ bits') :
    failureTarget bits' ≤ failureTarget bits := by
  unfold failureTarget
  exact pow_le_pow_of_le_one (by positivity) (by norm_num) hbits

end CertifiedJL
