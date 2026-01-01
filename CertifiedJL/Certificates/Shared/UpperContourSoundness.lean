/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Shared.UpperContourKernel
import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpDerivativeMajorant

/-!
# Semantic soundness of the shared upper-contour kernel

This module connects the executable dyadic evaluator to literal real
expressions.  It remains distribution-neutral: sparse and sign coefficients
are supplied as data by downstream certificate modules.
-/

namespace CertifiedJL
namespace UpperContourKernel

/-- Real value represented by one normalized derivative-majorant term. -/
noncomputable def normalizedDerivativeTermValue
    (order index : ℕ) (rho : ℝ) (oneMinus : ℚ) : ℝ :=
  let ell := (order - 2 * index) / 2
  let coefficient : ℚ :=
    (Nat.factorial order * 2 ^ (order - 2 * index) *
        oddDoubleFactorial ell : ℕ) /
      (Nat.factorial index * Nat.factorial (order - 2 * index) * 2 ^ ell : ℕ) /
      oneMinus ^ ell
  (coefficient : ℝ) * rho ^ (order - index)

/-- Literal real sum evaluated by `normalizedDerivativeMajorant`. -/
noncomputable def normalizedDerivativeMajorantValue
    (order : ℕ) (rho : ℝ) (oneMinus : ℚ) : ℝ :=
  (List.range (order / 2 + 1)).foldl
    (fun result index =>
      result + normalizedDerivativeTermValue order index rho oneMinus) 0

/-- Linear interval powering encloses ordinary natural powers. -/
theorem contains_powNat {p : ℕ} {x : ℝ} {xInterval : DInterval p}
    (hx : xInterval.Contains x) (n : ℕ) :
    (powNat xInterval n).Contains (x ^ n) := by
  induction n with
  | zero =>
      simpa [powNat, one, frac] using Interval.contains_ofRat p (1 : ℚ)
  | succ n ih =>
      simpa [powNat, pow_succ] using Interval.contains_mul ih hx

/-- One executable derivative term encloses its literal real value. -/
theorem contains_normalizedDerivativeTerm
    (p order index : ℕ) {rho : ℝ} {rhoInterval : DInterval p}
    (oneMinus : ℚ) (hrho : rhoInterval.Contains rho) :
    (normalizedDerivativeTerm p order index rhoInterval oneMinus).Contains
      (normalizedDerivativeTermValue order index rho oneMinus) := by
  let ell := (order - 2 * index) / 2
  let coefficient : ℚ :=
    (Nat.factorial order * 2 ^ (order - 2 * index) *
        oddDoubleFactorial ell : ℕ) /
      (Nat.factorial index * Nat.factorial (order - 2 * index) * 2 ^ ell : ℕ) /
      oneMinus ^ ell
  have hcoefficient : (frac p coefficient).Contains (coefficient : ℝ) :=
    Interval.contains_ofRat p coefficient
  have hpower := contains_powNat hrho (order - index)
  simpa [normalizedDerivativeTerm, normalizedDerivativeTermValue,
    ell, coefficient, frac] using Interval.contains_mul hcoefficient hpower

private theorem contains_normalizedDerivativeFold
    (p order : ℕ) {rho : ℝ} {rhoInterval : DInterval p}
    (oneMinus : ℚ) (hrho : rhoInterval.Contains rho)
    (indices : List ℕ) {accInterval : DInterval p} {accValue : ℝ}
    (hacc : accInterval.Contains accValue) :
    (indices.foldl
      (fun result index =>
        result + normalizedDerivativeTerm p order index rhoInterval oneMinus)
      accInterval).Contains
    (indices.foldl
      (fun result index =>
        result + normalizedDerivativeTermValue order index rho oneMinus)
      accValue) := by
  induction indices generalizing accInterval accValue with
  | nil => exact hacc
  | cons index indices ih =>
      rw [List.foldl_cons, List.foldl_cons]
      apply ih
      exact Interval.contains_add hacc
        (contains_normalizedDerivativeTerm p order index oneMinus hrho)

/-- The executable normalized derivative sum encloses its literal real sum. -/
theorem contains_normalizedDerivativeMajorant
    (p order : ℕ) {rho : ℝ} {rhoInterval : DInterval p}
    (oneMinus : ℚ) (hrho : rhoInterval.Contains rho) :
    (normalizedDerivativeMajorant p order rhoInterval oneMinus).Contains
      (normalizedDerivativeMajorantValue order rho oneMinus) := by
  apply contains_normalizedDerivativeFold p order oneMinus hrho
  simpa [zero, frac] using Interval.contains_ofRat p (0 : ℚ)

/-- Closed real expansion of the normalized sixth-derivative majorant. -/
theorem normalizedDerivativeMajorantValue_six (rho : ℝ) (oneMinus : ℚ) :
    normalizedDerivativeMajorantValue 6 rho oneMinus =
      120 * rho ^ 3 + 360 * rho ^ 4 / (oneMinus : ℝ) +
        360 * rho ^ 5 / (oneMinus : ℝ) ^ 2 +
          120 * rho ^ 6 / (oneMinus : ℝ) ^ 3 := by
  unfold normalizedDerivativeMajorantValue
  rw [show List.range (6 / 2 + 1) = [0, 1, 2, 3] by decide]
  norm_num [normalizedDerivativeTermValue, oddDoubleFactorial, List.foldl]
  ring

/-- Closed real expansion of the normalized eighth-derivative majorant. -/
theorem normalizedDerivativeMajorantValue_eight (rho : ℝ) (oneMinus : ℚ) :
    normalizedDerivativeMajorantValue 8 rho oneMinus =
      1680 * rho ^ 4 + 6720 * rho ^ 5 / (oneMinus : ℝ) +
        10080 * rho ^ 6 / (oneMinus : ℝ) ^ 2 +
          6720 * rho ^ 7 / (oneMinus : ℝ) ^ 3 +
            1680 * rho ^ 8 / (oneMinus : ℝ) ^ 4 := by
  unfold normalizedDerivativeMajorantValue
  rw [show List.range (8 / 2 + 1) = [0, 1, 2, 3, 4] by decide]
  norm_num [normalizedDerivativeTermValue, oddDoubleFactorial, List.foldl]
  ring

private theorem sqrt_mul_rpow_neg_nat_sub_half
    {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.sqrt x * x ^ (-(n : ℝ) - 1 / 2) = 1 / x ^ n := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
  have hexponent : (1 / 2 : ℝ) + (-(n : ℝ) - 1 / 2) = -(n : ℝ) := by
    ring
  rw [hexponent, Real.rpow_neg_natCast]
  simp [div_eq_mul_inv]

/-- The normalized order-six certificate sum is exactly
`sqrt (1-lambda) * D₆`. -/
theorem normalizedDerivativeMajorantValue_six_eq
    (rho : ℝ) {lambda : ℚ} (hlambda : (lambda : ℝ) < 1) :
    normalizedDerivativeMajorantValue 6 rho (1 - lambda) =
      Real.sqrt (1 - (lambda : ℝ)) *
        quadraticExpDerivativeMajorant 6 rho (lambda : ℝ) := by
  have hx : 0 < 1 - (lambda : ℝ) := sub_pos.mpr hlambda
  have h0 := sqrt_mul_rpow_neg_nat_sub_half hx 0
  have h1 := sqrt_mul_rpow_neg_nat_sub_half hx 1
  have h2 := sqrt_mul_rpow_neg_nat_sub_half hx 2
  have h3 := sqrt_mul_rpow_neg_nat_sub_half hx 3
  rw [normalizedDerivativeMajorantValue_six,
    quadraticExpDerivativeMajorant_six]
  push_cast
  ring_nf at h0 h1 h2 h3 ⊢
  linear_combination
    -(120 * rho ^ 3) * h0 -
    (360 * rho ^ 4) * h1 -
    (360 * rho ^ 5) * h2 -
    (120 * rho ^ 6) * h3

/-- The normalized order-eight certificate sum is exactly
`sqrt (1-lambda) * D₈`. -/
theorem normalizedDerivativeMajorantValue_eight_eq
    (rho : ℝ) {lambda : ℚ} (hlambda : (lambda : ℝ) < 1) :
    normalizedDerivativeMajorantValue 8 rho (1 - lambda) =
      Real.sqrt (1 - (lambda : ℝ)) *
        quadraticExpDerivativeMajorant 8 rho (lambda : ℝ) := by
  have hx : 0 < 1 - (lambda : ℝ) := sub_pos.mpr hlambda
  have h0 := sqrt_mul_rpow_neg_nat_sub_half hx 0
  have h1 := sqrt_mul_rpow_neg_nat_sub_half hx 1
  have h2 := sqrt_mul_rpow_neg_nat_sub_half hx 2
  have h3 := sqrt_mul_rpow_neg_nat_sub_half hx 3
  have h4 := sqrt_mul_rpow_neg_nat_sub_half hx 4
  rw [normalizedDerivativeMajorantValue_eight,
    quadraticExpDerivativeMajorant_eight]
  push_cast
  ring_nf at h0 h1 h2 h3 h4 ⊢
  linear_combination
    -(1680 * rho ^ 4) * h0 -
    (6720 * rho ^ 5) * h1 -
    (10080 * rho ^ 6) * h2 -
    (6720 * rho ^ 7) * h3 -
    (1680 * rho ^ 8) * h4

/-- The expanded square root used by the interval kernel is the literal norm
of the complex leading correction. -/
theorem leadingCorrectionValue_eq_norm
    (coefficient profile zReal zImaginary : ℝ) :
    Real.sqrt
        ((1 - coefficient * profile * (zReal ^ 2 - zImaginary ^ 2)) ^ 2 +
          (-(coefficient * profile * (2 * zReal * zImaginary))) ^ 2) =
      ‖1 - ((coefficient * profile : ℝ) : ℂ) *
        ((zReal : ℂ) + (zImaginary : ℂ) * Complex.I) ^ 2‖ := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp only [pow_two, Complex.sub_re, Complex.one_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.I_re, Complex.I_im, Complex.sub_im, Complex.one_im]
  ring

/-- Literal normalized U4 bound evaluated at one contour frequency. This is
the complex leading modulus plus the exact paper D8 and D6 error terms. -/
noncomputable def normalizedFourthOrderRowBound
    (coefficients : RowCoefficients) (profile lam : ℚ) (frequency : ℝ) : ℝ :=
  let oneMinus : ℚ := 1 - lam
  let denominator := (oneMinus : ℝ) ^ 2 + frequency ^ 2
  let zReal := ((lam * oneMinus : ℚ) : ℝ) / denominator -
    frequency ^ 2 / denominator
  let zImaginary := frequency / denominator
  let z : ℂ := (zReal : ℂ) + (zImaginary : ℂ) * Complex.I
  let rho := Real.sqrt (((lam * lam : ℚ) : ℝ) + frequency ^ 2)
  Real.sqrt (oneMinus : ℝ) / Real.sqrt (Real.sqrt denominator) *
      ‖1 - (((coefficients.leading * profile : ℚ) : ℝ) : ℂ) * z ^ 2‖ +
    ((coefficients.error8 * profile * profile : ℚ) : ℝ) *
      (Real.sqrt (oneMinus : ℝ) *
        quadraticExpDerivativeMajorant 8 rho (lam : ℝ)) +
    if profile = 0 then 0 else
      (coefficients.error6 : ℝ) *
        ((profile : ℝ) * Real.sqrt (profile : ℝ)) *
          (Real.sqrt (oneMinus : ℝ) *
            quadraticExpDerivativeMajorant 6 rho (lam : ℝ))

/-- Literal real expression evaluated by `rowExpressionOnCell` at one
frequency.  The expression is normalized by `sqrt (1 - lambda)`; the contour
prefactor restores the corresponding power of `(1 - lambda)⁻¹/²`. -/
noncomputable def rowExpressionValue
    (coefficients : RowCoefficients) (profile lam : ℚ) (frequency : ℝ) : ℝ :=
  let oneMinus : ℚ := 1 - lam
  let denominator := (oneMinus : ℝ) ^ 2 + frequency ^ 2
  let zReal := ((lam * oneMinus : ℚ) : ℝ) / denominator -
    frequency ^ 2 / denominator
  let zImaginary := frequency / denominator
  let leadingModulus := Real.sqrt
    ((1 - (coefficients.leading * profile : ℚ) *
        (zReal ^ 2 - zImaginary ^ 2)) ^ 2 +
      (-((coefficients.leading * profile : ℚ) *
        (2 * zReal * zImaginary))) ^ 2)
  let gaussianModulus :=
    Real.sqrt (oneMinus : ℝ) / Real.sqrt (Real.sqrt denominator)
  let rho := Real.sqrt (((lam * lam : ℚ) : ℝ) + frequency ^ 2)
  let error8 := ((coefficients.error8 * profile * profile : ℚ) : ℝ) *
    normalizedDerivativeMajorantValue 8 rho oneMinus
  let error6 := if profile = 0 then 0 else
    (coefficients.error6 : ℝ) *
      ((profile : ℝ) * Real.sqrt (profile : ℝ)) *
        normalizedDerivativeMajorantValue 6 rho oneMinus
  gaussianModulus * leadingModulus + error8 + error6

/-- The expanded real expression enclosed by the kernel is exactly the
literal normalized U4 complex-modulus bound. -/
theorem rowExpressionValue_eq_normalizedFourthOrderRowBound
    (coefficients : RowCoefficients) (profile lam : ℚ) (frequency : ℝ)
    (hlam : (lam : ℝ) < 1) :
    rowExpressionValue coefficients profile lam frequency =
      normalizedFourthOrderRowBound coefficients profile lam frequency := by
  let rho := Real.sqrt (((lam * lam : ℚ) : ℝ) + frequency ^ 2)
  have hD6 := normalizedDerivativeMajorantValue_six_eq rho hlam
  have hD8 := normalizedDerivativeMajorantValue_eight_eq rho hlam
  let oneMinus : ℚ := 1 - lam
  let denominator := (oneMinus : ℝ) ^ 2 + frequency ^ 2
  let zReal := ((lam * oneMinus : ℚ) : ℝ) / denominator -
    frequency ^ 2 / denominator
  let zImaginary := frequency / denominator
  have hleading :
      Real.sqrt
          ((1 - ((coefficients.leading * profile : ℚ) : ℝ) *
              (zReal ^ 2 - zImaginary ^ 2)) ^ 2 +
            (-(((coefficients.leading * profile : ℚ) : ℝ) *
              (2 * zReal * zImaginary))) ^ 2) =
        norm (1 - ((((coefficients.leading * profile : ℚ) : ℝ) : ℂ) *
          ((zReal : ℂ) + (zImaginary : ℂ) * Complex.I) ^ 2)) := by
    simpa using leadingCorrectionValue_eq_norm
      (((coefficients.leading * profile : ℚ) : ℝ)) 1 zReal zImaginary
  rw [rowExpressionValue, normalizedFourthOrderRowBound]
  rw [hleading, hD8]
  simp only [rho, zReal, zImaginary, denominator, oneMinus]
  by_cases hprofile : profile = 0
  · rw [if_pos hprofile, if_pos hprofile]
    simp only [Rat.cast_sub, Rat.cast_one, Rat.cast_mul]
  · rw [if_neg hprofile, if_neg hprofile, hD6]
    simp only [rho, Rat.cast_sub, Rat.cast_one, Rat.cast_mul]

/-- The canonical sparse U4 expression, repeated here so the certificate
soundness layer stays below the sparse contour assembly in the import DAG. -/
noncomputable def canonicalSparseFourthOrderNormalizedMajorant
    (profile lambda frequency : ℝ) : ℝ :=
  let s : ℂ := lambda + frequency * Complex.I
  Real.sqrt (1 - lambda) *
    (‖(1 - s) ^ (-1 / 2 : ℂ) -
        ((profile / 8 : ℝ) : ℂ) * s ^ 2 *
          (1 - s) ^ (-5 / 2 : ℂ)‖ +
      profile ^ 2 / 9216 *
        quadraticExpDerivativeMajorant 8 ‖s‖ lambda +
      11 * (profile * Real.sqrt profile) / 5760 *
        quadraticExpDerivativeMajorant 6 ‖s‖ lambda)

/-- The sparse certificate coefficients and factored `z = s/(1-s)` kernel
are exactly the canonical U4 majorant. The hypothesis `lambda < 1` keeps
`1-s` away from the complex-power branch point. -/
theorem normalizedFourthOrderRowBound_sparse_eq_canonical
    (profile lambda : ℚ) (frequency : ℝ) (hlambda : (lambda : ℝ) < 1) :
    normalizedFourthOrderRowBound
        { leading := 1 / 8, error8 := 1 / 9216, error6 := 11 / 5760 }
        profile lambda frequency =
      canonicalSparseFourthOrderNormalizedMajorant
        (profile : ℝ) (lambda : ℝ) frequency := by
  let s : ℂ := (lambda : ℝ) + frequency * Complex.I
  let w : ℂ := 1 - s
  let denominator : ℝ := (1 - (lambda : ℝ)) ^ 2 + frequency ^ 2
  let zReal : ℝ :=
    ((lambda * (1 - lambda) : ℚ) : ℝ) / denominator -
      frequency ^ 2 / denominator
  let zImaginary : ℝ := frequency / denominator
  let z : ℂ := (zReal : ℂ) + (zImaginary : ℂ) * Complex.I
  have hx : 0 < 1 - (lambda : ℝ) := sub_pos.mpr hlambda
  have hdenominator : 0 < denominator := by
    dsimp only [denominator]
    positivity
  have hw : w ≠ 0 := by
    intro hw0
    have hre := congrArg Complex.re hw0
    dsimp only [w, s] at hre
    simp only [Complex.sub_re, Complex.one_re, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, zero_mul, sub_zero, Complex.zero_re] at hre
    linarith
  have hnormw : ‖w‖ = Real.sqrt denominator := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    dsimp only [w, s, denominator]
    simp only [Complex.sub_re, Complex.one_re, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, sub_zero, Complex.sub_im,
      Complex.one_im, Complex.add_im, mul_one, add_zero]
    ring
  have hz : z = s / w := by
    rw [eq_div_iff hw]
    apply Complex.ext
    · dsimp only [z, zReal, zImaginary, s, w]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        zero_mul, sub_zero, Complex.sub_re, Complex.one_re, Complex.sub_im,
        Complex.one_im, Complex.add_im, mul_one, add_zero]
      field_simp [hdenominator.ne']
      push_cast
      ring
    · dsimp only [z, zReal, zImaginary, s, w]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul,
        add_zero, Complex.sub_re, Complex.one_re, Complex.add_re,
        Complex.mul_re, Complex.sub_im, Complex.one_im]
      field_simp [hdenominator.ne']
      push_cast
      ring
  have hnegTwo : w ^ (-2 : ℂ) = w⁻¹ ^ 2 := by
    rw [show (-2 : ℂ) = ((-2 : ℤ) : ℂ) by norm_num,
      Complex.cpow_intCast, show (-2 : ℤ) = -(2 : ℤ) by norm_num,
      zpow_neg]
    exact (inv_pow w 2).symm
  have hfactor :
      w ^ (-1 / 2 : ℂ) -
          ((((profile : ℝ) / 8 : ℝ) : ℂ) * s ^ 2 * w ^ (-5 / 2 : ℂ)) =
        w ^ (-1 / 2 : ℂ) *
          (1 - ((((profile : ℝ) / 8 : ℝ) : ℂ) * z ^ 2)) := by
    rw [show (-5 / 2 : ℂ) = (-1 / 2 : ℂ) + (-2 : ℂ) by ring,
      Complex.cpow_add (-1 / 2) (-2) hw, hnegTwo, hz]
    field_simp [hw]
  have hnormHalf : ‖w ^ (-1 / 2 : ℂ)‖ =
      1 / Real.sqrt (Real.sqrt denominator) := by
    rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_real, hnormw,
      show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg (Real.sqrt_nonneg _) (1 / 2)]
    rw [← Real.sqrt_eq_rpow]
    simp [div_eq_mul_inv]
  have hnorms : ‖s‖ = Real.sqrt (((lambda * lambda : ℚ) : ℝ) + frequency ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    dsimp only [s]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, add_zero,
      Complex.add_im, Complex.mul_im, mul_one]
    push_cast
    ring
  rw [normalizedFourthOrderRowBound,
    canonicalSparseFourthOrderNormalizedMajorant]
  dsimp only
  dsimp only [s, w, z, zReal, zImaginary, denominator] at hfactor hnormHalf hnorms
  rw [hfactor, norm_mul, hnormHalf, hnorms]
  push_cast
  by_cases hprofile : profile = 0
  · rw [if_pos hprofile]
    subst profile
    norm_num [div_eq_mul_inv]
  · rw [if_neg hprofile]
    ring

/-- The shared row evaluator encloses its literal normalized U4 expression
at every real frequency in the certified cell.  All side conditions are
primitive positivity conditions required by interval reciprocal or square
root soundness; none assumes the desired enclosure. -/
theorem contains_rowExpressionOnCell
    (p : ℕ) (coefficients : RowCoefficients)
    (profile frequencyLeft frequencyRight lam : ℚ) (frequency : ℝ)
    (hfrequency : (frequencyLeft : ℝ) ≤ frequency ∧
      frequency ≤ (frequencyRight : ℝ))
    (honeMinus : 0 ≤ (frac p (1 - lam)).lo)
    (hdenominator : 0 <
      (frac p ((1 - lam) * (1 - lam)) +
        (Interval.enclose p frequencyLeft frequencyRight).square).lo)
    (hgaussianDenominator : 0 <
      ((frac p ((1 - lam) * (1 - lam)) +
        (Interval.enclose p frequencyLeft frequencyRight).square).sqrt.sqrt).lo)
    (hrho : 0 ≤
      (frac p (lam * lam) +
        (Interval.enclose p frequencyLeft frequencyRight).square).lo)
    (hprofile : profile = 0 ∨ 0 ≤ (frac p profile).lo) :
    (rowExpressionOnCell p coefficients profile frequencyLeft frequencyRight lam).Contains
      (rowExpressionValue coefficients profile lam frequency) := by
  let oneMinus : ℚ := 1 - lam
  let frequencyInterval := Interval.enclose p frequencyLeft frequencyRight
  let frequencySquared := frequencyInterval.square
  let denominator := frac p (oneMinus * oneMinus) + frequencySquared
  let zRealInterval :=
    divide (frac p (lam * oneMinus) - frequencySquared) denominator
  let zImaginaryInterval := divide frequencyInterval denominator
  let rhoInterval := (frac p (lam * lam) + frequencySquared).sqrt
  have hfrequencyInterval : frequencyInterval.Contains frequency :=
    Interval.contains_enclose hfrequency
  have hfrequencySquared : frequencySquared.Contains (frequency ^ 2) :=
    Interval.contains_square hfrequencyInterval
  have honeMinusValue : (frac p oneMinus).Contains (oneMinus : ℝ) :=
    Interval.contains_ofRat p oneMinus
  have hdenominatorValue : denominator.Contains
      ((oneMinus : ℝ) ^ 2 + frequency ^ 2) :=
    Interval.contains_add
      (by simpa [pow_two, frac] using
        Interval.contains_ofRat p (oneMinus * oneMinus))
      hfrequencySquared
  have hzRealNumerator :
      (frac p (lam * oneMinus) - frequencySquared).Contains
        (((lam * oneMinus : ℚ) : ℝ) - frequency ^ 2) :=
    Interval.contains_sub
      (Interval.contains_ofRat p (lam * oneMinus)) hfrequencySquared
  have hzReal : zRealInterval.Contains
      ((((lam * oneMinus : ℚ) : ℝ) - frequency ^ 2) /
        ((oneMinus : ℝ) ^ 2 + frequency ^ 2)) :=
    contains_divide_of_pos hdenominator hzRealNumerator hdenominatorValue
  have hzImaginary : zImaginaryInterval.Contains
      (frequency / ((oneMinus : ℝ) ^ 2 + frequency ^ 2)) :=
    contains_divide_of_pos hdenominator hfrequencyInterval hdenominatorValue
  have hleading := contains_leadingCorrectionModulus p
    coefficients.leading profile
    ((((lam * oneMinus : ℚ) : ℝ) - frequency ^ 2) /
      ((oneMinus : ℝ) ^ 2 + frequency ^ 2))
    (frequency / ((oneMinus : ℝ) ^ 2 + frequency ^ 2)) hzReal hzImaginary
  have honeMinusSqrt : (frac p oneMinus).sqrt.Contains
      (Real.sqrt (oneMinus : ℝ)) :=
    Interval.contains_sqrt honeMinus honeMinusValue
  have hdenominatorSqrt : denominator.sqrt.Contains
      (Real.sqrt ((oneMinus : ℝ) ^ 2 + frequency ^ 2)) :=
    Interval.contains_sqrt hdenominator.le hdenominatorValue
  have hdenominatorSqrtSqrt : denominator.sqrt.sqrt.Contains
      (Real.sqrt (Real.sqrt ((oneMinus : ℝ) ^ 2 + frequency ^ 2))) :=
    Interval.contains_sqrt (by simp [Interval.sqrt]) hdenominatorSqrt
  have hgaussian :
      (divide (frac p oneMinus).sqrt denominator.sqrt.sqrt).Contains
        (Real.sqrt (oneMinus : ℝ) /
          Real.sqrt (Real.sqrt ((oneMinus : ℝ) ^ 2 + frequency ^ 2))) :=
    contains_divide_of_pos hgaussianDenominator honeMinusSqrt
      hdenominatorSqrtSqrt
  have hrhoBase : (frac p (lam * lam) + frequencySquared).Contains
      (((lam * lam : ℚ) : ℝ) + frequency ^ 2) :=
    Interval.contains_add (Interval.contains_ofRat p (lam * lam))
      hfrequencySquared
  have hrhoValue : rhoInterval.Contains
      (Real.sqrt (((lam * lam : ℚ) : ℝ) + frequency ^ 2)) :=
    Interval.contains_sqrt hrho hrhoBase
  have hD8 := contains_normalizedDerivativeMajorant p 8 oneMinus hrhoValue
  have herror8 :
      (frac p (coefficients.error8 * profile * profile) *
        normalizedDerivativeMajorant p 8 rhoInterval oneMinus).Contains
      (((coefficients.error8 * profile * profile : ℚ) : ℝ) *
        normalizedDerivativeMajorantValue 8
          (Real.sqrt (((lam * lam : ℚ) : ℝ) + frequency ^ 2)) oneMinus) :=
    Interval.contains_mul
      (Interval.contains_ofRat p (coefficients.error8 * profile * profile)) hD8
  have herror6 :
      (if profile = 0 then zero p else
        frac p coefficients.error6 *
          (frac p profile * (frac p profile).sqrt) *
          normalizedDerivativeMajorant p 6 rhoInterval oneMinus).Contains
        (if profile = 0 then 0 else
          (coefficients.error6 : ℝ) *
            ((profile : ℝ) * Real.sqrt (profile : ℝ)) *
              normalizedDerivativeMajorantValue 6
                (Real.sqrt (((lam * lam : ℚ) : ℝ) + frequency ^ 2))
                oneMinus) := by
    by_cases hprofileZero : profile = 0
    · rw [if_pos hprofileZero, if_pos hprofileZero]
      simpa [zero, frac] using Interval.contains_ofRat p (0 : ℚ)
    · rw [if_neg hprofileZero, if_neg hprofileZero]
      have hprofileNonneg : 0 ≤ (frac p profile).lo :=
        hprofile.resolve_left hprofileZero
      have hprofileValue : (frac p profile).Contains (profile : ℝ) :=
        Interval.contains_ofRat p profile
      have hprofileSqrt : (frac p profile).sqrt.Contains
          (Real.sqrt (profile : ℝ)) :=
        Interval.contains_sqrt hprofileNonneg hprofileValue
      have hD6 := contains_normalizedDerivativeMajorant p 6 oneMinus hrhoValue
      exact Interval.contains_mul
        (Interval.contains_mul
          (Interval.contains_ofRat p coefficients.error6)
          (Interval.contains_mul hprofileValue hprofileSqrt)) hD6
  have hsum := Interval.contains_add
    (Interval.contains_add (Interval.contains_mul hgaussian hleading) herror8)
    herror6
  simpa [rowExpressionOnCell, rowExpressionValue, oneMinus,
    frequencyInterval, frequencySquared, denominator, zRealInterval,
    zImaginaryInterval, rhoInterval, sub_div] using hsum

/-- Direct consumer form: a successful row-cell evaluation encloses the
literal normalized U4 complex-modulus bound, not merely an internal expanded
surrogate. -/
theorem contains_normalizedFourthOrderRowBound
    (p : ℕ) (coefficients : RowCoefficients)
    (profile frequencyLeft frequencyRight lam : ℚ) (frequency : ℝ)
    (hlam : (lam : ℝ) < 1)
    (hfrequency : (frequencyLeft : ℝ) ≤ frequency ∧
      frequency ≤ (frequencyRight : ℝ))
    (honeMinus : 0 ≤ (frac p (1 - lam)).lo)
    (hdenominator : 0 <
      (frac p ((1 - lam) * (1 - lam)) +
        (Interval.enclose p frequencyLeft frequencyRight).square).lo)
    (hgaussianDenominator : 0 <
      ((frac p ((1 - lam) * (1 - lam)) +
        (Interval.enclose p frequencyLeft frequencyRight).square).sqrt.sqrt).lo)
    (hrho : 0 ≤
      (frac p (lam * lam) +
        (Interval.enclose p frequencyLeft frequencyRight).square).lo)
    (hprofile : profile = 0 ∨ 0 ≤ (frac p profile).lo) :
    (rowExpressionOnCell p coefficients profile frequencyLeft frequencyRight lam).Contains
      (normalizedFourthOrderRowBound coefficients profile lam frequency) := by
  rw [← rowExpressionValue_eq_normalizedFourthOrderRowBound
    coefficients profile lam frequency hlam]
  exact contains_rowExpressionOnCell p coefficients profile frequencyLeft
    frequencyRight lam frequency hfrequency honeMinus hdenominator
      hgaussianDenominator hrho hprofile

end UpperContourKernel
end CertifiedJL
