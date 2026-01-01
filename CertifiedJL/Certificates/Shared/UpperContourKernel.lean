/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Interval.Reflection

/-!
# Distribution-neutral upper-contour arithmetic

This module contains only the fixed-point arithmetic shared by the sparse and
sign upper-contour certificates.  The law-specific fourth-order coefficients
are explicit data, so sharing the evaluator does not identify the two analytic
row bounds.
-/

namespace CertifiedJL
namespace UpperContourKernel

/-- The signed-dyadic interval type used by contour profile boxes. -/
abbrev DInterval (p : ℕ) := Interval p

/-- The three law-specific multipliers in the normalized row expression. -/
structure RowCoefficients where
  /-- Multiplier of `r z^2` in the leading correction. -/
  leading : ℚ
  /-- Multiplier of `r^2 D_8`. -/
  error8 : ℚ
  /-- Multiplier of `r^(3/2) D_6`. -/
  error6 : ℚ
deriving DecidableEq

/-- Enclose an exact rational on the contour dyadic grid. -/
def frac (p : ℕ) (x : ℚ) : DInterval p := Interval.ofRat p x

/-- The smallest contour-grid enclosure of zero. -/
def zero (p : ℕ) : DInterval p := frac p 0

/-- The smallest contour-grid enclosure of one. -/
def one (p : ℕ) : DInterval p := frac p 1

/-- Linear powering for the small exponents in derivative majorants. -/
def powNat {p : ℕ} (x : DInterval p) : ℕ → DInterval p
  | 0 => one p
  | n + 1 => powNat x n * x

/-- Efficient tensor power for exponents `oddPart * 2^squareCount`. -/
def tensorPower {p : ℕ} (x : DInterval p)
    (oddPart squareCount : ℕ) : DInterval p :=
  powNat (x.squareN squareCount) oddPart

/-- The factored tensor-power evaluator encloses the corresponding real power. -/
theorem tensorPower_contains {p : ℕ} {x : ℝ} {xInterval : DInterval p}
    (hx : xInterval.Contains x) (oddPart squareCount : ℕ) :
    (tensorPower xInterval oddPart squareCount).Contains
      (x ^ (oddPart * 2 ^ squareCount)) := by
  have hsquare := Interval.contains_squareN hx squareCount
  have hpow : ∀ n,
      (powNat (xInterval.squareN squareCount) n).Contains
        ((Interval.iterSquare x squareCount) ^ n) := by
    intro n
    induction n with
    | zero =>
        simpa [powNat, one, frac] using Interval.contains_ofRat p (1 : ℚ)
    | succ n ih =>
        simpa [powNat, pow_succ] using Interval.contains_mul ih hsquare
  simpa [tensorPower, Interval.iterSquare_eq_pow_two_pow, ← pow_mul,
    Nat.mul_comm] using
    hpow oddPart

/--
Outward enclosure of a security-scaled negative exponential without first
rounding an exponentially tiny unscaled value to the dyadic grid.

The executable identity is
`2^(blockBits * 2^r) * exp (-x) =
  (2^blockBits * exp (-(x / 2^r)))^(2^r)`.
For the high-security family we use `blockBits = 12` at 192 bits and
`blockBits = 16` at 256 bits, both with `r = 4`.
-/
def scaledNegExpUpper (p blockBits : ℕ) (x : ℚ)
    (expSquarings scaleSquarings : ℕ) : DInterval p :=
  let divisor : ℕ := 2 ^ scaleSquarings
  (frac p (2 ^ blockBits) *
      Exp.negUpper p (x / divisor) expSquarings).squareN scaleSquarings

/-- The scaled negative-exponential evaluator encloses its exact value. -/
theorem scaledNegExpUpper_contains
    (p blockBits : ℕ) (x : ℚ) (expSquarings scaleSquarings : ℕ)
    (hx : 0 ≤ x) :
    (scaledNegExpUpper p blockBits x expSquarings scaleSquarings).Contains
      ((2 : ℝ) ^ (blockBits * 2 ^ scaleSquarings) * Real.exp (-(x : ℝ))) := by
  let divisor : ℕ := 2 ^ scaleSquarings
  have hscale : (frac p (2 ^ blockBits : ℚ)).Contains
      ((2 : ℝ) ^ blockBits) := by
    simpa [frac] using Interval.contains_ofRat p (2 ^ blockBits : ℚ)
  have hxdiv : 0 ≤ x / (divisor : ℚ) := div_nonneg hx (by positivity)
  have hexp := Exp.negUpper_contains (p := p) (k := expSquarings) hxdiv
  have hbase := Interval.contains_mul hscale hexp
  have hpower := Interval.contains_squareN hbase scaleSquarings
  have hvalue :
      (((2 : ℝ) ^ blockBits * Real.exp (-(x / (divisor : ℚ) : ℚ))) ^ divisor) =
        (2 : ℝ) ^ (blockBits * divisor) * Real.exp (-(x : ℝ)) := by
    rw [mul_pow, ← pow_mul, ← Real.exp_nat_mul]
    congr 2
    push_cast
    field_simp [divisor]
  simpa only [scaledNegExpUpper, divisor,
    Interval.iterSquare_eq_pow_two_pow, hvalue] using hpower

/-- Outward-rounded division, used when the denominator interval is positive. -/
def divide {p : ℕ} (x y : DInterval p) : DInterval p := x * y.reciprocal

/-- Division encloses the exact quotient when the denominator interval is positive. -/
theorem contains_divide_of_pos
    {p : ℕ} {x y : ℝ} {xInterval yInterval : DInterval p}
    (hyPos : 0 < yInterval.lo)
    (hx : xInterval.Contains x) (hy : yInterval.Contains y) :
    (divide xInterval yInterval).Contains (x / y) := by
  simpa only [divide, div_eq_mul_inv] using
    Interval.contains_mul hx (Interval.contains_reciprocal_of_pos hyPos hy)

/-- Replace an interval's lower endpoint by zero. -/
def nonnegativeUpperHull {p : ℕ} (x : DInterval p) : DInterval p := ⟨0, x.hi⟩

/-- A nonnegative enclosed value remains enclosed by the nonnegative hull. -/
theorem contains_nonnegativeUpperHull
    {p : ℕ} {x : ℝ} {xInterval : DInterval p}
    (hxNonneg : 0 ≤ x) (hx : xInterval.Contains x) :
    (nonnegativeUpperHull xInterval).Contains x := by
  exact ⟨by simpa [nonnegativeUpperHull, Interval.Contains, Dyadic.toReal_zero], hx.2⟩

/-- `(2n-1)!!`, with the conventional value one at `n = 0`. -/
def oddDoubleFactorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (2 * n + 1) * oddDoubleFactorial n

/-- One term of a normalized derivative majorant. -/
def normalizedDerivativeTerm
    (p order index : ℕ) (rho : DInterval p) (oneMinus : ℚ) : DInterval p :=
  let ell := (order - 2 * index) / 2
  let coefficient : ℚ :=
    (Nat.factorial order * 2 ^ (order - 2 * index) *
        oddDoubleFactorial ell : ℕ) /
      (Nat.factorial index * Nat.factorial (order - 2 * index) * 2 ^ ell : ℕ) /
      oneMinus ^ ell
  frac p coefficient * powNat rho (order - index)

/-- Sum of the normalized derivative-majorant terms at one order. -/
def normalizedDerivativeMajorant
    (p order : ℕ) (rho : DInterval p) (oneMinus : ℚ) : DInterval p :=
  (List.range (order / 2 + 1)).foldl
    (fun result index =>
      result + normalizedDerivativeTerm p order index rho oneMinus)
    (zero p)

/--
Enclose the modulus of the complex leading correction
`1 - c r (zReal + i zImag)^2`.

The radicand is explicitly hulled at zero before square root.  This is the
primitive needed by both law-specific row expressions.
-/
def leadingCorrectionModulus
    (p : ℕ) (coefficient profile : ℚ)
    (zReal zImag : DInterval p) : DInterval p :=
  let zSquaredReal := zReal.square - zImag.square
  let zSquaredImaginary := frac p 2 * zReal * zImag
  let leadingReal := one p - frac p (coefficient * profile) * zSquaredReal
  let leadingImaginary := -(frac p (coefficient * profile) * zSquaredImaginary)
  let radicand := leadingReal.square + leadingImaginary.square
  (nonnegativeUpperHull radicand).sqrt

/-- Soundness of the leading-correction modulus enclosure. -/
theorem contains_leadingCorrectionModulus
    (p : ℕ)
    (coefficient profile : ℚ) (zReal zImag : ℝ)
    {zRealInterval zImagInterval : DInterval p}
    (hzReal : zRealInterval.Contains zReal)
    (hzImag : zImagInterval.Contains zImag) :
    (leadingCorrectionModulus p coefficient profile zRealInterval zImagInterval).Contains
      (Real.sqrt
        ((1 - coefficient * profile * (zReal ^ 2 - zImag ^ 2)) ^ 2 +
          (-(coefficient * profile * (2 * zReal * zImag))) ^ 2)) := by
  have hcoefficient : (frac p (coefficient * profile)).Contains
      ((coefficient * profile : ℚ) : ℝ) :=
    Interval.contains_ofRat p (coefficient * profile)
  have htwo : (frac p 2).Contains (2 : ℝ) := by
    simpa [frac] using Interval.contains_ofRat p (2 : ℚ)
  have hzSquaredReal := Interval.contains_sub
    (Interval.contains_square hzReal) (Interval.contains_square hzImag)
  have hzSquaredImaginary := Interval.contains_mul
    (Interval.contains_mul htwo hzReal) hzImag
  have hone := Interval.contains_ofRat p (1 : ℚ)
  have hleadingReal := Interval.contains_sub hone
    (Interval.contains_mul hcoefficient hzSquaredReal)
  have hleadingImaginary := Interval.contains_neg
    (Interval.contains_mul hcoefficient hzSquaredImaginary)
  have hradicand := Interval.contains_add
    (Interval.contains_square hleadingReal)
    (Interval.contains_square hleadingImaginary)
  have hhulled := contains_nonnegativeUpperHull (xInterval :=
      (one p - frac p (coefficient * profile) *
        (zRealInterval.square - zImagInterval.square)).square +
      (-(frac p (coefficient * profile) *
        (frac p 2 * zRealInterval * zImagInterval))).square)
    (by positivity) hradicand
  have hsqrt := Interval.contains_sqrt (I := nonnegativeUpperHull
      ((one p - frac p (coefficient * profile) *
        (zRealInterval.square - zImagInterval.square)).square +
      (-(frac p (coefficient * profile) *
        (frac p 2 * zRealInterval * zImagInterval))).square)) le_rfl hhulled
  simpa [leadingCorrectionModulus, one, frac, mul_assoc] using hsqrt

/-- Interval evaluation of a law-specific fourth-order row expression. -/
def rowExpressionOnCell
    (p : ℕ)
    (coefficients : RowCoefficients)
    (profile frequencyLeft frequencyRight lam : ℚ) : DInterval p :=
  let oneMinus := 1 - lam
  let frequency := Interval.enclose p frequencyLeft frequencyRight
  let frequencySquared := frequency.square
  let denominator := frac p (oneMinus * oneMinus) + frequencySquared
  let zReal := divide (frac p (lam * oneMinus) - frequencySquared) denominator
  let zImaginary := divide frequency denominator
  let leadingModulus :=
    leadingCorrectionModulus p coefficients.leading profile zReal zImaginary
  let gaussianModulus :=
    divide (frac p oneMinus).sqrt denominator.sqrt.sqrt
  let rho := (frac p (lam * lam) + frequencySquared).sqrt
  let error8 :=
    frac p (coefficients.error8 * profile * profile) *
      normalizedDerivativeMajorant p 8 rho oneMinus
  let error6 :=
    if profile = 0 then zero p
    else
      frac p coefficients.error6 *
        (frac p profile * (frac p profile).sqrt) *
        normalizedDerivativeMajorant p 6 rho oneMinus
  gaussianModulus * leadingModulus + error8 + error6

/-- Upper enclosure of the inverse square root at a cell's left endpoint. -/
def inverseSqrtAtLeft (p : ℕ) (frequencyLeft lam : ℚ) : DInterval p :=
  (frac p (lam * lam + frequencyLeft * frequencyLeft)).sqrt.reciprocal

/-- Rational lower bound for the standard normal CDF on `[0,1]`. -/
def phiLower (value : ℚ) : ℚ :=
  1 / 2 + 199 / 500 *
    ((List.range 6).foldl
      (fun result index =>
        result +
          (if index % 2 = 1 then (-1 : ℚ) else 1) * value ^ (2 * index + 1) /
            (2 ^ index * Nat.factorial index * (2 * index + 1) : ℕ))
      0)

/-- Flatten any chunk plan into the cell indices that it covers. -/
def coveredCellsFor (plan : List (ℕ × ℕ)) : List ℕ :=
  plan.flatMap fun chunk =>
    (List.range chunk.2).map fun offset => chunk.1 + offset

end UpperContourKernel
end CertifiedJL
