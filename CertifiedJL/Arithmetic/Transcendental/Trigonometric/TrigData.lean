/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Interval.Interval
import Mathlib.Data.Nat.Factorial.Basic

/-! Executable trigonometric interval evaluators; analytic soundness is separate. -/
namespace CertifiedJL.TrigInterval

/-- Twenty-decimal rational lower endpoint for `pi`. -/
def piLower : ℚ := 314159265358979323846 / 100000000000000000000

/-- Twenty-decimal rational upper endpoint for `pi`. -/
def piUpper : ℚ := 314159265358979323847 / 100000000000000000000

/-- Linear interval power, used by the finite Taylor evaluators. -/
def pow {p : ℕ} (I : Interval p) : ℕ → Interval p
  | 0 => Interval.ofRat p 1
  | n + 1 => pow I n * I

/-- One signed sine Taylor term. -/
def sinTerm {p : ℕ} (X : Interval p) (i : ℕ) : Interval p :=
  pow X (2 * i + 1) *
    Interval.ofRat p
      (((-1 : ℚ) ^ i) / ((2 * i + 1).factorial : ℚ))

/-- The first `n` signed sine Taylor terms. -/
def sinPartial {p : ℕ} (X : Interval p) : ℕ → Interval p
  | 0 => Interval.ofRat p 0
  | n + 1 => sinPartial X n + sinTerm X n

/-- High-order sine interval on `[0, pi / 2]`. -/
def sinTaylor {p : ℕ} (X : Interval p) (k : ℕ) : Interval p :=
  ⟨(sinPartial X (2 * k)).lo, (sinPartial X (2 * k + 1)).hi⟩

/-- One signed term in the alternating series for `1 - cos x`. -/
def cosTailTerm {p : ℕ} (X : Interval p) (i : ℕ) : Interval p :=
  pow X (2 * (i + 1)) *
    Interval.ofRat p
      (((-1 : ℚ) ^ i) / ((2 * (i + 1)).factorial : ℚ))

/-- The first `n` signed terms in the series for `1 - cos x`. -/
def cosTailPartial {p : ℕ} (X : Interval p) : ℕ → Interval p
  | 0 => Interval.ofRat p 0
  | n + 1 => cosTailPartial X n + cosTailTerm X n

/-- High-order cosine interval on `[0, pi / 2]`. -/
def cosTaylor {p : ℕ} (X : Interval p) (k : ℕ) : Interval p :=
  let lower := Interval.ofRat p 1 - cosTailPartial X (2 * k + 1)
  let upper := Interval.ofRat p 1 - cosTailPartial X (2 * k)
  ⟨lower.lo, upper.hi⟩

/-- Dyadic enclosure of `pi * s` for a nonnegative rational `s`. -/
def piMul {p : ℕ} (s : ℚ) : Interval p :=
  Interval.enclose p (piLower * s) (piUpper * s)

/-- Outward enclosure of `pi * s` for every real `s` in a rational range.
The nonnegative lower endpoint is part of the soundness interface because
the endpoint products use the positive interval for `pi`. -/
def piRange {p : ℕ} (lower upper : ℚ) : Interval p :=
  Interval.enclose p (piLower * lower) (piUpper * upper)

/-- Sine enclosure uniform over a rational subrange of the first quadrant. -/
def sinPiRange {p : ℕ} (lower upper : ℚ) (k : ℕ) : Interval p :=
  sinTaylor (piRange lower upper) k

/-- Cosine enclosure uniform over a rational subrange of the first quadrant. -/
def cosPiRange {p : ℕ} (lower upper : ℚ) (k : ℕ) : Interval p :=
  cosTaylor (piRange lower upper) k

/-- Executable sine enclosure for `sin (pi * s)`, `0 ≤ s ≤ 1/2`. -/
def sinPiHalf {p : ℕ} (s : ℚ) (k : ℕ) : Interval p :=
  sinTaylor (piMul s) k

/-- Executable cosine enclosure for `cos (pi * s)`, `0 ≤ s ≤ 1/2`. -/
def cosPiHalf {p : ℕ} (s : ℚ) (k : ℕ) : Interval p :=
  cosTaylor (piMul s) k

end CertifiedJL.TrigInterval
