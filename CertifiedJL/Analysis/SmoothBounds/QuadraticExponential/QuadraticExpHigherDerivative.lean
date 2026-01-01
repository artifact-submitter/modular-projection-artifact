/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpDerivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

/-!
# Higher derivatives of the quadratic exponential

The upper-tail replacement argument uses the sixth and eighth derivatives of
`x ↦ exp (s * x²)`.  This module derives every real-domain derivative from one
polynomial recurrence and then exposes the two exact formulas needed by the
row comparison.
-/

namespace CertifiedJL

open scoped Polynomial

/-- The polynomial multiplying `exp (s * z²)` after `n` derivatives. -/
noncomputable def complexQuadraticExpDerivativePolynomial (s : ℂ) : ℕ → ℂ[X]
  | 0 => 1
  | n + 1 =>
      (complexQuadraticExpDerivativePolynomial s n).derivative +
        Polynomial.C (2 * s) * Polynomial.X *
          complexQuadraticExpDerivativePolynomial s n

private theorem hasDerivAt_complexQuadraticExpComplex_generic (s z : ℂ) :
    HasDerivAt (complexQuadraticExpComplex s)
      (2 * s * z * complexQuadraticExpComplex s z) z := by
  have hsq : HasDerivAt (fun y : ℂ => y ^ 2) (2 * z) z := by
    simpa using hasDerivAt_pow 2 z
  have harg : HasDerivAt (fun y : ℂ => s * y ^ 2) (s * (2 * z)) z := by
    simpa using hsq.const_mul s
  have h := harg.cexp
  change HasDerivAt (fun y : ℂ => Complex.exp (s * y ^ 2))
    (2 * s * z * Complex.exp (s * z ^ 2)) z
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

/-- Real-argument restriction of the recurrence formula. -/
theorem iteratedDeriv_complexQuadraticExp (n : ℕ) (s : ℂ) (x : ℝ) :
    iteratedDeriv n (complexQuadraticExp s) x =
      (complexQuadraticExpDerivativePolynomial s n).eval (x : ℂ) *
        complexQuadraticExp s x := by
  induction n generalizing x with
  | zero => simp [complexQuadraticExpDerivativePolynomial]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hfun :
          iteratedDeriv n (complexQuadraticExp s) =
            fun y : ℝ =>
              (complexQuadraticExpDerivativePolynomial s n).eval (y : ℂ) *
                complexQuadraticExp s y := by
        funext y
        exact ih y
      rw [hfun]
      have hp :=
        ((complexQuadraticExpDerivativePolynomial s n).hasDerivAt
          (x : ℂ)).comp_ofReal
      have he :=
        (hasDerivAt_complexQuadraticExpComplex_generic s (x : ℂ)).comp_ofReal
      have hprod := hp.mul he
      change deriv
        ((fun y : ℝ =>
            (complexQuadraticExpDerivativePolynomial s n).eval (y : ℂ)) *
          (fun y : ℝ => Complex.exp (s * (y : ℂ) ^ 2))) x =
        (complexQuadraticExpDerivativePolynomial s (n + 1)).eval (x : ℂ) *
          Complex.exp (s * (x : ℂ) ^ 2)
      have hderiv :
          deriv
            ((fun y : ℝ =>
                (complexQuadraticExpDerivativePolynomial s n).eval (y : ℂ)) *
              (fun y : ℝ => Complex.exp (s * (y : ℂ) ^ 2))) x =
            (complexQuadraticExpDerivativePolynomial s n).derivative.eval (x : ℂ) *
                Complex.exp (s * (x : ℂ) ^ 2) +
              (complexQuadraticExpDerivativePolynomial s n).eval (x : ℂ) *
                (2 * s * (x : ℂ) * Complex.exp (s * (x : ℂ) ^ 2)) := by
        simpa only [complexQuadraticExpComplex] using hprod.deriv
      rw [hderiv]
      simp only [complexQuadraticExpDerivativePolynomial,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      ring

/-- Real-argument specialization of the exact sixth derivative. -/
theorem iteratedDeriv_six_complexQuadraticExp (s : ℂ) (x : ℝ) :
    iteratedDeriv 6 (complexQuadraticExp s) x =
      (120 * s ^ 3 + 720 * s ^ 4 * (x : ℂ) ^ 2 +
        480 * s ^ 5 * (x : ℂ) ^ 4 + 64 * s ^ 6 * (x : ℂ) ^ 6) *
        complexQuadraticExp s x := by
  rw [iteratedDeriv_complexQuadraticExp]
  congr 1
  norm_num [complexQuadraticExpDerivativePolynomial]
  ring

/-- Real-argument specialization of the exact eighth derivative. -/
theorem iteratedDeriv_eight_complexQuadraticExp (s : ℂ) (x : ℝ) :
    iteratedDeriv 8 (complexQuadraticExp s) x =
      (1680 * s ^ 4 + 13440 * s ^ 5 * (x : ℂ) ^ 2 +
        13440 * s ^ 6 * (x : ℂ) ^ 4 + 3584 * s ^ 7 * (x : ℂ) ^ 6 +
        256 * s ^ 8 * (x : ℂ) ^ 8) * complexQuadraticExp s x := by
  rw [iteratedDeriv_complexQuadraticExp]
  congr 1
  norm_num [complexQuadraticExpDerivativePolynomial]
  ring

end CertifiedJL
