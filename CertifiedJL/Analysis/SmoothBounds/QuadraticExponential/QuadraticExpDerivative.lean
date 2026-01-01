/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

/-!
# Complex-domain derivative polynomial for the quadratic exponential

The real-argument restriction is exposed by `QuadraticExp`.  This module
first proves the exact fourth derivative on the complex domain, where the
calculus instances are canonical; the later real restriction and envelope
lemmas are separate bridges.
-/

namespace CertifiedJL

open scoped Topology

noncomputable def complexQuadraticExpComplex (s z : ℂ) : ℂ :=
  Complex.exp (s * z ^ 2)

noncomputable def complexQuadraticExpFourthPolynomialComplex (s z : ℂ) : ℂ :=
  12 * s ^ 2 + 48 * s ^ 3 * z ^ 2 + 16 * s ^ 4 * z ^ 4

private lemma hasDerivAt_complexQuadraticExpComplex (s z : ℂ) :
    HasDerivAt (fun y : ℂ => complexQuadraticExpComplex s y)
      (2 * s * z * complexQuadraticExpComplex s z) z := by
  have hsq : HasDerivAt (fun y : ℂ => y ^ 2) (2 * z) z := by
    simpa using hasDerivAt_pow 2 z
  have harg : HasDerivAt (fun y : ℂ => s * y ^ 2) (s * (2 * z)) z := by
    have h := hsq.const_mul s
    simpa using h
  have h := harg.cexp
  simpa only [complexQuadraticExpComplex, mul_assoc, mul_left_comm, mul_comm] using h

private lemma hasDerivAt_complexQuadraticExpComplex_first (s z : ℂ) :
    HasDerivAt (fun y : ℂ =>
      2 * s * y * complexQuadraticExpComplex s y)
      ((2 * s + 4 * s ^ 2 * z ^ 2) * complexQuadraticExpComplex s z) z := by
  have hy : HasDerivAt (fun y : ℂ => y) 1 z := hasDerivAt_id z
  have hf := hasDerivAt_complexQuadraticExpComplex s z
  have hleft : HasDerivAt (fun y : ℂ => 2 * s * y) (2 * s) z := by
    have h := hy.const_mul (2 * s)
    simpa using h
  have h := hleft.mul hf
  have hfun :
      (fun y : ℂ => 2 * s * y * complexQuadraticExpComplex s y) =ᶠ[𝓝 z]
        (fun y : ℂ => 2 * s * y) * (fun y : ℂ => complexQuadraticExpComplex s y) := by
    filter_upwards [] with y
    rfl
  exact (h.congr_of_eventuallyEq hfun).congr_deriv (by ring)

private lemma hasDerivAt_complexQuadraticExpComplex_second (s z : ℂ) :
    HasDerivAt (fun y : ℂ =>
      (2 * s + 4 * s ^ 2 * y ^ 2) * complexQuadraticExpComplex s y)
      ((12 * s ^ 2 * z + 8 * s ^ 3 * z ^ 3) * complexQuadraticExpComplex s z) z := by
  have hsq : HasDerivAt (fun y : ℂ => y ^ 2) (2 * z) z := by
    simpa using hasDerivAt_pow 2 z
  have hconst : HasDerivAt (fun _ : ℂ => 2 * s) 0 z := hasDerivAt_const z (2 * s)
  have hterm := hsq.const_mul (4 * s ^ 2)
  have hcoef := hconst.add hterm
  have hcoef' : HasDerivAt (fun y : ℂ => 2 * s + 4 * s ^ 2 * y ^ 2)
      (8 * s ^ 2 * z) z := by
    have hfun :
        (fun y : ℂ => 2 * s + 4 * s ^ 2 * y ^ 2) =ᶠ[𝓝 z]
          (fun _ : ℂ => 2 * s) + (fun y : ℂ => 4 * s ^ 2 * y ^ 2) := by
      filter_upwards [] with y
      rfl
    exact (hcoef.congr_of_eventuallyEq hfun).congr_deriv (by ring)
  have hf := hasDerivAt_complexQuadraticExpComplex s z
  have h := hcoef'.mul hf
  have hfun :
      (fun y : ℂ =>
        (2 * s + 4 * s ^ 2 * y ^ 2) * complexQuadraticExpComplex s y) =ᶠ[𝓝 z]
        (fun y : ℂ => 2 * s + 4 * s ^ 2 * y ^ 2) *
          (fun y : ℂ => complexQuadraticExpComplex s y) := by
    filter_upwards [] with y
    rfl
  exact (h.congr_of_eventuallyEq hfun).congr_deriv (by ring)

private lemma hasDerivAt_complexQuadraticExpComplex_third (s z : ℂ) :
    HasDerivAt (fun y : ℂ =>
      (12 * s ^ 2 * y + 8 * s ^ 3 * y ^ 3) * complexQuadraticExpComplex s y)
      ((12 * s ^ 2 + 48 * s ^ 3 * z ^ 2 + 16 * s ^ 4 * z ^ 4) *
        complexQuadraticExpComplex s z) z := by
  have hy : HasDerivAt (fun y : ℂ => y) 1 z := hasDerivAt_id z
  have hcube : HasDerivAt (fun y : ℂ => y ^ 3) (3 * z ^ 2) z := by
    simpa using hasDerivAt_pow 3 z
  have hlinear := hy.const_mul (12 * s ^ 2)
  have hcubic := hcube.const_mul (8 * s ^ 3)
  have hcoef := hlinear.add hcubic
  have hcoef' : HasDerivAt (fun y : ℂ => 12 * s ^ 2 * y + 8 * s ^ 3 * y ^ 3)
      (12 * s ^ 2 + 24 * s ^ 3 * z ^ 2) z := by
    have hfun :
        (fun y : ℂ => 12 * s ^ 2 * y + 8 * s ^ 3 * y ^ 3) =ᶠ[𝓝 z]
          (fun y : ℂ => 12 * s ^ 2 * y) + (fun y : ℂ => 8 * s ^ 3 * y ^ 3) := by
      filter_upwards [] with y
      rfl
    exact (hcoef.congr_of_eventuallyEq hfun).congr_deriv (by ring)
  have hf := hasDerivAt_complexQuadraticExpComplex s z
  have h := hcoef'.mul hf
  have hfun :
      (fun y : ℂ =>
        (12 * s ^ 2 * y + 8 * s ^ 3 * y ^ 3) * complexQuadraticExpComplex s y) =ᶠ[𝓝 z]
        (fun y : ℂ => 12 * s ^ 2 * y + 8 * s ^ 3 * y ^ 3) *
          (fun y : ℂ => complexQuadraticExpComplex s y) := by
    filter_upwards [] with y
    rfl
  exact (h.congr_of_eventuallyEq hfun).congr_deriv (by ring)

theorem iteratedDeriv_four_complexQuadraticExpComplex (s z : ℂ) :
    iteratedDeriv 4 (complexQuadraticExpComplex s) z =
      complexQuadraticExpFourthPolynomialComplex s z * complexQuadraticExpComplex s z := by
  have h0 :
      deriv (complexQuadraticExpComplex s) =
        (fun y : ℂ => 2 * s * y * complexQuadraticExpComplex s y) := by
    funext y
    exact (hasDerivAt_complexQuadraticExpComplex s y).deriv
  have h1 :
      deriv (fun y : ℂ => 2 * s * y * complexQuadraticExpComplex s y) =
        (fun y : ℂ =>
          (2 * s + 4 * s ^ 2 * y ^ 2) * complexQuadraticExpComplex s y) := by
    funext y
    exact (hasDerivAt_complexQuadraticExpComplex_first s y).deriv
  have h2 :
      deriv (fun y : ℂ =>
        (2 * s + 4 * s ^ 2 * y ^ 2) * complexQuadraticExpComplex s y) =
        (fun y : ℂ =>
          (12 * s ^ 2 * y + 8 * s ^ 3 * y ^ 3) * complexQuadraticExpComplex s y) := by
    funext y
    exact (hasDerivAt_complexQuadraticExpComplex_second s y).deriv
  have h3 :
      deriv (fun y : ℂ =>
        (12 * s ^ 2 * y + 8 * s ^ 3 * y ^ 3) * complexQuadraticExpComplex s y) =
        (fun y : ℂ =>
          (12 * s ^ 2 + 48 * s ^ 3 * y ^ 2 + 16 * s ^ 4 * y ^ 4) *
            complexQuadraticExpComplex s y) := by
    funext y
    exact (hasDerivAt_complexQuadraticExpComplex_third s y).deriv
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [h0, h1, h2, h3]
  rfl

private theorem deriv_complexQuadraticExp_eq (s : ℂ) :
    deriv (complexQuadraticExp s) =
      (fun y : ℝ => 2 * s * (y : ℂ) * complexQuadraticExp s y) := by
  funext y
  have h := (hasDerivAt_complexQuadraticExpComplex s (y : ℂ)).comp_ofReal
  change deriv (fun z : ℝ => Complex.exp (s * (z : ℂ) ^ 2)) y =
    2 * s * (y : ℂ) * Complex.exp (s * (y : ℂ) ^ 2)
  simpa only [complexQuadraticExpComplex] using h.deriv

private theorem deriv_complexQuadraticExp_one_eq (s : ℂ) :
    deriv (fun y : ℝ => 2 * s * (y : ℂ) * complexQuadraticExp s y) =
      (fun y : ℝ =>
        (2 * s + 4 * s ^ 2 * (y : ℂ) ^ 2) * complexQuadraticExp s y) := by
  funext y
  have h := (hasDerivAt_complexQuadraticExpComplex_first s (y : ℂ)).comp_ofReal
  simpa only [complexQuadraticExp, complexQuadraticExpComplex] using h.deriv

private theorem deriv_complexQuadraticExp_two_eq (s : ℂ) :
    deriv (fun y : ℝ =>
      (2 * s + 4 * s ^ 2 * (y : ℂ) ^ 2) * complexQuadraticExp s y) =
      (fun y : ℝ =>
        (12 * s ^ 2 * (y : ℂ) + 8 * s ^ 3 * (y : ℂ) ^ 3) *
          complexQuadraticExp s y) := by
  funext y
  have h := (hasDerivAt_complexQuadraticExpComplex_second s (y : ℂ)).comp_ofReal
  simpa only [complexQuadraticExp, complexQuadraticExpComplex] using h.deriv

private theorem deriv_complexQuadraticExp_three_eq (s : ℂ) :
    deriv (fun y : ℝ =>
      (12 * s ^ 2 * (y : ℂ) + 8 * s ^ 3 * (y : ℂ) ^ 3) *
        complexQuadraticExp s y) =
      (fun y : ℝ =>
        (12 * s ^ 2 + 48 * s ^ 3 * (y : ℂ) ^ 2 +
          16 * s ^ 4 * (y : ℂ) ^ 4) * complexQuadraticExp s y) := by
  funext y
  have h := (hasDerivAt_complexQuadraticExpComplex_third s (y : ℂ)).comp_ofReal
  simpa only [complexQuadraticExp, complexQuadraticExpComplex] using h.deriv

/-- The first derivative of the real-argument quadratic exponential. -/
theorem iteratedDeriv_one_complexQuadraticExp (s : ℂ) (x : ℝ) :
    iteratedDeriv 1 (complexQuadraticExp s) x =
      2 * s * (x : ℂ) * complexQuadraticExp s x := by
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [deriv_complexQuadraticExp_eq]

/-- The second derivative of the real-argument quadratic exponential. -/
theorem iteratedDeriv_two_complexQuadraticExp (s : ℂ) (x : ℝ) :
    iteratedDeriv 2 (complexQuadraticExp s) x =
      (2 * s + 4 * s ^ 2 * (x : ℂ) ^ 2) * complexQuadraticExp s x := by
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [deriv_complexQuadraticExp_eq, deriv_complexQuadraticExp_one_eq]

/-- The third derivative of the real-argument quadratic exponential. -/
theorem iteratedDeriv_three_complexQuadraticExp (s : ℂ) (x : ℝ) :
    iteratedDeriv 3 (complexQuadraticExp s) x =
      (12 * s ^ 2 * (x : ℂ) + 8 * s ^ 3 * (x : ℂ) ^ 3) *
        complexQuadraticExp s x := by
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [deriv_complexQuadraticExp_eq, deriv_complexQuadraticExp_one_eq,
    deriv_complexQuadraticExp_two_eq]

theorem iteratedDeriv_four_complexQuadraticExp (s : ℂ) (x : ℝ) :
    iteratedDeriv 4 (complexQuadraticExp s) x =
      complexQuadraticExpFourthPolynomialComplex s (x : ℂ) * complexQuadraticExp s x := by
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [deriv_complexQuadraticExp_eq, deriv_complexQuadraticExp_one_eq,
    deriv_complexQuadraticExp_two_eq, deriv_complexQuadraticExp_three_eq]
  rfl

end CertifiedJL
