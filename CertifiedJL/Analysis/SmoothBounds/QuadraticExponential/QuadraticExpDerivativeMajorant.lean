/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpHigherDerivative
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic

/-!
# Pointwise majorants for quadratic-exponential derivatives

This module records the finite-sum derivative majorant used in the sparse
upper-tail argument.  Its sixth- and eighth-order specializations are linked
directly to the exact derivative formulas; expectation bounds are left to the
later moment-comparison layer.
-/

namespace CertifiedJL

open scoped BigOperators

/-- The finite pointwise majorant for the `m`-th derivative of
`x ↦ exp (s * x²)`, before taking an expectation. -/
noncomputable def quadraticExpDerivativePointwiseMajorant
    (m : ℕ) (rho lambda x : ℝ) : ℝ :=
  Nat.factorial m *
    ∑ j ∈ Finset.range (m / 2 + 1),
      (2 : ℝ) ^ (m - 2 * j) * rho ^ (m - j) /
          (Nat.factorial j * Nat.factorial (m - 2 * j)) *
        |x| ^ (m - 2 * j) * Real.exp (lambda * x ^ 2)

/-- The pointwise derivative majorant is nonnegative when `rho` is. -/
theorem quadraticExpDerivativePointwiseMajorant_nonneg
    {m : ℕ} {rho lambda x : ℝ} (hrho : 0 ≤ rho) :
    0 ≤ quadraticExpDerivativePointwiseMajorant m rho lambda x := by
  unfold quadraticExpDerivativePointwiseMajorant
  positivity

/-- A total arithmetic extension of the coefficient-uniform derivative
majorant.  For even `m`, this is exactly the paper's `D_m(ρ; λ)`; semantic
consumers must retain that parity condition.  In that case the `j = m / 2`
term uses `0‼ = 1`, matching the paper's convention `(-1)!! = 1`.

Values at odd `m` are bookkeeping values of this total `ℕ`-indexed formula,
not claims about the paper's Gaussian even-moment expansion. -/
noncomputable def quadraticExpDerivativeMajorant
    (m : ℕ) (rho lambda : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m / 2 + 1),
    let ell := (m - 2 * j) / 2
    Nat.factorial m * (2 : ℝ) ^ (m - 2 * j) * rho ^ (m - j) /
          (Nat.factorial j * Nat.factorial (m - 2 * j)) *
        (Nat.doubleFactorial (2 * ell - 1) : ℝ) / (2 : ℝ) ^ ell *
      Real.rpow (1 - lambda) (-(ell : ℝ) - 1 / 2)

/-- The total arithmetic extension is nonnegative when `ρ ≥ 0` and `λ < 1`.
For paper-level uses of `D_m`, the separate even-order condition still applies. -/
theorem quadraticExpDerivativeMajorant_nonneg
    {m : ℕ} {rho lambda : ℝ} (hrho : 0 ≤ rho) (hlambda : lambda < 1) :
    0 ≤ quadraticExpDerivativeMajorant m rho lambda := by
  unfold quadraticExpDerivativeMajorant
  have hbase : 0 ≤ 1 - lambda := by linarith
  refine Finset.sum_nonneg (fun j _ => ?_)
  dsimp only
  have hfactj : (0 : ℝ) < Nat.factorial j := by positivity
  have hfactrest : (0 : ℝ) < Nat.factorial (m - 2 * j) := by positivity
  have hdouble : (0 : ℝ) ≤ Nat.doubleFactorial
      (2 * ((m - 2 * j) / 2) - 1) := by positivity
  have hrpow : 0 ≤ Real.rpow (1 - lambda)
      (-(((m - 2 * j) / 2 : ℕ) : ℝ) - 1 / 2) :=
    Real.rpow_nonneg hbase _
  positivity

/-- Closed finite expansion of `D₆`. -/
theorem quadraticExpDerivativeMajorant_six (rho lambda : ℝ) :
    quadraticExpDerivativeMajorant 6 rho lambda =
      120 * rho ^ 3 * Real.rpow (1 - lambda) (-(1 : ℝ) / 2) +
      360 * rho ^ 4 * Real.rpow (1 - lambda) (-(3 : ℝ) / 2) +
      360 * rho ^ 5 * Real.rpow (1 - lambda) (-(5 : ℝ) / 2) +
      120 * rho ^ 6 * Real.rpow (1 - lambda) (-(7 : ℝ) / 2) := by
  norm_num [quadraticExpDerivativeMajorant, Finset.sum_range_succ]
  ring

/-- Closed finite expansion of `D₈`. -/
theorem quadraticExpDerivativeMajorant_eight (rho lambda : ℝ) :
    quadraticExpDerivativeMajorant 8 rho lambda =
      1680 * rho ^ 4 * Real.rpow (1 - lambda) (-(1 : ℝ) / 2) +
      6720 * rho ^ 5 * Real.rpow (1 - lambda) (-(3 : ℝ) / 2) +
      10080 * rho ^ 6 * Real.rpow (1 - lambda) (-(5 : ℝ) / 2) +
      6720 * rho ^ 7 * Real.rpow (1 - lambda) (-(7 : ℝ) / 2) +
      1680 * rho ^ 8 * Real.rpow (1 - lambda) (-(9 : ℝ) / 2) := by
  norm_num [quadraticExpDerivativeMajorant, Finset.sum_range_succ]
  ring

private theorem complexQuadraticExp_norm (s : ℂ) (x : ℝ) :
    ‖complexQuadraticExp s x‖ = Real.exp (s.re * x ^ 2) := by
  simp only [complexQuadraticExp, Complex.norm_exp]
  congr 1
  rw [Complex.mul_re]
  norm_num [pow_two, Complex.mul_re, Complex.mul_im]

private theorem sixth_polynomial_norm_le (s : ℂ) (x : ℝ) :
    ‖120 * s ^ 3 + 720 * s ^ 4 * (x : ℂ) ^ 2 +
        480 * s ^ 5 * (x : ℂ) ^ 4 + 64 * s ^ 6 * (x : ℂ) ^ 6‖ ≤
      120 * ‖s‖ ^ 3 + 720 * ‖s‖ ^ 4 * |x| ^ 2 +
        480 * ‖s‖ ^ 5 * |x| ^ 4 + 64 * ‖s‖ ^ 6 * |x| ^ 6 := by
  calc
    _ ≤ ‖120 * s ^ 3‖ + ‖720 * s ^ 4 * (x : ℂ) ^ 2‖ +
          ‖480 * s ^ 5 * (x : ℂ) ^ 4‖ + ‖64 * s ^ 6 * (x : ℂ) ^ 6‖ := by
      exact norm_add₄_le
    _ = _ := by
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      norm_num

private theorem eighth_polynomial_norm_le (s : ℂ) (x : ℝ) :
    ‖1680 * s ^ 4 + 13440 * s ^ 5 * (x : ℂ) ^ 2 +
        13440 * s ^ 6 * (x : ℂ) ^ 4 + 3584 * s ^ 7 * (x : ℂ) ^ 6 +
        256 * s ^ 8 * (x : ℂ) ^ 8‖ ≤
      1680 * ‖s‖ ^ 4 + 13440 * ‖s‖ ^ 5 * |x| ^ 2 +
        13440 * ‖s‖ ^ 6 * |x| ^ 4 + 3584 * ‖s‖ ^ 7 * |x| ^ 6 +
        256 * ‖s‖ ^ 8 * |x| ^ 8 := by
  calc
    _ ≤ ‖1680 * s ^ 4‖ + ‖13440 * s ^ 5 * (x : ℂ) ^ 2‖ +
          ‖13440 * s ^ 6 * (x : ℂ) ^ 4‖ +
          ‖3584 * s ^ 7 * (x : ℂ) ^ 6‖ +
          ‖256 * s ^ 8 * (x : ℂ) ^ 8‖ := by
      exact (norm_add_le
        (1680 * s ^ 4 + 13440 * s ^ 5 * (x : ℂ) ^ 2 +
          13440 * s ^ 6 * (x : ℂ) ^ 4 + 3584 * s ^ 7 * (x : ℂ) ^ 6)
        (256 * s ^ 8 * (x : ℂ) ^ 8)).trans
          (add_le_add norm_add₄_le le_rfl)
    _ = _ := by
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      norm_num

/-- Closed finite expansion of the sixth-order pointwise majorant. -/
theorem quadraticExpDerivativePointwiseMajorant_six
    (rho lambda x : ℝ) :
    quadraticExpDerivativePointwiseMajorant 6 rho lambda x =
      (120 * rho ^ 3 + 720 * rho ^ 4 * |x| ^ 2 +
        480 * rho ^ 5 * |x| ^ 4 + 64 * rho ^ 6 * |x| ^ 6) *
        Real.exp (lambda * x ^ 2) := by
  norm_num [quadraticExpDerivativePointwiseMajorant, Finset.sum_range_succ]
  ring

/-- Closed finite expansion of the eighth-order pointwise majorant. -/
theorem quadraticExpDerivativePointwiseMajorant_eight
    (rho lambda x : ℝ) :
    quadraticExpDerivativePointwiseMajorant 8 rho lambda x =
      (1680 * rho ^ 4 + 13440 * rho ^ 5 * |x| ^ 2 +
        13440 * rho ^ 6 * |x| ^ 4 + 3584 * rho ^ 7 * |x| ^ 6 +
        256 * rho ^ 8 * |x| ^ 8) * Real.exp (lambda * x ^ 2) := by
  norm_num [quadraticExpDerivativePointwiseMajorant, Finset.sum_range_succ]
  ring

/-- Sixth-derivative pointwise bound in the exact finite-sum normalization
used by the upper-tail derivative majorant. -/
theorem norm_iteratedDeriv_six_complexQuadraticExp_le (s : ℂ) (x : ℝ) :
    ‖iteratedDeriv 6 (complexQuadraticExp s) x‖ ≤
      quadraticExpDerivativePointwiseMajorant 6 ‖s‖ s.re x := by
  rw [iteratedDeriv_six_complexQuadraticExp, norm_mul,
    complexQuadraticExp_norm, quadraticExpDerivativePointwiseMajorant_six]
  exact mul_le_mul_of_nonneg_right (sixth_polynomial_norm_le s x)
    (Real.exp_pos _).le

/-- Eighth-derivative pointwise bound in the exact finite-sum normalization
used by the upper-tail derivative majorant. -/
theorem norm_iteratedDeriv_eight_complexQuadraticExp_le (s : ℂ) (x : ℝ) :
    ‖iteratedDeriv 8 (complexQuadraticExp s) x‖ ≤
      quadraticExpDerivativePointwiseMajorant 8 ‖s‖ s.re x := by
  rw [iteratedDeriv_eight_complexQuadraticExp, norm_mul,
    complexQuadraticExp_norm, quadraticExpDerivativePointwiseMajorant_eight]
  exact mul_le_mul_of_nonneg_right (eighth_polynomial_norm_le s x)
    (Real.exp_pos _).le

end CertifiedJL
