/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpIntegrability
import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpMomentMajorant
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Exact tilted moments of the variance-one-half Gaussian

This module evaluates the reference moments on the right side of the paper's
hybrid moment comparison.  It is the concrete Gaussian half of U3c; the
separate comparison layer transfers these bounds to hybrid laws.
-/

namespace CertifiedJL

open MeasureTheory ProbabilityTheory Set
open scoped Nat

private theorem integral_abs_evenPow_mul_exp_neg_mul_sq
    (ell : ℕ) {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ, |x| ^ (2 * ell) * Real.exp (-b * x ^ 2)) =
      (Nat.doubleFactorial (2 * ell - 1) : ℝ) * Real.sqrt Real.pi /
        (2 : ℝ) ^ ell * Real.rpow b (-(ell : ℝ) - 1 / 2) := by
  rw [show (fun x : ℝ => |x| ^ (2 * ell) * Real.exp (-b * x ^ 2)) =
      (fun x : ℝ => |x| ^ ((2 * ell : ℕ) : ℝ) * Real.exp (-b * |x| ^ 2)) by
    funext x
    rw [Real.rpow_natCast, sq_abs]]
  rw [integral_comp_abs
    (f := fun x : ℝ => x ^ ((2 * ell : ℕ) : ℝ) * Real.exp (-b * x ^ 2))]
  have hhalf := integral_rpow_mul_exp_neg_mul_rpow (p := (2 : ℝ))
    (q := ((2 * ell : ℕ) : ℝ)) (b := b) (by norm_num)
      (by
        have h : (0 : ℝ) ≤ ((2 * ell : ℕ) : ℝ) := by positivity
        linarith) hb
  rw [show (∫ x : ℝ in Ioi 0,
      x ^ ((2 * ell : ℕ) : ℝ) * Real.exp (-b * x ^ 2)) =
      Real.rpow b (-(((2 * ell : ℕ) : ℝ) + 1) / 2) * (1 / 2) *
        Real.Gamma ((((2 * ell : ℕ) : ℝ) + 1) / 2) by
    simpa using hhalf]
  rw [show (((2 * ell : ℕ) : ℝ) + 1) / 2 = (ell : ℝ) + 1 / 2 by norm_num; ring]
  rw [Real.Gamma_nat_add_half]
  rw [show -(((2 * ell : ℕ) : ℝ) + 1) / 2 =
      -(ell : ℝ) - 1 / 2 by push_cast; ring]
  ring

/-- The variance-one-half Gaussian has the exact tilted `2ℓ`-th moment
appearing in the U3/U3c derivative majorant. -/
theorem integral_gaussianHalf_abs_evenPow_mul_exp_sq
    (ell : ℕ) {lambda : ℝ} (hlambda : lambda < 1) :
    (∫ x : ℝ, |x| ^ (2 * ell) * Real.exp (lambda * x ^ 2)
        ∂(gaussianReal 0 (2 : NNReal)⁻¹)) =
      gaussianHalfTiltedEvenMomentMajorant ell lambda := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [smul_eq_mul, gaussianPDFReal]
  have hsqrt_two : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsqrt_pi : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
  calc
    _ = ∫ x : ℝ, (Real.sqrt Real.pi)⁻¹ *
        (|x| ^ (2 * ell) * Real.exp (-(1 - lambda) * x ^ 2)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      norm_num [Real.exp_add]
      field_simp [hsqrt_two, hsqrt_pi]
      calc
        Real.exp (-x ^ 2) * |x| ^ (2 * ell) * Real.exp (x ^ 2 * lambda) =
            |x| ^ (2 * ell) *
              (Real.exp (-x ^ 2) * Real.exp (x ^ 2 * lambda)) := by ring
        _ = |x| ^ (2 * ell) * Real.exp (x ^ 2 * (lambda - 1)) := by
          rw [← Real.exp_add]
          congr 2
          ring
    _ = _ := by
      rw [integral_const_mul]
      rw [integral_abs_evenPow_mul_exp_neg_mul_sq ell (sub_pos.mpr hlambda)]
      unfold gaussianHalfTiltedEvenMomentMajorant
      have hsqrt : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
      field_simp

/-- The variance-one-half Gaussian realizes the exact tilted even-moment
interface used by the sixth- and eighth-derivative expectation bounds. -/
theorem gaussianHalf_quadraticExpEvenMomentBound
    {lambda : ℝ} (hlambda_nonneg : 0 ≤ lambda) (hlambda_lt_one : lambda < 1) :
    QuadraticExpEvenMomentBound
      (gaussianReal 0 (2 : NNReal)⁻¹) lambda := by
  refine ⟨hlambda_nonneg, hlambda_lt_one, ?_, ?_⟩
  · intro ell
    have hcomplex := integrable_gaussianReal_evenPow_mul_complexQuadraticExp
      (s := (lambda : ℂ)) (μ := 0)
      (v := (2 : NNReal)⁻¹) (by norm_num)
      (by simpa using hlambda_lt_one) ell
    refine hcomplex.norm.congr ?_
    filter_upwards [] with x
    rw [norm_mul, norm_pow, Complex.norm_real]
    simp only [complexQuadraticExp, Complex.norm_exp]
    norm_num [Complex.mul_re]
    exact Or.inl (Or.inl (by norm_num [pow_two, Complex.mul_re]))
  · intro ell
    exact (integral_gaussianHalf_abs_evenPow_mul_exp_sq ell hlambda_lt_one).le

end CertifiedJL
