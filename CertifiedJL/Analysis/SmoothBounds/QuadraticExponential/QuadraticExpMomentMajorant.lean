/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpDerivativeMajorant
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Moment interface for quadratic-exponential derivative majorants

This module isolates the exact tilted even-moment estimates needed to turn
the pointwise sixth- and eighth-derivative bounds into the paper's `D₆` and
`D₈` expectation bounds.  The later hybrid comparison proves this interface
from termwise mixed-moment domination.
-/

namespace CertifiedJL

open MeasureTheory

/-- A total arithmetic extension of the closed tilted `2ℓ`-th-moment formula.

For `lambda < 1` this is the exact variance-one-half Gaussian tilted moment;
the paper and every semantic consumer use the narrower domain
`0 ≤ lambda < 1`.  Values at or above one are only Lean's total `Real.rpow`
bookkeeping and do not represent the divergent Gaussian integral. -/
noncomputable def gaussianHalfTiltedEvenMomentMajorant
    (ell : ℕ) (lambda : ℝ) : ℝ :=
  (Nat.doubleFactorial (2 * ell - 1) : ℝ) / (2 : ℝ) ^ ell *
    Real.rpow (1 - lambda) (-(ell : ℝ) - 1 / 2)

/-- A law satisfies the exact tilted even-moment estimates used in U3c. -/
structure QuadraticExpEvenMomentBound (μ : Measure ℝ) (lambda : ℝ) : Prop where
  lambda_nonneg : 0 ≤ lambda
  lambda_lt_one : lambda < 1
  integrable (ell : ℕ) : Integrable
    (fun x : ℝ => |x| ^ (2 * ell) * Real.exp (lambda * x ^ 2)) μ
  integral_le (ell : ℕ) :
    (∫ x : ℝ, |x| ^ (2 * ell) * Real.exp (lambda * x ^ 2) ∂μ) ≤
      gaussianHalfTiltedEvenMomentMajorant ell lambda

private theorem pointwiseMajorant_six_fun_eq (rho lambda : ℝ) :
    (fun x : ℝ => quadraticExpDerivativePointwiseMajorant 6 rho lambda x) =
      (fun x : ℝ =>
        ((120 * rho ^ 3) * (|x| ^ (2 * 0) * Real.exp (lambda * x ^ 2)) +
          (720 * rho ^ 4) * (|x| ^ (2 * 1) * Real.exp (lambda * x ^ 2))) +
        ((480 * rho ^ 5) * (|x| ^ (2 * 2) * Real.exp (lambda * x ^ 2)) +
          (64 * rho ^ 6) * (|x| ^ (2 * 3) * Real.exp (lambda * x ^ 2)))) := by
  funext x
  rw [quadraticExpDerivativePointwiseMajorant_six]
  norm_num
  ring

private theorem integrable_pointwiseMajorant_six
    {μ : Measure ℝ} {lambda rho : ℝ}
    (h : QuadraticExpEvenMomentBound μ lambda) :
    Integrable
      (fun x : ℝ => quadraticExpDerivativePointwiseMajorant 6 rho lambda x) μ := by
  rw [pointwiseMajorant_six_fun_eq]
  exact
    (((h.integrable 0).const_mul (120 * rho ^ 3)).add
      ((h.integrable 1).const_mul (720 * rho ^ 4))).add
      (((h.integrable 2).const_mul (480 * rho ^ 5)).add
        ((h.integrable 3).const_mul (64 * rho ^ 6)))

private theorem integral_pointwiseMajorant_six_le
    {μ : Measure ℝ} {lambda rho : ℝ}
    (h : QuadraticExpEvenMomentBound μ lambda) (hrho : 0 ≤ rho) :
    (∫ x : ℝ, quadraticExpDerivativePointwiseMajorant 6 rho lambda x ∂μ) ≤
      quadraticExpDerivativeMajorant 6 rho lambda := by
  have h0 := h.integrable 0
  have h1 := h.integrable 1
  have h2 := h.integrable 2
  have h3 := h.integrable 3
  rw [quadraticExpDerivativeMajorant_six]
  rw [pointwiseMajorant_six_fun_eq]
  have ha : Integrable (fun x : ℝ =>
      (120 * rho ^ 3) * (|x| ^ (2 * 0) * Real.exp (lambda * x ^ 2))) μ :=
    h0.const_mul _
  have hb : Integrable (fun x : ℝ =>
      (720 * rho ^ 4) * (|x| ^ (2 * 1) * Real.exp (lambda * x ^ 2))) μ :=
    h1.const_mul _
  have hc : Integrable (fun x : ℝ =>
      (480 * rho ^ 5) * (|x| ^ (2 * 2) * Real.exp (lambda * x ^ 2))) μ :=
    h2.const_mul _
  have hd : Integrable (fun x : ℝ =>
      (64 * rho ^ 6) * (|x| ^ (2 * 3) * Real.exp (lambda * x ^ 2))) μ :=
    h3.const_mul _
  have hab : Integrable (fun x : ℝ =>
      (120 * rho ^ 3) * (|x| ^ (2 * 0) * Real.exp (lambda * x ^ 2)) +
      (720 * rho ^ 4) * (|x| ^ (2 * 1) * Real.exp (lambda * x ^ 2))) μ :=
    ha.add hb
  have hcd : Integrable (fun x : ℝ =>
      (480 * rho ^ 5) * (|x| ^ (2 * 2) * Real.exp (lambda * x ^ 2)) +
      (64 * rho ^ 6) * (|x| ^ (2 * 3) * Real.exp (lambda * x ^ 2))) μ :=
    hc.add hd
  rw [integral_add hab hcd, integral_add ha hb, integral_add hc hd]
  simp only [integral_const_mul]
  calc
    _ ≤ (120 * rho ^ 3) * gaussianHalfTiltedEvenMomentMajorant 0 lambda +
        (720 * rho ^ 4) * gaussianHalfTiltedEvenMomentMajorant 1 lambda +
        (480 * rho ^ 5) * gaussianHalfTiltedEvenMomentMajorant 2 lambda +
        (64 * rho ^ 6) * gaussianHalfTiltedEvenMomentMajorant 3 lambda := by
      have hle0 := mul_le_mul_of_nonneg_left (h.integral_le 0)
        (by positivity : 0 ≤ 120 * rho ^ 3)
      have hle1 := mul_le_mul_of_nonneg_left (h.integral_le 1)
        (by positivity : 0 ≤ 720 * rho ^ 4)
      have hle2 := mul_le_mul_of_nonneg_left (h.integral_le 2)
        (by positivity : 0 ≤ 480 * rho ^ 5)
      have hle3 := mul_le_mul_of_nonneg_left (h.integral_le 3)
        (by positivity : 0 ≤ 64 * rho ^ 6)
      linarith
    _ = _ := by
      norm_num [gaussianHalfTiltedEvenMomentMajorant]
      ring

/-- The sixth derivative expectation is bounded by the exact `D₆` formula
whenever the law supplies the Gaussian-half tilted even-moment bounds. -/
theorem integral_norm_iteratedDeriv_six_complexQuadraticExp_le
    {μ : Measure ℝ} (s : ℂ)
    (h : QuadraticExpEvenMomentBound μ s.re) :
    (∫ x : ℝ, ‖iteratedDeriv 6 (complexQuadraticExp s) x‖ ∂μ) ≤
      quadraticExpDerivativeMajorant 6 ‖s‖ s.re := by
  have hmajor := integrable_pointwiseMajorant_six (rho := ‖s‖) h
  have hpointwise : ∀ x : ℝ,
      ‖iteratedDeriv 6 (complexQuadraticExp s) x‖ ≤
        quadraticExpDerivativePointwiseMajorant 6 ‖s‖ s.re x :=
    norm_iteratedDeriv_six_complexQuadraticExp_le s
  have hnorm : Integrable
      (fun x : ℝ => ‖iteratedDeriv 6 (complexQuadraticExp s) x‖) μ := by
    refine Integrable.mono' hmajor ?_ ?_
    · have hcont : Continuous
          (fun x : ℝ => ‖iteratedDeriv 6 (complexQuadraticExp s) x‖) := by
        have hfun :
            (fun x : ℝ => ‖iteratedDeriv 6 (complexQuadraticExp s) x‖) =
              fun x : ℝ => ‖(120 * s ^ 3 + 720 * s ^ 4 * (x : ℂ) ^ 2 +
                480 * s ^ 5 * (x : ℂ) ^ 4 + 64 * s ^ 6 * (x : ℂ) ^ 6) *
                  complexQuadraticExp s x‖ := by
          funext x
          rw [iteratedDeriv_six_complexQuadraticExp]
        rw [hfun]
        simp only [complexQuadraticExp]
        fun_prop
      exact hcont.aestronglyMeasurable
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hpointwise x
  exact (integral_mono hnorm hmajor hpointwise).trans
    (integral_pointwiseMajorant_six_le h (norm_nonneg s))

private theorem pointwiseMajorant_eight_fun_eq (rho lambda : ℝ) :
    (fun x : ℝ => quadraticExpDerivativePointwiseMajorant 8 rho lambda x) =
      (fun x : ℝ =>
        (((1680 * rho ^ 4) * (|x| ^ (2 * 0) * Real.exp (lambda * x ^ 2)) +
          (13440 * rho ^ 5) * (|x| ^ (2 * 1) * Real.exp (lambda * x ^ 2))) +
        ((13440 * rho ^ 6) * (|x| ^ (2 * 2) * Real.exp (lambda * x ^ 2)) +
          (3584 * rho ^ 7) * (|x| ^ (2 * 3) * Real.exp (lambda * x ^ 2)))) +
        (256 * rho ^ 8) * (|x| ^ (2 * 4) * Real.exp (lambda * x ^ 2))) := by
  funext x
  rw [quadraticExpDerivativePointwiseMajorant_eight]
  norm_num
  ring

private theorem integrable_pointwiseMajorant_eight
    {μ : Measure ℝ} {lambda rho : ℝ}
    (h : QuadraticExpEvenMomentBound μ lambda) :
    Integrable
      (fun x : ℝ => quadraticExpDerivativePointwiseMajorant 8 rho lambda x) μ := by
  rw [pointwiseMajorant_eight_fun_eq]
  exact
    ((((h.integrable 0).const_mul (1680 * rho ^ 4)).add
      ((h.integrable 1).const_mul (13440 * rho ^ 5))).add
      (((h.integrable 2).const_mul (13440 * rho ^ 6)).add
        ((h.integrable 3).const_mul (3584 * rho ^ 7)))).add
      ((h.integrable 4).const_mul (256 * rho ^ 8))

private theorem integral_pointwiseMajorant_eight_le
    {μ : Measure ℝ} {lambda rho : ℝ}
    (h : QuadraticExpEvenMomentBound μ lambda) (hrho : 0 ≤ rho) :
    (∫ x : ℝ, quadraticExpDerivativePointwiseMajorant 8 rho lambda x ∂μ) ≤
      quadraticExpDerivativeMajorant 8 rho lambda := by
  have h0 := h.integrable 0
  have h1 := h.integrable 1
  have h2 := h.integrable 2
  have h3 := h.integrable 3
  have h4 := h.integrable 4
  rw [quadraticExpDerivativeMajorant_eight]
  rw [pointwiseMajorant_eight_fun_eq]
  have ha : Integrable (fun x : ℝ =>
      (1680 * rho ^ 4) * (|x| ^ (2 * 0) * Real.exp (lambda * x ^ 2))) μ :=
    h0.const_mul _
  have hb : Integrable (fun x : ℝ =>
      (13440 * rho ^ 5) * (|x| ^ (2 * 1) * Real.exp (lambda * x ^ 2))) μ :=
    h1.const_mul _
  have hc : Integrable (fun x : ℝ =>
      (13440 * rho ^ 6) * (|x| ^ (2 * 2) * Real.exp (lambda * x ^ 2))) μ :=
    h2.const_mul _
  have hd : Integrable (fun x : ℝ =>
      (3584 * rho ^ 7) * (|x| ^ (2 * 3) * Real.exp (lambda * x ^ 2))) μ :=
    h3.const_mul _
  have he : Integrable (fun x : ℝ =>
      (256 * rho ^ 8) * (|x| ^ (2 * 4) * Real.exp (lambda * x ^ 2))) μ :=
    h4.const_mul _
  have hab : Integrable (fun x : ℝ =>
      (1680 * rho ^ 4) * (|x| ^ (2 * 0) * Real.exp (lambda * x ^ 2)) +
      (13440 * rho ^ 5) * (|x| ^ (2 * 1) * Real.exp (lambda * x ^ 2))) μ :=
    ha.add hb
  have hcd : Integrable (fun x : ℝ =>
      (13440 * rho ^ 6) * (|x| ^ (2 * 2) * Real.exp (lambda * x ^ 2)) +
      (3584 * rho ^ 7) * (|x| ^ (2 * 3) * Real.exp (lambda * x ^ 2))) μ :=
    hc.add hd
  have habcd : Integrable (fun x : ℝ =>
      ((1680 * rho ^ 4) * (|x| ^ (2 * 0) * Real.exp (lambda * x ^ 2)) +
        (13440 * rho ^ 5) * (|x| ^ (2 * 1) * Real.exp (lambda * x ^ 2))) +
      ((13440 * rho ^ 6) * (|x| ^ (2 * 2) * Real.exp (lambda * x ^ 2)) +
        (3584 * rho ^ 7) * (|x| ^ (2 * 3) * Real.exp (lambda * x ^ 2)))) μ :=
    hab.add hcd
  rw [integral_add habcd he, integral_add hab hcd,
    integral_add ha hb, integral_add hc hd]
  simp only [integral_const_mul]
  calc
    _ ≤ (1680 * rho ^ 4) * gaussianHalfTiltedEvenMomentMajorant 0 lambda +
        (13440 * rho ^ 5) * gaussianHalfTiltedEvenMomentMajorant 1 lambda +
        (13440 * rho ^ 6) * gaussianHalfTiltedEvenMomentMajorant 2 lambda +
        (3584 * rho ^ 7) * gaussianHalfTiltedEvenMomentMajorant 3 lambda +
        (256 * rho ^ 8) * gaussianHalfTiltedEvenMomentMajorant 4 lambda := by
      have hle0 := mul_le_mul_of_nonneg_left (h.integral_le 0)
        (by positivity : 0 ≤ 1680 * rho ^ 4)
      have hle1 := mul_le_mul_of_nonneg_left (h.integral_le 1)
        (by positivity : 0 ≤ 13440 * rho ^ 5)
      have hle2 := mul_le_mul_of_nonneg_left (h.integral_le 2)
        (by positivity : 0 ≤ 13440 * rho ^ 6)
      have hle3 := mul_le_mul_of_nonneg_left (h.integral_le 3)
        (by positivity : 0 ≤ 3584 * rho ^ 7)
      have hle4 := mul_le_mul_of_nonneg_left (h.integral_le 4)
        (by positivity : 0 ≤ 256 * rho ^ 8)
      linarith
    _ = _ := by
      norm_num [gaussianHalfTiltedEvenMomentMajorant]
      ring

/-- The eighth derivative expectation is bounded by the exact `D₈` formula
whenever the law supplies the Gaussian-half tilted even-moment bounds. -/
theorem integral_norm_iteratedDeriv_eight_complexQuadraticExp_le
    {μ : Measure ℝ} (s : ℂ)
    (h : QuadraticExpEvenMomentBound μ s.re) :
    (∫ x : ℝ, ‖iteratedDeriv 8 (complexQuadraticExp s) x‖ ∂μ) ≤
      quadraticExpDerivativeMajorant 8 ‖s‖ s.re := by
  have hmajor := integrable_pointwiseMajorant_eight (rho := ‖s‖) h
  have hpointwise : ∀ x : ℝ,
      ‖iteratedDeriv 8 (complexQuadraticExp s) x‖ ≤
        quadraticExpDerivativePointwiseMajorant 8 ‖s‖ s.re x :=
    norm_iteratedDeriv_eight_complexQuadraticExp_le s
  have hnorm : Integrable
      (fun x : ℝ => ‖iteratedDeriv 8 (complexQuadraticExp s) x‖) μ := by
    refine Integrable.mono' hmajor ?_ ?_
    · have hcont : Continuous
          (fun x : ℝ => ‖iteratedDeriv 8 (complexQuadraticExp s) x‖) := by
        have hfun :
            (fun x : ℝ => ‖iteratedDeriv 8 (complexQuadraticExp s) x‖) =
              fun x : ℝ => ‖(1680 * s ^ 4 + 13440 * s ^ 5 * (x : ℂ) ^ 2 +
                13440 * s ^ 6 * (x : ℂ) ^ 4 + 3584 * s ^ 7 * (x : ℂ) ^ 6 +
                256 * s ^ 8 * (x : ℂ) ^ 8) * complexQuadraticExp s x‖ := by
          funext x
          rw [iteratedDeriv_eight_complexQuadraticExp]
        rw [hfun]
        simp only [complexQuadraticExp]
        fun_prop
      exact hcont.aestronglyMeasurable
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hpointwise x
  exact (integral_mono hnorm hmajor hpointwise).trans
    (integral_pointwiseMajorant_eight_le h (norm_nonneg s))

end CertifiedJL
