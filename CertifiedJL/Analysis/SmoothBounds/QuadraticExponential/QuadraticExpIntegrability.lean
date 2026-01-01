/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpDerivative
import CertifiedJL.Analysis.Peano.PeanoMoments
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# Integrability boundary for the quadratic exponential

This module records the first noncompact analytic consumer of the exact
quadratic-exponential derivative.  The Gaussian density supplies the negative
quadratic term, so the condition is `Re(s) < 1/(2v)` for variance `v`; no
cutoff or dominated-convergence conclusion is asserted here.
-/

open MeasureTheory
open scoped NNReal

namespace CertifiedJL

open ProbabilityTheory

/-- The strict negative-real-part volume envelope used before a Gaussian
   density is introduced. -/
theorem integrable_complexQuadraticExp_volume {s : ℂ} (hs : s.re < 0) :
    Integrable (fun x : ℝ => complexQuadraticExp s x) := by
  simpa [complexQuadraticExp, Complex.ofReal_pow] using
    (integrable_cexp_quadratic' (b := s) hs 0 0)

/-- The exact Gaussian-density boundary for nonzero variance. -/
theorem integrable_gaussianPDFReal_mul_complexQuadraticExp
    {s : ℂ} {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hs : s.re < 1 / (2 * (v : ℝ))) :
    Integrable (fun x : ℝ =>
      (gaussianPDFReal μ v x : ℂ) * complexQuadraticExp s x) := by
  have hvposNN : 0 < v := pos_iff_ne_zero.mpr hv
  have hvpos : 0 < (v : ℝ) := by exact_mod_cast hvposNN
  have hfrac : (1 / (2 * (v : ℂ)) : ℂ) =
      ((1 / (2 * (v : ℝ)) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [Complex.normSq_ofReal]
  have hbre : (1 / (2 * (v : ℂ)) - s).re =
      1 / (2 * (v : ℝ)) - s.re := by
    rw [Complex.sub_re, hfrac]
    simp
  have hb : 0 < (1 / (2 * (v : ℂ)) - s).re := by
    rw [hbre]
    exact sub_pos.mpr hs
  have hquad := integrable_cexp_quadratic
    (b := (1 / (2 * (v : ℂ)) - s)) hb
    ((μ : ℂ) / (v : ℂ)) (-(μ : ℂ) ^ 2 / (2 * (v : ℂ)))
  have hscaled := hquad.const_mul
    ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ : ℂ)
  refine hscaled.congr (Filter.Eventually.of_forall ?_)
  intro x
  simp only [gaussianPDFReal, complexQuadraticExp]
  simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_inv]
  conv_rhs => rw [mul_assoc]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring_nf

/-- The corresponding Bochner-integrability statement for `gaussianReal`. -/
theorem integrable_gaussianReal_complexQuadraticExp
    {s : ℂ} {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hs : s.re < 1 / (2 * (v : ℝ))) :
    Integrable (fun x : ℝ => complexQuadraticExp s x) (gaussianReal μ v) := by
  rw [gaussianReal_of_var_ne_zero μ hv]
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF μ v)
    (Filter.Eventually.of_forall fun x => gaussianPDF_lt_top)]
  simpa [toReal_gaussianPDF, Complex.real_smul] using
    (integrable_gaussianPDFReal_mul_complexQuadraticExp (s := s) (μ := μ) (v := v)
      hv hs)

private theorem integrable_real_exp_mul_sq_gaussianReal
    {t : ℝ} {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (ht : t < 1 / (2 * (v : ℝ))) :
    Integrable (fun x : ℝ => Real.exp (t * x ^ 2)) (gaussianReal μ v) := by
  have h := integrable_gaussianReal_complexQuadraticExp
    (s := (t : ℂ)) (μ := μ) (v := v) hv (by simpa using ht)
  have hr := h.re
  convert hr using 1
  funext x
  change Real.exp (t * x ^ 2) =
    (Complex.exp ((t : ℂ) * (x : ℂ) ^ 2)).re
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.exp_ofReal_re]

theorem complexQuadraticExp_add_expand (s : ℂ) (x y : ℝ) :
    complexQuadraticExp s (x + y) =
      Complex.exp (s * (y : ℂ) ^ 2 + (2 * s * (x : ℂ)) * (y : ℂ) +
        s * (x : ℂ) ^ 2) := by
  simp only [complexQuadraticExp]
  congr 1
  push_cast
  ring

theorem integrable_gaussianReal_shifted_complexQuadraticExp
    {s : ℂ} {μ x : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hs : s.re < 1 / (2 * (v : ℝ))) :
    Integrable (fun y : ℝ => complexQuadraticExp s (x + y))
      (gaussianReal μ v) := by
  have hbase : Integrable (fun z : ℝ => complexQuadraticExp s z)
      (Measure.map (fun y : ℝ => y + x) (gaussianReal μ v)) := by
    rw [gaussianReal_map_add_const]
    exact integrable_gaussianReal_complexQuadraticExp (μ := μ + x) (v := v) hv hs
  have hcomp := hbase.comp_measurable (by fun_prop : Measurable (fun y : ℝ => y + x))
  convert hcomp using 1
  funext y
  simp [add_comm]

private lemma integrable_gaussianReal_pow {μ : ℝ} {v : ℝ≥0} (k : ℕ) :
    Integrable (fun y : ℝ => y ^ k) (gaussianReal μ v) := by
  simpa only [id_eq] using
    (integrable_pow_of_mem_interior_integrableExpSet
      (X := id) (μ := gaussianReal μ v)
      (by simp) k)

theorem integrable_gaussianReal_taylorPolynomial3
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {μ : ℝ} {v : ℝ≥0}
    (f : ℝ → E) (x : ℝ) :
    Integrable (fun y : ℝ => taylorPolynomial3 f x y) (gaussianReal μ v) := by
  have h0 := integrable_gaussianReal_pow (μ := μ) (v := v) 0
  have h1 := integrable_gaussianReal_pow (μ := μ) (v := v) 1
  have h2 := integrable_gaussianReal_pow (μ := μ) (v := v) 2
  have h3 := integrable_gaussianReal_pow (μ := μ) (v := v) 3
  have h0' := h0.smul_const (f x)
  have h1' := h1.smul_const (deriv f x)
  have h2' := (h2.div_const 2).smul_const (deriv (deriv f) x)
  have h3' := (h3.div_const 6).smul_const (deriv (deriv (deriv f)) x)
  refine (((h0'.add h1').add h2').add h3').congr
    (Filter.Eventually.of_forall (fun y => ?_))
  simp [taylorPolynomial3]

theorem integrable_gaussianReal_shifted_complexQuadraticExp_remainder
    {s : ℂ} {μ x : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hs : s.re < 1 / (2 * (v : ℝ))) :
    Integrable
      (fun y : ℝ => complexQuadraticExp s (x + y) -
        taylorPolynomial3 (complexQuadraticExp s) x y)
      (gaussianReal μ v) := by
  exact (integrable_gaussianReal_shifted_complexQuadraticExp (μ := μ) (x := x)
    (v := v) hv hs).sub (integrable_gaussianReal_taylorPolynomial3
      (μ := μ) (v := v) (complexQuadraticExp s) x)

theorem integrable_gaussianReal_evenPow_mul_complexQuadraticExp
    {s : ℂ} {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hs : s.re < 1 / (2 * (v : ℝ))) (n : ℕ) :
    Integrable (fun x : ℝ => (x : ℂ) ^ (2 * n) * complexQuadraticExp s x)
      (gaussianReal μ v) := by
  let δ : ℝ := (1 / (2 * (v : ℝ)) - s.re) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  have hplus : s.re + δ < 1 / (2 * (v : ℝ)) := by
    dsimp [δ]
    linarith
  have hminus : s.re - δ < 1 / (2 * (v : ℝ)) := by
    dsimp [δ]
    linarith
  have hpow : Integrable
      (fun x : ℝ => (x ^ 2) ^ n * Real.exp (s.re * x ^ 2))
      (gaussianReal μ v) := by
    have h := integrable_pow_mul_exp_of_integrable_exp_mul
      (μ := gaussianReal μ v) (X := fun x : ℝ => x ^ 2)
      (v := s.re) (t := δ) hδ.ne'
      (by simpa [add_comm] using
        integrable_real_exp_mul_sq_gaussianReal (μ := μ) (v := v) hv hplus)
      (by simpa [sub_eq_add_neg] using
        integrable_real_exp_mul_sq_gaussianReal (μ := μ) (v := v) hv hminus)
      n
    simpa using h
  refine Integrable.mono'
    (f := fun x : ℝ => (x : ℂ) ^ (2 * n) * complexQuadraticExp s x)
    (g := fun x : ℝ => (x ^ 2) ^ n * Real.exp (s.re * x ^ 2))
    hpow ?_ ?_
  · apply Measurable.aestronglyMeasurable
    change Measurable (fun x : ℝ =>
      (x : ℂ) ^ (2 * n) * Complex.exp (s * (x : ℂ) ^ 2))
    fun_prop
  filter_upwards [] with x
  have hexp : (s * (x : ℂ) ^ 2).re = s.re * x ^ 2 := by
    have hxpow : ((x : ℂ) ^ 2).re = x ^ 2 := by
      norm_num [pow_two, Complex.mul_re]
    have hxpow_im : ((x : ℂ) ^ 2).im = 0 := by
      norm_num [pow_two, Complex.mul_im]
    rw [Complex.mul_re, hxpow, hxpow_im]
    ring
  have hpow_abs : ‖x‖ ^ (2 * n) = (x ^ 2) ^ n := by
    rw [Real.norm_eq_abs, pow_mul, sq_abs]
  change ‖(x : ℂ) ^ (2 * n) * Complex.exp (s * (x : ℂ) ^ 2)‖ ≤
    (x ^ 2) ^ n * Real.exp (s.re * x ^ 2)
  rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_exp, hexp, hpow_abs]

theorem integrable_gaussianReal_shifted_evenPow_mul_complexQuadraticExp
    {s : ℂ} {μ x : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hs : s.re < 1 / (2 * (v : ℝ))) (n : ℕ) :
    Integrable
      (fun y : ℝ => ((x + y : ℝ) : ℂ) ^ (2 * n) *
        complexQuadraticExp s (x + y))
      (gaussianReal μ v) := by
  have hbase : Integrable
      (fun z : ℝ => (z : ℂ) ^ (2 * n) * complexQuadraticExp s z)
      (Measure.map (fun y : ℝ => y + x) (gaussianReal μ v)) := by
    rw [gaussianReal_map_add_const]
    exact integrable_gaussianReal_evenPow_mul_complexQuadraticExp
      (μ := μ + x) (v := v) hv hs n
  have hcomp := hbase.comp_measurable
    (by fun_prop : Measurable (fun y : ℝ => y + x))
  convert hcomp using 1
  funext y
  simp [add_comm]

theorem integrable_gaussianReal_shifted_iteratedDeriv_four_complexQuadraticExp
    {s : ℂ} {μ x : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hs : s.re < 1 / (2 * (v : ℝ))) :
    Integrable
      (fun y : ℝ => iteratedDeriv 4 (complexQuadraticExp s) (x + y))
      (gaussianReal μ v) := by
  have h0 := integrable_gaussianReal_shifted_evenPow_mul_complexQuadraticExp
    (μ := μ) (x := x) (v := v) hv hs 0
  have h2 := integrable_gaussianReal_shifted_evenPow_mul_complexQuadraticExp
    (μ := μ) (x := x) (v := v) hv hs 1
  have h4 := integrable_gaussianReal_shifted_evenPow_mul_complexQuadraticExp
    (μ := μ) (x := x) (v := v) hv hs 2
  have h0' : Integrable
      (fun y : ℝ => (12 * s ^ 2) * complexQuadraticExp s (x + y))
      (gaussianReal μ v) := by
    simpa using h0.const_mul (12 * s ^ 2)
  have h2' : Integrable
      (fun y : ℝ => (48 * s ^ 3) *
        (((x + y : ℝ) : ℂ) ^ 2 * complexQuadraticExp s (x + y)))
      (gaussianReal μ v) := by
    exact h2.const_mul (48 * s ^ 3)
  have h4' : Integrable
      (fun y : ℝ => (16 * s ^ 4) *
        (((x + y : ℝ) : ℂ) ^ 4 * complexQuadraticExp s (x + y)))
      (gaussianReal μ v) := by
    exact h4.const_mul (16 * s ^ 4)
  refine (h0'.add (h2'.add h4')).congr
    (Filter.Eventually.of_forall (fun y => ?_))
  change
    12 * s ^ 2 * complexQuadraticExp s (x + y) +
        (48 * s ^ 3 * (((x + y : ℝ) : ℂ) ^ 2 *
          complexQuadraticExp s (x + y)) +
          16 * s ^ 4 * (((x + y : ℝ) : ℂ) ^ 4 *
            complexQuadraticExp s (x + y))) =
      iteratedDeriv 4 (complexQuadraticExp s) (x + y)
  rw [iteratedDeriv_four_complexQuadraticExp]
  simp only [complexQuadraticExpFourthPolynomialComplex]
  ring

end CertifiedJL
