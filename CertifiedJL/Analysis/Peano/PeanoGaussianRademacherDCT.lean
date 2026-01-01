/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import CertifiedJL.Analysis.Peano.PeanoGaussianRademacher
import CertifiedJL.Analysis.Peano.PeanoCutoffKernelData
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# Weighted noncompact Gaussian--Rademacher Peano boundary

This module contains the concrete weighted integrability and dominated-
convergence bridge for the Gaussian-versus-Rademacher cubic kernel.  The
first exported boundary is deliberately strict (`Re(s) < 0`): it is already
an actual noncompact complex consumer, while the later variance-scaled U3b
domain remains a separate obligation.
-/

open MeasureTheory Set Filter
open ProbabilityTheory
open scoped Topology

namespace CertifiedJL

private theorem integrable_volume_shifted_exp_sq
    {v x : ℝ} (hv : v < 0) :
    Integrable (fun t : ℝ => Real.exp (v * (x + t) ^ 2)) volume := by
  have hbase0 := integrable_exp_neg_mul_sq (b := -v) (by linarith)
  have hbase : Integrable (fun z : ℝ => Real.exp (v * z ^ 2)) volume := by
    convert hbase0 using 1
    ext z
    congr 1
    ring
  have hshift :=
    (measurePreserving_add_left (volume : Measure ℝ) x).integrable_comp_of_integrable
      hbase
  simpa [Function.comp_def] using hshift

private theorem volume_shifted_square_re_exp_mem_interior
    {s : ℂ} {x : ℝ} (hs : s.re < 0) :
    s.re ∈ interior (integrableExpSet (fun t : ℝ => (x + t) ^ 2) volume) := by
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset]
  let δ : ℝ := -s.re / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  refine ⟨s.re - δ, s.re + δ, ?_, ?_⟩
  · constructor <;> linarith
  · intro v hv
    rw [mem_Ioo] at hv
    rcases hv with ⟨hvL, hvU⟩
    have hvneg : v < 0 := by
      dsimp [δ] at hvL hvU ⊢
      linarith
    change Integrable (fun t : ℝ => Real.exp (v * (x + t) ^ 2)) volume
    exact integrable_volume_shifted_exp_sq (x := x) hvneg

/-- Every even polynomial weight remains integrable against the negative-real
    quadratic exponential on Lebesgue measure, after an arbitrary real shift. -/
theorem integrable_volume_shifted_abs_evenPow_mul_complexQuadraticExp
    {s : ℂ} {x : ℝ} (hs : s.re < 0) (n : ℕ) :
    Integrable
      (fun t : ℝ => ((|x + t| ^ (2 * n) : ℝ) : ℂ) *
        complexQuadraticExp s (x + t)) volume := by
  have hinterior := volume_shifted_square_re_exp_mem_interior (x := x) hs
  have h :=
    integrable_pow_abs_mul_cexp_of_re_mem_interior_integrableExpSet
      (X := fun t : ℝ => (x + t) ^ 2) (μ := volume) (z := s) hinterior n
  refine h.congr (Filter.Eventually.of_forall (fun t => ?_))
  simp only [complexQuadraticExp, Complex.ofReal_pow]
  simp only [abs_of_nonneg (sq_nonneg (x + t))]
  congr 1
  norm_cast
  rw [← sq_abs, pow_mul]

/-- Arbitrary polynomial weights are reduced to an even-power envelope. -/
theorem integrable_volume_shifted_absPow_mul_complexQuadraticExp
    {s : ℂ} {x : ℝ} (hs : s.re < 0) (m : ℕ) :
    Integrable
      (fun t : ℝ => ((|x + t| ^ m : ℝ) : ℂ) *
        complexQuadraticExp s (x + t)) volume := by
  have h0 := integrable_volume_shifted_abs_evenPow_mul_complexQuadraticExp
    (x := x) hs 0
  have h2m := integrable_volume_shifted_abs_evenPow_mul_complexQuadraticExp
    (x := x) hs m
  have hmajor : Integrable
      (fun t : ℝ => (1 + |x + t| ^ (2 * m)) *
        Real.exp (s.re * (x + t) ^ 2)) volume := by
    refine (h0.norm.add h2m.norm).congr
      (Filter.Eventually.of_forall (fun t => ?_))
    simp only [Pi.add_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      complexQuadraticExp, Complex.norm_exp]
    have hexp :
        (s * ((x + t : ℝ) : ℂ) ^ 2).re = s.re * (x + t) ^ 2 := by
      have hxpow : (((x + t : ℝ) : ℂ) ^ 2).re = (x + t) ^ 2 := by
        norm_num [pow_two, Complex.mul_re]
      have hxpow_im : (((x + t : ℝ) : ℂ) ^ 2).im = 0 := by
        norm_num [pow_two, Complex.mul_im]
      rw [Complex.mul_re, hxpow, hxpow_im]
      ring
    rw [abs_of_nonneg (pow_nonneg (abs_nonneg (x + t)) (2 * m)), hexp]
    norm_num
    ring_nf
  refine Integrable.mono'
    (f := fun t : ℝ => ((|x + t| ^ m : ℝ) : ℂ) *
      complexQuadraticExp s (x + t))
    (g := fun t : ℝ => (1 + |x + t| ^ (2 * m)) *
      Real.exp (s.re * (x + t) ^ 2)) hmajor ?_ ?_
  · have hcont : Continuous
        (fun t : ℝ => ((|x + t| ^ m : ℝ) : ℂ) *
          complexQuadraticExp s (x + t)) := by
      apply Continuous.mul
      · fun_prop
      · exact (contDiff_complexQuadraticExp s).continuous.comp
          (continuous_const.add continuous_id)
    exact hcont.aestronglyMeasurable
  filter_upwards [] with t
  have hpow : |x + t| ^ m ≤ 1 + |x + t| ^ (2 * m) := by
    by_cases hle : |x + t| ≤ 1
    · have hm : |x + t| ^ m ≤ 1 := pow_le_one₀ (abs_nonneg _) hle
      exact hm.trans (by
        linarith [pow_nonneg (abs_nonneg (x + t)) (2 * m)])
    · have hone : 1 ≤ |x + t| := le_of_not_ge hle
      have hmn : m ≤ 2 * m := by omega
      exact (pow_le_pow_right₀ hone hmn).trans (by
        linarith [pow_nonneg (abs_nonneg (x + t)) (2 * m)])
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    complexQuadraticExp, Complex.norm_exp]
  have hexp :
      (s * ((x + t : ℝ) : ℂ) ^ 2).re = s.re * (x + t) ^ 2 := by
    have hxpow : (((x + t : ℝ) : ℂ) ^ 2).re = (x + t) ^ 2 := by
      norm_num [pow_two, Complex.mul_re]
    have hxpow_im : (((x + t : ℝ) : ℂ) ^ 2).im = 0 := by
      norm_num [pow_two, Complex.mul_im]
    rw [Complex.mul_re, hxpow, hxpow_im]
    ring
  rw [abs_of_nonneg (pow_nonneg (abs_nonneg (x + t)) m), hexp]
  exact mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le

private theorem integrable_volume_shifted_absPow_mul_realExp
    {s : ℂ} {x : ℝ} (hs : s.re < 0) (m : ℕ) :
    Integrable
      (fun t : ℝ => |x + t| ^ m * Real.exp (s.re * (x + t) ^ 2)) volume := by
  have h := integrable_volume_shifted_absPow_mul_complexQuadraticExp
    (x := x) hs m
  refine h.norm.congr (Filter.Eventually.of_forall (fun t => ?_))
  simp only [norm_mul, Real.norm_eq_abs, Complex.norm_real,
    complexQuadraticExp, Complex.norm_exp]
  have hexp :
      (s * ((x + t : ℝ) : ℂ) ^ 2).re = s.re * (x + t) ^ 2 := by
    have hxpow : (((x + t : ℝ) : ℂ) ^ 2).re = (x + t) ^ 2 := by
      norm_num [pow_two, Complex.mul_re]
    have hxpow_im : (((x + t : ℝ) : ℂ) ^ 2).im = 0 := by
      norm_num [pow_two, Complex.mul_im]
    rw [Complex.mul_re, hxpow, hxpow_im]
    ring
  rw [abs_of_nonneg (pow_nonneg (abs_nonneg (x + t)) m), hexp]

private theorem integrable_volume_shifted_one_add_abs_cubic_mul_absPow_realExp
    {s : ℂ} {x : ℝ} (hs : s.re < 0) (m : ℕ) :
    Integrable
      (fun t : ℝ => (1 + |x + t|) ^ 3 * |x + t| ^ m *
        Real.exp (s.re * (x + t) ^ 2)) volume := by
  have h0 := integrable_volume_shifted_absPow_mul_realExp
    (x := x) hs m
  have h1 := integrable_volume_shifted_absPow_mul_realExp
    (x := x) hs (m + 1)
  have h2 := integrable_volume_shifted_absPow_mul_realExp
    (x := x) hs (m + 2)
  have h3 := integrable_volume_shifted_absPow_mul_realExp
    (x := x) hs (m + 3)
  have hsum := h0.add ((h1.const_mul 3).add
    ((h2.const_mul 3).add h3))
  refine hsum.congr (Filter.Eventually.of_forall (fun t => ?_))
  simp only [Pi.add_apply]
  ring

private theorem
    integrable_volume_shifted_one_add_abs_cubic_mul_norm_monomial_complexQuadraticExp
    {s a : ℂ} {x : ℝ} (hs : s.re < 0) (m : ℕ) :
    Integrable
      (fun t : ℝ => (1 + |x + t|) ^ 3 *
        ‖a * ((x + t : ℝ) : ℂ) ^ m * complexQuadraticExp s (x + t)‖) volume := by
  have h := (integrable_volume_shifted_one_add_abs_cubic_mul_absPow_realExp
    (x := x) hs m).const_mul ‖a‖
  refine h.congr (Filter.Eventually.of_forall (fun t => ?_))
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    complexQuadraticExp, Complex.norm_exp]
  have hexp :
      (s * ((x + t : ℝ) : ℂ) ^ 2).re = s.re * (x + t) ^ 2 := by
    have hxpow : (((x + t : ℝ) : ℂ) ^ 2).re = (x + t) ^ 2 := by
      norm_num [pow_two, Complex.mul_re]
    have hxpow_im : (((x + t : ℝ) : ℂ) ^ 2).im = 0 := by
      norm_num [pow_two, Complex.mul_im]
    rw [Complex.mul_re, hxpow, hxpow_im]
    ring
  rw [hexp]
  ring

private theorem integrable_volume_shifted_one_add_abs_cubic_mul_iteratedDeriv_zero_norm
    {s : ℂ} {x : ℝ} (hs : s.re < 0) :
    Integrable
      (fun t : ℝ => (1 + |x + t|) ^ 3 *
        ‖iteratedDeriv 0 (complexQuadraticExp s) (x + t)‖) volume := by
  simpa [iteratedDeriv_zero] using
    (integrable_volume_shifted_one_add_abs_cubic_mul_norm_monomial_complexQuadraticExp
      (s := s) (a := 1) (x := x) hs 0)

private theorem integrable_volume_shifted_one_add_abs_cubic_mul_iteratedDeriv_one_norm
    {s : ℂ} {x : ℝ} (hs : s.re < 0) :
    Integrable
      (fun t : ℝ => (1 + |x + t|) ^ 3 *
        ‖iteratedDeriv 1 (complexQuadraticExp s) (x + t)‖) volume := by
  simpa [iteratedDeriv_one_complexQuadraticExp, mul_assoc] using
    (integrable_volume_shifted_one_add_abs_cubic_mul_norm_monomial_complexQuadraticExp
      (s := s) (a := 2 * s) (x := x) hs 1)

private theorem integrable_volume_shifted_one_add_abs_cubic_mul_iteratedDeriv_two_norm
    {s : ℂ} {x : ℝ} (hs : s.re < 0) :
    Integrable
      (fun t : ℝ => (1 + |x + t|) ^ 3 *
        ‖iteratedDeriv 2 (complexQuadraticExp s) (x + t)‖) volume := by
  have h0 :=
    integrable_volume_shifted_one_add_abs_cubic_mul_norm_monomial_complexQuadraticExp
      (s := s) (a := 2 * s) (x := x) hs 0
  have h2 :=
    integrable_volume_shifted_one_add_abs_cubic_mul_norm_monomial_complexQuadraticExp
      (s := s) (a := 4 * s ^ 2) (x := x) hs 2
  refine Integrable.mono'
    (g := fun t : ℝ =>
      (1 + |x + t|) ^ 3 *
          ‖(2 * s) * ((x + t : ℝ) : ℂ) ^ 0 * complexQuadraticExp s (x + t)‖ +
        (1 + |x + t|) ^ 3 *
          ‖(4 * s ^ 2) * ((x + t : ℝ) : ℂ) ^ 2 *
            complexQuadraticExp s (x + t)‖)
    (h0.add h2) (by
      have hD : Continuous (fun t : ℝ =>
          iteratedDeriv 2 (complexQuadraticExp s) (x + t)) :=
        (((contDiff_complexQuadraticExp s).of_le (by norm_num)).continuous_iteratedDeriv' 2).comp
          (continuous_const.add continuous_id)
      exact (by fun_prop : Continuous (fun t : ℝ => (1 + |x + t|) ^ 3))
        |>.mul hD.norm |>.aestronglyMeasurable) ?_
  filter_upwards [] with t
  rw [iteratedDeriv_two_complexQuadraticExp]
  simp only [pow_zero, mul_one]
  calc
    ‖(1 + |x + t|) ^ 3 *
        ‖(2 * s + 4 * s ^ 2 * ((x + t : ℝ) : ℂ) ^ 2) *
          complexQuadraticExp s (x + t)‖‖ =
        (1 + |x + t|) ^ 3 *
          ‖(2 * s + 4 * s ^ 2 * ((x + t : ℝ) : ℂ) ^ 2) *
            complexQuadraticExp s (x + t)‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ (1 + |x + t|) ^ 3 *
          (‖(2 * s) * complexQuadraticExp s (x + t)‖ +
            ‖(4 * s ^ 2) * ((x + t : ℝ) : ℂ) ^ 2 *
              complexQuadraticExp s (x + t)‖) := by
      gcongr
      rw [add_mul]
      exact norm_add_le _ _
    _ = (1 + |x + t|) ^ 3 *
          ‖(2 * s) * complexQuadraticExp s (x + t)‖ +
        (1 + |x + t|) ^ 3 *
          ‖(4 * s ^ 2) * ((x + t : ℝ) : ℂ) ^ 2 *
            complexQuadraticExp s (x + t)‖ := by ring

private theorem integrable_volume_shifted_one_add_abs_cubic_mul_iteratedDeriv_three_norm
    {s : ℂ} {x : ℝ} (hs : s.re < 0) :
    Integrable
      (fun t : ℝ => (1 + |x + t|) ^ 3 *
        ‖iteratedDeriv 3 (complexQuadraticExp s) (x + t)‖) volume := by
  have h1 :=
    integrable_volume_shifted_one_add_abs_cubic_mul_norm_monomial_complexQuadraticExp
      (s := s) (a := 12 * s ^ 2) (x := x) hs 1
  have h3 :=
    integrable_volume_shifted_one_add_abs_cubic_mul_norm_monomial_complexQuadraticExp
      (s := s) (a := 8 * s ^ 3) (x := x) hs 3
  have hsum : Integrable (fun t : ℝ =>
      (1 + |x + t|) ^ 3 *
          ‖(12 * s ^ 2) * ((x + t : ℝ) : ℂ) * complexQuadraticExp s (x + t)‖ +
        (1 + |x + t|) ^ 3 *
          ‖(8 * s ^ 3) * ((x + t : ℝ) : ℂ) ^ 3 *
            complexQuadraticExp s (x + t)‖) := by
    refine (h1.add h3).congr (Filter.Eventually.of_forall (fun t => ?_))
    simp only [Pi.add_apply, pow_one]
  refine Integrable.mono'
    (g := fun t : ℝ =>
      (1 + |x + t|) ^ 3 *
          ‖(12 * s ^ 2) * ((x + t : ℝ) : ℂ) * complexQuadraticExp s (x + t)‖ +
        (1 + |x + t|) ^ 3 *
          ‖(8 * s ^ 3) * ((x + t : ℝ) : ℂ) ^ 3 *
            complexQuadraticExp s (x + t)‖)
    hsum (by
      have hD : Continuous (fun t : ℝ =>
          iteratedDeriv 3 (complexQuadraticExp s) (x + t)) :=
        (((contDiff_complexQuadraticExp s).of_le (by norm_num)).continuous_iteratedDeriv' 3).comp
          (continuous_const.add continuous_id)
      exact (by fun_prop : Continuous (fun t : ℝ => (1 + |x + t|) ^ 3))
        |>.mul hD.norm |>.aestronglyMeasurable) ?_
  filter_upwards [] with t
  rw [iteratedDeriv_three_complexQuadraticExp]
  calc
    ‖(1 + |x + t|) ^ 3 *
        ‖(12 * s ^ 2 * ((x + t : ℝ) : ℂ) +
          8 * s ^ 3 * ((x + t : ℝ) : ℂ) ^ 3) *
            complexQuadraticExp s (x + t)‖‖ =
        (1 + |x + t|) ^ 3 *
          ‖(12 * s ^ 2 * ((x + t : ℝ) : ℂ) +
            8 * s ^ 3 * ((x + t : ℝ) : ℂ) ^ 3) *
              complexQuadraticExp s (x + t)‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ (1 + |x + t|) ^ 3 *
          (‖(12 * s ^ 2) * ((x + t : ℝ) : ℂ) *
              complexQuadraticExp s (x + t)‖ +
            ‖(8 * s ^ 3) * ((x + t : ℝ) : ℂ) ^ 3 *
              complexQuadraticExp s (x + t)‖) := by
      gcongr
      rw [add_mul]
      exact norm_add_le _ _
    _ = (1 + |x + t|) ^ 3 *
          ‖(12 * s ^ 2) * ((x + t : ℝ) : ℂ) *
            complexQuadraticExp s (x + t)‖ +
        (1 + |x + t|) ^ 3 *
          ‖(8 * s ^ 3) * ((x + t : ℝ) : ℂ) ^ 3 *
            complexQuadraticExp s (x + t)‖ := by ring

/-- The exact fourth derivative is integrable on the volume side of the
    stop-loss integral in the strict negative-real-part domain. -/
theorem integrable_volume_shifted_iteratedDeriv_four_complexQuadraticExp
    {s : ℂ} {x : ℝ} (hs : s.re < 0) :
    Integrable
      (fun t : ℝ => iteratedDeriv 4 (complexQuadraticExp s) (x + t)) volume := by
  have h0 := integrable_volume_shifted_abs_evenPow_mul_complexQuadraticExp
    (x := x) hs 0
  have h2 := integrable_volume_shifted_abs_evenPow_mul_complexQuadraticExp
    (x := x) hs 1
  have h4 := integrable_volume_shifted_abs_evenPow_mul_complexQuadraticExp
    (x := x) hs 2
  have h0' : Integrable
      (fun t : ℝ => (12 * s ^ 2) * complexQuadraticExp s (x + t)) volume := by
    simpa using h0.const_mul (12 * s ^ 2)
  have h2' : Integrable
      (fun t : ℝ => (48 * s ^ 3) *
        (((x + t : ℝ) : ℂ) ^ 2 * complexQuadraticExp s (x + t))) volume := by
    refine (h2.const_mul (48 * s ^ 3)).congr
      (Filter.Eventually.of_forall (fun t => ?_))
    simp only [Complex.ofReal_pow]
    congr 2
    norm_num [← Complex.ofReal_pow, sq_abs]
    push_cast
    ring
  have h4' : Integrable
      (fun t : ℝ => (16 * s ^ 4) *
        (((x + t : ℝ) : ℂ) ^ 4 * complexQuadraticExp s (x + t))) volume := by
    refine (h4.const_mul (16 * s ^ 4)).congr
      (Filter.Eventually.of_forall (fun t => ?_))
    simp only [Complex.ofReal_pow]
    congr 2
    norm_num [← Complex.ofReal_pow]
    have hreal : |x + t| ^ 4 = (x + t) ^ 4 := by
      calc
        |x + t| ^ 4 = (|x + t| ^ 2) ^ 2 := by
          rw [← pow_mul]
        _ = ((x + t) ^ 2) ^ 2 := by rw [sq_abs]
        _ = (x + t) ^ 4 := by ring
    rw [hreal, Complex.ofReal_pow]
    push_cast
    ring
  refine (h0'.add (h2'.add h4')).congr
    (Filter.Eventually.of_forall (fun t => ?_))
  change
    12 * s ^ 2 * complexQuadraticExp s (x + t) +
        (48 * s ^ 3 * (((x + t : ℝ) : ℂ) ^ 2 *
          complexQuadraticExp s (x + t)) +
          16 * s ^ 4 * (((x + t : ℝ) : ℂ) ^ 4 *
            complexQuadraticExp s (x + t))) =
      iteratedDeriv 4 (complexQuadraticExp s) (x + t)
  rw [iteratedDeriv_four_complexQuadraticExp]
  simp only [complexQuadraticExpFourthPolynomialComplex]
  ring

private theorem cubicStopLossDifference_abs_le
    {μ ν : Measure ℝ} {t : ℝ}
    (hμstop : Integrable (fun y : ℝ => (max (y - t) 0) ^ 3) μ)
    (hνstop : Integrable (fun y : ℝ => (max (y - t) 0) ^ 3) ν)
    (hμenv : Integrable (fun y : ℝ => (1 + |y|) ^ 3) μ)
    (hνenv : Integrable (fun y : ℝ => (1 + |y|) ^ 3) ν) :
    |cubicStopLossDifference μ ν t| ≤
      ((∫ y, (1 + |y|) ^ 3 ∂μ) +
        ∫ y, (1 + |y|) ^ 3 ∂ν) * (1 + |t|) ^ 3 := by
  let A : ℝ := ∫ y, (max (y - t) 0) ^ 3 ∂μ
  let B : ℝ := ∫ y, (max (y - t) 0) ^ 3 ∂ν
  let Cμ : ℝ := ∫ y, (1 + |y|) ^ 3 ∂μ
  let Cν : ℝ := ∫ y, (1 + |y|) ^ 3 ∂ν
  have hA : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg_of_ae (ae_of_all μ (fun y => by positivity))
  have hB : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg_of_ae (ae_of_all ν (fun y => by positivity))
  have hCμ : 0 ≤ Cμ := by
    dsimp [Cμ]
    exact integral_nonneg_of_ae (ae_of_all μ (fun y => by positivity))
  have hCν : 0 ≤ Cν := by
    dsimp [Cν]
    exact integral_nonneg_of_ae (ae_of_all ν (fun y => by positivity))
  have hpoint (y : ℝ) :
      (max (y - t) 0) ^ 3 ≤
        (1 + |t|) ^ 3 * (1 + |y|) ^ 3 := by
    have hy : 0 ≤ |y| := abs_nonneg y
    have ht : 0 ≤ |t| := abs_nonneg t
    have hmax : max (y - t) 0 ≤ (1 + |t|) * (1 + |y|) := by
      apply max_le
      · nlinarith [le_abs_self y, neg_le_abs t]
      · positivity
    have hbase : 0 ≤ max (y - t) 0 := le_max_right _ _
    have hprod : 0 ≤ (1 + |t|) * (1 + |y|) := by positivity
    exact (pow_le_pow_left₀ hbase hmax 3).trans_eq (by ring_nf)
  have hμbound : A ≤ Cμ * (1 + |t|) ^ 3 := by
    dsimp [A, Cμ]
    have hscale : Integrable
        (fun y : ℝ => (1 + |t|) ^ 3 * (1 + |y|) ^ 3) μ :=
      hμenv.const_mul ((1 + |t|) ^ 3)
    have hmono := integral_mono_ae hμstop hscale
      (ae_of_all μ (fun y => hpoint y))
    simpa [integral_const_mul, mul_comm] using hmono
  have hνbound : B ≤ Cν * (1 + |t|) ^ 3 := by
    dsimp [B, Cν]
    have hscale : Integrable
        (fun y : ℝ => (1 + |t|) ^ 3 * (1 + |y|) ^ 3) ν :=
      hνenv.const_mul ((1 + |t|) ^ 3)
    have hmono := integral_mono_ae hνstop hscale
      (ae_of_all ν (fun y => hpoint y))
    simpa [integral_const_mul, mul_comm] using hmono
  have hsum : |A - B| ≤ (Cμ + Cν) * (1 + |t|) ^ 3 := by
    calc
      |A - B| ≤ |A| + |B| := by
        rw [abs_of_nonneg hA, abs_of_nonneg hB, abs_sub_le_iff]
        constructor <;> linarith
      _ = A + B := by rw [abs_of_nonneg hA, abs_of_nonneg hB]
      _ ≤ Cμ * (1 + |t|) ^ 3 + Cν * (1 + |t|) ^ 3 :=
        add_le_add hμbound hνbound
      _ = (Cμ + Cν) * (1 + |t|) ^ 3 := by ring
  simpa [cubicStopLossDifference, A, B, Cμ, Cν] using hsum

private theorem standardGaussianRademacher_cubicStopLoss_abs_le (t : ℝ) :
    |cubicStopLossDifference (gaussianReal 0 1)
      standardRademacherMeasure t| ≤
      ((∫ y, (1 + |y|) ^ 3 ∂(gaussianReal 0 1)) +
        ∫ y, (1 + |y|) ^ 3 ∂standardRademacherMeasure) * (1 + |t|) ^ 3 := by
  exact cubicStopLossDifference_abs_le
    (integrable_standardGaussian_cubicStopLoss t)
    (integrable_standardRademacher_cubicStopLoss t)
    (integrable_one_add_abs_cubic_of_pows
      (integrable_standardGaussian_pow 0)
      (integrable_standardGaussian_pow 1)
      (integrable_standardGaussian_pow 2)
      (integrable_standardGaussian_pow 3))
    (integrable_one_add_abs_cubic_of_pows
      (integrable_standardRademacher_pow 0)
      (integrable_standardRademacher_pow 1)
      (integrable_standardRademacher_pow 2)
      (integrable_standardRademacher_pow 3))

private theorem integrable_volume_shifted_one_add_abs_cubic_mul_fourthDeriv_norm
    {s : ℂ} {x : ℝ} (hs : s.re < 0) :
    Integrable
      (fun t : ℝ => (1 + |x + t|) ^ 3 *
        ‖iteratedDeriv 4 (complexQuadraticExp s) (x + t)‖) volume := by
  have h0 := integrable_volume_shifted_one_add_abs_cubic_mul_absPow_realExp
    (x := x) hs 0
  have h1 := integrable_volume_shifted_one_add_abs_cubic_mul_absPow_realExp
    (x := x) hs 2
  have h2 := integrable_volume_shifted_one_add_abs_cubic_mul_absPow_realExp
    (x := x) hs 4
  have h0' := h0.const_mul ‖(12 * s ^ 2 : ℂ)‖
  have h1' := h1.const_mul ‖(48 * s ^ 3 : ℂ)‖
  have h2' := h2.const_mul ‖(16 * s ^ 4 : ℂ)‖
  let A : ℝ → ℝ := fun t =>
    ‖(12 : ℂ)‖ * ‖s ^ 2‖ *
      ((1 + |x + t|) ^ 3 * |x + t| ^ 0 *
        Real.exp (s.re * (x + t) ^ 2))
  let B : ℝ → ℝ := fun t =>
    ‖(48 : ℂ)‖ * ‖s ^ 3‖ *
      ((1 + |x + t|) ^ 3 * |x + t| ^ 2 *
        Real.exp (s.re * (x + t) ^ 2))
  let D : ℝ → ℝ := fun t =>
    ‖(16 : ℂ)‖ * ‖s ^ 4‖ *
      ((1 + |x + t|) ^ 3 * |x + t| ^ 4 *
        Real.exp (s.re * (x + t) ^ 2))
  have h0A : Integrable A volume := by simpa [A, norm_mul] using h0'
  have h1B : Integrable B volume := by simpa [B, norm_mul] using h1'
  have h2D : Integrable D volume := by simpa [D, norm_mul] using h2'
  have hmajor : Integrable (A + (B + D)) volume :=
    h0A.add (h1B.add h2D)
  refine Integrable.mono'
    (f := fun t : ℝ => (1 + |x + t|) ^ 3 *
      ‖iteratedDeriv 4 (complexQuadraticExp s) (x + t)‖)
    (g := A + (B + D)) hmajor ?_ ?_
  · have hcontF : Continuous
        (fun t : ℝ => iteratedDeriv 4 (complexQuadraticExp s) (x + t)) :=
      (contDiff_complexQuadraticExp s).continuous_iteratedDeriv' 4 |>.comp
        (continuous_const.add continuous_id)
    have hcont : Continuous (fun t : ℝ => (1 + |x + t|) ^ 3 *
        ‖iteratedDeriv 4 (complexQuadraticExp s) (x + t)‖) := by
      fun_prop
    exact hcont.aestronglyMeasurable
  filter_upwards [] with t
  simp only [Pi.add_apply]
  dsimp [A, B, D]
  have hP :
      ‖complexQuadraticExpFourthPolynomialComplex s ((x + t : ℝ) : ℂ)‖ ≤
        ‖(12 * s ^ 2 : ℂ)‖ +
          ‖(48 * s ^ 3 : ℂ)‖ * |x + t| ^ 2 +
          ‖(16 * s ^ 4 : ℂ)‖ * |x + t| ^ 4 := by
    unfold complexQuadraticExpFourthPolynomialComplex
    calc
      ‖12 * s ^ 2 + 48 * s ^ 3 * ((x + t : ℝ) : ℂ) ^ 2 +
          16 * s ^ 4 * ((x + t : ℝ) : ℂ) ^ 4‖ ≤
          ‖12 * s ^ 2 + 48 * s ^ 3 * ((x + t : ℝ) : ℂ) ^ 2‖ +
            ‖16 * s ^ 4 * ((x + t : ℝ) : ℂ) ^ 4‖ := norm_add_le _ _
      _ ≤ (‖(12 * s ^ 2 : ℂ)‖ +
            ‖48 * s ^ 3 * ((x + t : ℝ) : ℂ) ^ 2‖) +
            ‖16 * s ^ 4 * ((x + t : ℝ) : ℂ) ^ 4‖ := by
        exact add_le_add_left (norm_add_le _ _) _
      _ = ‖(12 * s ^ 2 : ℂ)‖ +
          ‖(48 * s ^ 3 : ℂ)‖ * |x + t| ^ 2 +
        ‖(16 * s ^ 4 : ℂ)‖ * |x + t| ^ 4 := by
        simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  rw [iteratedDeriv_four_complexQuadraticExp]
  rw [norm_mul]
  rw [abs_of_nonneg (mul_nonneg (by positivity :
    0 ≤ (1 + |x + t|) ^ 3)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)))]
  calc
    (1 + |x + t|) ^ 3 *
        (‖complexQuadraticExpFourthPolynomialComplex s ((x + t : ℝ) : ℂ)‖ *
          ‖complexQuadraticExp s (x + t)‖) ≤
      (1 + |x + t|) ^ 3 *
        ((‖(12 * s ^ 2 : ℂ)‖ +
          ‖(48 * s ^ 3 : ℂ)‖ * |x + t| ^ 2 +
          ‖(16 * s ^ 4 : ℂ)‖ * |x + t| ^ 4) *
          ‖complexQuadraticExp s (x + t)‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hP (norm_nonneg _)) (by positivity)
    _ = ‖(12 : ℂ)‖ * ‖s ^ 2‖ *
          ((1 + |x + t|) ^ 3 * |x + t| ^ 0 *
            Real.exp (s.re * (x + t) ^ 2)) +
        (‖(48 : ℂ)‖ * ‖s ^ 3‖ *
          ((1 + |x + t|) ^ 3 * |x + t| ^ 2 *
            Real.exp (s.re * (x + t) ^ 2)) +
          ‖(16 : ℂ)‖ * ‖s ^ 4‖ *
            ((1 + |x + t|) ^ 3 * |x + t| ^ 4 *
              Real.exp (s.re * (x + t) ^ 2))) := by
      simp only [complexQuadraticExp, Complex.norm_exp]
      have hexp :
          (s * ((x + t : ℝ) : ℂ) ^ 2).re = s.re * (x + t) ^ 2 := by
        have hxpow : (((x + t : ℝ) : ℂ) ^ 2).re = (x + t) ^ 2 := by
          norm_num [pow_two, Complex.mul_re]
        have hxpow_im : (((x + t : ℝ) : ℂ) ^ 2).im = 0 := by
          norm_num [pow_two, Complex.mul_im]
        rw [Complex.mul_re, hxpow, hxpow_im]
        ring
      rw [hexp]
      norm_num [pow_two]
      ring

private theorem integral_Ioi_cubic_exp_neg_half {b : ℝ} (hb : 0 ≤ b) :
    (∫ y : ℝ in Set.Ioi b, y ^ 3 * Real.exp (-(1 / 2 : ℝ) * y ^ 2)) =
      (b ^ 2 + 2) * Real.exp (-(1 / 2 : ℝ) * b ^ 2) := by
  let F : ℝ → ℝ := fun y => -(y ^ 2 + 2) *
    Real.exp (-(1 / 2 : ℝ) * y ^ 2)
  have hderiv : ∀ y ∈ Set.Ici b,
      HasDerivAt F (y ^ 3 * Real.exp (-(1 / 2 : ℝ) * y ^ 2)) y := by
    intro y _
    have hpoly : HasDerivAt (fun z : ℝ => -(z ^ 2 + 2)) (-2 * y) y := by
      simpa [neg_add, id_eq] using
        (((hasDerivAt_id y).pow 2).neg.add_const (-2 : ℝ))
    have hexp : HasDerivAt
        (fun z : ℝ => Real.exp (-(1 / 2 : ℝ) * z ^ 2))
        (-y * Real.exp (-(1 / 2 : ℝ) * y ^ 2)) y := by
      simpa [id_eq, mul_comm, mul_left_comm, mul_assoc] using
        (((((hasDerivAt_id y).pow 2).const_mul (-(1 / 2 : ℝ))).exp))
    have h := hpoly.mul hexp
    have hfun :
        ((fun z : ℝ => -(z ^ 2 + 2)) *
          (fun z : ℝ => Real.exp (-(1 / 2 : ℝ) * z ^ 2))) =ᶠ[𝓝 y] F := by
      filter_upwards [] with z
      rfl
    exact (h.congr_of_eventuallyEq hfun).congr_deriv (by ring)
  have hglobal : Integrable
      (fun y : ℝ => |y| ^ 3 * Real.exp (-(1 / 2 : ℝ) * y ^ 2)) volume := by
    simpa using
      (integrable_volume_shifted_absPow_mul_realExp
        (s := (-(1 / 2 : ℝ) : ℂ)) (x := 0) (by norm_num) 3)
  have hint : IntegrableOn
      (fun y : ℝ => y ^ 3 * Real.exp (-(1 / 2 : ℝ) * y ^ 2)) (Set.Ioi b) := by
    refine hglobal.integrableOn.congr_fun ?_ measurableSet_Ioi
    intro y hy
    change |y| ^ 3 * Real.exp (-(1 / 2 : ℝ) * y ^ 2) =
      y ^ 3 * Real.exp (-(1 / 2 : ℝ) * y ^ 2)
    rw [abs_of_nonneg (hb.trans (Set.mem_Ioi.mp hy).le)]
  have hlimExp : Tendsto
      (fun y : ℝ => Real.exp (-(1 / 2 : ℝ) * y ^ 2)) atTop (𝓝 0) := by
    have hquad : Tendsto
        (fun y : ℝ => (1 / 2 : ℝ) * y ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop
        (by norm_num)
    apply (Real.tendsto_exp_neg_atTop_nhds_zero.comp hquad).congr'
    filter_upwards [] with y
    simp only [Function.comp_apply]
    congr 1
    ring
  have hlimPow : Tendsto
      (fun y : ℝ => y ^ 2 * Real.exp (-(1 / 2 : ℝ) * y ^ 2)) atTop (𝓝 0) := by
    have hquad : Tendsto
        (fun y : ℝ => (1 / 2 : ℝ) * y ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop
        (by norm_num)
    have hbase : Tendsto
        (fun y : ℝ => (1 / 2 : ℝ) * y ^ 2 *
          Real.exp (-(1 / 2 : ℝ) * y ^ 2)) atTop (𝓝 0) := by
      have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hquad
      apply h.congr'
      filter_upwards [] with y
      simp only [Function.comp_apply, pow_one]
      ring_nf
    have hscaled := hbase.const_mul 2
    have hscaled' : Tendsto
        (fun y : ℝ => 2 * ((1 / 2 : ℝ) * y ^ 2 *
          Real.exp (-(1 / 2 : ℝ) * y ^ 2))) atTop (𝓝 0) := by
      simpa using hscaled
    apply hscaled'.congr'
    filter_upwards [] with y
    ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    have htwo : Tendsto
      (fun y : ℝ => (2 : ℝ) * Real.exp (-(1 / 2 : ℝ) * y ^ 2)) atTop (𝓝 0) :=
      by simpa using hlimExp.const_mul 2
    have hsum := hlimPow.add htwo
    have hneg := hsum.neg
    simpa [F, mul_add, add_mul, neg_mul, mul_comm, mul_left_comm, mul_assoc] using hneg
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    hderiv hint hlim
  calc
    (∫ y : ℝ in Set.Ioi b, y ^ 3 * Real.exp (-(1 / 2 : ℝ) * y ^ 2)) =
        -F b := by simpa using h
    _ = (b ^ 2 + 2) * Real.exp (-(1 / 2 : ℝ) * b ^ 2) := by
      dsimp [F]
      ring

private theorem integral_Ioi_cube_standardGaussian {b : ℝ} (hb : 0 ≤ b) :
    (∫ y : ℝ in Set.Ioi b, y ^ 3 ∂(gaussianReal 0 1)) =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        ((b ^ 2 + 2) * Real.exp (-(1 / 2 : ℝ) * b ^ 2)) := by
  rw [← integral_indicator measurableSet_Ioi]
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  calc
    (∫ y : ℝ,
        gaussianPDFReal 0 1 y • Set.indicator (Set.Ioi b) (fun z : ℝ => z ^ 3) y) =
        (Real.sqrt (2 * Real.pi))⁻¹ *
          ∫ y : ℝ in Set.Ioi b,
            y ^ 3 * Real.exp (-(1 / 2 : ℝ) * y ^ 2) := by
      rw [← integral_const_mul]
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hy : y ∈ Set.Ioi b
      · simp only [Set.indicator_of_mem hy, smul_eq_mul, gaussianPDFReal,
          NNReal.coe_one, sub_zero]
        ring_nf
      · simp only [Set.indicator_of_notMem hy, smul_zero]
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
        ((b ^ 2 + 2) * Real.exp (-(1 / 2 : ℝ) * b ^ 2)) := by
      rw [integral_Ioi_cubic_exp_neg_half hb]

/-- On the strict upper branch, the concrete Gaussian-minus-Rademacher
cubic stop-loss has an explicit normalized Gaussian envelope. -/
theorem abs_cubicStopLossDifference_standardGaussian_rademacher_le_of_one_le
    {t : ℝ} (ht : 1 ≤ t) :
    |cubicStopLossDifference (gaussianReal 0 1)
        standardRademacherMeasure t| ≤
      (Real.sqrt (2 * Real.pi))⁻¹ *
        ((t ^ 2 + 2) * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) := by
  rw [cubicStopLossDifference_standardGaussian_rademacher_of_one_le ht]
  have hnonneg :
      0 ≤ ∫ y : ℝ in Set.Ioi t, (y - t) ^ 3 ∂(gaussianReal 0 1) := by
    exact setIntegral_nonneg measurableSet_Ioi (fun y hy => by
      have hyt : 0 ≤ y - t := sub_nonneg.mpr (Set.mem_Ioi.mp hy).le
      positivity)
  rw [abs_of_nonneg hnonneg]
  have hf : IntegrableOn (fun y : ℝ => (y - t) ^ 3)
      (Set.Ioi t) (gaussianReal 0 1) := by
    refine (integrable_standardGaussian_cubicStopLoss t).integrableOn.congr_fun
      ?_ measurableSet_Ioi
    intro y hy
    change (max (y - t) 0) ^ 3 = (y - t) ^ 3
    rw [max_eq_left (sub_nonneg.mpr (Set.mem_Ioi.mp hy).le)]
  have hg : IntegrableOn (fun y : ℝ => y ^ 3)
      (Set.Ioi t) (gaussianReal 0 1) :=
    (integrable_standardGaussian_pow 3).integrableOn
  calc
    (∫ y : ℝ in Set.Ioi t, (y - t) ^ 3 ∂(gaussianReal 0 1)) ≤
        ∫ y : ℝ in Set.Ioi t, y ^ 3 ∂(gaussianReal 0 1) := by
      apply setIntegral_mono_on hf hg measurableSet_Ioi
      intro y hy
      have hyt : 0 ≤ y - t := sub_nonneg.mpr (Set.mem_Ioi.mp hy).le
      have hy0 : 0 ≤ y := by linarith [Set.mem_Ioi.mp hy]
      exact pow_le_pow_left₀ hyt (by linarith) 3
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
        ((t ^ 2 + 2) * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) :=
      integral_Ioi_cube_standardGaussian (by linarith)

private theorem integral_Iio_neg_cube_standardGaussian {b : ℝ} (hb : b ≤ 0) :
    (∫ y : ℝ in Set.Iio b, (-y) ^ 3 ∂(gaussianReal 0 1)) =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        ((b ^ 2 + 2) * Real.exp (-(1 / 2 : ℝ) * b ^ 2)) := by
  have hreflect :
      (∫ y : ℝ in Set.Iio b,
          (-y) ^ 3 * Real.exp (-(1 / 2 : ℝ) * y ^ 2)) =
        ∫ y : ℝ in Set.Ioi (-b),
          y ^ 3 * Real.exp (-(1 / 2 : ℝ) * y ^ 2) := by
    let F : ℝ → ℝ := fun y =>
      (-y) ^ 3 * Real.exp (-(1 / 2 : ℝ) * y ^ 2)
    have hraw :
        (∫ y : ℝ in Set.Iic b, F y) =
          ∫ y : ℝ in Set.Ioi (-b), F (-y) := by
      simpa only [neg_neg] using
        (integral_comp_neg_Ioi (-b) F).symm
    calc
      (∫ y : ℝ in Set.Iio b,
          (-y) ^ 3 * Real.exp (-(1 / 2 : ℝ) * y ^ 2)) =
          ∫ y : ℝ in Set.Iic b, F y := by
        simp only [F]
        rw [integral_Iic_eq_integral_Iio]
      _ = ∫ y : ℝ in Set.Ioi (-b), F (-y) := hraw
      _ = ∫ y : ℝ in Set.Ioi (-b),
          y ^ 3 * Real.exp (-(1 / 2 : ℝ) * y ^ 2) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y _
        dsimp [F]
        ring_nf
  rw [← integral_indicator measurableSet_Iio]
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  calc
    (∫ y : ℝ,
        gaussianPDFReal 0 1 y • Set.indicator (Set.Iio b)
          (fun z : ℝ => (-z) ^ 3) y) =
        (Real.sqrt (2 * Real.pi))⁻¹ *
          ∫ y : ℝ in Set.Iio b,
            (-y) ^ 3 * Real.exp (-(1 / 2 : ℝ) * y ^ 2) := by
      rw [← integral_const_mul]
      rw [← integral_indicator measurableSet_Iio]
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hy : y ∈ Set.Iio b
      · simp only [Set.indicator_of_mem hy, smul_eq_mul, gaussianPDFReal,
          NNReal.coe_one, sub_zero]
        ring_nf
      · simp only [Set.indicator_of_notMem hy, smul_zero]
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
        ((b ^ 2 + 2) * Real.exp (-(1 / 2 : ℝ) * b ^ 2)) := by
      rw [hreflect, integral_Ioi_cubic_exp_neg_half (by linarith)]
      congr 2 <;> ring_nf

/-- On the strict lower branch, moment cancellation leaves a reflected
Gaussian tail with the same explicit envelope as the upper branch. -/
theorem abs_cubicStopLossDifference_standardGaussian_rademacher_le_of_le_neg_one
    {t : ℝ} (ht : t ≤ -1) :
    |cubicStopLossDifference (gaussianReal 0 1)
        standardRademacherMeasure t| ≤
      (Real.sqrt (2 * Real.pi))⁻¹ *
        ((t ^ 2 + 2) * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) := by
  rw [cubicStopLossDifference_standardGaussian_rademacher_of_le_neg_one ht]
  have hnonneg :
      0 ≤ ∫ y : ℝ in Set.Iio t, (t - y) ^ 3 ∂(gaussianReal 0 1) := by
    exact setIntegral_nonneg measurableSet_Iio (fun y hy => by
      have hyt : 0 ≤ t - y := sub_nonneg.mpr (Set.mem_Iio.mp hy).le
      positivity)
  rw [abs_of_nonneg hnonneg]
  have h0 := integrable_standardGaussian_pow 0
  have h1 := integrable_standardGaussian_pow 1
  have h2 := integrable_standardGaussian_pow 2
  have h3 := integrable_standardGaussian_pow 3
  have hfGlobal : Integrable (fun y : ℝ => (t - y) ^ 3)
      (gaussianReal 0 1) := by
    have hpoly := (h0.const_mul (t ^ 3)).add
      ((h1.const_mul (-3 * t ^ 2)).add
        ((h2.const_mul (3 * t)).add (h3.const_mul (-1))))
    refine hpoly.congr (Filter.Eventually.of_forall (fun y => ?_))
    simp only [Pi.add_apply]
    ring
  have hgGlobal : Integrable (fun y : ℝ => (-y) ^ 3)
      (gaussianReal 0 1) := by
    refine (h3.const_mul (-1)).congr
      (Filter.Eventually.of_forall (fun y => ?_))
    ring
  calc
    (∫ y : ℝ in Set.Iio t, (t - y) ^ 3 ∂(gaussianReal 0 1)) ≤
        ∫ y : ℝ in Set.Iio t, (-y) ^ 3 ∂(gaussianReal 0 1) := by
      apply setIntegral_mono_on hfGlobal.integrableOn hgGlobal.integrableOn
        measurableSet_Iio
      intro y hy
      have hty : 0 ≤ t - y := sub_nonneg.mpr (Set.mem_Iio.mp hy).le
      have hnegY : 0 ≤ -y := by linarith [Set.mem_Iio.mp hy]
      exact pow_le_pow_left₀ hty (by linarith) 3
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
        ((t ^ 2 + 2) * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) :=
      integral_Iio_neg_cube_standardGaussian (by linarith)

/-- A uniform bound on the compact middle branch of the concrete cubic
stop-loss difference.  The factor `8` is the endpoint value of
`(1 + |t|)^3` on `[-1, 1]`. -/
theorem abs_cubicStopLossDifference_standardGaussian_rademacher_le_of_abs_lt_one
    {t : ℝ} (ht : |t| < 1) :
    |cubicStopLossDifference (gaussianReal 0 1)
        standardRademacherMeasure t| ≤
      8 * ((∫ y, (1 + |y|) ^ 3 ∂(gaussianReal 0 1)) +
        ∫ y, (1 + |y|) ^ 3 ∂standardRademacherMeasure) := by
  have h := standardGaussianRademacher_cubicStopLoss_abs_le t
  have hC : 0 ≤
      (∫ y, (1 + |y|) ^ 3 ∂(gaussianReal 0 1)) +
        ∫ y, (1 + |y|) ^ 3 ∂standardRademacherMeasure := by
    apply add_nonneg
    · exact integral_nonneg_of_ae (ae_of_all _ (fun y => by positivity))
    · exact integral_nonneg_of_ae (ae_of_all _ (fun y => by positivity))
  have ht' : (1 + |t|) ^ 3 ≤ 8 := by
    calc
      (1 + |t|) ^ 3 ≤ (2 : ℝ) ^ 3 := by
        exact pow_le_pow_left₀ (by positivity) (by linarith) 3
      _ = 8 := by norm_num
  calc
    |cubicStopLossDifference (gaussianReal 0 1)
        standardRademacherMeasure t| ≤
        ((∫ y, (1 + |y|) ^ 3 ∂(gaussianReal 0 1)) +
          ∫ y, (1 + |y|) ^ 3 ∂standardRademacherMeasure) *
            (1 + |t|) ^ 3 := h
    _ ≤ ((∫ y, (1 + |y|) ^ 3 ∂(gaussianReal 0 1)) +
          ∫ y, (1 + |y|) ^ 3 ∂standardRademacherMeasure) * 8 := by
      exact mul_le_mul_of_nonneg_left ht' hC
    _ = 8 * ((∫ y, (1 + |y|) ^ 3 ∂(gaussianReal 0 1)) +
        ∫ y, (1 + |y|) ^ 3 ∂standardRademacherMeasure) := by ring

/-- The compact-middle/Gaussian-tail envelope used for the noncompact
cutoff dominated-convergence argument. -/
noncomputable def standardGaussianRademacherCubicEnvelope (t : ℝ) : ℝ :=
  Set.indicator (Set.Ioo (-1 : ℝ) 1)
      (fun _ => 8 * ((∫ y, (1 + |y|) ^ 3 ∂(gaussianReal 0 1)) +
        ∫ y, (1 + |y|) ^ 3 ∂standardRademacherMeasure)) t +
    (Real.sqrt (2 * Real.pi))⁻¹ *
      ((t ^ 2 + 2) * Real.exp (-(1 / 2 : ℝ) * t ^ 2))

/-- The concrete cubic stop-loss difference is pointwise dominated by the
single envelope that combines the compact middle interval with both exact
Gaussian tails. -/
theorem abs_cubicStopLossDifference_standardGaussian_rademacher_le_envelope
    (t : ℝ) :
    |cubicStopLossDifference (gaussianReal 0 1)
        standardRademacherMeasure t| ≤
      standardGaussianRademacherCubicEnvelope t := by
  have htail_nonneg : 0 ≤
      (Real.sqrt (2 * Real.pi))⁻¹ *
        ((t ^ 2 + 2) * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) := by
    positivity
  by_cases hmiddle : |t| < 1
  · have hmem : t ∈ Set.Ioo (-1 : ℝ) 1 := by
      rw [abs_lt] at hmiddle
      exact hmiddle
    have hmiddleBound :=
      abs_cubicStopLossDifference_standardGaussian_rademacher_le_of_abs_lt_one
        hmiddle
    rw [standardGaussianRademacherCubicEnvelope,
      Set.indicator_of_mem hmem]
    exact hmiddleBound.trans (le_add_of_nonneg_right htail_nonneg)
  · have hbranches : t ≤ -1 ∨ 1 ≤ t := by
      rw [not_lt, le_abs] at hmiddle
      rcases hmiddle with ht | ht
      · exact Or.inr ht
      · exact Or.inl (by linarith)
    have hnotmem : t ∉ Set.Ioo (-1 : ℝ) 1 := by
      intro ht
      apply hmiddle
      rw [abs_lt]
      exact ht
    rw [standardGaussianRademacherCubicEnvelope,
      Set.indicator_of_notMem hnotmem, zero_add]
    rcases hbranches with ht | ht
    · exact
        abs_cubicStopLossDifference_standardGaussian_rademacher_le_of_le_neg_one ht
    · exact
        abs_cubicStopLossDifference_standardGaussian_rademacher_le_of_one_le ht

/-- The global compact-middle/Gaussian-tail envelope is pointwise
nonnegative. -/
theorem standardGaussianRademacherCubicEnvelope_nonneg (t : ℝ) :
    0 ≤ standardGaussianRademacherCubicEnvelope t := by
  have hC : 0 ≤ 8 *
      ((∫ y, (1 + |y|) ^ 3 ∂(gaussianReal 0 1)) +
        ∫ y, (1 + |y|) ^ 3 ∂standardRademacherMeasure) := by
    apply mul_nonneg (by norm_num)
    apply add_nonneg
    · exact integral_nonneg_of_ae (ae_of_all _ (fun y => by positivity))
    · exact integral_nonneg_of_ae (ae_of_all _ (fun y => by positivity))
  rw [standardGaussianRademacherCubicEnvelope]
  apply add_nonneg
  · by_cases ht : t ∈ Set.Ioo (-1 : ℝ) 1
    · simpa [Set.indicator_of_mem ht] using hC
    · simp [Set.indicator_of_notMem ht]
  · positivity

/-- Every polynomial moment of the global compact-middle/Gaussian-tail
envelope is Lebesgue integrable. -/
theorem integrable_absPow_mul_standardGaussianRademacherCubicEnvelope (m : ℕ) :
    Integrable
      (fun t : ℝ => |t| ^ m * standardGaussianRademacherCubicEnvelope t)
      volume := by
  let C : ℝ := 8 * ((∫ y, (1 + |y|) ^ 3 ∂(gaussianReal 0 1)) +
    ∫ y, (1 + |y|) ^ 3 ∂standardRademacherMeasure)
  let M : ℝ → ℝ := fun t =>
    Set.indicator (Set.Ioo (-1 : ℝ) 1) (fun z => C * |z| ^ m) t
  let T : ℝ → ℝ := fun t =>
    (Real.sqrt (2 * Real.pi))⁻¹ *
      (|t| ^ (m + 2) + 2 * |t| ^ m) *
        Real.exp (-(1 / 2 : ℝ) * t ^ 2)
  have hmiddleOn : IntegrableOn (fun t : ℝ => C * |t| ^ m)
      (Set.Ioo (-1 : ℝ) 1) volume := by
    have hIcc : IntegrableOn (fun t : ℝ => C * |t| ^ m)
        (Set.Icc (-1 : ℝ) 1) volume := by
      exact ContinuousOn.integrableOn_Icc (by fun_prop)
    exact hIcc.mono_set Set.Ioo_subset_Icc_self
  have hmiddle : Integrable M volume := by
    simpa [M] using hmiddleOn.integrable_indicator measurableSet_Ioo
  have hm := integrable_volume_shifted_absPow_mul_realExp
    (s := (-(1 / 2 : ℝ) : ℂ)) (x := 0) (by norm_num) m
  have hm2 := integrable_volume_shifted_absPow_mul_realExp
    (s := (-(1 / 2 : ℝ) : ℂ)) (x := 0) (by norm_num) (m + 2)
  have htail : Integrable T volume := by
    have hsum := hm2.add (hm.const_mul 2)
    have hscaled := hsum.const_mul (Real.sqrt (2 * Real.pi))⁻¹
    refine hscaled.congr (Filter.Eventually.of_forall (fun t => ?_))
    dsimp [T]
    simp only [zero_add]
    ring_nf
  have hsum := hmiddle.add htail
  refine hsum.congr (Filter.Eventually.of_forall (fun t => ?_))
  simp only [Pi.add_apply]
  dsimp [M, T, standardGaussianRademacherCubicEnvelope, C]
  by_cases ht : t ∈ Set.Ioo (-1 : ℝ) 1
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
    have habsSq : |t| ^ 2 = t ^ 2 := sq_abs t
    rw [show |t| ^ (m + 2) = |t| ^ m * t ^ 2 by
      rw [pow_add, habsSq]]
    ring
  · simp only [Set.indicator_of_notMem ht, zero_add]
    have habsSq : |t| ^ 2 = t ^ 2 := sq_abs t
    rw [show |t| ^ (m + 2) = |t| ^ m * t ^ 2 by
      rw [pow_add, habsSq]]
    ring

private theorem deriv_taylorPolynomial3_eq
    (f : ℝ → ℂ) (x : ℝ) :
    deriv (taylorPolynomial3 f x) = fun t : ℝ =>
      deriv f x + t • deriv (deriv f) x +
        (t ^ 2 / 2) • deriv (deriv (deriv f)) x := by
  funext t
  apply HasDerivAt.deriv
  have h0 := hasDerivAt_const t (f x)
  have h1 := (hasDerivAt_id t).smul_const (deriv f x)
  have h2 := (((hasDerivAt_id t).pow 2).div_const 2).smul_const
    (deriv (deriv f) x)
  have h3 := (((hasDerivAt_id t).pow 3).div_const 6).smul_const
    (deriv (deriv (deriv f)) x)
  have h := h0.add h1 |>.add h2 |>.add h3
  convert h using 1
  · ext z
    simp [taylorPolynomial3, id_eq]
  · simp only [id_eq]
    module

private theorem deriv_taylorPolynomial3_one_eq
    (f : ℝ → ℂ) (x : ℝ) :
    deriv (fun t : ℝ =>
      deriv f x + t • deriv (deriv f) x +
        (t ^ 2 / 2) • deriv (deriv (deriv f)) x) = fun t : ℝ =>
      deriv (deriv f) x + t • deriv (deriv (deriv f)) x := by
  funext t
  apply HasDerivAt.deriv
  have h0 := hasDerivAt_const t (deriv f x)
  have h1 := (hasDerivAt_id t).smul_const (deriv (deriv f) x)
  have h2 := (((hasDerivAt_id t).pow 2).div_const 2).smul_const
    (deriv (deriv (deriv f)) x)
  have h := h0.add h1 |>.add h2
  convert h using 1
  · ext z
    simp [id_eq]
  · simp only [id_eq]
    module

private theorem deriv_taylorPolynomial3_two_eq
    (f : ℝ → ℂ) (x : ℝ) :
    deriv (fun t : ℝ =>
      deriv (deriv f) x + t • deriv (deriv (deriv f)) x) = fun _ : ℝ =>
      deriv (deriv (deriv f)) x := by
  funext t
  apply HasDerivAt.deriv
  have h0 := hasDerivAt_const t (deriv (deriv f) x)
  have h1 := (hasDerivAt_id t).smul_const (deriv (deriv (deriv f)) x)
  have h := h0.add h1
  convert h using 1
  · ext z
    simp [id_eq]
  · simp

private theorem deriv_taylorPolynomial3_three_eq
    (f : ℝ → ℂ) (x : ℝ) :
    deriv (fun _ : ℝ => deriv (deriv (deriv f)) x) = fun _ : ℝ => 0 := by
  funext t
  exact hasDerivAt_const t (deriv (deriv (deriv f)) x) |>.deriv

private theorem iteratedDeriv_taylorPolynomial3_eq
    (f : ℝ → ℂ) (x : ℝ) (j : ℕ) (hj : j ≤ 4) :
    iteratedDeriv j (taylorPolynomial3 f x) =
      match j with
      | 0 => taylorPolynomial3 f x
      | 1 => fun t : ℝ =>
          deriv f x + t • deriv (deriv f) x +
            (t ^ 2 / 2) • deriv (deriv (deriv f)) x
      | 2 => fun t : ℝ =>
          deriv (deriv f) x + t • deriv (deriv (deriv f)) x
      | 3 => fun _ : ℝ => deriv (deriv (deriv f)) x
      | _ => fun _ : ℝ => 0 := by
  interval_cases j
  · rfl
  · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      deriv_taylorPolynomial3_eq f x
  · simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    rw [deriv_taylorPolynomial3_eq, deriv_taylorPolynomial3_one_eq]
  · simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    rw [deriv_taylorPolynomial3_eq, deriv_taylorPolynomial3_one_eq,
      deriv_taylorPolynomial3_two_eq]
  · simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    rw [deriv_taylorPolynomial3_eq, deriv_taylorPolynomial3_one_eq,
      deriv_taylorPolynomial3_two_eq, deriv_taylorPolynomial3_three_eq]

private theorem integrable_standardGaussianRademacherCubicEnvelope_mul_norm_cubic
    (a0 a1 a2 a3 : ℂ) :
    Integrable (fun t : ℝ => standardGaussianRademacherCubicEnvelope t *
      ‖a0 + t • a1 + t ^ 2 • a2 + t ^ 3 • a3‖) volume := by
  have h0 := (integrable_absPow_mul_standardGaussianRademacherCubicEnvelope 0).const_mul
    ‖a0‖
  have h1 := (integrable_absPow_mul_standardGaussianRademacherCubicEnvelope 1).const_mul
    ‖a1‖
  have h2 := (integrable_absPow_mul_standardGaussianRademacherCubicEnvelope 2).const_mul
    ‖a2‖
  have h3 := (integrable_absPow_mul_standardGaussianRademacherCubicEnvelope 3).const_mul
    ‖a3‖
  have hmajor := h0.add (h1.add (h2.add h3))
  have hmajor' : Integrable (fun t : ℝ =>
      ‖a0‖ * (|t| ^ 0 * standardGaussianRademacherCubicEnvelope t) +
        (‖a1‖ * (|t| ^ 1 * standardGaussianRademacherCubicEnvelope t) +
          (‖a2‖ * (|t| ^ 2 * standardGaussianRademacherCubicEnvelope t) +
            ‖a3‖ * (|t| ^ 3 * standardGaussianRademacherCubicEnvelope t)))) := by
    refine hmajor.congr (Filter.Eventually.of_forall (fun t => ?_))
    rfl
  refine Integrable.mono'
    (g := fun t : ℝ =>
      ‖a0‖ * (|t| ^ 0 * standardGaussianRademacherCubicEnvelope t) +
        (‖a1‖ * (|t| ^ 1 * standardGaussianRademacherCubicEnvelope t) +
          (‖a2‖ * (|t| ^ 2 * standardGaussianRademacherCubicEnvelope t) +
            ‖a3‖ * (|t| ^ 3 * standardGaussianRademacherCubicEnvelope t))))
    hmajor' ?_ ?_
  · have henv := integrable_absPow_mul_standardGaussianRademacherCubicEnvelope 0
    have henvAE : AEStronglyMeasurable standardGaussianRademacherCubicEnvelope volume := by
      simpa using henv.aestronglyMeasurable
    have hpoly : Continuous (fun t : ℝ =>
        ‖a0 + t • a1 + t ^ 2 • a2 + t ^ 3 • a3‖) := by
      fun_prop
    exact henvAE.mul hpoly.aestronglyMeasurable
  filter_upwards [] with t
  have hpoly :
      ‖a0 + t • a1 + t ^ 2 • a2 + t ^ 3 • a3‖ ≤
        ‖a0‖ + |t| * ‖a1‖ + |t| ^ 2 * ‖a2‖ + |t| ^ 3 * ‖a3‖ := by
    calc
      ‖a0 + t • a1 + t ^ 2 • a2 + t ^ 3 • a3‖ ≤
          ‖a0 + t • a1 + t ^ 2 • a2‖ + ‖t ^ 3 • a3‖ := norm_add_le _ _
      _ ≤ (‖a0 + t • a1‖ + ‖t ^ 2 • a2‖) + ‖t ^ 3 • a3‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ((‖a0‖ + ‖t • a1‖) + ‖t ^ 2 • a2‖) + ‖t ^ 3 • a3‖ := by
        gcongr
        exact norm_add_le _ _
      _ = ‖a0‖ + |t| * ‖a1‖ + |t| ^ 2 * ‖a2‖ + |t| ^ 3 * ‖a3‖ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_pow]
  have henv := standardGaussianRademacherCubicEnvelope_nonneg t
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg henv (norm_nonneg _))]
  calc
    standardGaussianRademacherCubicEnvelope t *
        ‖a0 + t • a1 + t ^ 2 • a2 + t ^ 3 • a3‖ ≤
      standardGaussianRademacherCubicEnvelope t *
        (‖a0‖ + |t| * ‖a1‖ + |t| ^ 2 * ‖a2‖ + |t| ^ 3 * ‖a3‖) :=
      mul_le_mul_of_nonneg_left hpoly henv
    _ = ‖a0‖ * (|t| ^ 0 * standardGaussianRademacherCubicEnvelope t) +
        (‖a1‖ * (|t| ^ 1 * standardGaussianRademacherCubicEnvelope t) +
          (‖a2‖ * (|t| ^ 2 * standardGaussianRademacherCubicEnvelope t) +
            ‖a3‖ * (|t| ^ 3 * standardGaussianRademacherCubicEnvelope t))) := by
      ring

private theorem
    integrable_standardGaussianRademacherCubicEnvelope_mul_norm_iteratedDeriv_taylor
    (f : ℝ → ℂ) (x : ℝ) (j : ℕ) (hj : j ≤ 4) :
    Integrable (fun t : ℝ => standardGaussianRademacherCubicEnvelope t *
      ‖iteratedDeriv j (taylorPolynomial3 f x) t‖) volume := by
  interval_cases j
  · have h := integrable_standardGaussianRademacherCubicEnvelope_mul_norm_cubic
      (f x) (deriv f x) ((2 : ℝ)⁻¹ • deriv (deriv f) x)
        ((6 : ℝ)⁻¹ • deriv (deriv (deriv f)) x)
    refine h.congr (Filter.Eventually.of_forall (fun t => ?_))
    rw [iteratedDeriv_taylorPolynomial3_eq f x 0 (by norm_num)]
    simp only [taylorPolynomial3, smul_smul, div_eq_mul_inv,
      pow_zero, one_smul, pow_one]
  · have h := integrable_standardGaussianRademacherCubicEnvelope_mul_norm_cubic
      (deriv f x) (deriv (deriv f) x)
        ((2 : ℝ)⁻¹ • deriv (deriv (deriv f)) x) 0
    refine h.congr (Filter.Eventually.of_forall (fun t => ?_))
    rw [iteratedDeriv_taylorPolynomial3_eq f x 1 (by norm_num)]
    simp only [smul_smul, div_eq_mul_inv, smul_zero, add_zero]
  · simpa [iteratedDeriv_taylorPolynomial3_eq] using
      integrable_standardGaussianRademacherCubicEnvelope_mul_norm_cubic
        (deriv (deriv f) x) (deriv (deriv (deriv f)) x) 0 0
  · simpa [iteratedDeriv_taylorPolynomial3_eq] using
      integrable_standardGaussianRademacherCubicEnvelope_mul_norm_cubic
        (deriv (deriv (deriv f)) x) 0 0 0
  · simp [iteratedDeriv_taylorPolynomial3_eq]

private theorem
    integrable_volume_shifted_one_add_abs_cubic_mul_iteratedDeriv_norm
    {s : ℂ} {x : ℝ} (hs : s.re < 0) (j : ℕ) (hj : j ≤ 4) :
    Integrable (fun t : ℝ => (1 + |x + t|) ^ 3 *
      ‖iteratedDeriv j (complexQuadraticExp s) (x + t)‖) volume := by
  interval_cases j
  · exact integrable_volume_shifted_one_add_abs_cubic_mul_iteratedDeriv_zero_norm hs
  · exact integrable_volume_shifted_one_add_abs_cubic_mul_iteratedDeriv_one_norm hs
  · exact integrable_volume_shifted_one_add_abs_cubic_mul_iteratedDeriv_two_norm hs
  · exact integrable_volume_shifted_one_add_abs_cubic_mul_iteratedDeriv_three_norm hs
  · exact integrable_volume_shifted_one_add_abs_cubic_mul_fourthDeriv_norm hs

private theorem
    integrable_abs_cubicStopLossDifference_mul_norm_iteratedDeriv_complexQuadraticExp
    {s : ℂ} {x : ℝ} (hs : s.re < 0) (j : ℕ) (hj : j ≤ 4) :
    Integrable (fun t : ℝ =>
      |cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t| *
        ‖iteratedDeriv j (complexQuadraticExp s) (x + t)‖) volume := by
  let C : ℝ := (1 + |x|) ^ 3 *
    ((∫ y, (1 + |y|) ^ 3 ∂(gaussianReal 0 1)) +
      ∫ y, (1 + |y|) ^ 3 ∂standardRademacherMeasure)
  have hbase :=
    integrable_volume_shifted_one_add_abs_cubic_mul_iteratedDeriv_norm
      (x := x) hs j hj
  have hmajor := hbase.const_mul C
  refine Integrable.mono'
    (g := fun t : ℝ => C * ((1 + |x + t|) ^ 3 *
      ‖iteratedDeriv j (complexQuadraticExp s) (x + t)‖))
    hmajor ?_ ?_
  · have hΔ := stronglyMeasurable_standardGaussianRademacher_cubicStopLossDifference
    have hΔabs : AEStronglyMeasurable (fun t : ℝ =>
        |cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t|) volume := by
      simpa [Real.norm_eq_abs] using hΔ.norm.aestronglyMeasurable
    have hD : Continuous (fun t : ℝ =>
        ‖iteratedDeriv j (complexQuadraticExp s) (x + t)‖) := by
      have hf : ContDiff ℝ j (complexQuadraticExp s) :=
        (contDiff_complexQuadraticExp s).of_le (by exact_mod_cast hj)
      exact (hf.continuous_iteratedDeriv' j).comp
        (continuous_const.add continuous_id) |>.norm
    exact hΔabs.mul hD.aestronglyMeasurable
  filter_upwards [] with t
  have hΔ := standardGaussianRademacher_cubicStopLoss_abs_le t
  have htri : 1 + |t| ≤ (1 + |x|) * (1 + |x + t|) := by
    have habs : |t| ≤ |x| + |x + t| := by
      calc
        |t| = |(-x) + (x + t)| := by ring_nf
        _ ≤ |-x| + |x + t| := abs_add_le _ _
        _ = |x| + |x + t| := by rw [abs_neg]
    nlinarith [mul_nonneg (abs_nonneg x) (abs_nonneg (x + t))]
  have hcube : (1 + |t|) ^ 3 ≤
      ((1 + |x|) * (1 + |x + t|)) ^ 3 := by
    exact pow_le_pow_left₀ (by positivity) htri 3
  have hΔ' :
      |cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t| ≤
        ((∫ y, (1 + |y|) ^ 3 ∂(gaussianReal 0 1)) +
          ∫ y, (1 + |y|) ^ 3 ∂standardRademacherMeasure) *
            (((1 + |x|) * (1 + |x + t|)) ^ 3) :=
    hΔ.trans (mul_le_mul_of_nonneg_left hcube (by
      apply add_nonneg
      · exact integral_nonneg_of_ae (ae_of_all _ (fun y => by positivity))
      · exact integral_nonneg_of_ae (ae_of_all _ (fun y => by positivity))))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _)
    (norm_nonneg _))]
  calc
    |cubicStopLossDifference (gaussianReal 0 1)
        standardRademacherMeasure t| *
        ‖iteratedDeriv j (complexQuadraticExp s) (x + t)‖ ≤
      (((∫ y, (1 + |y|) ^ 3 ∂(gaussianReal 0 1)) +
          ∫ y, (1 + |y|) ^ 3 ∂standardRademacherMeasure) *
            (((1 + |x|) * (1 + |x + t|)) ^ 3)) *
        ‖iteratedDeriv j (complexQuadraticExp s) (x + t)‖ :=
      mul_le_mul_of_nonneg_right hΔ' (norm_nonneg _)
    _ = C * ((1 + |x + t|) ^ 3 *
        ‖iteratedDeriv j (complexQuadraticExp s) (x + t)‖) := by
      dsimp [C]
      ring

theorem
    integrable_standardGaussianRademacherCubicEnvelope_mul_norm_shifted_taylor
    (f : ℝ → ℂ) (x : ℝ) (j : ℕ) (hj : j ≤ 4) :
    Integrable (fun t : ℝ => standardGaussianRademacherCubicEnvelope t *
      ‖iteratedDeriv j
        (fun z : ℝ => taylorPolynomial3 f x (z - x)) (x + t)‖) volume := by
  have h :=
    integrable_standardGaussianRademacherCubicEnvelope_mul_norm_iteratedDeriv_taylor
      f x j hj
  refine h.congr (Filter.Eventually.of_forall (fun t => ?_))
  have hshift := congrFun
    (iteratedDeriv_comp_sub_const j (taylorPolynomial3 f x) x) (x + t)
  simpa only [add_sub_cancel_left] using congrArg
    (fun z : ℂ => standardGaussianRademacherCubicEnvelope t * ‖z‖) hshift.symm

/-- The cutoff-radius-independent pointwise majorant for the weighted fourth
derivative of the translated quadratic-exponential remainder. -/
noncomputable def upperCutoffRemainder_standardGaussianRademacher_majorant
    (C : ℕ → ℝ) (s : ℂ) (x t : ℝ) : ℝ :=
  (1 / 6 : ℝ) *
    (|cubicStopLossDifference (gaussianReal 0 1)
        standardRademacherMeasure t| *
      (∑ i ∈ Finset.range (4 + 1), Nat.choose 4 i * C i *
        ‖iteratedDeriv (4 - i) (complexQuadraticExp s) (x + t)‖) +
    standardGaussianRademacherCubicEnvelope t *
      (∑ i ∈ Finset.range (4 + 1), Nat.choose 4 i * C i *
        ‖iteratedDeriv (4 - i)
          (fun z : ℝ => taylorPolynomial3 (complexQuadraticExp s) x (z - x))
          (x + t)‖))

/-- One cutoff-profile constant family simultaneously dominates every
weighted fourth derivative in the translated cutoff sequence.  The witness
precedes `s`, `x`, and the cutoff index, so its public type records the
required independence. -/
theorem upperCutoffRemainder_standardGaussianRademacher_integrable_majorant :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ {s : ℂ} {x : ℝ}, s.re < 0 →
        Integrable
          (upperCutoffRemainder_standardGaussianRademacher_majorant C s x)
          volume ∧
        ∀ (n : ℕ) (t : ℝ),
          ‖((1 / 6 : ℝ) *
              cubicStopLossDifference (gaussianReal 0 1)
                standardRademacherMeasure t) •
            iteratedDeriv 4
              (upperCutoffRemainder n (complexQuadraticExp s) x) (x + t)‖ ≤
            upperCutoffRemainder_standardGaussianRademacher_majorant C s x t := by
  obtain ⟨C, hC, hcut⟩ :=
    upperCutoffRemainder_iteratedDeriv_four_norm_le
  refine ⟨C, hC, ?_⟩
  intro s x hs
  have hfSum : Integrable (fun t : ℝ =>
      ∑ i ∈ Finset.range (4 + 1),
        (Nat.choose 4 i * C i) *
          (|cubicStopLossDifference (gaussianReal 0 1)
              standardRademacherMeasure t| *
            ‖iteratedDeriv (4 - i) (complexQuadraticExp s) (x + t)‖))
      volume := by
    apply integrable_finsetSum (Finset.range (4 + 1))
    intro i hi
    exact (integrable_abs_cubicStopLossDifference_mul_norm_iteratedDeriv_complexQuadraticExp
      (x := x) hs (4 - i) (Nat.sub_le 4 i)).const_mul (Nat.choose 4 i * C i)
  have hpSum : Integrable (fun t : ℝ =>
      ∑ i ∈ Finset.range (4 + 1),
        (Nat.choose 4 i * C i) *
          (standardGaussianRademacherCubicEnvelope t *
            ‖iteratedDeriv (4 - i)
              (fun z : ℝ => taylorPolynomial3 (complexQuadraticExp s) x (z - x))
              (x + t)‖)) volume := by
    apply integrable_finsetSum (Finset.range (4 + 1))
    intro i hi
    exact
      (integrable_standardGaussianRademacherCubicEnvelope_mul_norm_shifted_taylor
        (complexQuadraticExp s) x (4 - i) (Nat.sub_le 4 i)).const_mul
          (Nat.choose 4 i * C i)
  have hmajor : Integrable
      (upperCutoffRemainder_standardGaussianRademacher_majorant C s x)
      volume := by
    have hsum := hfSum.add hpSum |>.const_mul (1 / 6 : ℝ)
    refine hsum.congr (Filter.Eventually.of_forall (fun t => ?_))
    simp only [Pi.add_apply]
    rw [upperCutoffRemainder_standardGaussianRademacher_majorant]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i hi
      ring
    · apply Finset.sum_congr rfl
      intro i hi
      ring
  refine ⟨hmajor, ?_⟩
  intro n t
  let A : ℝ := ∑ i ∈ Finset.range (4 + 1), Nat.choose 4 i * C i *
    ‖iteratedDeriv (4 - i) (complexQuadraticExp s) (x + t)‖
  let B : ℝ := ∑ i ∈ Finset.range (4 + 1), Nat.choose 4 i * C i *
    ‖iteratedDeriv (4 - i)
      (fun z : ℝ => taylorPolynomial3 (complexQuadraticExp s) x (z - x))
      (x + t)‖
  have hA : 0 ≤ A := by
    dsimp [A]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC i)) (norm_nonneg _)
  have hB : 0 ≤ B := by
    dsimp [B]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC i)) (norm_nonneg _)
  have hrem :
      ‖iteratedDeriv 4
          (upperCutoffRemainder n (complexQuadraticExp s) x) (x + t)‖ ≤
        A + B := by
    refine (hcut (contDiff_complexQuadraticExp s) n x t).trans ?_
    dsimp [A, B]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have hcoef : 0 ≤ Nat.choose 4 i * C i :=
      mul_nonneg (Nat.cast_nonneg _) (hC i)
    have hf : ContDiffAt ℝ ((4 - i : ℕ) : WithTop ℕ∞)
        (complexQuadraticExp s) (x + t) :=
      (contDiff_complexQuadraticExp s).contDiffAt.of_le (by
        exact_mod_cast Nat.sub_le 4 i)
    have hp : ContDiffAt ℝ ((4 - i : ℕ) : WithTop ℕ∞)
        (fun z : ℝ => taylorPolynomial3 (complexQuadraticExp s) x (z - x))
        (x + t) := by
      simp only [taylorPolynomial3]
      fun_prop
    change Nat.choose 4 i * C i *
        ‖iteratedDeriv (4 - i)
          (complexQuadraticExp s -
            fun z : ℝ => taylorPolynomial3 (complexQuadraticExp s) x (z - x))
          (x + t)‖ ≤ _
    rw [iteratedDeriv_sub hf hp]
    calc
      Nat.choose 4 i * C i *
          ‖iteratedDeriv (4 - i) (complexQuadraticExp s) (x + t) -
            iteratedDeriv (4 - i)
              (fun z : ℝ => taylorPolynomial3 (complexQuadraticExp s) x (z - x))
              (x + t)‖ ≤
        Nat.choose 4 i * C i *
          (‖iteratedDeriv (4 - i) (complexQuadraticExp s) (x + t)‖ +
            ‖iteratedDeriv (4 - i)
              (fun z : ℝ => taylorPolynomial3 (complexQuadraticExp s) x (z - x))
              (x + t)‖) := mul_le_mul_of_nonneg_left (norm_sub_le _ _) hcoef
      _ = _ := by ring
  have hΔ :=
    abs_cubicStopLossDifference_standardGaussian_rademacher_le_envelope t
  have hscale : 0 ≤ (1 / 6 : ℝ) := by norm_num
  rw [upperCutoffRemainder_standardGaussianRademacher_majorant]
  simp only [norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hscale]
  change (1 / 6 : ℝ) *
      |cubicStopLossDifference (gaussianReal 0 1)
        standardRademacherMeasure t| *
      ‖iteratedDeriv 4
        (upperCutoffRemainder n (complexQuadraticExp s) x) (x + t)‖ ≤
    (1 / 6 : ℝ) *
      (|cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t| * A +
        standardGaussianRademacherCubicEnvelope t * B)
  calc
    (1 / 6 : ℝ) *
        |cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t| *
        ‖iteratedDeriv 4
          (upperCutoffRemainder n (complexQuadraticExp s) x) (x + t)‖ ≤
      (1 / 6 : ℝ) *
        |cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t| * (A + B) := by
      gcongr
    _ = (1 / 6 : ℝ) *
        (|cubicStopLossDifference (gaussianReal 0 1)
            standardRademacherMeasure t| * A +
          |cubicStopLossDifference (gaussianReal 0 1)
            standardRademacherMeasure t| * B) := by ring
    _ ≤ (1 / 6 : ℝ) *
        (|cubicStopLossDifference (gaussianReal 0 1)
            standardRademacherMeasure t| * A +
          standardGaussianRademacherCubicEnvelope t * B) := by
      gcongr

/-- The concrete Gaussian-minus-Rademacher cubic stop-loss weight is
    integrable against the shifted fourth derivative in the strict
    development domain `Re(s) < 0`.  The later cutoff-DCT theorem consumes
    this proved bound; it is not an assumption carried into the API. -/
theorem integrable_standardGaussianRademacher_weighted_fourthDeriv
    {s : ℂ} {x : ℝ} (hs : s.re < 0) :
    Integrable
      (fun t : ℝ => ((1 / 6 : ℝ) *
        cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t) •
        iteratedDeriv 4 (complexQuadraticExp s) (x + t)) volume := by
  have hnorm :=
    integrable_abs_cubicStopLossDifference_mul_norm_iteratedDeriv_complexQuadraticExp
      (x := x) hs 4 (by norm_num)
  have hmajor := hnorm.const_mul (1 / 6 : ℝ)
  refine Integrable.mono'
    (g := fun t : ℝ => (1 / 6 : ℝ) *
      (|cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t| *
        ‖iteratedDeriv 4 (complexQuadraticExp s) (x + t)‖))
    hmajor ?_ ?_
  · have hΔ := stronglyMeasurable_standardGaussianRademacher_cubicStopLossDifference
    have hcoef : StronglyMeasurable (fun t : ℝ =>
        (1 / 6 : ℝ) * cubicStopLossDifference
          (gaussianReal 0 1) standardRademacherMeasure t) := by
      simpa using hΔ.const_mul (1 / 6 : ℝ)
    have hfour : StronglyMeasurable (fun t : ℝ =>
        iteratedDeriv 4 (complexQuadraticExp s) (x + t)) := by
      exact ((contDiff_complexQuadraticExp s).continuous_iteratedDeriv' 4 |>.comp
        (continuous_const.add continuous_id)).stronglyMeasurable
    exact hcoef.smul hfour |>.aestronglyMeasurable
  filter_upwards [] with t
  simp only [norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by norm_num : 0 ≤ (1 / 6 : ℝ))]
  simp only [mul_assoc]
  exact le_rfl

end CertifiedJL
