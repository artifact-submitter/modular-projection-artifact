/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Peano.PeanoGaussianRademacherNoncompact
import CertifiedJL.Analysis.Peano.PeanoKStopLossMoments

/-!
# Scaled Gaussian--Rademacher fourth-Peano replacement

The upper hybrid comparison only uses coefficients whose squared sum is one
half.  Accordingly, the noncompact identity in this file is developed under
the sharp scaled integrability condition `2 * c^2 * re s < 1`, rather than an
incorrect unscaled positive-strip condition.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

namespace CertifiedJL

/-- The K law has polynomially weighted quadratic-exponential integrability
up to the standard-Gaussian threshold `lambda < 1 / 2`. -/
theorem integrable_abs_evenPow_mul_exp_sq_peanoKMeasure
    (ell : ℕ) {lambda : ℝ} (hlambda0 : 0 ≤ lambda)
    (hlambdaHalf : lambda < 1 / 2) :
    Integrable (fun x : ℝ =>
      |x| ^ (2 * ell) * Real.exp (lambda * x ^ 2)) peanoKMeasure := by
  let c : ℝ := (Real.sqrt 2)⁻¹
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hc : c ≠ 0 := inv_ne_zero hsqrt
  have hc_sq : c ^ 2 = (1 / 2 : ℝ) := by
    dsimp [c]
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hvariance : scaledVariance c 1 = (2 : NNReal)⁻¹ := by
    apply NNReal.eq
    simp only [scaledVariance, NNReal.coe_mk, mul_one, NNReal.coe_inv,
      NNReal.coe_ofNat]
    rw [hc_sq]
    norm_num
  have hscaled := peanoK_evenMomentDomination.map_const_mul c
  rw [hvariance] at hscaled
  have hpack := tiltedEvenMoment_le_of_gaussianEvenMomentDomination
    hscaled (le_refl _) ell (show 0 ≤ 2 * lambda by positivity)
      (show 2 * lambda < 1 by linarith)
  have hmapped := hpack.1
  rw [integrable_map_measure (by fun_prop) (by fun_prop)] at hmapped
  have hconst : 0 < |c| ^ (2 * ell) := pow_pos (abs_pos.mpr hc) _
  have hscaledInt := hmapped.const_mul (|c| ^ (2 * ell))⁻¹
  refine hscaledInt.congr (ae_of_all _ fun x => ?_)
  simp only [Function.comp_apply, abs_mul, mul_pow]
  rw [hc_sq]
  have hexp : 2 * lambda * (1 / 2 * x ^ 2) = lambda * x ^ 2 := by ring
  rw [hexp]
  field_simp [hconst.ne']

private theorem integrable_gaussianReal_shifted_absPow_mul_realExp
    {q : ℂ} {x : ℝ} (hq : q.re < 1 / 2) (m : ℕ) :
    Integrable (fun t : ℝ =>
      |x + t| ^ m * Real.exp (q.re * (x + t) ^ 2))
      (gaussianReal 0 1) := by
  have h0 := integrable_gaussianReal_shifted_evenPow_mul_complexQuadraticExp
    (s := q) (μ := 0) (x := x) (v := 1) (by norm_num) (by simpa using hq) 0
  have h2m := integrable_gaussianReal_shifted_evenPow_mul_complexQuadraticExp
    (s := q) (μ := 0) (x := x) (v := 1) (by norm_num) (by simpa using hq) m
  have hmajor : Integrable (fun t : ℝ =>
      (1 + |x + t| ^ (2 * m)) * Real.exp (q.re * (x + t) ^ 2))
      (gaussianReal 0 1) := by
    refine (h0.norm.add h2m.norm).congr (ae_of_all _ fun t => ?_)
    simp only [Pi.add_apply, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, complexQuadraticExp, Complex.norm_exp]
    have hexp : (q * (((x + t : ℝ) : ℂ) ^ 2)).re =
        q.re * (x + t) ^ 2 := by
      rw [Complex.mul_re]
      norm_num [pow_two, Complex.mul_re, Complex.mul_im]
    rw [hexp]
    norm_num [sq_abs]
    ring
  refine Integrable.mono' hmajor (by fun_prop) ?_
  filter_upwards [] with t
  have hpow : |x + t| ^ m ≤ 1 + |x + t| ^ (2 * m) := by
    by_cases ht : |x + t| ≤ 1
    · exact (pow_le_one₀ (abs_nonneg _) ht).trans
        (le_add_of_nonneg_right (pow_nonneg (abs_nonneg _) _))
    · exact (pow_le_pow_right₀ (le_of_not_ge ht) (by omega : m ≤ 2 * m)).trans
        (le_add_of_nonneg_left (by norm_num))
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (pow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le)]
  exact mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le

private theorem integrable_gaussianReal_sq_add_mul_absPow_shifted_realExp
    {q : ℂ} {x : ℝ} (hq : q.re < 1 / 2) (m : ℕ) :
    Integrable (fun t : ℝ => (t ^ 2 + 2) * |x + t| ^ m *
      Real.exp (q.re * (x + t) ^ 2)) (gaussianReal 0 1) := by
  have hm := integrable_gaussianReal_shifted_absPow_mul_realExp (x := x) hq m
  have hm2 := integrable_gaussianReal_shifted_absPow_mul_realExp (x := x) hq (m + 2)
  let C : ℝ := 2 * x ^ 2 + 2
  have hmajor := (hm.const_mul C).add (hm2.const_mul 2)
  refine Integrable.mono' hmajor (by fun_prop) ?_
  filter_upwards [] with t
  have ht : t ^ 2 ≤ 2 * (x + t) ^ 2 + 2 * x ^ 2 := by
    nlinarith [sq_nonneg ((x + t) + x)]
  have hp : 0 ≤ |x + t| ^ m := pow_nonneg (abs_nonneg _) _
  have he : 0 ≤ Real.exp (q.re * (x + t) ^ 2) := (Real.exp_pos _).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (by positivity) hp) he)]
  dsimp [C]
  have hbase : t ^ 2 + 2 ≤ 2 * |x + t| ^ 2 + (2 * x ^ 2 + 2) := by
    rw [sq_abs]
    linarith
  calc
    (t ^ 2 + 2) * |x + t| ^ m * Real.exp (q.re * (x + t) ^ 2) ≤
        (2 * |x + t| ^ 2 + (2 * x ^ 2 + 2)) * |x + t| ^ m *
          Real.exp (q.re * (x + t) ^ 2) := by gcongr
    _ = (2 * x ^ 2 + 2) *
          (|x + t| ^ m * Real.exp (q.re * (x + t) ^ 2)) +
        2 * (|x + t| ^ (m + 2) *
          Real.exp (q.re * (x + t) ^ 2)) := by
      rw [pow_add]
      ring

private theorem integrable_gaussianReal_sq_add_mul_norm_monomial_complexQuadraticExp
    {q a : ℂ} {x : ℝ} (hq : q.re < 1 / 2) (m : ℕ) :
    Integrable (fun t : ℝ => (t ^ 2 + 2) *
      ‖a * (((x + t : ℝ) : ℂ) ^ m) * complexQuadraticExp q (x + t)‖)
      (gaussianReal 0 1) := by
  have h := (integrable_gaussianReal_sq_add_mul_absPow_shifted_realExp
    (x := x) hq m).const_mul ‖a‖
  refine h.congr (ae_of_all _ fun t => ?_)
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    complexQuadraticExp, Complex.norm_exp]
  have hexp : (q * (((x + t : ℝ) : ℂ) ^ 2)).re =
      q.re * (x + t) ^ 2 := by
    rw [Complex.mul_re]
    norm_num [pow_two, Complex.mul_re, Complex.mul_im]
  rw [hexp]
  ring

private theorem integrable_gaussianReal_sq_add_mul_norm_iteratedDeriv
    {q : ℂ} {x : ℝ} (hq : q.re < 1 / 2) (j : ℕ) (hj : j ≤ 4) :
    Integrable (fun t : ℝ => (t ^ 2 + 2) *
      ‖iteratedDeriv j (complexQuadraticExp q) (x + t)‖)
      (gaussianReal 0 1) := by
  have hD : Continuous (fun t : ℝ =>
      iteratedDeriv j (complexQuadraticExp q) (x + t)) :=
    (((contDiff_complexQuadraticExp q).of_le (by exact_mod_cast hj))
      |>.continuous_iteratedDeriv' j).comp
        (continuous_const.add continuous_id)
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (t ^ 2 + 2) *
      ‖iteratedDeriv j (complexQuadraticExp q) (x + t)‖)
      (gaussianReal 0 1) := ((by fun_prop : Continuous (fun t : ℝ => t ^ 2 + 2))
        |>.mul hD.norm).aestronglyMeasurable
  interval_cases j
  · simpa [iteratedDeriv_zero] using
      (integrable_gaussianReal_sq_add_mul_norm_monomial_complexQuadraticExp
        (q := q) (a := 1) (x := x) hq 0)
  · simpa [iteratedDeriv_one_complexQuadraticExp, mul_assoc] using
      (integrable_gaussianReal_sq_add_mul_norm_monomial_complexQuadraticExp
        (q := q) (a := 2 * q) (x := x) hq 1)
  · have h0 :=
      integrable_gaussianReal_sq_add_mul_norm_monomial_complexQuadraticExp
        (q := q) (a := 2 * q) (x := x) hq 0
    have h2 :=
      integrable_gaussianReal_sq_add_mul_norm_monomial_complexQuadraticExp
        (q := q) (a := 4 * q ^ 2) (x := x) hq 2
    refine Integrable.mono' (h0.add h2) hmeas ?_
    filter_upwards [] with t
    rw [iteratedDeriv_two_complexQuadraticExp]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))]
    calc
      (t ^ 2 + 2) * ‖(2 * q + 4 * q ^ 2 * ((x + t : ℝ) : ℂ) ^ 2) *
          complexQuadraticExp q (x + t)‖ ≤
        (t ^ 2 + 2) *
          (‖(2 * q) * (((x + t : ℝ) : ℂ) ^ 0) *
              complexQuadraticExp q (x + t)‖ +
            ‖(4 * q ^ 2) * (((x + t : ℝ) : ℂ) ^ 2) *
              complexQuadraticExp q (x + t)‖) := by
        gcongr
        simp only [pow_zero, mul_one]
        rw [add_mul]
        exact norm_add_le _ _
      _ = _ := by
        simp only [Pi.add_apply, norm_mul, norm_pow, Complex.norm_real,
          Real.norm_eq_abs]
        ring
  · have h1 :=
      integrable_gaussianReal_sq_add_mul_norm_monomial_complexQuadraticExp
        (q := q) (a := 12 * q ^ 2) (x := x) hq 1
    have h3 :=
      integrable_gaussianReal_sq_add_mul_norm_monomial_complexQuadraticExp
        (q := q) (a := 8 * q ^ 3) (x := x) hq 3
    refine Integrable.mono' (h1.add h3) hmeas ?_
    filter_upwards [] with t
    rw [iteratedDeriv_three_complexQuadraticExp]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))]
    calc
      (t ^ 2 + 2) * ‖(12 * q ^ 2 * ((x + t : ℝ) : ℂ) +
          8 * q ^ 3 * ((x + t : ℝ) : ℂ) ^ 3) *
          complexQuadraticExp q (x + t)‖ ≤
        (t ^ 2 + 2) *
          (‖(12 * q ^ 2) * (((x + t : ℝ) : ℂ) ^ 1) *
              complexQuadraticExp q (x + t)‖ +
            ‖(8 * q ^ 3) * (((x + t : ℝ) : ℂ) ^ 3) *
              complexQuadraticExp q (x + t)‖) := by
        gcongr
        simp only [pow_one]
        rw [add_mul]
        exact norm_add_le _ _
      _ = _ := by
        simp only [Pi.add_apply, norm_mul, norm_pow, Complex.norm_real,
          Real.norm_eq_abs]
        ring
  · have h0 :=
      integrable_gaussianReal_sq_add_mul_norm_monomial_complexQuadraticExp
        (q := q) (a := 12 * q ^ 2) (x := x) hq 0
    have h2 :=
      integrable_gaussianReal_sq_add_mul_norm_monomial_complexQuadraticExp
        (q := q) (a := 48 * q ^ 3) (x := x) hq 2
    have h4 :=
      integrable_gaussianReal_sq_add_mul_norm_monomial_complexQuadraticExp
        (q := q) (a := 16 * q ^ 4) (x := x) hq 4
    refine Integrable.mono' (h0.add (h2.add h4)) hmeas ?_
    filter_upwards [] with t
    rw [iteratedDeriv_four_complexQuadraticExp]
    simp only [complexQuadraticExpFourthPolynomialComplex]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))]
    calc
      (t ^ 2 + 2) * ‖(12 * q ^ 2 + 48 * q ^ 3 * ((x + t : ℝ) : ℂ) ^ 2 +
          16 * q ^ 4 * ((x + t : ℝ) : ℂ) ^ 4) *
          complexQuadraticExp q (x + t)‖ ≤
        (t ^ 2 + 2) *
          (‖(12 * q ^ 2) * (((x + t : ℝ) : ℂ) ^ 0) *
              complexQuadraticExp q (x + t)‖ +
            (‖(48 * q ^ 3) * (((x + t : ℝ) : ℂ) ^ 2) *
                complexQuadraticExp q (x + t)‖ +
              ‖(16 * q ^ 4) * (((x + t : ℝ) : ℂ) ^ 4) *
                complexQuadraticExp q (x + t)‖)) := by
        gcongr
        simp only [pow_zero, mul_one]
        rw [add_mul, add_mul]
        simpa only [add_assoc] using
          (norm_add₃_le : ‖_ + _ + _‖ ≤ ‖_‖ + ‖_‖ + ‖_‖)
      _ = _ := by
        simp only [Pi.add_apply, norm_mul, norm_pow, Complex.norm_real,
          Real.norm_eq_abs]
        ring

/-- Polynomially weighted derivatives of every order remain integrable under
the Gaussian tail in the full domain `re q < 1/2`. -/
theorem integrable_gaussianReal_sq_add_mul_norm_iteratedDeriv_all
    {q : ℂ} {x : ℝ} (hq : q.re < 1 / 2) (j : ℕ) :
    Integrable (fun t : ℝ => (t ^ 2 + 2) *
      ‖iteratedDeriv j (complexQuadraticExp q) (x + t)‖)
      (gaussianReal 0 1) := by
  let p := complexQuadraticExpDerivativePolynomial q j
  have hsum : Integrable (fun t : ℝ =>
      ∑ n ∈ p.support, (t ^ 2 + 2) *
        ‖p.coeff n * (((x + t : ℝ) : ℂ) ^ n) *
          complexQuadraticExp q (x + t)‖) (gaussianReal 0 1) := by
    apply integrable_finsetSum
    intro n hn
    exact integrable_gaussianReal_sq_add_mul_norm_monomial_complexQuadraticExp
      (q := q) (a := p.coeff n) (x := x) hq n
  have hfun : (fun t : ℝ =>
      iteratedDeriv j (complexQuadraticExp q) (x + t)) =
      fun t : ℝ => p.eval ((x + t : ℝ) : ℂ) *
        complexQuadraticExp q (x + t) := by
    funext t
    exact iteratedDeriv_complexQuadraticExp j q (x + t)
  have hD : Continuous (fun t : ℝ =>
      iteratedDeriv j (complexQuadraticExp q) (x + t)) := by
    rw [hfun]
    have hp : Continuous (fun t : ℝ => p.eval ((x + t : ℝ) : ℂ)) := by
      fun_prop
    have he : Continuous (fun t : ℝ => complexQuadraticExp q (x + t)) :=
      (contDiff_complexQuadraticExp q).continuous.comp
        (continuous_const.add continuous_id)
    exact hp.mul he
  refine Integrable.mono' hsum
    (((by fun_prop : Continuous (fun t : ℝ => t ^ 2 + 2)).mul hD.norm)
      |>.aestronglyMeasurable) ?_
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (by positivity) (norm_nonneg _))]
  rw [iteratedDeriv_complexQuadraticExp]
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
  calc
    (t ^ 2 + 2) * ‖∑ n ∈ p.support,
        p.coeff n * (((x + t : ℝ) : ℂ) ^ n) *
          complexQuadraticExp q (x + t)‖ ≤
      (t ^ 2 + 2) * ∑ n ∈ p.support,
        ‖p.coeff n * (((x + t : ℝ) : ℂ) ^ n) *
          complexQuadraticExp q (x + t)‖ := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ n ∈ p.support, (t ^ 2 + 2) *
        ‖p.coeff n * (((x + t : ℝ) : ℂ) ^ n) *
          complexQuadraticExp q (x + t)‖ := by
      rw [Finset.mul_sum]

/-- The Gaussian-tail cubic envelope remains integrable against every
derivative throughout the true standard-Gaussian domain `re q < 1/2`. -/
theorem integrable_cubicEnvelope_mul_norm_iteratedDeriv_all_of_re_lt_half
    {q : ℂ} {x : ℝ} (hq : q.re < 1 / 2) (j : ℕ) :
    Integrable (fun t : ℝ => standardGaussianRademacherCubicEnvelope t *
      ‖iteratedDeriv j (complexQuadraticExp q) (x + t)‖) volume := by
  let C : ℝ := 8 *
    ((∫ y, (1 + |y|) ^ 3 ∂(gaussianReal 0 1)) +
      ∫ y, (1 + |y|) ^ 3 ∂standardRademacherMeasure)
  let M : ℝ → ℝ := Set.indicator (Set.Ioo (-1 : ℝ) 1)
    (fun t => C * ‖iteratedDeriv j (complexQuadraticExp q) (x + t)‖)
  let T : ℝ → ℝ := fun t =>
    (Real.sqrt (2 * Real.pi))⁻¹ *
      ((t ^ 2 + 2) * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) *
        ‖iteratedDeriv j (complexQuadraticExp q) (x + t)‖
  have hfun : (fun t : ℝ =>
      iteratedDeriv j (complexQuadraticExp q) (x + t)) =
      fun t : ℝ =>
        (complexQuadraticExpDerivativePolynomial q j).eval
            ((x + t : ℝ) : ℂ) * complexQuadraticExp q (x + t) := by
    funext t
    exact iteratedDeriv_complexQuadraticExp j q (x + t)
  have hD : Continuous (fun t : ℝ =>
      ‖iteratedDeriv j (complexQuadraticExp q) (x + t)‖) := by
    have hp : Continuous (fun t : ℝ =>
        (complexQuadraticExpDerivativePolynomial q j).eval
          ((x + t : ℝ) : ℂ)) := by fun_prop
    have he : Continuous (fun t : ℝ => complexQuadraticExp q (x + t)) :=
      (contDiff_complexQuadraticExp q).continuous.comp
        (continuous_const.add continuous_id)
    have hbase : Continuous (fun t : ℝ =>
        iteratedDeriv j (complexQuadraticExp q) (x + t)) := by
      rw [hfun]
      exact hp.mul he
    exact hbase.norm
  have hmiddleOn : IntegrableOn
      (fun t : ℝ => C * ‖iteratedDeriv j (complexQuadraticExp q) (x + t)‖)
      (Set.Ioo (-1 : ℝ) 1) volume := by
    have hIcc : IntegrableOn
        (fun t : ℝ => C * ‖iteratedDeriv j (complexQuadraticExp q) (x + t)‖)
        (Set.Icc (-1 : ℝ) 1) volume :=
      ContinuousOn.integrableOn_Icc ((continuous_const.mul hD).continuousOn)
    exact hIcc.mono_set Set.Ioo_subset_Icc_self
  have hmiddle : Integrable M volume := by
    simpa only [M] using hmiddleOn.integrable_indicator measurableSet_Ioo
  have hgaussian := integrable_gaussianReal_sq_add_mul_norm_iteratedDeriv_all
    (x := x) hq j
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num)] at hgaussian
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1)
    (ae_of_all _ fun _ => gaussianPDF_lt_top)] at hgaussian
  have htail : Integrable T volume := by
    refine hgaussian.congr (ae_of_all _ fun t => ?_)
    dsimp [T]
    rw [toReal_gaussianPDF]
    rw [gaussianPDFReal]
    norm_num
    ring_nf
  have hsum := hmiddle.add htail
  refine hsum.congr (ae_of_all _ fun t => ?_)
  simp only [Pi.add_apply]
  dsimp [M, T, C, standardGaussianRademacherCubicEnvelope]
  by_cases ht : t ∈ Set.Ioo (-1 : ℝ) 1
  · simp only [Set.indicator_of_mem ht]
    ring
  · simp only [Set.indicator_of_notMem ht]
    ring

/-- Compatibility wrapper for the original order-at-most-four API. -/
theorem integrable_cubicEnvelope_mul_norm_iteratedDeriv_of_re_lt_half
    {q : ℂ} {x : ℝ} (hq : q.re < 1 / 2) (j : ℕ) (_hj : j ≤ 4) :
    Integrable (fun t : ℝ => standardGaussianRademacherCubicEnvelope t *
      ‖iteratedDeriv j (complexQuadraticExp q) (x + t)‖) volume :=
  integrable_cubicEnvelope_mul_norm_iteratedDeriv_all_of_re_lt_half hq j

theorem iteratedDeriv_iteratedDeriv_add (r j : ℕ) (f : ℝ → ℂ) :
    iteratedDeriv j (iteratedDeriv r f) = iteratedDeriv (r + j) f := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    iteratedDeriv_eq_iterate]
  rw [Nat.add_comm, ← Function.iterate_add_apply]

private noncomputable def fourthPeanoMajorant
    (C : ℕ → ℝ) (f : ℝ → ℂ) (x t : ℝ) : ℝ :=
  (1 / 6 : ℝ) * standardGaussianRademacherCubicEnvelope t *
    ∑ i ∈ Finset.range (4 + 1), Nat.choose 4 i * C i *
      (‖iteratedDeriv (4 - i) f (x + t)‖ +
        ‖iteratedDeriv (4 - i)
          (fun z : ℝ => taylorPolynomial3 f x (z - x)) (x + t)‖)

private theorem fourthPeanoMajorant_exists
    {f : ℝ → ℂ} {x : ℝ} (hf : ContDiff ℝ 4 f)
    (hInt : ∀ j, j ≤ 4 → Integrable (fun t : ℝ =>
      standardGaussianRademacherCubicEnvelope t *
        ‖iteratedDeriv j f (x + t)‖) volume) :
    ∃ C : ℕ → ℝ,
      Integrable (fourthPeanoMajorant C f x) volume ∧
      ∀ (n : ℕ) (t : ℝ),
        ‖((1 / 6 : ℝ) *
            cubicStopLossDifference (gaussianReal 0 1)
              standardRademacherMeasure t) •
          iteratedDeriv 4 (upperCutoffRemainder n f x) (x + t)‖ ≤
          fourthPeanoMajorant C f x t := by
  obtain ⟨C, hC, hcut⟩ := upperCutoffRemainder_iteratedDeriv_four_norm_le
  refine ⟨C, ?_, ?_⟩
  · unfold fourthPeanoMajorant
    have hsum : Integrable (fun t : ℝ =>
        ∑ i ∈ Finset.range (4 + 1),
          (Nat.choose 4 i * C i) *
            (standardGaussianRademacherCubicEnvelope t *
                ‖iteratedDeriv (4 - i) f (x + t)‖ +
              standardGaussianRademacherCubicEnvelope t *
                ‖iteratedDeriv (4 - i)
                  (fun z : ℝ => taylorPolynomial3 f x (z - x))
                  (x + t)‖)) volume := by
      apply integrable_finsetSum
      intro i hi
      have hi4 : 4 - i ≤ 4 := Nat.sub_le 4 i
      exact ((hInt (4 - i) hi4).add
        (integrable_standardGaussianRademacherCubicEnvelope_mul_norm_shifted_taylor
          f x (4 - i) hi4)).const_mul (Nat.choose 4 i * C i)
    have hscaled := hsum.const_mul (1 / 6 : ℝ)
    refine hscaled.congr (ae_of_all _ fun t => ?_)
    change (1 / 6 : ℝ) * _ = (1 / 6 : ℝ) *
      standardGaussianRademacherCubicEnvelope t * _
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · intro n t
    have hrem := hcut hf n x t
    have hsum :
        ‖iteratedDeriv 4 (upperCutoffRemainder n f x) (x + t)‖ ≤
          ∑ i ∈ Finset.range (4 + 1), Nat.choose 4 i * C i *
            (‖iteratedDeriv (4 - i) f (x + t)‖ +
              ‖iteratedDeriv (4 - i)
                (fun z : ℝ => taylorPolynomial3 f x (z - x))
                (x + t)‖) := by
      refine hrem.trans (Finset.sum_le_sum fun i hi => ?_)
      have hcoef : 0 ≤ Nat.choose 4 i * C i :=
        mul_nonneg (Nat.cast_nonneg _) (hC i)
      have hfat : ContDiffAt ℝ ((4 - i : ℕ) : WithTop ℕ∞) f (x + t) :=
        hf.contDiffAt.of_le (by exact_mod_cast Nat.sub_le 4 i)
      have hp : ContDiffAt ℝ ((4 - i : ℕ) : WithTop ℕ∞)
          (fun z : ℝ => taylorPolynomial3 f x (z - x)) (x + t) := by
        simp only [taylorPolynomial3]
        fun_prop
      change Nat.choose 4 i * C i *
          ‖iteratedDeriv (4 - i)
            (f - fun z : ℝ => taylorPolynomial3 f x (z - x))
            (x + t)‖ ≤ _
      rw [iteratedDeriv_sub hfat hp]
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hcoef
    have henv :=
      abs_cubicStopLossDifference_standardGaussian_rademacher_le_envelope t
    have henv0 := standardGaussianRademacherCubicEnvelope_nonneg t
    have hsix : 0 ≤ (1 / 6 : ℝ) := by norm_num
    rw [fourthPeanoMajorant, norm_smul, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg hsix]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (mul_le_mul henv hsum (norm_nonneg _) henv0) hsix

private theorem upperCutoffRemainder_weighted_fourthDeriv_integral_tendsto
    {f : ℝ → ℂ} {x : ℝ} (hf : ContDiff ℝ 4 f)
    (hInt : ∀ j, j ≤ 4 → Integrable (fun t : ℝ =>
      standardGaussianRademacherCubicEnvelope t *
        ‖iteratedDeriv j f (x + t)‖) volume) :
    Tendsto
      (fun n => ∫ t, ((1 / 6 : ℝ) *
        cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t) •
        iteratedDeriv 4 (upperCutoffRemainder n f x) (x + t)) atTop
      (𝓝 (∫ t, ((1 / 6 : ℝ) *
        cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t) • iteratedDeriv 4 f (x + t))) := by
  obtain ⟨C, hCint, hC⟩ := fourthPeanoMajorant_exists hf hInt
  refine tendsto_integral_of_dominated_convergence
    (fourthPeanoMajorant C f x) ?_ hCint ?_ ?_
  · intro n
    have hDelta := stronglyMeasurable_standardGaussianRademacher_cubicStopLossDifference
    have hD : StronglyMeasurable (fun t : ℝ => iteratedDeriv 4
        (upperCutoffRemainder n f x) (x + t)) :=
      (((upperCutoffRemainder_contDiff hf n x).continuous_iteratedDeriv' 4).comp
        (continuous_const.add continuous_id)).stronglyMeasurable
    exact (hDelta.const_mul (1 / 6 : ℝ)).smul hD |>.aestronglyMeasurable
  · intro n
    exact ae_of_all _ (hC n)
  · filter_upwards [] with t
    exact tendsto_const_nhds.smul
      (upperCutoffRemainder_iteratedDeriv_four_tendsto hf x t)

private theorem contDiff_four_iteratedDeriv_complexQuadraticExp
    (r : ℕ) (q : ℂ) :
    ContDiff ℝ 4 (iteratedDeriv r (complexQuadraticExp q)) := by
  have hfun : iteratedDeriv r (complexQuadraticExp q) = fun z : ℝ =>
      (complexQuadraticExpDerivativePolynomial q r).eval (z : ℂ) *
        complexQuadraticExp q z := by
    funext z
    exact iteratedDeriv_complexQuadraticExp r q z
  rw [hfun]
  have hz : ContDiff ℝ 4 (fun z : ℝ => (z : ℂ)) :=
    Complex.ofRealCLM.contDiff
  have hp : ContDiff ℝ 4 (fun z : ℝ =>
      (complexQuadraticExpDerivativePolynomial q r).eval (z : ℂ)) := by
    let p := complexQuadraticExpDerivativePolynomial q r
    have heval : (fun z : ℝ => p.eval (z : ℂ)) = fun z : ℝ =>
        ∑ n ∈ p.support, p.coeff n * (z : ℂ) ^ n := by
      funext z
      rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    change ContDiff ℝ 4 (fun z : ℝ => p.eval (z : ℂ))
    rw [heval]
    apply ContDiff.sum
    intro n hn
    exact (show ContDiff ℝ 4 (fun _ : ℝ =>
      p.coeff n) from
        contDiff_const).mul (hz.pow n)
  exact hp.mul (contDiff_complexQuadraticExp q)

private theorem integrable_gaussianReal_shifted_iteratedDeriv_all
    {q : ℂ} {x : ℝ} (hq : q.re < 1 / 2) (r : ℕ) :
    Integrable (fun y : ℝ =>
      iteratedDeriv r (complexQuadraticExp q) (x + y))
      (gaussianReal 0 1) := by
  have hmajor := integrable_gaussianReal_sq_add_mul_norm_iteratedDeriv_all
    (x := x) hq r
  have hcont : Continuous (fun y : ℝ =>
      iteratedDeriv r (complexQuadraticExp q) (x + y)) :=
    ((contDiff_four_iteratedDeriv_complexQuadraticExp r q).continuous.comp
      (continuous_const.add continuous_id))
  refine Integrable.mono' hmajor hcont.aestronglyMeasurable ?_
  filter_upwards [] with y
  calc
    ‖iteratedDeriv r (complexQuadraticExp q) (x + y)‖ =
        1 * ‖iteratedDeriv r (complexQuadraticExp q) (x + y)‖ := by ring
    _ ≤ (y ^ 2 + 2) *
        ‖iteratedDeriv r (complexQuadraticExp q) (x + y)‖ := by
      gcongr
      nlinarith [sq_nonneg y]

/-- The fourth-Peano identity on the full Gaussian domain for every initial
derivative order. -/
theorem peanoIdentity4_standardGaussianRademacher_iteratedDeriv_complexQuadraticExp_of_re_lt_half
    (r : ℕ) {q : ℂ} (hq : q.re < 1 / 2) (x : ℝ) :
    (∫ y : ℝ, iteratedDeriv r (complexQuadraticExp q) (x + y)
        ∂(gaussianReal 0 1)) -
      ∫ y : ℝ, iteratedDeriv r (complexQuadraticExp q) (x + y)
        ∂standardRademacherMeasure =
      ∫ t : ℝ, ((1 / 6 : ℝ) *
        cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t) •
        iteratedDeriv (r + 4) (complexQuadraticExp q) (x + t) := by
  let f : ℝ → ℂ := iteratedDeriv r (complexQuadraticExp q)
  have hf : ContDiff ℝ 4 f :=
    contDiff_four_iteratedDeriv_complexQuadraticExp r q
  have hμf : Integrable (fun y : ℝ => f (x + y)) (gaussianReal 0 1) :=
    integrable_gaussianReal_shifted_iteratedDeriv_all hq r
  have hνf : Integrable (fun y : ℝ => f (x + y))
      standardRademacherMeasure := by
    rw [standardRademacherMeasure]
    apply Integrable.add_measure
    · exact (integrable_dirac (f := fun y : ℝ => f (x + y))
        (a := (-1 : ℝ)) (by simp)).smul_measure (by norm_num)
    · exact (integrable_dirac (f := fun y : ℝ => f (x + y))
        (a := (1 : ℝ)) (by simp)).smul_measure (by norm_num)
  have hμT : Integrable (fun y : ℝ => taylorPolynomial3 f x y)
      (gaussianReal 0 1) :=
    integrable_taylorPolynomial3_left standardGaussianRademacher_equalMoments f x
  have hμrem : Integrable (fun y : ℝ =>
      f (x + y) - taylorPolynomial3 f x y) (gaussianReal 0 1) :=
    hμf.sub hμT
  have hμLimit := upperCutoffRemainder_integral_tendsto
    (μ := gaussianReal 0 1) hf x hμrem
  have hνLimit := upperCutoffRemainder_standardRademacher_integral_tendsto hf x
  have hdata (n : ℕ) :=
    upperCutoffRemainder_standardGaussianRademacher_kernel_data hf x n
  have henv (j : ℕ) (hj : j ≤ 4) : Integrable (fun t : ℝ =>
      standardGaussianRademacherCubicEnvelope t *
        ‖iteratedDeriv j f (x + t)‖) volume := by
    rw [show iteratedDeriv j f =
      iteratedDeriv (r + j) (complexQuadraticExp q) by
        exact iteratedDeriv_iteratedDeriv_add r j (complexQuadraticExp q)]
    exact integrable_cubicEnvelope_mul_norm_iteratedDeriv_all_of_re_lt_half
      hq (r + j)
  have hRhsLimit :=
    upperCutoffRemainder_weighted_fourthDeriv_integral_tendsto hf henv
  have hidentity := peanoIdentity4_of_compact_approximants
    (E := ℂ) (μ := gaussianReal 0 1) (ν := standardRademacherMeasure)
    (f := f) (x := x) standardGaussianRademacher_equalMoments hμf hνf
    (fun n => upperCutoffRemainder n f x)
    (fun n => upperCutoffRemainder_contDiff hf n x)
    (fun n => upperCutoffRemainder_hasCompactSupport n f x)
    (fun n => (hdata n).1.1) (fun n => (hdata n).2.1)
    (fun n => (hdata n).1.2) (fun n => (hdata n).2.2)
    hμLimit hνLimit (by
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hRhsLimit)
  have hidentity' :
      (∫ y : ℝ, f (x + y) ∂(gaussianReal 0 1)) -
          ∫ y : ℝ, f (x + y) ∂standardRademacherMeasure =
        ∫ t : ℝ, ((1 / 6 : ℝ) *
          cubicStopLossDifference (gaussianReal 0 1)
            standardRademacherMeasure t) • iteratedDeriv 4 f (x + t) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hidentity
  rw [show iteratedDeriv 4 f =
    iteratedDeriv (r + 4) (complexQuadraticExp q) by
      exact iteratedDeriv_iteratedDeriv_add r 4 (complexQuadraticExp q)] at hidentity'
  simpa only [f] using hidentity'

/-- The scaled fourth-Peano replacement for the fourth derivative, with the
eighth derivative on the K-law remainder. -/
theorem peanoIdentity4_standardGaussianRademacher_scaled_iteratedDeriv_four_complexQuadraticExp
    {s : ℂ} (w c : ℝ) (hscale : 2 * c ^ 2 * s.re < 1) :
    (∫ y : ℝ, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
        ∂(gaussianReal 0 1)) -
      ∫ y : ℝ, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
        ∂standardRademacherMeasure =
      (c ^ 4 / 12 : ℝ) •
        ∫ k : ℝ, iteratedDeriv 8 (complexQuadraticExp s) (w + c * k)
          ∂peanoKMeasure := by
  by_cases hc : c = 0
  · subst c
    simp
  · let q : ℂ := s * (c : ℂ) ^ 2
    let x : ℝ := w / c
    have hq : q.re < 1 / 2 := by
      have hcre : ((c : ℂ) ^ 2).re = c ^ 2 := by
        norm_num [pow_two, Complex.mul_re]
      have hcim : ((c : ℂ) ^ 2).im = 0 := by
        norm_num [pow_two, Complex.mul_im]
      dsimp [q]
      rw [Complex.mul_re, hcre, hcim]
      simp only [mul_zero, sub_zero]
      nlinarith
    have harg (z : ℝ) :
        complexQuadraticExp q (x + z) =
          complexQuadraticExp s (w + c * z) := by
      unfold complexQuadraticExp
      congr 1
      dsimp [q, x]
      push_cast
      field_simp [hc]
    have hD4 (z : ℝ) :
        iteratedDeriv 4 (complexQuadraticExp q) (x + z) =
          c ^ 4 • iteratedDeriv 4 (complexQuadraticExp s) (w + c * z) := by
      rw [iteratedDeriv_four_complexQuadraticExp,
        iteratedDeriv_four_complexQuadraticExp]
      simp only [complexQuadraticExpFourthPolynomialComplex, harg]
      dsimp [q, x]
      push_cast
      field_simp [hc]
    have hD8 (z : ℝ) :
        iteratedDeriv 8 (complexQuadraticExp q) (x + z) =
          c ^ 8 • iteratedDeriv 8 (complexQuadraticExp s) (w + c * z) := by
      rw [iteratedDeriv_eight_complexQuadraticExp,
        iteratedDeriv_eight_complexQuadraticExp, harg]
      dsimp [q, x]
      push_cast
      field_simp [hc]
    have hbase :=
      peanoIdentity4_standardGaussianRademacher_iteratedDeriv_complexQuadraticExp_of_re_lt_half
        4 hq x
    have hleft :
        (∫ y : ℝ, iteratedDeriv 4 (complexQuadraticExp q) (x + y)
            ∂(gaussianReal 0 1)) -
          ∫ y : ℝ, iteratedDeriv 4 (complexQuadraticExp q) (x + y)
            ∂standardRademacherMeasure =
        c ^ 4 • ((∫ y : ℝ, iteratedDeriv 4 (complexQuadraticExp s)
              (w + c * y) ∂(gaussianReal 0 1)) -
            ∫ y : ℝ, iteratedDeriv 4 (complexQuadraticExp s)
              (w + c * y) ∂standardRademacherMeasure) := by
      rw [smul_sub, ← integral_smul, ← integral_smul]
      congr 1 <;> apply integral_congr_ae <;>
        exact ae_of_all _ hD4
    have hright :
        (∫ t : ℝ, ((1 / 6 : ℝ) *
            cubicStopLossDifference (gaussianReal 0 1)
              standardRademacherMeasure t) •
          iteratedDeriv 8 (complexQuadraticExp q) (x + t)) =
        c ^ 8 • ∫ t : ℝ, ((1 / 6 : ℝ) *
            cubicStopLossDifference (gaussianReal 0 1)
              standardRademacherMeasure t) •
          iteratedDeriv 8 (complexQuadraticExp s) (w + c * t) := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hD8]
      simp only [smul_smul]
      congr 1
      ring
    rw [hleft, hright] at hbase
    have hcancel :
        (∫ y : ℝ, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
            ∂(gaussianReal 0 1)) -
          ∫ y : ℝ, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
            ∂standardRademacherMeasure =
        c ^ 4 • ∫ t : ℝ, ((1 / 6 : ℝ) *
            cubicStopLossDifference (gaussianReal 0 1)
              standardRademacherMeasure t) •
          iteratedDeriv 8 (complexQuadraticExp s) (w + c * t) := by
      have hc4 : ((c ^ 4 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast pow_ne_zero 4 hc
      apply mul_left_cancel₀ hc4
      change (c ^ 4 : ℝ) •
          ((∫ y : ℝ, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
              ∂(gaussianReal 0 1)) -
            ∫ y : ℝ, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
              ∂standardRademacherMeasure) =
        (c ^ 4 : ℝ) • ((c ^ 4 : ℝ) •
          ∫ t : ℝ, ((1 / 6 : ℝ) *
            cubicStopLossDifference (gaussianReal 0 1)
              standardRademacherMeasure t) •
            iteratedDeriv 8 (complexQuadraticExp s) (w + c * t))
      calc
        _ = (c ^ 8 : ℝ) • ∫ t : ℝ, ((1 / 6 : ℝ) *
            cubicStopLossDifference (gaussianReal 0 1)
              standardRademacherMeasure t) •
            iteratedDeriv 8 (complexQuadraticExp s) (w + c * t) := hbase
        _ = _ := by
          rw [smul_smul]
          congr 1
          ring
    rw [hcancel]
    rw [show c ^ 4 / 12 = c ^ 4 * (1 / 12 : ℝ) by ring, mul_smul]
    congr 1
    unfold peanoKMeasure
    rw [integral_positiveDensityMeasure peanoKDensity
      stronglyMeasurable_peanoKDensity.measurable peanoKDensity_nonneg]
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [peanoKDensity_eq_two_mul_cubicStopLossDifference]
    simp only [smul_smul]
    ring_nf

/-- A cutoff-index-independent majorant for the fourth derivative of the
translated Taylor-remainder approximants in the full domain `re q < 1/2`. -/
noncomputable def scaledFourthPeanoMajorant
    (C : ℕ → ℝ) (q : ℂ) (x t : ℝ) : ℝ :=
  (1 / 6 : ℝ) * standardGaussianRademacherCubicEnvelope t *
    ∑ i ∈ Finset.range (4 + 1), Nat.choose 4 i * C i *
      (‖iteratedDeriv (4 - i) (complexQuadraticExp q) (x + t)‖ +
        ‖iteratedDeriv (4 - i)
          (fun z : ℝ => taylorPolynomial3 (complexQuadraticExp q) x (z - x))
          (x + t)‖)

/-- The scaled fourth-Peano cutoff sequence has one integrable majorant on
the sharp standard-Gaussian domain `re q < 1/2`. -/
theorem scaledFourthPeanoMajorant_exists
    {q : ℂ} {x : ℝ} (hq : q.re < 1 / 2) :
    ∃ C : ℕ → ℝ,
      Integrable (scaledFourthPeanoMajorant C q x) volume ∧
      ∀ (n : ℕ) (t : ℝ),
        ‖((1 / 6 : ℝ) *
            cubicStopLossDifference (gaussianReal 0 1)
              standardRademacherMeasure t) •
          iteratedDeriv 4
            (upperCutoffRemainder n (complexQuadraticExp q) x) (x + t)‖ ≤
          scaledFourthPeanoMajorant C q x t := by
  obtain ⟨C, hC, hcut⟩ := upperCutoffRemainder_iteratedDeriv_four_norm_le
  refine ⟨C, ?_, ?_⟩
  · unfold scaledFourthPeanoMajorant
    have hsum : Integrable (fun t : ℝ =>
        ∑ i ∈ Finset.range (4 + 1),
          (Nat.choose 4 i * C i) *
            (standardGaussianRademacherCubicEnvelope t *
                ‖iteratedDeriv (4 - i) (complexQuadraticExp q) (x + t)‖ +
              standardGaussianRademacherCubicEnvelope t *
                ‖iteratedDeriv (4 - i)
                  (fun z : ℝ => taylorPolynomial3
                    (complexQuadraticExp q) x (z - x)) (x + t)‖)) volume := by
      apply integrable_finsetSum
      intro i hi
      have hi4 : 4 - i ≤ 4 := Nat.sub_le 4 i
      exact ((integrable_cubicEnvelope_mul_norm_iteratedDeriv_of_re_lt_half
        (x := x) hq (4 - i) hi4).add
          (integrable_standardGaussianRademacherCubicEnvelope_mul_norm_shifted_taylor
            (complexQuadraticExp q) x (4 - i) hi4)).const_mul
              (Nat.choose 4 i * C i)
    have hscaled := hsum.const_mul (1 / 6 : ℝ)
    refine hscaled.congr (ae_of_all _ fun t => ?_)
    change (1 / 6 : ℝ) * _ = (1 / 6 : ℝ) *
      standardGaussianRademacherCubicEnvelope t * _
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · intro n t
    have hrem := hcut (contDiff_complexQuadraticExp q) n x t
    have hsum :
        ‖iteratedDeriv 4
            (upperCutoffRemainder n (complexQuadraticExp q) x) (x + t)‖ ≤
          ∑ i ∈ Finset.range (4 + 1), Nat.choose 4 i * C i *
            (‖iteratedDeriv (4 - i) (complexQuadraticExp q) (x + t)‖ +
              ‖iteratedDeriv (4 - i)
                (fun z : ℝ => taylorPolynomial3
                  (complexQuadraticExp q) x (z - x)) (x + t)‖) := by
      refine hrem.trans (Finset.sum_le_sum fun i hi => ?_)
      have hcoef : 0 ≤ Nat.choose 4 i * C i :=
        mul_nonneg (Nat.cast_nonneg _) (hC i)
      have hf : ContDiffAt ℝ ((4 - i : ℕ) : WithTop ℕ∞)
          (complexQuadraticExp q) (x + t) :=
        (contDiff_complexQuadraticExp q).contDiffAt.of_le
          (by exact_mod_cast Nat.sub_le 4 i)
      have hp : ContDiffAt ℝ ((4 - i : ℕ) : WithTop ℕ∞)
          (fun z : ℝ => taylorPolynomial3
            (complexQuadraticExp q) x (z - x)) (x + t) := by
        simp only [taylorPolynomial3]
        fun_prop
      change Nat.choose 4 i * C i *
          ‖iteratedDeriv (4 - i)
            (complexQuadraticExp q - fun z : ℝ =>
              taylorPolynomial3 (complexQuadraticExp q) x (z - x))
            (x + t)‖ ≤ _
      rw [iteratedDeriv_sub hf hp]
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hcoef
    have henv :=
      abs_cubicStopLossDifference_standardGaussian_rademacher_le_envelope t
    have henv0 := standardGaussianRademacherCubicEnvelope_nonneg t
    have hsix : 0 ≤ (1 / 6 : ℝ) := by norm_num
    rw [scaledFourthPeanoMajorant, norm_smul, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg hsix]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (mul_le_mul henv hsum (norm_nonneg _) henv0) hsix

/-- Weighted fourth derivatives of the translated cutoff remainders converge
in integral throughout `re q < 1/2`. -/
theorem upperCutoffRemainder_weighted_fourthDeriv_integral_tendsto_of_re_lt_half
    {q : ℂ} {x : ℝ} (hq : q.re < 1 / 2) :
    Tendsto
      (fun n => ∫ t, ((1 / 6 : ℝ) *
        cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t) •
        iteratedDeriv 4
          (upperCutoffRemainder n (complexQuadraticExp q) x) (x + t))
      atTop
      (𝓝 (∫ t, ((1 / 6 : ℝ) *
        cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t) •
        iteratedDeriv 4 (complexQuadraticExp q) (x + t))) := by
  obtain ⟨C, hCint, hC⟩ := scaledFourthPeanoMajorant_exists (x := x) hq
  refine tendsto_integral_of_dominated_convergence
    (scaledFourthPeanoMajorant C q x) ?_ hCint ?_ ?_
  · intro n
    have hΔ := stronglyMeasurable_standardGaussianRademacher_cubicStopLossDifference
    have hD : StronglyMeasurable (fun t : ℝ => iteratedDeriv 4
        (upperCutoffRemainder n (complexQuadraticExp q) x) (x + t)) :=
      (((upperCutoffRemainder_contDiff (contDiff_complexQuadraticExp q) n x)
        |>.continuous_iteratedDeriv' 4).comp
          (continuous_const.add continuous_id)).stronglyMeasurable
    exact (hΔ.const_mul (1 / 6 : ℝ)).smul hD |>.aestronglyMeasurable
  · intro n
    exact ae_of_all _ (hC n)
  · filter_upwards [] with t
    exact tendsto_const_nhds.smul
      (upperCutoffRemainder_iteratedDeriv_four_tendsto
        (contDiff_complexQuadraticExp q) x t)

private theorem integrable_standardRademacher_scaled
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : Integrable f standardRademacherMeasure := by
  rw [standardRademacherMeasure]
  apply Integrable.add_measure
  · exact (integrable_dirac (f := f) (a := (-1 : ℝ)) (by simp)).smul_measure
      (by norm_num)
  · exact (integrable_dirac (f := f) (a := (1 : ℝ)) (by simp)).smul_measure
      (by norm_num)

/-- The fourth-order Gaussian--Rademacher Peano identity holds throughout
the full integrability domain of the standard Gaussian. -/
theorem peanoIdentity4_standardGaussianRademacher_complexQuadraticExp_of_re_lt_half
    {q : ℂ} (hq : q.re < 1 / 2) (x : ℝ) :
    (∫ y : ℝ, complexQuadraticExp q (x + y) ∂(gaussianReal 0 1)) -
        ∫ y : ℝ, complexQuadraticExp q (x + y) ∂standardRademacherMeasure =
      ∫ t : ℝ, ((1 / 6 : ℝ) *
        cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t) •
        iteratedDeriv 4 (complexQuadraticExp q) (x + t) := by
  have hqGaussian : q.re < 1 / (2 * (1 : ℝ)) := by simpa using hq
  have hμf : Integrable (fun y : ℝ => complexQuadraticExp q (x + y))
      (gaussianReal 0 1) :=
    integrable_gaussianReal_shifted_complexQuadraticExp
      (μ := 0) (v := 1) (x := x) (by norm_num) hqGaussian
  have hνf : Integrable (fun y : ℝ => complexQuadraticExp q (x + y))
      standardRademacherMeasure :=
    integrable_standardRademacher_scaled _
  have hμrem : Integrable
      (fun y : ℝ => complexQuadraticExp q (x + y) -
        taylorPolynomial3 (complexQuadraticExp q) x y)
      (gaussianReal 0 1) :=
    integrable_gaussianReal_shifted_complexQuadraticExp_remainder
      (μ := 0) (v := 1) (x := x) (by norm_num) hqGaussian
  have hμLimit := upperCutoffRemainder_integral_tendsto
    (μ := gaussianReal 0 1) (contDiff_complexQuadraticExp q) x hμrem
  have hνLimit := upperCutoffRemainder_standardRademacher_integral_tendsto
    (contDiff_complexQuadraticExp q) x
  have hdata (n : ℕ) :=
    upperCutoffRemainder_standardGaussianRademacher_kernel_data
      (contDiff_complexQuadraticExp q) x n
  have hRhsLimit : Tendsto
      (fun n => ∫ t, ((1 / 6 : ℝ) *
        cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t) •
        deriv (deriv (deriv (deriv
          (upperCutoffRemainder n (complexQuadraticExp q) x)))) (x + t))
      atTop
      (𝓝 (∫ t, ((1 / 6 : ℝ) *
        cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t) •
        deriv (deriv (deriv (deriv (complexQuadraticExp q)))) (x + t))) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      (upperCutoffRemainder_weighted_fourthDeriv_integral_tendsto_of_re_lt_half
        (q := q) (x := x) hq)
  have hidentity := peanoIdentity4_of_compact_approximants
    (E := ℂ) (μ := gaussianReal 0 1) (ν := standardRademacherMeasure)
    (f := complexQuadraticExp q) (x := x)
    standardGaussianRademacher_equalMoments hμf hνf
    (fun n => upperCutoffRemainder n (complexQuadraticExp q) x)
    (fun n => upperCutoffRemainder_contDiff (contDiff_complexQuadraticExp q) n x)
    (fun n => upperCutoffRemainder_hasCompactSupport n (complexQuadraticExp q) x)
    (fun n => (hdata n).1.1) (fun n => (hdata n).2.1)
    (fun n => (hdata n).1.2) (fun n => (hdata n).2.2)
    hμLimit hνLimit hRhsLimit
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hidentity

/-- Four derivatives of a real affine scaling produce the expected fourth
power of the scale. -/
theorem iteratedDeriv_four_scaled_complexQuadraticExp
    (s : ℂ) (w c z : ℝ) :
    iteratedDeriv 4
        (fun y : ℝ => complexQuadraticExp s (w + c * y)) z =
      c ^ 4 • iteratedDeriv 4 (complexQuadraticExp s) (w + c * z) := by
  let F : ℝ → ℂ := complexQuadraticExp s
  have hF : ContDiff ℝ 4 F :=
    (contDiff_complexQuadraticExp s).of_le (by norm_num)
  have hshift : ContDiff ℝ 4 (fun u : ℝ => F (w + u)) :=
    hF.comp (by fun_prop)
  have hscale := congrFun (iteratedDeriv_comp_const_smul hshift c) z
  have htranslate := congrFun (iteratedDeriv_comp_const_add 4 F w) (c * z)
  simpa only [F, htranslate] using hscale

/-- A scaled Gaussian coordinate can be replaced by a scaled Rademacher
coordinate whenever its individual quadratic-exponential budget is below the
standard-Gaussian threshold. -/
theorem peanoIdentity4_standardGaussianRademacher_scaled_complexQuadraticExp
    {s : ℂ} (w c : ℝ) (hscale : 2 * c ^ 2 * s.re < 1) :
    (∫ y : ℝ, complexQuadraticExp s (w + c * y) ∂(gaussianReal 0 1)) -
        ∫ y : ℝ, complexQuadraticExp s (w + c * y)
          ∂standardRademacherMeasure =
      ∫ t : ℝ, ((1 / 6 : ℝ) *
        cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t) •
        (c ^ 4 • iteratedDeriv 4 (complexQuadraticExp s) (w + c * t)) := by
  by_cases hc : c = 0
  · subst c
    simp
  · let q : ℂ := s * (c : ℂ) ^ 2
    let x : ℝ := w / c
    have hq : q.re < 1 / 2 := by
      have hcre : ((c : ℂ) ^ 2).re = c ^ 2 := by
        norm_num [pow_two, Complex.mul_re]
      have hcim : ((c : ℂ) ^ 2).im = 0 := by
        norm_num [pow_two, Complex.mul_im]
      dsimp [q]
      rw [Complex.mul_re, hcre, hcim]
      simp only [mul_zero, sub_zero]
      nlinarith
    have harg (z : ℝ) :
        complexQuadraticExp q (x + z) =
          complexQuadraticExp s (w + c * z) := by
      unfold complexQuadraticExp
      congr 1
      dsimp [q, x]
      push_cast
      field_simp [hc]
    have hfun : (fun z : ℝ => complexQuadraticExp q (x + z)) =
        fun z : ℝ => complexQuadraticExp s (w + c * z) :=
      funext harg
    have hderiv (t : ℝ) :
        iteratedDeriv 4 (complexQuadraticExp q) (x + t) =
          c ^ 4 • iteratedDeriv 4 (complexQuadraticExp s) (w + c * t) := by
      have htranslate := congrFun
        (iteratedDeriv_comp_const_add 4 (complexQuadraticExp q) x) t
      have hfunctions := congrArg (iteratedDeriv 4) hfun
      calc
        iteratedDeriv 4 (complexQuadraticExp q) (x + t) =
            iteratedDeriv 4 (fun z : ℝ =>
              complexQuadraticExp q (x + z)) t := htranslate.symm
        _ = iteratedDeriv 4 (fun z : ℝ =>
              complexQuadraticExp s (w + c * z)) t := by rw [hfunctions]
        _ = c ^ 4 • iteratedDeriv 4 (complexQuadraticExp s) (w + c * t) :=
          iteratedDeriv_four_scaled_complexQuadraticExp s w c t
    have hidentity :=
      peanoIdentity4_standardGaussianRademacher_complexQuadraticExp_of_re_lt_half
        hq x
    simpa only [harg, hderiv] using hidentity

/-- The scaled fourth-Peano replacement written directly as expectation under
the K probability measure. -/
theorem peanoIdentity4_standardGaussianRademacher_scaled_complexQuadraticExp_peanoK
    {s : ℂ} (w c : ℝ) (hscale : 2 * c ^ 2 * s.re < 1) :
    (∫ y : ℝ, complexQuadraticExp s (w + c * y) ∂(gaussianReal 0 1)) -
        ∫ y : ℝ, complexQuadraticExp s (w + c * y)
          ∂standardRademacherMeasure =
      (c ^ 4 / 12 : ℝ) •
        ∫ k : ℝ, iteratedDeriv 4 (complexQuadraticExp s) (w + c * k)
          ∂peanoKMeasure := by
  rw [peanoIdentity4_standardGaussianRademacher_scaled_complexQuadraticExp
    w c hscale]
  unfold peanoKMeasure
  rw [integral_positiveDensityMeasure peanoKDensity
    stronglyMeasurable_peanoKDensity.measurable peanoKDensity_nonneg]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [peanoKDensity_eq_two_mul_cubicStopLossDifference]
  simp only [smul_smul]
  ring_nf

/-- Integrating the scaled fourth-Peano replacement over an independent
partial-sum law. -/
theorem peanoIdentity4_partialSum_standardGaussianRademacher_scaled
    {rho : Measure ℝ} {s : ℂ} (c : ℝ)
    (hscale : 2 * c ^ 2 * s.re < 1)
    (hG : Integrable (fun w =>
      ∫ y : ℝ, complexQuadraticExp s (w + c * y) ∂(gaussianReal 0 1)) rho)
    (hR : Integrable (fun w =>
      ∫ y : ℝ, complexQuadraticExp s (w + c * y)
        ∂standardRademacherMeasure) rho) :
    (∫ w, ∫ y : ℝ, complexQuadraticExp s (w + c * y)
        ∂(gaussianReal 0 1) ∂rho) -
      ∫ w, ∫ y : ℝ, complexQuadraticExp s (w + c * y)
        ∂standardRademacherMeasure ∂rho =
      (c ^ 4 / 12 : ℝ) •
        ∫ w, ∫ k : ℝ, iteratedDeriv 4 (complexQuadraticExp s) (w + c * k)
          ∂peanoKMeasure ∂rho := by
  rw [← integral_sub hG hR]
  calc
    _ = ∫ w, (c ^ 4 / 12 : ℝ) •
          ∫ k : ℝ, iteratedDeriv 4 (complexQuadraticExp s) (w + c * k)
            ∂peanoKMeasure ∂rho := by
      apply integral_congr_ae
      exact ae_of_all rho fun w =>
        peanoIdentity4_standardGaussianRademacher_scaled_complexQuadraticExp_peanoK
          w c hscale
    _ = _ := by rw [integral_smul]

/-- The derivative-offset fourth-Peano replacement lifted over an independent
partial-sum law.  This is the exact D4-to-D8 coordinate step in U7. -/
theorem peanoIdentity4_partialSum_standardGaussianRademacher_scaled_iteratedDeriv_four
    {rho : Measure ℝ} {s : ℂ} (c : ℝ)
    (hscale : 2 * c ^ 2 * s.re < 1)
    (hG : Integrable (fun w => ∫ y : ℝ,
      iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
        ∂gaussianReal 0 1) rho)
    (hR : Integrable (fun w => ∫ y : ℝ,
      iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
        ∂standardRademacherMeasure) rho) :
    (∫ w, ∫ y : ℝ, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
        ∂gaussianReal 0 1 ∂rho) -
      ∫ w, ∫ y : ℝ, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
        ∂standardRademacherMeasure ∂rho =
      (c ^ 4 / 12 : ℝ) • ∫ w, ∫ k : ℝ,
        iteratedDeriv 8 (complexQuadraticExp s) (w + c * k)
          ∂peanoKMeasure ∂rho := by
  rw [← integral_sub hG hR]
  calc
    _ = ∫ w, (c ^ 4 / 12 : ℝ) • ∫ k : ℝ,
          iteratedDeriv 8 (complexQuadraticExp s) (w + c * k)
            ∂peanoKMeasure ∂rho := by
      apply integral_congr_ae
      exact ae_of_all rho fun w =>
        peanoIdentity4_standardGaussianRademacher_scaled_iteratedDeriv_four_complexQuadraticExp
          w c hscale
    _ = _ := by rw [integral_smul]

end CertifiedJL
