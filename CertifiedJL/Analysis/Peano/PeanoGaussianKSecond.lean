/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Peano.PeanoGaussianRademacherScaled
import CertifiedJL.Analysis.Peano.PeanoQuadraticExpSecond

/-!
# Noncompact Gaussian--K second-Peano replacement
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace CertifiedJL

private theorem integrable_abs_evenPow_mul_exp_sq_of_gaussianDomination_one
    {μ : Measure ℝ} {mass : ℝ}
    (hμ : GaussianEvenMomentDomination μ mass 1)
    (ell : ℕ) {lambda : ℝ} (hlambda0 : 0 ≤ lambda)
    (hlambdaHalf : lambda < 1 / 2) :
    Integrable (fun x : ℝ =>
      |x| ^ (2 * ell) * Real.exp (lambda * x ^ 2)) μ := by
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
  have hscaled := hμ.map_const_mul c
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

private theorem integrable_absPow_mul_exp_sq_of_gaussianDomination_one
    {μ : Measure ℝ} {mass : ℝ}
    (hμ : GaussianEvenMomentDomination μ mass 1)
    (m : ℕ) {lambda : ℝ} (hlambda0 : 0 ≤ lambda)
    (hlambdaHalf : lambda < 1 / 2) :
    Integrable (fun t : ℝ => |t| ^ m * Real.exp (lambda * t ^ 2)) μ := by
  have h0 := integrable_abs_evenPow_mul_exp_sq_of_gaussianDomination_one
    hμ 0 hlambda0 hlambdaHalf
  have h2m := integrable_abs_evenPow_mul_exp_sq_of_gaussianDomination_one
    hμ m hlambda0 hlambdaHalf
  refine Integrable.mono' (h0.add h2m) (by fun_prop) ?_
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (pow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le)]
  have hpow : |t| ^ m ≤ 1 + |t| ^ (2 * m) := by
    by_cases ht : |t| ≤ 1
    · exact (pow_le_one₀ (abs_nonneg _) ht).trans
        (le_add_of_nonneg_right (pow_nonneg (abs_nonneg _) _))
    · exact (pow_le_pow_right₀ (le_of_not_ge ht) (by omega : m ≤ 2 * m)).trans
        (le_add_of_nonneg_left (by norm_num))
  calc
    |t| ^ m * Real.exp (lambda * t ^ 2) ≤
        (1 + |t| ^ (2 * m)) * Real.exp (lambda * t ^ 2) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = |t| ^ (2 * 0) * Real.exp (lambda * t ^ 2) +
        |t| ^ (2 * m) * Real.exp (lambda * t ^ 2) := by ring

private theorem integrable_shifted_absPow_mul_exp_sq_of_gaussianDomination_one
    {μ : Measure ℝ} {mass : ℝ}
    (hμ : GaussianEvenMomentDomination μ mass 1)
    (m : ℕ) (x : ℝ) {a : ℝ} (ha0 : 0 ≤ a) (haHalf : a < 1 / 2) :
    Integrable (fun t : ℝ => |x + t| ^ m * Real.exp (a * (x + t) ^ 2)) μ := by
  let lambda : ℝ := (a + 1 / 2) / 2
  let delta : ℝ := lambda - a
  let C : ℝ := a * x ^ 2 + (a * x) ^ 2 / delta
  have hlambda0 : 0 ≤ lambda := by dsimp [lambda]; linarith
  have hlambdaHalf : lambda < 1 / 2 := by dsimp [lambda]; linarith
  have hdelta : 0 < delta := by dsimp [delta, lambda]; linarith
  have hk (k : ℕ) : Integrable (fun t : ℝ =>
      |t| ^ k * Real.exp (lambda * t ^ 2)) μ :=
    integrable_absPow_mul_exp_sq_of_gaussianDomination_one
      hμ k hlambda0 hlambdaHalf
  have hsum : Integrable (fun t : ℝ => Real.exp C *
      ∑ k ∈ Finset.range (m + 1), Nat.choose m k * |x| ^ k *
        (|t| ^ (m - k) * Real.exp (lambda * t ^ 2))) μ := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro k hk_mem
    exact (hk (m - k)).const_mul (Nat.choose m k * |x| ^ k)
  refine Integrable.mono' hsum (by fun_prop) ?_
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (pow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le)]
  have hyoung : 2 * a * x * t ≤ delta * t ^ 2 + (a * x) ^ 2 / delta := by
    rw [show delta * t ^ 2 + (a * x) ^ 2 / delta =
        (delta ^ 2 * t ^ 2 + (a * x) ^ 2) / delta by
      field_simp [hdelta.ne']
      ]
    rw [le_div_iff₀ hdelta]
    nlinarith [sq_nonneg (delta * t - a * x)]
  have hquad : a * (x + t) ^ 2 ≤ C + lambda * t ^ 2 := by
    dsimp [C, delta] at hyoung ⊢
    nlinarith
  have hexp : Real.exp (a * (x + t) ^ 2) ≤
      Real.exp C * Real.exp (lambda * t ^ 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hquad
  have habs : |x + t| ≤ |x| + |t| := abs_add_le x t
  have hpow : |x + t| ^ m ≤ (|x| + |t|) ^ m :=
    pow_le_pow_left₀ (abs_nonneg _) habs m
  calc
    |x + t| ^ m * Real.exp (a * (x + t) ^ 2) ≤
        (|x| + |t|) ^ m *
          (Real.exp C * Real.exp (lambda * t ^ 2)) := by
      exact mul_le_mul hpow hexp (Real.exp_pos _).le
        (pow_nonneg (add_nonneg (abs_nonneg x) (abs_nonneg t)) _)
    _ = Real.exp C * ∑ k ∈ Finset.range (m + 1),
        Nat.choose m k * |x| ^ k *
          (|t| ^ (m - k) * Real.exp (lambda * t ^ 2)) := by
      rw [add_pow, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk_mem
      ring

private theorem integrable_firstStopLossDifference_mul_norm_iteratedDeriv
    {q : ℂ} {x : ℝ} (hq0 : 0 ≤ q.re) (hq : q.re < 1 / 2) (j : ℕ) :
    Integrable (fun t : ℝ =>
      firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t *
        ‖iteratedDeriv j (complexQuadraticExp q) (x + t)‖) volume := by
  let p := complexQuadraticExpDerivativePolynomial q j
  have hmono (n : ℕ) : Integrable (fun t : ℝ =>
      ‖p.coeff n‖ * (|x + t| ^ n * Real.exp (q.re * (x + t) ^ 2)))
      peanoKStopLossMeasure :=
    (integrable_shifted_absPow_mul_exp_sq_of_gaussianDomination_one
      peanoK_positiveStopLossMomentDomination.domination n x hq0 hq).const_mul _
  have hsum : Integrable (fun t : ℝ =>
      ∑ n ∈ p.support, ‖p.coeff n‖ *
        (|x + t| ^ n * Real.exp (q.re * (x + t) ^ 2)))
      peanoKStopLossMeasure := by
    apply integrable_finsetSum
    intro n hn
    exact hmono n
  have hderiv : Integrable (fun t : ℝ =>
      ‖iteratedDeriv j (complexQuadraticExp q) (x + t)‖)
      peanoKStopLossMeasure := by
    have hfun : (fun t : ℝ => iteratedDeriv j
        (complexQuadraticExp q) (x + t)) = fun t : ℝ =>
        p.eval ((x + t : ℝ) : ℂ) * complexQuadraticExp q (x + t) := by
      funext t
      exact iteratedDeriv_complexQuadraticExp j q (x + t)
    have hcont : Continuous (fun t : ℝ => iteratedDeriv j
        (complexQuadraticExp q) (x + t)) := by
      rw [hfun]
      have hp : Continuous (fun t : ℝ => p.eval ((x + t : ℝ) : ℂ)) := by
        fun_prop
      have he : Continuous (fun t : ℝ => complexQuadraticExp q (x + t)) :=
        (contDiff_complexQuadraticExp q).continuous.comp
          (continuous_const.add continuous_id)
      exact hp.mul he
    refine Integrable.mono' hsum hcont.norm.aestronglyMeasurable ?_
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [iteratedDeriv_complexQuadraticExp, Polynomial.eval_eq_sum,
      Polynomial.sum_def, Finset.sum_mul]
    calc
      ‖∑ n ∈ p.support, p.coeff n * (((x + t : ℝ) : ℂ) ^ n) *
          complexQuadraticExp q (x + t)‖ ≤
        ∑ n ∈ p.support, ‖p.coeff n * (((x + t : ℝ) : ℂ) ^ n) *
          complexQuadraticExp q (x + t)‖ := norm_sum_le _ _
      _ = ∑ n ∈ p.support, ‖p.coeff n‖ *
          (|x + t| ^ n * Real.exp (q.re * (x + t) ^ 2)) := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          complexQuadraticExp, Complex.norm_exp]
        have hexp : (q * (((x + t : ℝ) : ℂ) ^ 2)).re =
            q.re * (x + t) ^ 2 := by
          rw [Complex.mul_re]
          norm_num [pow_two, Complex.mul_re, Complex.mul_im]
        rw [hexp]
        ring
  unfold peanoKStopLossMeasure positiveDensityMeasure at hderiv
  rw [integrable_withDensity_iff_integrable_smul'
    (stronglyMeasurable_firstStopLossDifference_standardGaussian_peanoKMeasure
      |>.measurable.ennreal_ofReal)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at hderiv
  refine hderiv.congr (ae_of_all _ fun t => ?_)
  change (ENNReal.ofReal
      (firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t)).toReal •
      ‖iteratedDeriv j (complexQuadraticExp q) (x + t)‖ = _
  simp only [ENNReal.toReal_ofReal
    (firstStopLossDifference_standardGaussian_peanoKMeasure_nonneg t), smul_eq_mul]

private theorem integrable_shifted_iteratedDeriv_of_gaussianDomination_one
    {μ : Measure ℝ} {mass : ℝ}
    (hμ : GaussianEvenMomentDomination μ mass 1)
    {q : ℂ} {x : ℝ} (hq0 : 0 ≤ q.re) (hq : q.re < 1 / 2) (j : ℕ) :
    Integrable (fun t : ℝ =>
      iteratedDeriv j (complexQuadraticExp q) (x + t)) μ := by
  let p := complexQuadraticExpDerivativePolynomial q j
  have hsum : Integrable (fun t : ℝ =>
      ∑ n ∈ p.support, ‖p.coeff n‖ *
        (|x + t| ^ n * Real.exp (q.re * (x + t) ^ 2))) μ := by
    apply integrable_finsetSum
    intro n hn
    exact (integrable_shifted_absPow_mul_exp_sq_of_gaussianDomination_one
      hμ n x hq0 hq).const_mul _
  have hcont : Continuous (fun t : ℝ => iteratedDeriv j
      (complexQuadraticExp q) (x + t)) := by
    have hfun : (fun t : ℝ => iteratedDeriv j
        (complexQuadraticExp q) (x + t)) = fun t : ℝ =>
        p.eval ((x + t : ℝ) : ℂ) * complexQuadraticExp q (x + t) := by
      funext t
      exact iteratedDeriv_complexQuadraticExp j q (x + t)
    rw [hfun]
    have hp : Continuous (fun t : ℝ => p.eval ((x + t : ℝ) : ℂ)) := by
      fun_prop
    have he : Continuous (fun t : ℝ => complexQuadraticExp q (x + t)) :=
      (contDiff_complexQuadraticExp q).continuous.comp
        (continuous_const.add continuous_id)
    exact hp.mul he
  refine Integrable.mono' hsum hcont.aestronglyMeasurable ?_
  filter_upwards [] with t
  rw [iteratedDeriv_complexQuadraticExp, Polynomial.eval_eq_sum,
    Polynomial.sum_def, Finset.sum_mul]
  calc
    ‖∑ n ∈ p.support, p.coeff n * (((x + t : ℝ) : ℂ) ^ n) *
        complexQuadraticExp q (x + t)‖ ≤
      ∑ n ∈ p.support, ‖p.coeff n * (((x + t : ℝ) : ℂ) ^ n) *
        complexQuadraticExp q (x + t)‖ := norm_sum_le _ _
    _ = ∑ n ∈ p.support, ‖p.coeff n‖ *
        (|x + t| ^ n * Real.exp (q.re * (x + t) ^ 2)) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        complexQuadraticExp, Complex.norm_exp]
      have hexp : (q * (((x + t : ℝ) : ℂ) ^ 2)).re =
          q.re * (x + t) ^ 2 := by
        rw [Complex.mul_re]
        norm_num [pow_two, Complex.mul_re, Complex.mul_im]
      rw [hexp]
      ring

private noncomputable def secondPeanoMajorant
    (C : ℕ → ℝ) (q : ℂ) (x t : ℝ) : ℝ :=
  firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t *
    ∑ i ∈ Finset.range (2 + 1), Nat.choose 2 i * C i *
      ‖iteratedDeriv (6 - i) (complexQuadraticExp q) (x + t)‖

private theorem secondPeanoMajorant_exists
    {q : ℂ} {x : ℝ} (hq0 : 0 ≤ q.re) (hq : q.re < 1 / 2) :
    ∃ C : ℕ → ℝ, Integrable (secondPeanoMajorant C q x) volume ∧
      ∀ n t, ‖firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t •
        iteratedDeriv 2 (upperCutoffProduct n
          (iteratedDeriv 4 (complexQuadraticExp q)) x) (x + t)‖ ≤
        secondPeanoMajorant C q x t := by
  choose C hC using fun i => upperCutoff_iteratedDeriv_bound i
  have hC0 (i : ℕ) : 0 ≤ C i := by
    have hpos : 0 < (upperCutoffRadius 0)⁻¹ ^ i :=
      pow_pos (inv_pos.mpr (upperCutoffRadius_pos 0)) i
    exact nonneg_of_mul_nonneg_left
      ((norm_nonneg _).trans (hC i 0 0)) hpos
  refine ⟨C, ?_, ?_⟩
  · unfold secondPeanoMajorant
    have hsum : Integrable (fun t : ℝ =>
        ∑ i ∈ Finset.range (2 + 1),
          firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t *
            (Nat.choose 2 i * C i *
              ‖iteratedDeriv (6 - i) (complexQuadraticExp q) (x + t)‖))
        volume := by
      apply integrable_finsetSum
      intro i hi
      have hterm := (integrable_firstStopLossDifference_mul_norm_iteratedDeriv
        (x := x) hq0 hq (6 - i)).const_mul (Nat.choose 2 i * C i)
      refine hterm.congr (ae_of_all _ fun t => ?_)
      ring
    simpa only [Finset.mul_sum, mul_assoc] using hsum
  · intro n t
    let f : ℝ → ℂ := iteratedDeriv 4 (complexQuadraticExp q)
    have hf : ContDiff ℝ 2 f :=
      contDiff_two_iteratedDeriv_four_complexQuadraticExp q
    have hshift (i : ℕ) :
        iteratedDeriv i (fun w : ℝ => upperCutoff n (w - x)) (x + t) =
          iteratedDeriv i (upperCutoff n) t := by
      have h := congrFun (iteratedDeriv_comp_sub_const i (upperCutoff n) x) (x + t)
      simpa only [add_sub_cancel_left] using h
    have hcut (i : ℕ) : ‖iteratedDeriv i (upperCutoff n) t‖ ≤ C i := by
      calc
        _ ≤ C i * (upperCutoffRadius n)⁻¹ ^ i := hC i n t
        _ ≤ C i * 1 :=
          mul_le_mul_of_nonneg_left
            (pow_le_one₀ (inv_pos.mpr (upperCutoffRadius_pos n)).le
              (inv_le_one_of_one_le₀
                (show (1 : ℝ) ≤ upperCutoffRadius n by simp [upperCutoffRadius])))
            (hC0 i)
        _ = C i := mul_one _
    rw [upperCutoffProduct_iteratedDeriv_two hf n x (x + t)]
    rw [secondPeanoMajorant, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (firstStopLossDifference_standardGaussian_peanoKMeasure_nonneg t)]
    apply mul_le_mul_of_nonneg_left
    · calc
        ‖∑ i ∈ Finset.range (2 + 1),
            Nat.choose 2 i •
              iteratedDeriv i (fun w : ℝ => upperCutoff n (w - x)) (x + t) •
              iteratedDeriv (2 - i) f (x + t)‖ ≤
          ∑ i ∈ Finset.range (2 + 1), ‖Nat.choose 2 i •
              iteratedDeriv i (fun w : ℝ => upperCutoff n (w - x)) (x + t) •
              iteratedDeriv (2 - i) f (x + t)‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range (2 + 1), Nat.choose 2 i * C i *
            ‖iteratedDeriv (6 - i) (complexQuadraticExp q) (x + t)‖ := by
          apply Finset.sum_le_sum
          intro i hi
          have hi2 : i ≤ 2 := by
            have := Finset.mem_range.mp hi
            omega
          rw [hshift]
          simp only [nsmul_eq_mul, norm_smul, norm_mul, norm_natCast,
            Real.norm_eq_abs]
          rw [show iteratedDeriv (2 - i) f =
              iteratedDeriv (4 + (2 - i)) (complexQuadraticExp q) by
            exact iteratedDeriv_iteratedDeriv_add 4 (2 - i)
              (complexQuadraticExp q)]
          rw [show 4 + (2 - i) = 6 - i by omega]
          rw [← Real.norm_eq_abs]
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hcut i)
                (Nat.cast_nonneg (Nat.choose 2 i)))
              (norm_nonneg
                (iteratedDeriv (6 - i) (complexQuadraticExp q) (x + t)))
    · exact firstStopLossDifference_standardGaussian_peanoKMeasure_nonneg t

private theorem secondPeano_compactKernelData
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (habs : Integrable (fun y : ℝ => |y|) μ)
    {D : ℝ → ℂ} (hD : Continuous D) (hDc : HasCompactSupport D) :
    Integrable (Function.uncurry (fun t y : ℝ =>
      max (y - t) 0 • D t)) (volume.prod μ) ∧
    Integrable (fun t : ℝ =>
      (∫ y, max (y - t) 0 ∂μ) • D t) volume := by
  have hDnorm : Integrable (fun t : ℝ => ‖D t‖) volume :=
    hD.norm.integrable_of_hasCompactSupport hDc.norm
  have htD : Integrable (fun t : ℝ => |t| * ‖D t‖) volume := by
    apply ((continuous_abs.mul hD.norm).integrable_of_hasCompactSupport)
    exact hDc.norm.mul_left
  have hmajor : Integrable (fun p : ℝ × ℝ =>
      ‖D p.1‖ * |p.2| + (|p.1| * ‖D p.1‖) * 1) (volume.prod μ) :=
    (hDnorm.mul_prod habs).add (htD.mul_prod (integrable_const 1))
  have hkernel : Integrable (Function.uncurry (fun t y : ℝ =>
      max (y - t) 0 • D t)) (volume.prod μ) := by
    refine Integrable.mono' hmajor (by fun_prop) ?_
    filter_upwards [] with p
    rw [Function.uncurry_apply_pair, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (le_max_right _ _)]
    have hstop : max (p.2 - p.1) 0 ≤ |p.2| + |p.1| := by
      apply max_le
      · linarith [le_abs_self p.2, neg_le_abs p.1]
      · positivity
    calc
      max (p.2 - p.1) 0 * ‖D p.1‖ ≤
          (|p.2| + |p.1|) * ‖D p.1‖ := by gcongr
      _ = ‖D p.1‖ * |p.2| + (|p.1| * ‖D p.1‖) * 1 := by ring
  refine ⟨hkernel, ?_⟩
  have hleft := hkernel.integral_prod_left
  refine hleft.congr (ae_of_all _ fun t => ?_)
  exact integral_smul_const (fun y : ℝ => max (y - t) 0) (D t)

/-- The exact second-Peano replacement from the standard Gaussian law to the
Peano K law for the fourth derivative of the quadratic exponential. -/
theorem peanoIdentity2_standardGaussian_peanoK_iteratedDeriv_four
    {q : ℂ} (hq0 : 0 ≤ q.re) (hq : q.re < 1 / 2) (x : ℝ) :
    (∫ y, iteratedDeriv 4 (complexQuadraticExp q) (x + y)
        ∂gaussianReal 0 1) -
      ∫ y, iteratedDeriv 4 (complexQuadraticExp q) (x + y)
        ∂peanoKMeasure =
      ∫ t, firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t •
        iteratedDeriv 6 (complexQuadraticExp q) (x + t) := by
  let f : ℝ → ℂ := iteratedDeriv 4 (complexQuadraticExp q)
  have hf : ContDiff ℝ 2 f :=
    contDiff_two_iteratedDeriv_four_complexQuadraticExp q
  have hGf : Integrable (fun y => f (x + y)) (gaussianReal 0 1) := by
    dsimp [f]
    exact integrable_gaussianReal_shifted_iteratedDeriv_four_complexQuadraticExp
      (v := 1) (by norm_num) (by simpa using hq)
  have hKf : Integrable (fun y => f (x + y)) peanoKMeasure := by
    dsimp [f]
    exact integrable_shifted_iteratedDeriv_of_gaussianDomination_one
      peanoK_evenMomentDomination hq0 hq 4
  have hcompact (n : ℕ) : HasCompactSupport (fun t : ℝ =>
      iteratedDeriv 2 (upperCutoffProduct n f x) (x + t)) := by
    simpa [iteratedDeriv_succ, iteratedDeriv_zero, Function.comp_def] using
      ((upperCutoffProduct_hasCompactSupport n f x).deriv.deriv
        |>.comp_isClosedEmbedding (Homeomorph.addLeft x).isClosedEmbedding)
  have hcontinuous (n : ℕ) : Continuous (fun t : ℝ =>
      iteratedDeriv 2 (upperCutoffProduct n f x) (x + t)) :=
    ((upperCutoffProduct_contDiff hf n x).continuous_iteratedDeriv' 2).comp
      (continuous_const.add continuous_id)
  have hGabs : Integrable (fun y : ℝ => |y|) (gaussianReal 0 1) := by
    simpa only [Real.norm_eq_abs, norm_pow, pow_one] using
      (integrable_standardGaussian_pow 1).norm
  have hKabs : Integrable (fun y : ℝ => |y|) peanoKMeasure := by
    simpa only [pow_one] using integrable_absPow_peanoKMeasure 1
  have hGdata (n : ℕ) := secondPeano_compactKernelData hGabs
    (hcontinuous n) (hcompact n)
  have hKdata (n : ℕ) := secondPeano_compactKernelData hKabs
    (hcontinuous n) (hcompact n)
  obtain ⟨C, hMint, hbound⟩ := secondPeanoMajorant_exists (x := x) hq0 hq
  exact peanoIdentity2_iteratedDeriv_four_complexQuadraticExp q x hGf hKf
    (fun n => (hGdata n).1) (fun n => (hKdata n).1)
    (fun n => (hGdata n).2) (fun n => (hKdata n).2)
    stronglyMeasurable_firstStopLossDifference_standardGaussian_peanoKMeasure
    (secondPeanoMajorant C q x) hMint hbound

/-- The scaled Gaussian-to-K second-Peano identity needed for each sparse-row
coordinate. -/
theorem peanoIdentity2_standardGaussian_peanoK_scaled_iteratedDeriv_four
    {s : ℂ} (w c : ℝ) (hs0 : 0 ≤ s.re)
    (hscale : 2 * c ^ 2 * s.re < 1) :
    (∫ y : ℝ, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
        ∂gaussianReal 0 1) -
      ∫ y : ℝ, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
        ∂peanoKMeasure =
      c ^ 2 • ∫ t : ℝ,
        firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t •
          iteratedDeriv 6 (complexQuadraticExp s) (w + c * t) := by
  by_cases hc : c = 0
  · subst c
    simp
  · let q : ℂ := s * (c : ℂ) ^ 2
    let x : ℝ := w / c
    have hcre : ((c : ℂ) ^ 2).re = c ^ 2 := by
      norm_num [pow_two, Complex.mul_re]
    have hcim : ((c : ℂ) ^ 2).im = 0 := by
      norm_num [pow_two, Complex.mul_im]
    have hq0 : 0 ≤ q.re := by
      dsimp [q]
      rw [Complex.mul_re, hcre, hcim]
      simp only [mul_zero, sub_zero]
      positivity
    have hq : q.re < 1 / 2 := by
      dsimp [q]
      rw [Complex.mul_re, hcre, hcim]
      simp only [mul_zero, sub_zero]
      nlinarith
    have harg (z : ℝ) : complexQuadraticExp q (x + z) =
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
    have hD6 (z : ℝ) :
        iteratedDeriv 6 (complexQuadraticExp q) (x + z) =
          c ^ 6 • iteratedDeriv 6 (complexQuadraticExp s) (w + c * z) := by
      rw [iteratedDeriv_six_complexQuadraticExp,
        iteratedDeriv_six_complexQuadraticExp, harg]
      dsimp [q, x]
      push_cast
      field_simp [hc]
    have hbase :=
      peanoIdentity2_standardGaussian_peanoK_iteratedDeriv_four hq0 hq x
    have hleft :
        (∫ y : ℝ, iteratedDeriv 4 (complexQuadraticExp q) (x + y)
            ∂gaussianReal 0 1) -
          ∫ y : ℝ, iteratedDeriv 4 (complexQuadraticExp q) (x + y)
            ∂peanoKMeasure =
        c ^ 4 • ((∫ y : ℝ, iteratedDeriv 4 (complexQuadraticExp s)
              (w + c * y) ∂gaussianReal 0 1) -
            ∫ y : ℝ, iteratedDeriv 4 (complexQuadraticExp s)
              (w + c * y) ∂peanoKMeasure) := by
      rw [smul_sub, ← integral_smul, ← integral_smul]
      congr 1 <;> apply integral_congr_ae <;> exact ae_of_all _ hD4
    have hright :
        (∫ t : ℝ, firstStopLossDifference (gaussianReal 0 1)
            peanoKMeasure t • iteratedDeriv 6 (complexQuadraticExp q) (x + t)) =
          c ^ 6 • ∫ t : ℝ, firstStopLossDifference (gaussianReal 0 1)
            peanoKMeasure t •
              iteratedDeriv 6 (complexQuadraticExp s) (w + c * t) := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hD6]
      simp only [smul_smul]
      congr 1
      ring
    rw [hleft, hright] at hbase
    have hc4 : ((c ^ 4 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast pow_ne_zero 4 hc
    apply mul_left_cancel₀ hc4
    change (c ^ 4 : ℝ) •
        ((∫ y : ℝ, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
            ∂gaussianReal 0 1) -
          ∫ y : ℝ, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
            ∂peanoKMeasure) =
      (c ^ 4 : ℝ) • (c ^ 2 • ∫ t : ℝ,
        firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t •
          iteratedDeriv 6 (complexQuadraticExp s) (w + c * t))
    calc
      _ = (c ^ 6 : ℝ) • ∫ t : ℝ,
          firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t •
            iteratedDeriv 6 (complexQuadraticExp s) (w + c * t) := hbase
      _ = _ := by
        rw [smul_smul]
        congr 1
        ring

/-- The Gaussian-to-K U3b estimate with the analytic replacement produced
internally, rather than supplied as a restated lifted premise. -/
theorem norm_partialSum_secondPeanoDifference_standardGaussian_peanoKMeasure_le_unconditional
    {ρ : Measure ℝ} {varianceW : NNReal}
    (s : ℂ) (c : ℝ)
    (hG : Integrable (fun w =>
      ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
        ∂gaussianReal 0 1) ρ)
    (hK : Integrable (fun w =>
      ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
        ∂peanoKMeasure) ρ)
    (hW : GaussianEvenMomentDomination ρ 1 varianceW)
    (hvariance : varianceW + scaledVariance c 1 ≤ (2 : NNReal)⁻¹)
    (hs_nonneg : 0 ≤ s.re) (hs_lt_one : s.re < 1)
    (hscale : 2 * c ^ 2 * s.re < 1) :
    ‖(∫ w, ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
          ∂gaussianReal 0 1 ∂ρ) -
        ∫ w, ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
          ∂peanoKMeasure ∂ρ‖ ≤
      (11 / 15 : ℝ) * c ^ 2 *
        quadraticExpDerivativeMajorant 6 ‖s‖ s.re := by
  apply norm_partialSum_secondPeanoDifference_standardGaussian_peanoKMeasure_le
    s c
  · apply peanoIdentity2_partialSum_scaled_iteratedDeriv_four_complexQuadraticExp
      s c hG hK
    intro w
    rw [peanoIdentity2_standardGaussian_peanoK_scaled_iteratedDeriv_four
      w c hs_nonneg hscale]
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [smul_smul]
    congr 1
    ring
  · exact hW
  · exact hvariance
  · exact hs_nonneg
  · exact hs_lt_one

end CertifiedJL
