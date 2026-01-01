/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import CertifiedJL.Analysis.Peano.PeanoGaussianRademacher

/-!
# Compact Peano cutoff kernel data

This module owns the product-kernel and integrated-kernel facts for compactly
supported cutoff derivatives.  It depends only on the concrete laws and
cutoff layer; the noncompact Gaussian--Rademacher majorants live above it.
-/

open MeasureTheory Set Filter
open ProbabilityTheory
open scoped Topology

namespace CertifiedJL

private theorem integrable_cubicStopLoss_kernel_of_compact_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure ℝ} [SFinite μ]
    {D : ℝ → E}
    (hstop : ∀ t : ℝ,
      Integrable (fun y : ℝ => (max (y - t) 0) ^ 3) μ)
    (henv : Integrable (fun y : ℝ => (1 + |y|) ^ 3) μ)
    (hDcont : Continuous D)
    (hDcompact : HasCompactSupport D) :
    Integrable
      (Function.uncurry (fun t y : ℝ =>
        ((1 / 6 : ℝ) * (max (y - t) 0) ^ 3) • D t))
      (volume.prod μ) := by
  let F : ℝ × ℝ → E := fun p =>
    ((1 / 6 : ℝ) * (max (p.2 - p.1) 0) ^ 3) • D p.1
  have hFcont : Continuous F := by
    have hscalar : Continuous (fun p : ℝ × ℝ =>
        (1 / 6 : ℝ) * (max (p.2 - p.1) 0) ^ 3) := by
      fun_prop
    have hDprod : Continuous (fun p : ℝ × ℝ => D p.1) :=
      hDcont.comp continuous_fst
    exact hscalar.smul hDprod
  have hFstrong : StronglyMeasurable F := hFcont.stronglyMeasurable
  have hweight : Integrable
      (fun t : ℝ => (1 + |t|) ^ 3 * ‖D t‖) volume := by
    have hweight_cont : Continuous
        (fun t : ℝ => (1 + |t|) ^ 3 * ‖D t‖) := by
      fun_prop
    apply hweight_cont.integrable_of_hasCompactSupport
    exact hDcompact.norm.mul_left
  have hinner : Integrable (fun t : ℝ => ∫ y, ‖F (t, y)‖ ∂μ) volume := by
    let C : ℝ := ∫ y, (1 + |y|) ^ 3 ∂μ
    have hmajor := hweight.const_mul (1 / 6 * C)
    refine Integrable.mono'
      (f := fun t : ℝ => ∫ y, ‖F (t, y)‖ ∂μ)
      (g := fun t : ℝ => (1 / 6 * C) *
        ((1 + |t|) ^ 3 * ‖D t‖)) hmajor ?_ ?_
    · exact (hFstrong.norm.integral_prod_right').aestronglyMeasurable
    · filter_upwards [] with t
      have hpoint (y : ℝ) :
          (max (y - t) 0) ^ 3 ≤
            (1 + |t|) ^ 3 * (1 + |y|) ^ 3 := by
        have hy : 0 ≤ |y| := abs_nonneg y
        have ht : 0 ≤ |t| := abs_nonneg t
        have hmax : max (y - t) 0 ≤
            (1 + |t|) * (1 + |y|) := by
          apply max_le
          · nlinarith [le_abs_self y, neg_le_abs t]
          · positivity
        exact (pow_le_pow_left₀ (le_max_right _ _) hmax 3).trans_eq
          (by ring_nf)
      have hstop_bound :
          (∫ y, (max (y - t) 0) ^ 3 ∂μ) ≤
            (∫ y, (1 + |y|) ^ 3 ∂μ) * (1 + |t|) ^ 3 := by
        have hscale : Integrable
            (fun y : ℝ => (1 + |t|) ^ 3 * (1 + |y|) ^ 3) μ :=
          henv.const_mul ((1 + |t|) ^ 3)
        have hmono := integral_mono_ae (hstop t) hscale
          (ae_of_all μ (fun y => hpoint y))
        simpa [integral_const_mul, mul_comm] using hmono
      have hnorm :
          (∫ y, ‖F (t, y)‖ ∂μ) =
            ((1 / 6 : ℝ) *
              (∫ y, (max (y - t) 0) ^ 3 ∂μ)) * ‖D t‖ := by
        calc
          (∫ y, ‖F (t, y)‖ ∂μ) =
              ∫ y, ((1 / 6 : ℝ) * (max (y - t) 0) ^ 3) *
                ‖D t‖ ∂μ := by
            apply integral_congr_ae
            exact Eventually.of_forall (fun y => by
              dsimp [F]
              rw [norm_smul, Real.norm_eq_abs,
                abs_of_nonneg (by positivity)])
          _ = (∫ y, (1 / 6 : ℝ) * (max (y - t) 0) ^ 3 ∂μ) *
                ‖D t‖ := by
            rw [integral_mul_const]
          _ = ((1 / 6 : ℝ) *
              (∫ y, (max (y - t) 0) ^ 3 ∂μ)) * ‖D t‖ := by
            rw [integral_const_mul]
      rw [hnorm]
      have hstop_nonneg :
          0 ≤ ∫ y, (max (y - t) 0) ^ 3 ∂μ :=
        integral_nonneg_of_ae (ae_of_all μ (fun y => by positivity))
      have hcoef_nonneg :
          0 ≤ (1 / 6 : ℝ) * (∫ y, (max (y - t) 0) ^ 3 ∂μ) :=
        mul_nonneg (by norm_num) hstop_nonneg
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hcoef_nonneg (norm_nonneg _))]
      calc
        ((1 / 6 : ℝ) *
            (∫ y, (max (y - t) 0) ^ 3 ∂μ)) * ‖D t‖ ≤
          (1 / 6 : ℝ) *
            ((∫ y, (1 + |y|) ^ 3 ∂μ) * (1 + |t|) ^ 3) * ‖D t‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hstop_bound (by norm_num))
            (norm_nonneg _)
        _ = (1 / 6 * C) * ((1 + |t|) ^ 3 * ‖D t‖) := by
          dsimp [C]
          ring
  change Integrable F (volume.prod μ)
  rw [integrable_prod_iff hFstrong.aestronglyMeasurable]
  constructor
  · filter_upwards [] with t
    have hs := (hstop t).const_mul (1 / 6 : ℝ)
    simpa [F] using hs.smul_const (D t)
  · exact hinner

private theorem integrable_cubicStopLoss_rhs_of_compact_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure ℝ} [SFinite μ]
    {D : ℝ → E}
    (hKernel : Integrable
      (Function.uncurry (fun t y : ℝ =>
        ((1 / 6 : ℝ) * (max (y - t) 0) ^ 3) • D t))
      (volume.prod μ)) :
    Integrable
      (fun t : ℝ =>
        ((1 / 6 : ℝ) *
          (∫ y, (max (y - t) 0) ^ 3 ∂μ)) • D t) volume := by
  have hleft := hKernel.integral_prod_left
  refine hleft.congr ?_
  exact Filter.Eventually.of_forall (fun t => by
  change (∫ y, ((1 / 6 : ℝ) * (max (y - t) 0) ^ 3) • D t ∂μ) = _
  rw [integral_smul_const, integral_const_mul])

private theorem upperCutoffRemainder_kernel_data
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure ℝ} [SFinite μ]
    {f : ℝ → E} (hf : ContDiff ℝ 4 f)
    (hstop : ∀ t : ℝ,
      Integrable (fun y : ℝ => (max (y - t) 0) ^ 3) μ)
    (henv : Integrable (fun y : ℝ => (1 + |y|) ^ 3) μ)
    (x : ℝ) (n : ℕ) :
    Integrable
        (Function.uncurry (fun t y : ℝ =>
          ((1 / 6 : ℝ) * (max (y - t) 0) ^ 3) •
            deriv (deriv (deriv (deriv (upperCutoffRemainder n f x))))
              (x + t))) (volume.prod μ) ∧
      Integrable (fun t : ℝ =>
        ((1 / 6 : ℝ) *
          (∫ y, (max (y - t) 0) ^ 3 ∂μ)) •
          deriv (deriv (deriv (deriv (upperCutoffRemainder n f x))))
            (x + t)) volume := by
  let D : ℝ → E := fun t => iteratedDeriv 4
    (upperCutoffRemainder n f x) (x + t)
  have hcont : Continuous D := by
    dsimp [D]
    exact ((upperCutoffRemainder_contDiff hf n x).continuous_iteratedDeriv' 4).comp
      (continuous_const.add continuous_id)
  have hcompact : HasCompactSupport D := by
    dsimp [D]
    simpa [iteratedDeriv_succ, iteratedDeriv_zero, Function.comp_def] using
      ((upperCutoffRemainder_hasCompactSupport n f x).deriv.deriv.deriv.deriv
        |>.comp_isClosedEmbedding (Homeomorph.addLeft x).isClosedEmbedding)
  have hkernel := integrable_cubicStopLoss_kernel_of_compact_deriv
    hstop henv hcont hcompact
  have hrhs := integrable_cubicStopLoss_rhs_of_compact_deriv hkernel
  constructor
  · simpa only [D, iteratedDeriv_succ, iteratedDeriv_zero] using hkernel
  · simpa only [D, iteratedDeriv_succ, iteratedDeriv_zero] using hrhs

/-- The concrete Gaussian and two-point Rademacher laws discharge all four
compact-kernel integrability premises for the translated cutoff remainder. -/
theorem upperCutoffRemainder_standardGaussianRademacher_kernel_data
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : ContDiff ℝ 4 f) (x : ℝ) (n : ℕ) :
    (Integrable
        (Function.uncurry (fun t y : ℝ =>
          ((1 / 6 : ℝ) * (max (y - t) 0) ^ 3) •
            deriv (deriv (deriv (deriv (upperCutoffRemainder n f x))))
              (x + t)))
        (volume.prod (gaussianReal 0 1)) ∧
      Integrable
        (fun t : ℝ =>
          ((1 / 6 : ℝ) *
            (∫ y, (max (y - t) 0) ^ 3 ∂(gaussianReal 0 1))) •
            deriv (deriv (deriv (deriv (upperCutoffRemainder n f x))))
              (x + t)) volume) ∧
    (Integrable
        (Function.uncurry (fun t y : ℝ =>
          ((1 / 6 : ℝ) * (max (y - t) 0) ^ 3) •
            deriv (deriv (deriv (deriv (upperCutoffRemainder n f x))))
              (x + t)))
        (volume.prod standardRademacherMeasure) ∧
      Integrable
        (fun t : ℝ =>
          ((1 / 6 : ℝ) *
            (∫ y, (max (y - t) 0) ^ 3 ∂standardRademacherMeasure)) •
            deriv (deriv (deriv (deriv (upperCutoffRemainder n f x))))
              (x + t)) volume) := by
  have hGaussian := upperCutoffRemainder_kernel_data
    (μ := gaussianReal 0 1) hf
    integrable_standardGaussian_cubicStopLoss
    (integrable_one_add_abs_cubic_of_pows
      (integrable_standardGaussian_pow 0)
      (integrable_standardGaussian_pow 1)
      (integrable_standardGaussian_pow 2)
      (integrable_standardGaussian_pow 3)) x n
  have hRademacher := upperCutoffRemainder_kernel_data
    (μ := standardRademacherMeasure) hf
    integrable_standardRademacher_cubicStopLoss
    (integrable_one_add_abs_cubic_of_pows
      (integrable_standardRademacher_pow 0)
      (integrable_standardRademacher_pow 1)
      (integrable_standardRademacher_pow 2)
      (integrable_standardRademacher_pow 3)) x n
  exact ⟨hGaussian, hRademacher⟩

end CertifiedJL
