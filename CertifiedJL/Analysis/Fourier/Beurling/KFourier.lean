/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Fourier.SincSquareIntegral
import Mathlib.Analysis.Fourier.Inversion

/-!
# Fourier transform of the Beurling squared-sinc correction

This file proves the compact-frequency identity

`𝓕 (x ↦ sinc (π x)^2) (t) = max (1 - |t|) 0`

for Mathlib's `exp (-2π i x t)` Fourier convention.  We first compute the
Fourier transform of the triangular function directly, then apply Fourier
inversion using the squared-sinc integrability theorem.
-/

open MeasureTheory Set intervalIntegral
open FourierTransform
open scoped ComplexConjugate

namespace CertifiedJL
namespace Probability

/-- The triangular function supported on `[-1,1]`, as a complex function. -/
noncomputable def beurlingTriangle (x : ℝ) : ℂ :=
  ((max (1 - |x|) 0 : ℝ) : ℂ)

theorem continuous_beurlingTriangle :
    Continuous beurlingTriangle := by
  unfold beurlingTriangle
  fun_prop

theorem beurlingTriangle_eq_zero_of_one_le_abs
    {x : ℝ} (hx : 1 ≤ |x|) :
    beurlingTriangle x = 0 := by
  unfold beurlingTriangle
  rw [max_eq_right]
  · simp
  · linarith

theorem support_beurlingTriangle_subset :
    Function.support beurlingTriangle ⊆ Ioc (-1) 1 := by
  intro x hx
  rw [mem_Ioc]
  have habs : |x| < 1 := by
    by_contra h
    exact hx (beurlingTriangle_eq_zero_of_one_le_abs (not_lt.mp h))
  exact ⟨(abs_lt.mp habs).1, (abs_lt.mp habs).2.le⟩

theorem hasCompactSupport_beurlingTriangle :
    HasCompactSupport beurlingTriangle :=
  HasCompactSupport.of_support_subset_isCompact
    isCompact_Icc
    (support_beurlingTriangle_subset.trans Ioc_subset_Icc_self)

theorem integrable_beurlingTriangle :
    Integrable beurlingTriangle :=
  continuous_beurlingTriangle.integrable_of_hasCompactSupport
    hasCompactSupport_beurlingTriangle

private theorem hasDerivAt_one_sub_mul_cos_primitive
    {a x : ℝ} (ha : a ≠ 0) :
    HasDerivAt
      (fun y : ℝ =>
        (1 - y) * Real.sin (a * y) / a +
          (1 - Real.cos (a * y)) / a ^ 2)
      ((1 - x) * Real.cos (a * x)) x := by
  have hsin :
      HasDerivAt (fun y : ℝ => Real.sin (a * y))
        (a * Real.cos (a * x)) x := by
    have hraw := (Real.hasDerivAt_sin (a * x)).comp x
      ((hasDerivAt_id x).const_mul a)
    change HasDerivAt (fun y : ℝ => Real.sin (a * y))
      (Real.cos (a * x) * (a * 1)) x at hraw
    exact hraw.congr_deriv (by ring)
  have hcos :
      HasDerivAt (fun y : ℝ => Real.cos (a * y))
        (-a * Real.sin (a * x)) x := by
    have hraw := (Real.hasDerivAt_cos (a * x)).comp x
      ((hasDerivAt_id x).const_mul a)
    change HasDerivAt (fun y : ℝ => Real.cos (a * y))
      (-Real.sin (a * x) * (a * 1)) x at hraw
    exact hraw.congr_deriv (by ring)
  have hraw :=
    ((((hasDerivAt_const x 1).sub (hasDerivAt_id x)).mul hsin).div_const a).add
      (((hasDerivAt_const x 1).sub hcos).div_const (a ^ 2))
  change HasDerivAt
    (fun y : ℝ =>
      (1 - y) * Real.sin (a * y) / a +
        (1 - Real.cos (a * y)) / a ^ 2)
    _ x at hraw
  simp only [Pi.sub_apply, id_eq] at hraw
  exact hraw.congr_deriv (by
    field_simp [ha]
    ring)

private theorem integral_one_sub_mul_cos
    {a : ℝ} (ha : a ≠ 0) :
    (∫ x in (0 : ℝ)..1, (1 - x) * Real.cos (a * x)) =
      (1 - Real.cos a) / a ^ 2 := by
  have h := integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (f := fun y : ℝ =>
      (1 - y) * Real.sin (a * y) / a +
        (1 - Real.cos (a * y)) / a ^ 2)
    (f' := fun x : ℝ => (1 - x) * Real.cos (a * x))
    (fun x _ => hasDerivAt_one_sub_mul_cos_primitive ha)
    ((by fun_prop :
      Continuous (fun x : ℝ => (1 - x) * Real.cos (a * x))).intervalIntegrable 0 1)
  simpa [ha] using h

private theorem beurlingTriangle_of_mem_zero_one
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    beurlingTriangle x = (1 - x : ℝ) := by
  unfold beurlingTriangle
  have hnonneg : 0 ≤ 1 - x := by linarith [hx.2]
  rw [abs_of_nonneg hx.1, max_eq_left hnonneg]

private theorem beurlingTriangle_neg (x : ℝ) :
    beurlingTriangle (-x) = beurlingTriangle x := by
  simp [beurlingTriangle]

private theorem fourierPair_integrand_sum
    (t x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    Complex.exp (((-2 * Real.pi * x * t : ℝ) : ℂ) * Complex.I) *
          beurlingTriangle x +
        Complex.exp (((-2 * Real.pi * (-x) * t : ℝ) : ℂ) * Complex.I) *
          beurlingTriangle (-x) =
      (2 * ((1 - x) * Real.cos (2 * Real.pi * t * x)) : ℝ) := by
  rw [beurlingTriangle_of_mem_zero_one hx, beurlingTriangle_neg,
    beurlingTriangle_of_mem_zero_one hx]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  norm_cast
  norm_num
  have harg : (2 : ℂ) * Real.pi * x * t =
      2 * Real.pi * t * x := by ring
  rw [harg]
  ring

private noncomputable def beurlingTriangleFourierIntegrand
    (t x : ℝ) : ℂ :=
  Complex.exp (((-2 * Real.pi * x * t : ℝ) : ℂ) * Complex.I) *
    beurlingTriangle x

private theorem continuous_beurlingTriangleFourierIntegrand (t : ℝ) :
    Continuous (beurlingTriangleFourierIntegrand t) := by
  unfold beurlingTriangleFourierIntegrand
  exact
    (by
      fun_prop :
      Continuous
        (fun x : ℝ =>
          Complex.exp (((-2 * Real.pi * x * t : ℝ) : ℂ) * Complex.I))).mul
      continuous_beurlingTriangle

private theorem support_beurlingTriangleFourierIntegrand_subset
    (t : ℝ) :
    Function.support (beurlingTriangleFourierIntegrand t) ⊆ Ioc (-1) 1 := by
  intro x hx
  apply support_beurlingTriangle_subset
  intro hzero
  exact hx (by simp [beurlingTriangleFourierIntegrand, hzero])

private theorem integral_beurlingTriangleFourierIntegrand
    (t : ℝ) :
    (∫ x : ℝ, beurlingTriangleFourierIntegrand t x) =
      2 * ∫ x in (0 : ℝ)..1,
        ((1 - x) * Real.cos (2 * Real.pi * t * x) : ℝ) := by
  have hcont := continuous_beurlingTriangleFourierIntegrand t
  have hfull :
      (∫ x in (-1 : ℝ)..1, beurlingTriangleFourierIntegrand t x) =
        ∫ x : ℝ, beurlingTriangleFourierIntegrand t x :=
    intervalIntegral.integral_eq_integral_of_support_subset
      (support_beurlingTriangleFourierIntegrand_subset t)
  rw [← hfull]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (-1) 0)
    (hcont.intervalIntegrable 0 1)]
  have hneg := intervalIntegral.integral_comp_neg
    (f := beurlingTriangleFourierIntegrand t) (a := 0) (b := 1)
  simp only [neg_zero] at hneg
  rw [← hneg]
  have hnegInt :
      IntervalIntegrable
        (fun x : ℝ => beurlingTriangleFourierIntegrand t (-x))
        volume 0 1 := by
    have hcomp :=
      (hcont.comp continuous_neg).intervalIntegrable
        (μ := volume) 0 1
    change IntervalIntegrable
      (fun x : ℝ => beurlingTriangleFourierIntegrand t (-x))
      volume 0 1 at hcomp
    exact hcomp
  rw [← intervalIntegral.integral_add
    hnegInt (hcont.intervalIntegrable 0 1)]
  rw [show
      (∫ x in (0 : ℝ)..1,
        (beurlingTriangleFourierIntegrand t) (-x) +
          beurlingTriangleFourierIntegrand t x) =
        ∫ x in (0 : ℝ)..1,
          (((2 * ((1 - x) *
            Real.cos (2 * Real.pi * t * x)) : ℝ)) : ℂ) by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    simpa only [beurlingTriangleFourierIntegrand, add_comm] using
      fourierPair_integrand_sum t x hx']
  rw [intervalIntegral.integral_ofReal]
  rw [intervalIntegral.integral_const_mul]
  norm_num

theorem fourier_beurlingTriangle (t : ℝ) :
    𝓕 beurlingTriangle t =
      ((Real.sinc (Real.pi * t) ^ 2 : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hfourier :
      (∫ x : ℝ,
        Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I) •
          beurlingTriangle x) =
        ∫ x : ℝ, beurlingTriangleFourierIntegrand t x := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    simp [beurlingTriangleFourierIntegrand, smul_eq_mul]
  rw [hfourier, integral_beurlingTriangleFourierIntegrand]
  by_cases ht : t = 0
  · subst t
    have hconst :
        IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    have hid :
        IntervalIntegrable (fun x : ℝ => x) volume 0 1 :=
      continuous_id.intervalIntegrable 0 1
    norm_num only [mul_zero, zero_mul, Real.cos_zero, mul_one,
      Real.sinc_zero, one_pow]
    rw [intervalIntegral.integral_sub hconst hid, integral_one, integral_id]
    norm_num
  · have ha : 2 * Real.pi * t ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) ht
    rw [integral_one_sub_mul_cos ha]
    rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero ht)]
    have htrig :
        1 - Real.cos (2 * Real.pi * t) =
          2 * Real.sin (Real.pi * t) ^ 2 := by
      rw [show 2 * Real.pi * t = 2 * (Real.pi * t) by ring,
        Real.cos_two_mul_eq_one_sub]
      ring
    rw [htrig]
    push_cast
    field_simp

/-- The Fourier transform of the squared-sinc correction is the triangular
function supported on `[-1,1]`. -/
theorem fourier_beurlingK (t : ℝ) :
    𝓕 (fun x : ℝ => ((beurlingK x : ℝ) : ℂ)) t =
      beurlingTriangle t := by
  have hpair :
      𝓕 beurlingTriangle =
        fun x : ℝ => ((beurlingK x : ℝ) : ℂ) := by
    funext x
    simpa only [beurlingK] using fourier_beurlingTriangle x
  have hK :
      Integrable (fun x : ℝ => ((beurlingK x : ℝ) : ℂ)) :=
    integrable_beurlingK.ofReal
  have hFourierTriangle :
      Integrable (𝓕 beurlingTriangle) := by
    rw [hpair]
    exact hK
  have hinv :
      𝓕⁻ (fun x : ℝ => ((beurlingK x : ℝ) : ℂ)) =
        beurlingTriangle := by
    rw [← hpair]
    exact continuous_beurlingTriangle.fourierInv_fourier_eq
      integrable_beurlingTriangle hFourierTriangle
  calc
    𝓕 (fun x : ℝ => ((beurlingK x : ℝ) : ℂ)) t =
        𝓕⁻ (fun x : ℝ => ((beurlingK x : ℝ) : ℂ)) (-t) := by
          rw [Real.fourierInv_eq_fourier_neg]
          simp only [neg_neg]
    _ = beurlingTriangle (-t) := congrFun hinv (-t)
    _ = beurlingTriangle t := beurlingTriangle_neg t

/-- Pointwise real form of `fourier_beurlingK`. -/
theorem fourier_beurlingK_eq_max (t : ℝ) :
    𝓕 (fun x : ℝ => ((beurlingK x : ℝ) : ℂ)) t =
      ((max (1 - |t|) 0 : ℝ) : ℂ) := by
  rw [fourier_beurlingK]
  rfl

end Probability
end CertifiedJL
