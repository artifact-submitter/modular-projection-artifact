/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.NormalApproximation.Tyurin.ProductEnvelope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Zero bias for a centered biased sign

For `X = a(ε - tanh u)`, the zero-bias law is uniform on the interval
between the two values of `X`.  Its characteristic function is therefore

`exp(-i t a tanh u) sinc(t a)`.

This file first develops the characteristic-function form directly.  It
avoids introducing a general zero-bias measure API before the two-point
analytic route has stabilized.
-/

open scoped BigOperators

namespace CertifiedJL
namespace Probability

/-- The first-moment Fourier transform `E[X exp(i t X)]`. -/
noncomputable def centeredBiasedSignFirstMomentChar
    (u a t : ℝ) : ℂ :=
  ∑ e : Bool, (biasedSignWeight u e : ℂ) *
    (a * (biasedSignValue e - Real.tanh u) : ℝ) *
    Complex.exp
      (((t * a * (biasedSignValue e - Real.tanh u) : ℝ) : ℂ) *
        Complex.I)

/--
Characteristic function of the zero-bias law of a centered biased sign.
-/
noncomputable def centeredBiasedSignZeroBiasChar
    (u a t : ℝ) : ℂ :=
  Complex.exp
      (((-(t * a * Real.tanh u) : ℝ) : ℂ) * Complex.I) *
    (Real.sinc (t * a) : ℂ)

/-- Monotone quantile of a centered sign with mean `m`. -/
noncomputable def centeredBiasedSignQuantile
    (m s : ℝ) : ℝ :=
  if s ≤ (1 - m) / 2 then -1 - m else 1 - m

/-- Monotone quantile of its zero-bias law, uniform between the two atoms. -/
noncomputable def centeredBiasedSignZeroBiasQuantile
    (m s : ℝ) : ℝ :=
  2 * s - 1 - m

/-- Coupling distance on the lower part of the unit interval. -/
theorem abs_centeredBiasedSignQuantile_sub_zeroBiasQuantile_of_le
    {m s : ℝ} (hs0 : 0 ≤ s) (hsp : s ≤ (1 - m) / 2) :
    |centeredBiasedSignQuantile m s -
        centeredBiasedSignZeroBiasQuantile m s| = 2 * s := by
  rw [centeredBiasedSignQuantile, if_pos hsp]
  unfold centeredBiasedSignZeroBiasQuantile
  rw [abs_of_nonpos]
  · ring
  · linarith

/-- Coupling distance on the upper part of the unit interval. -/
theorem abs_centeredBiasedSignQuantile_sub_zeroBiasQuantile_of_lt
    {m s : ℝ} (hsp : (1 - m) / 2 < s) (hs1 : s ≤ 1) :
    |centeredBiasedSignQuantile m s -
        centeredBiasedSignZeroBiasQuantile m s| = 2 * (1 - s) := by
  rw [centeredBiasedSignQuantile, if_neg (not_le.mpr hsp)]
  unfold centeredBiasedSignZeroBiasQuantile
  rw [abs_of_nonneg]
  · ring
  · linarith

/--
The centered biased-sign characteristic function as the two constant pieces
of its monotone-quantile integral.
-/
theorem centeredBiasedSignChar_eq_quantileSplit
    (u a t : ℝ) :
    centeredBiasedSignChar u a t =
      (∫ _ : ℝ in 0..(1 - Real.tanh u) / 2,
        Complex.exp
          (((t * a * (-1 - Real.tanh u) : ℝ) : ℂ) * Complex.I)) +
      (∫ _ : ℝ in (1 - Real.tanh u) / 2..1,
        Complex.exp
          (((t * a * (1 - Real.tanh u) : ℝ) : ℂ) * Complex.I)) := by
  rw [show centeredBiasedSignChar u a t =
      (biasedSignNegWeight u : ℂ) *
          Complex.exp
            (((t * a * (-1 - Real.tanh u) : ℝ) : ℂ) * Complex.I) +
        (biasedSignPosWeight u : ℂ) *
          Complex.exp
            (((t * a * (1 - Real.tanh u) : ℝ) : ℂ) * Complex.I) by
    simp [centeredBiasedSignChar, biasedSignWeight,
      biasedSignValue, add_comm]]
  simp only [intervalIntegral.integral_const, Complex.real_smul]
  unfold biasedSignNegWeight biasedSignPosWeight
  push_cast
  ring

/--
The characteristic function of the uniform law on `[-1,1]`, written as an
integral over its affine quantile, is `sinc`.
-/
theorem integral_exp_centeredUniformQuantile_eq_sinc
    (z : ℝ) :
    (∫ s : ℝ in 0..1,
      Complex.exp
        (((z * (2 * s - 1) : ℝ) : ℂ) * Complex.I)) =
      (Real.sinc z : ℂ) := by
  by_cases hz : z = 0
  · simp [hz]
  have hscale :=
    intervalIntegral.smul_integral_comp_mul_add
      (f := fun x : ℝ =>
        Complex.exp ((x : ℂ) * Complex.I))
      (a := 0) (b := 1) (2 * z) (-z)
  have hscale' :
      ((2 * z : ℝ) : ℂ) *
          (∫ s : ℝ in 0..1,
            Complex.exp
              (((z * (2 * s - 1) : ℝ) : ℂ) * Complex.I)) =
        ∫ x : ℝ in -z..z,
          Complex.exp ((x : ℂ) * Complex.I) := by
    rw [Complex.real_smul] at hscale
    calc
      ((2 * z : ℝ) : ℂ) *
            (∫ s : ℝ in 0..1,
              Complex.exp
                (((z * (2 * s - 1) : ℝ) : ℂ) * Complex.I)) =
          ((2 * z : ℝ) : ℂ) *
            (∫ s : ℝ in 0..1,
              Complex.exp
                (((2 * z * s - z : ℝ) : ℂ) * Complex.I)) := by
            congr 2
            funext s
            congr 2
            push_cast
            ring
      _ = ∫ x : ℝ in 2 * z * 0 + -z..2 * z * 1 + -z,
            Complex.exp ((x : ℂ) * Complex.I) := hscale
      _ = ∫ x : ℝ in -z..z,
            Complex.exp ((x : ℂ) * Complex.I) := by
          congr 2 <;> ring
  rw [integral_exp_mul_I_eq_sinc] at hscale'
  have hcoeff : ((2 * z : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hz)
  apply mul_left_cancel₀ hcoeff
  calc
    ((2 * z : ℝ) : ℂ) *
          (∫ s : ℝ in 0..1,
            Complex.exp
              (((z * (2 * s - 1) : ℝ) : ℂ) * Complex.I)) =
        (2 : ℝ) * z * Real.sinc z := hscale'
    _ = ((2 * z : ℝ) : ℂ) * (Real.sinc z : ℂ) := by
      push_cast
      ring

/--
The explicit `sinc` formula for the zero-bias characteristic function is
the interval integral of the uniform affine quantile.
-/
theorem centeredBiasedSignZeroBiasChar_eq_quantileIntegral
    (u a t : ℝ) :
    centeredBiasedSignZeroBiasChar u a t =
      ∫ s : ℝ in 0..1,
        Complex.exp
          (((t * a *
              centeredBiasedSignZeroBiasQuantile (Real.tanh u) s : ℝ) : ℂ) *
            Complex.I) := by
  let z : ℝ := t * a
  let phase : ℂ :=
    Complex.exp (((-(z * Real.tanh u) : ℝ) : ℂ) * Complex.I)
  have hintegrand :
      (fun s : ℝ =>
        Complex.exp
          (((t * a *
              centeredBiasedSignZeroBiasQuantile (Real.tanh u) s : ℝ) : ℂ) *
            Complex.I)) =
        fun s : ℝ =>
          phase *
            Complex.exp
              (((z * (2 * s - 1) : ℝ) : ℂ) * Complex.I) := by
    funext s
    rw [← Complex.exp_add]
    congr 2
    unfold centeredBiasedSignZeroBiasQuantile
    dsimp [z, phase]
    push_cast
    ring
  rw [hintegrand, intervalIntegral.integral_const_mul,
    integral_exp_centeredUniformQuantile_eq_sinc]
  unfold centeredBiasedSignZeroBiasChar
  dsimp [z, phase]

/--
The two-point characteristic function is the interval integral of its
monotone step quantile.
-/
theorem centeredBiasedSignChar_eq_quantileIntegral
    (u a t : ℝ) :
    centeredBiasedSignChar u a t =
      ∫ s : ℝ in 0..1,
        Complex.exp
          (((t * a *
              centeredBiasedSignQuantile (Real.tanh u) s : ℝ) : ℂ) *
            Complex.I) := by
  let p : ℝ := (1 - Real.tanh u) / 2
  let f : ℝ → ℂ := fun s =>
    Complex.exp
      (((t * a *
          centeredBiasedSignQuantile (Real.tanh u) s : ℝ) : ℂ) *
        Complex.I)
  let fneg : ℝ → ℂ := fun _ =>
    Complex.exp
      (((t * a * (-1 - Real.tanh u) : ℝ) : ℂ) * Complex.I)
  let fpos : ℝ → ℂ := fun _ =>
    Complex.exp
      (((t * a * (1 - Real.tanh u) : ℝ) : ℂ) * Complex.I)
  have hp0 : 0 ≤ p := by
    dsimp [p]
    linarith [Real.tanh_lt_one u]
  have hp1 : p ≤ 1 := by
    dsimp [p]
    linarith [Real.neg_one_lt_tanh u]
  have hnegEq : Set.EqOn f fneg (Set.uIoo 0 p) := by
    rw [Set.uIoo_of_le hp0]
    intro s hs
    dsimp [f, fneg]
    rw [centeredBiasedSignQuantile, if_pos hs.2.le]
  have hposEq : Set.EqOn f fpos (Set.uIoo p 1) := by
    rw [Set.uIoo_of_le hp1]
    intro s hs
    dsimp [f, fpos]
    rw [centeredBiasedSignQuantile, if_neg (not_le.mpr hs.1)]
  have hnegInt : IntervalIntegrable f MeasureTheory.volume 0 p :=
    (intervalIntegrable_const :
      IntervalIntegrable fneg MeasureTheory.volume 0 p).congr_uIoo hnegEq.symm
  have hposInt : IntervalIntegrable f MeasureTheory.volume p 1 :=
    (intervalIntegrable_const :
      IntervalIntegrable fpos MeasureTheory.volume p 1).congr_uIoo hposEq.symm
  rw [centeredBiasedSignChar_eq_quantileSplit]
  change (∫ _ : ℝ in 0..p, fneg 0) +
      (∫ _ : ℝ in p..1, fpos 0) = ∫ s : ℝ in 0..1, f s
  rw [← intervalIntegral.integral_congr_uIoo hnegEq,
    ← intervalIntegral.integral_congr_uIoo hposEq]
  exact intervalIntegral.integral_add_adjacent_intervals hnegInt hposInt

/--
The derivative of the characteristic function of a centered biased sign is
its first-moment Fourier transform multiplied by `i`.

This is proved directly from the finite two-point expectation, so the later
Stein differential identity does not depend on differentiation under an
integral.
-/
theorem hasDerivAt_centeredBiasedSignChar
    (u a t : ℝ) :
    HasDerivAt (centeredBiasedSignChar u a)
      (Complex.I * centeredBiasedSignFirstMomentChar u a t) t := by
  have hsummand (e : Bool) :
      HasDerivAt
        (fun s : ℝ =>
          (biasedSignWeight u e : ℂ) *
            Complex.exp
              (((s * a * (biasedSignValue e - Real.tanh u) : ℝ) : ℂ) *
                Complex.I))
        ((biasedSignWeight u e : ℂ) *
          (Complex.exp
              (((t * a * (biasedSignValue e - Real.tanh u) : ℝ) : ℂ) *
                Complex.I) *
            (((a * (biasedSignValue e - Real.tanh u) : ℝ) : ℂ) *
              Complex.I))) t := by
    let x : ℝ := a * (biasedSignValue e - Real.tanh u)
    have hlinear :
        HasDerivAt
          (fun s : ℝ => ((x : ℂ) * Complex.I) * (s : ℂ))
          ((x : ℂ) * Complex.I) t := by
      simpa only [mul_one] using!
        ((hasDerivAt_id (t : ℂ)).const_mul ((x : ℂ) * Complex.I)).comp_ofReal
    have hexp := hlinear.cexp
    have hweighted :=
      hexp.const_mul (biasedSignWeight u e : ℂ)
    have hfun :
        (fun s : ℝ =>
          (biasedSignWeight u e : ℂ) *
            Complex.exp
              (((s * a * (biasedSignValue e - Real.tanh u) : ℝ) : ℂ) *
                Complex.I)) =
          fun s : ℝ =>
            (biasedSignWeight u e : ℂ) *
              Complex.exp (((x : ℂ) * Complex.I) * (s : ℂ)) := by
      funext s
      congr 2
      dsimp [x]
      push_cast
      ring
    rw [hfun]
    apply hweighted.congr_deriv
    congr 2
    dsimp [x]
    push_cast
    ring_nf
  have hsum :
      HasDerivAt
        (fun s : ℝ =>
          ∑ e : Bool, (biasedSignWeight u e : ℂ) *
            Complex.exp
              (((s * a * (biasedSignValue e - Real.tanh u) : ℝ) : ℂ) *
                Complex.I))
        (∑ e : Bool, (biasedSignWeight u e : ℂ) *
          (Complex.exp
              (((t * a * (biasedSignValue e - Real.tanh u) : ℝ) : ℂ) *
                Complex.I) *
            (((a * (biasedSignValue e - Real.tanh u) : ℝ) : ℂ) *
              Complex.I))) t :=
    HasDerivAt.fun_sum (u := Finset.univ) fun e _ => hsummand e
  unfold centeredBiasedSignChar centeredBiasedSignFirstMomentChar
  convert hsum using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  push_cast
  ring

/-- Exact first-moment transform of a centered biased sign. -/
theorem centeredBiasedSignFirstMomentChar_eq
    (u a t : ℝ) :
    centeredBiasedSignFirstMomentChar u a t =
      Complex.exp
          (((-(t * a * Real.tanh u) : ℝ) : ℂ) * Complex.I) *
        Complex.I *
        (a * (1 - Real.tanh u ^ 2) * Real.sin (t * a) : ℝ) := by
  rw [show centeredBiasedSignFirstMomentChar u a t =
      (biasedSignNegWeight u : ℂ) *
          (a * (-1 - Real.tanh u) : ℝ) *
          Complex.exp
            (((t * a * (-1 - Real.tanh u) : ℝ) : ℂ) * Complex.I) +
        (biasedSignPosWeight u : ℂ) *
          (a * (1 - Real.tanh u) : ℝ) *
          Complex.exp
            (((t * a * (1 - Real.tanh u) : ℝ) : ℂ) * Complex.I) by
    simp [centeredBiasedSignFirstMomentChar, biasedSignWeight,
      biasedSignValue, add_comm]]
  have hneg :
      (((t * a * (-1 - Real.tanh u) : ℝ) : ℂ) * Complex.I) =
        (((-(t * a * Real.tanh u) : ℝ) : ℂ) * Complex.I) +
          (((-(t * a) : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  have hpos :
      (((t * a * (1 - Real.tanh u) : ℝ) : ℂ) * Complex.I) =
        (((-(t * a * Real.tanh u) : ℝ) : ℂ) * Complex.I) +
          ((((t * a) : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hneg, hpos, Complex.exp_add, Complex.exp_add]
  have hcoordNeg :
      Complex.exp (((-(t * a) : ℝ) : ℂ) * Complex.I) =
        (Real.cos (t * a) : ℂ) -
          (Real.sin (t * a) : ℂ) * Complex.I := by
    rw [Complex.exp_ofReal_mul_I]
    simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
    ring
  have hcoordPos :
      Complex.exp ((((t * a) : ℝ) : ℂ) * Complex.I) =
        (Real.cos (t * a) : ℂ) +
          (Real.sin (t * a) : ℂ) * Complex.I :=
    Complex.exp_ofReal_mul_I _
  rw [hcoordNeg, hcoordPos]
  unfold biasedSignNegWeight biasedSignPosWeight
  push_cast
  ring

theorem mul_sinc_eq_sin (z : ℝ) :
    z * Real.sinc z = Real.sin z := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [Real.sinc_of_ne_zero hz]
    exact mul_div_cancel₀ _ hz

/--
The complex exponential on the imaginary axis is `1`-Lipschitz in its real
phase.  This is the pointwise estimate used by the explicit zero-bias
coupling.
-/
theorem norm_exp_real_mul_I_sub_exp_real_mul_I_le
    (t x y : ℝ) :
    ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((t * y : ℝ) : ℂ) * Complex.I)‖
      ≤ |t| * |x - y| := by
  have hfactor :
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) -
          Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) *
          (Complex.exp (((t * (x - y) : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hfactor, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have h :=
    Real.norm_exp_I_mul_ofReal_sub_one_le
      (x := t * (x - y))
  have harg :
      Complex.I * ((t * (x - y) : ℝ) : ℂ) =
        ((t * (x - y) : ℝ) : ℂ) * Complex.I := by ring
  rw [harg] at h
  simpa [Real.norm_eq_abs, abs_mul] using h

/--
Exact transport cost of the monotone coupling between a sign of mean `m`
and the uniform law on the interval between its two centered support
points.  The sign quantile jumps at `(1-m)/2`; the uniform quantile is
linear.  No asymptotic estimate enters this identity.
-/
theorem biasedSignUniformCouplingCost_eq
    (m : ℝ) :
    (∫ s : ℝ in 0..(1 - m) / 2, 2 * s) +
        (∫ s : ℝ in (1 - m) / 2..1, 2 * (1 - s)) =
      (1 + m ^ 2) / 2 := by
  have hfirst :
      (∫ s : ℝ in 0..(1 - m) / 2, 2 * s) =
        ((1 - m) / 2) ^ 2 := by
    rw [intervalIntegral.integral_deriv_eq_sub'
      (fun s : ℝ => s ^ 2)]
    · norm_num
    · funext x
      convert (hasDerivAt_pow 2 x).deriv using 1
      norm_num
    · fun_prop
    · fun_prop
  have hsecond :
      (∫ s : ℝ in (1 - m) / 2..1, 2 * (1 - s)) =
        (2 * 1 - 1 ^ 2 : ℝ) -
          (2 * ((1 - m) / 2) - ((1 - m) / 2) ^ 2) := by
    rw [intervalIntegral.integral_deriv_eq_sub'
      (fun s : ℝ => 2 * s - s ^ 2)]
    · funext x
      have h :=
        ((hasDerivAt_const_mul (x := x) (2 : ℝ)).sub
          (hasDerivAt_pow 2 x)).deriv
      have hfun :
          (fun s : ℝ => 2 * s - s ^ 2) =
            (fun s : ℝ => 2 * s) - fun s : ℝ => s ^ 2 := by
        rfl
      rw [hfun]
      rw [h]
      ring
    · fun_prop
    · fun_prop
  rw [hfirst, hsecond]
  ring

/--
Multiplying the exact coupling cost by the coordinate variance gives
exactly half of the third absolute centered moment.  This is the source of
the sharp factor `1/2` in the zero-bias characteristic comparison.
-/
theorem biasedSignVariance_mul_couplingCost_eq_half_thirdMoment
    (u a : ℝ) :
    biasedSignVarianceTerm u a *
        (|a| * (1 + Real.tanh u ^ 2) / 2) =
      biasedSignThirdMomentTerm u a / 2 := by
  unfold biasedSignVarianceTerm biasedSignThirdMomentTerm
  have ha : a ^ 2 = |a| ^ 2 := by
    rw [sq_abs]
  rw [ha]
  ring

/--
The explicit monotone coupling gives the sharp characteristic-function
comparison between a centered biased sign and its zero-bias law.
-/
theorem norm_centeredBiasedSignChar_sub_zeroBiasChar_le
    (u a t : ℝ) :
    ‖centeredBiasedSignChar u a t -
        centeredBiasedSignZeroBiasChar u a t‖ ≤
      |t| * (|a| * (1 + Real.tanh u ^ 2) / 2) := by
  let m : ℝ := Real.tanh u
  let p : ℝ := (1 - m) / 2
  let z : ℝ := t * a
  let fneg : ℝ → ℂ := fun _ =>
    Complex.exp (((z * (-1 - m) : ℝ) : ℂ) * Complex.I)
  let fpos : ℝ → ℂ := fun _ =>
    Complex.exp (((z * (1 - m) : ℝ) : ℂ) * Complex.I)
  let g : ℝ → ℂ := fun s =>
    Complex.exp
      (((z * centeredBiasedSignZeroBiasQuantile m s : ℝ) : ℂ) *
        Complex.I)
  have hp0 : 0 ≤ p := by
    dsimp [p, m]
    linarith [Real.tanh_lt_one u]
  have hp1 : p ≤ 1 := by
    dsimp [p, m]
    linarith [Real.neg_one_lt_tanh u]
  have hgcont : Continuous g := by
    dsimp [g, centeredBiasedSignZeroBiasQuantile]
    fun_prop
  have hg0p : IntervalIntegrable g MeasureTheory.volume 0 p :=
    hgcont.intervalIntegrable 0 p
  have hgp1 : IntervalIntegrable g MeasureTheory.volume p 1 :=
    hgcont.intervalIntegrable p 1
  have hnegInt : IntervalIntegrable fneg MeasureTheory.volume 0 p :=
    intervalIntegrable_const
  have hposInt : IntervalIntegrable fpos MeasureTheory.volume p 1 :=
    intervalIntegrable_const
  have hlow :
      ‖∫ s : ℝ in 0..p, fneg s - g s‖ ≤
        ∫ s : ℝ in 0..p, |z| * (2 * s) := by
    apply intervalIntegral.norm_integral_le_of_norm_le hp0
    · filter_upwards with s hs
      have hphase :=
        norm_exp_real_mul_I_sub_exp_real_mul_I_le
          z (-1 - m) (centeredBiasedSignZeroBiasQuantile m s)
      dsimp [fneg, g]
      rw [show z * (-1 - m) =
          z * (-1 - m) by rfl]
      refine hphase.trans_eq ?_
      unfold centeredBiasedSignZeroBiasQuantile
      rw [show (-1 - m) - (2 * s - 1 - m) = -(2 * s) by ring]
      rw [abs_neg, abs_of_nonneg (by linarith [hs.1] : 0 ≤ 2 * s)]
    · exact (continuous_const.mul (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hupp :
      ‖∫ s : ℝ in p..1, fpos s - g s‖ ≤
        ∫ s : ℝ in p..1, |z| * (2 * (1 - s)) := by
    apply intervalIntegral.norm_integral_le_of_norm_le hp1
    · filter_upwards with s hs
      have hphase :=
        norm_exp_real_mul_I_sub_exp_real_mul_I_le
          z (1 - m) (centeredBiasedSignZeroBiasQuantile m s)
      dsimp [fpos, g]
      refine hphase.trans_eq ?_
      unfold centeredBiasedSignZeroBiasQuantile
      rw [show (1 - m) - (2 * s - 1 - m) = 2 * (1 - s) by ring]
      rw [abs_of_nonneg (by linarith [hs.2] : 0 ≤ 2 * (1 - s))]
    · exact
        (continuous_const.mul
          (continuous_const.mul (continuous_const.sub continuous_id))).intervalIntegrable _ _
  rw [centeredBiasedSignChar_eq_quantileSplit,
    centeredBiasedSignZeroBiasChar_eq_quantileIntegral]
  change
    ‖((∫ _ : ℝ in 0..p, fneg 0) + ∫ _ : ℝ in p..1, fpos 0) -
        ∫ s : ℝ in 0..1, g s‖ ≤
      |t| * (|a| * (1 + Real.tanh u ^ 2) / 2)
  rw [← intervalIntegral.integral_add_adjacent_intervals hg0p hgp1]
  change
    ‖((∫ s : ℝ in 0..p, fneg s) + ∫ s : ℝ in p..1, fpos s) -
        ((∫ s : ℝ in 0..p, g s) + ∫ s : ℝ in p..1, g s)‖ ≤
      |t| * (|a| * (1 + Real.tanh u ^ 2) / 2)
  rw [show
      ((∫ s : ℝ in 0..p, fneg s) + ∫ s : ℝ in p..1, fpos s) -
          ((∫ s : ℝ in 0..p, g s) + ∫ s : ℝ in p..1, g s) =
        ((∫ s : ℝ in 0..p, fneg s) - ∫ s : ℝ in 0..p, g s) +
          ((∫ s : ℝ in p..1, fpos s) - ∫ s : ℝ in p..1, g s) by ring]
  rw [← intervalIntegral.integral_sub hnegInt hg0p,
    ← intervalIntegral.integral_sub hposInt hgp1]
  calc
    ‖(∫ s : ℝ in 0..p, fneg s - g s) +
        ∫ s : ℝ in p..1, fpos s - g s‖
        ≤ ‖∫ s : ℝ in 0..p, fneg s - g s‖ +
          ‖∫ s : ℝ in p..1, fpos s - g s‖ := norm_add_le _ _
    _ ≤ (∫ s : ℝ in 0..p, |z| * (2 * s)) +
          ∫ s : ℝ in p..1, |z| * (2 * (1 - s)) :=
      add_le_add hlow hupp
    _ = |z| * ((1 + m ^ 2) / 2) := by
      rw [intervalIntegral.integral_const_mul
          (r := |z|) (f := fun s : ℝ => 2 * s),
        intervalIntegral.integral_const_mul
          (r := |z|) (f := fun s : ℝ => 2 * (1 - s)),
        ← mul_add,
        biasedSignUniformCouplingCost_eq]
    _ = |t| * (|a| * (1 + Real.tanh u ^ 2) / 2) := by
      dsimp [z, m]
      rw [abs_mul]
      ring

/--
Variance-weighted form of the sharp coordinate comparison:

`vᵢ ‖φᵢ(t)-φᵢ*(t)‖ ≤ βᵢ |t|/2`.
-/
theorem biasedSignVariance_mul_norm_char_sub_zeroBiasChar_le
    (u a t : ℝ) :
    biasedSignVarianceTerm u a *
        ‖centeredBiasedSignChar u a t -
          centeredBiasedSignZeroBiasChar u a t‖ ≤
      biasedSignThirdMomentTerm u a * |t| / 2 := by
  calc
    biasedSignVarianceTerm u a *
        ‖centeredBiasedSignChar u a t -
          centeredBiasedSignZeroBiasChar u a t‖
        ≤ biasedSignVarianceTerm u a *
          (|t| * (|a| * (1 + Real.tanh u ^ 2) / 2)) :=
      mul_le_mul_of_nonneg_left
        (norm_centeredBiasedSignChar_sub_zeroBiasChar_le u a t)
        (biasedSignVarianceTerm_nonneg u a)
    _ = biasedSignThirdMomentTerm u a * |t| / 2 := by
      rw [show biasedSignVarianceTerm u a *
          (|t| * (|a| * (1 + Real.tanh u ^ 2) / 2)) =
        |t| * (biasedSignVarianceTerm u a *
          (|a| * (1 + Real.tanh u ^ 2) / 2)) by ring]
      rw [biasedSignVariance_mul_couplingCost_eq_half_thirdMoment]
      ring

/--
Exact zero-bias characteristic identity

`E[X exp(i tX)] = i t Var(X) E[exp(i tX*)]`.
-/
theorem centeredBiasedSignFirstMomentChar_eq_zeroBias
    (u a t : ℝ) :
    centeredBiasedSignFirstMomentChar u a t =
      Complex.I * (t * biasedSignVarianceTerm u a : ℝ) *
        centeredBiasedSignZeroBiasChar u a t := by
  rw [centeredBiasedSignFirstMomentChar_eq]
  unfold centeredBiasedSignZeroBiasChar biasedSignVarianceTerm
  have hsinc :
      t * a ^ 2 * Real.sinc (t * a) =
        a * Real.sin (t * a) := by
    calc
      t * a ^ 2 * Real.sinc (t * a) =
          a * ((t * a) * Real.sinc (t * a)) := by ring
      _ = a * Real.sin (t * a) := by
        rw [mul_sinc_eq_sin]
  have hreal :
      a * (1 - Real.tanh u ^ 2) * Real.sin (t * a) =
        t * (a ^ 2 * (1 - Real.tanh u ^ 2)) *
          Real.sinc (t * a) := by
    calc
      a * (1 - Real.tanh u ^ 2) * Real.sin (t * a) =
          (1 - Real.tanh u ^ 2) *
            (a * Real.sin (t * a)) := by ring
      _ = (1 - Real.tanh u ^ 2) *
            (t * a ^ 2 * Real.sinc (t * a)) := by rw [hsinc]
      _ = t * (a ^ 2 * (1 - Real.tanh u ^ 2)) *
          Real.sinc (t * a) := by ring
  rw [hreal]
  push_cast
  ring

/--
Derivative form of the one-coordinate Stein identity.  The left-hand side
is the formal characteristic derivative `i E[X exp(i tX)]`.
-/
theorem I_mul_centeredBiasedSignFirstMomentChar
    (u a t : ℝ) :
    Complex.I * centeredBiasedSignFirstMomentChar u a t =
      -(t * biasedSignVarianceTerm u a : ℝ) *
        centeredBiasedSignZeroBiasChar u a t := by
  rw [centeredBiasedSignFirstMomentChar_eq_zeroBias]
  calc
    Complex.I *
          (Complex.I * (t * biasedSignVarianceTerm u a : ℝ) *
            centeredBiasedSignZeroBiasChar u a t) =
        (Complex.I * Complex.I) *
          (t * biasedSignVarianceTerm u a : ℝ) *
            centeredBiasedSignZeroBiasChar u a t := by ring
    _ = -(t * biasedSignVarianceTerm u a : ℝ) *
          centeredBiasedSignZeroBiasChar u a t := by
      rw [Complex.I_mul_I]
      push_cast
      ring

section FiniteProduct

universe u_1

variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

/-- First-moment transform of a finite independent centered-sign sum. -/
noncomputable def centeredBiasedSignProductFirstMomentChar
    (u a : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ i,
    centeredBiasedSignFirstMomentChar (u i) (a i) t *
      ∏ j ∈ Finset.univ.erase i,
        centeredBiasedSignChar (u j) (a j) t

/--
The derivative of a finite product of centered biased-sign characteristic
functions is the first-moment transform of the corresponding sum.
-/
theorem hasDerivAt_centeredBiasedSignChar_product
    (u a : ι → ℝ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => ∏ i, centeredBiasedSignChar (u i) (a i) s)
      (Complex.I * centeredBiasedSignProductFirstMomentChar u a t) t := by
  have hprod :=
    HasDerivAt.fun_finsetProd
      (u := Finset.univ)
      (f := fun i s => centeredBiasedSignChar (u i) (a i) s)
      (f' := fun i =>
        Complex.I * centeredBiasedSignFirstMomentChar (u i) (a i) t)
      (fun i _ => hasDerivAt_centeredBiasedSignChar (u i) (a i) t)
  simpa only [centeredBiasedSignProductFirstMomentChar, Finset.mul_sum,
    smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using hprod

/--
Variance-weighted zero-bias mixture characteristic function for a finite
independent centered-sign sum.
-/
noncomputable def centeredBiasedSignProductZeroBiasChar
    (u a : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ i,
    (biasedSignVarianceTerm (u i) (a i) : ℂ) *
      centeredBiasedSignZeroBiasChar (u i) (a i) t *
      ∏ j ∈ Finset.univ.erase i,
        centeredBiasedSignChar (u j) (a j) t

/--
Exact deleted-coordinate expansion of the difference between the product
characteristic function and its variance-weighted zero-bias mixture.
-/
theorem prod_centeredBiasedSignChar_sub_productZeroBiasChar_eq
    (u a : ι → ℝ) (t : ℝ)
    (hvar : ∑ i, biasedSignVarianceTerm (u i) (a i) = 1) :
    (∏ i, centeredBiasedSignChar (u i) (a i) t) -
        centeredBiasedSignProductZeroBiasChar u a t =
      ∑ i,
        (biasedSignVarianceTerm (u i) (a i) : ℂ) *
          (centeredBiasedSignChar (u i) (a i) t -
            centeredBiasedSignZeroBiasChar (u i) (a i) t) *
          ∏ j ∈ Finset.univ.erase i,
            centeredBiasedSignChar (u j) (a j) t := by
  unfold centeredBiasedSignProductZeroBiasChar
  have hvarC :
      (∑ i, (biasedSignVarianceTerm (u i) (a i) : ℂ)) = 1 := by
    exact_mod_cast hvar
  nth_rewrite 1 [← one_mul (∏ i,
    centeredBiasedSignChar (u i) (a i) t)]
  rw [← hvarC, Finset.sum_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => centeredBiasedSignChar (u j) (a j) t)
    (Finset.mem_univ i)]
  ring

/--
Global product comparison obtained from the exact telescope and the sharp
coordinate coupling.  Deleted-coordinate damping can strengthen the
right-hand side, but is not needed for this baseline bound.
-/
theorem norm_prod_centeredBiasedSignChar_sub_productZeroBiasChar_le
    (u a : ι → ℝ) (t : ℝ)
    (hvar : ∑ i, biasedSignVarianceTerm (u i) (a i) = 1) :
    ‖(∏ i, centeredBiasedSignChar (u i) (a i) t) -
        centeredBiasedSignProductZeroBiasChar u a t‖ ≤
      ∑ i, biasedSignThirdMomentTerm (u i) (a i) * |t| / 2 := by
  rw [prod_centeredBiasedSignChar_sub_productZeroBiasChar_eq
    u a t hvar]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (biasedSignVarianceTerm_nonneg (u i) (a i))]
  have hdeleted :
      ‖∏ j ∈ Finset.univ.erase i,
          centeredBiasedSignChar (u j) (a j) t‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one
      (fun j _ => norm_nonneg _)
      (fun j _ => norm_centeredBiasedSignChar_le_one
        (u j) (a j) t)
  calc
    biasedSignVarianceTerm (u i) (a i) *
          ‖centeredBiasedSignChar (u i) (a i) t -
            centeredBiasedSignZeroBiasChar (u i) (a i) t‖ *
        ‖∏ j ∈ Finset.univ.erase i,
          centeredBiasedSignChar (u j) (a j) t‖
        ≤ (biasedSignVarianceTerm (u i) (a i) *
          ‖centeredBiasedSignChar (u i) (a i) t -
            centeredBiasedSignZeroBiasChar (u i) (a i) t‖) * 1 := by
      exact mul_le_mul_of_nonneg_left hdeleted
        (mul_nonneg (biasedSignVarianceTerm_nonneg (u i) (a i))
          (norm_nonneg _))
    _ ≤ (biasedSignThirdMomentTerm (u i) (a i) * |t| / 2) * 1 := by
      exact mul_le_mul_of_nonneg_right
        (biasedSignVariance_mul_norm_char_sub_zeroBiasChar_le
          (u i) (a i) t) zero_le_one
    _ = biasedSignThirdMomentTerm (u i) (a i) * |t| / 2 := by ring

/--
Sharp deleted-coordinate version of the zero-bias product comparison.  It
retains the damping from every other local coordinate.
-/
theorem norm_prod_centeredBiasedSignChar_sub_productZeroBiasChar_le_deletedVariance
    (u a : ι → ℝ) (t : ℝ)
    (hvar : ∑ i, biasedSignVarianceTerm (u i) (a i) = 1) :
    ‖(∏ i, centeredBiasedSignChar (u i) (a i) t) -
        centeredBiasedSignProductZeroBiasChar u a t‖ ≤
      ∑ i,
        (biasedSignThirdMomentTerm (u i) (a i) * |t| / 2) *
          Real.exp
            (-((tiltedRademacherLocalVariance u a t -
                if |t * a i| ≤ 1 then
                  biasedSignVarianceTerm (u i) (a i)
                else 0) * t ^ 2) / 5) := by
  rw [prod_centeredBiasedSignChar_sub_productZeroBiasChar_eq
    u a t hvar]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (biasedSignVarianceTerm_nonneg (u i) (a i))]
  have hdeleted :
      ‖∏ j ∈ Finset.univ.erase i,
          centeredBiasedSignChar (u j) (a j) t‖ ≤
        Real.exp
          (-((tiltedRademacherLocalVariance u a t -
              if |t * a i| ≤ 1 then
                biasedSignVarianceTerm (u i) (a i)
              else 0) * t ^ 2) / 5) := by
    calc
      ‖∏ j ∈ Finset.univ.erase i,
          centeredBiasedSignChar (u j) (a j) t‖ =
          ∏ j ∈ Finset.univ.erase i,
            ‖centeredBiasedSignChar (u j) (a j) t‖ := by
              simp only [norm_prod]
      _ ≤ ∏ j ∈ Finset.univ.erase i,
          tiltedRademacherCoordinateMajorant u a t j := by
            exact Finset.prod_le_prod
              (fun j _ =>
                norm_nonneg
                  (centeredBiasedSignChar (u j) (a j) t))
              (fun j _ =>
                norm_centeredBiasedSignChar_le_coordinateMajorant
                  u a t j)
      _ = Real.exp
          (-((tiltedRademacherLocalVariance u a t -
              if |t * a i| ≤ 1 then
                biasedSignVarianceTerm (u i) (a i)
              else 0) * t ^ 2) / 5) :=
        prod_tiltedRademacherCoordinateMajorant_erase_eq u a t i
  calc
    biasedSignVarianceTerm (u i) (a i) *
          ‖centeredBiasedSignChar (u i) (a i) t -
            centeredBiasedSignZeroBiasChar (u i) (a i) t‖ *
        ‖∏ j ∈ Finset.univ.erase i,
          centeredBiasedSignChar (u j) (a j) t‖
        ≤ (biasedSignVarianceTerm (u i) (a i) *
          ‖centeredBiasedSignChar (u i) (a i) t -
            centeredBiasedSignZeroBiasChar (u i) (a i) t‖) *
          Real.exp
            (-((tiltedRademacherLocalVariance u a t -
                if |t * a i| ≤ 1 then
                  biasedSignVarianceTerm (u i) (a i)
                else 0) * t ^ 2) / 5) := by
      exact mul_le_mul_of_nonneg_left hdeleted
        (mul_nonneg (biasedSignVarianceTerm_nonneg (u i) (a i))
          (norm_nonneg _))
    _ ≤ (biasedSignThirdMomentTerm (u i) (a i) * |t| / 2) *
          Real.exp
            (-((tiltedRademacherLocalVariance u a t -
                if |t * a i| ≤ 1 then
                  biasedSignVarianceTerm (u i) (a i)
                else 0) * t ^ 2) / 5) := by
      exact mul_le_mul_of_nonneg_right
        (biasedSignVariance_mul_norm_char_sub_zeroBiasChar_le
          (u i) (a i) t)
        (Real.exp_pos _).le

/--
Exact product-level Stein identity.  No approximation is used:

`i E[S exp(i tS)] = -t E[exp(i tS*)]`.
-/
theorem I_mul_centeredBiasedSignProductFirstMomentChar
    (u a : ι → ℝ) (t : ℝ) :
    Complex.I * centeredBiasedSignProductFirstMomentChar u a t =
      -(t : ℂ) * centeredBiasedSignProductZeroBiasChar u a t := by
  unfold centeredBiasedSignProductFirstMomentChar
  unfold centeredBiasedSignProductZeroBiasChar
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    Complex.I *
        (centeredBiasedSignFirstMomentChar (u i) (a i) t *
          ∏ j ∈ Finset.univ.erase i,
            centeredBiasedSignChar (u j) (a j) t) =
      (Complex.I *
        centeredBiasedSignFirstMomentChar (u i) (a i) t) *
          ∏ j ∈ Finset.univ.erase i,
            centeredBiasedSignChar (u j) (a j) t := by ring
    _ = (-(t * biasedSignVarianceTerm (u i) (a i) : ℝ) *
        centeredBiasedSignZeroBiasChar (u i) (a i) t) *
          ∏ j ∈ Finset.univ.erase i,
            centeredBiasedSignChar (u j) (a j) t := by
      rw [I_mul_centeredBiasedSignFirstMomentChar]
    _ = -(t : ℂ) *
      ((biasedSignVarianceTerm (u i) (a i) : ℂ) *
        centeredBiasedSignZeroBiasChar (u i) (a i) t *
          ∏ j ∈ Finset.univ.erase i,
            centeredBiasedSignChar (u j) (a j) t) := by
      push_cast
      ring

/--
Differential Stein identity for the full product characteristic function.
-/
theorem hasDerivAt_centeredBiasedSignChar_product_eq_zeroBias
    (u a : ι → ℝ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => ∏ i, centeredBiasedSignChar (u i) (a i) s)
      (-(t : ℂ) * centeredBiasedSignProductZeroBiasChar u a t) t := by
  apply (hasDerivAt_centeredBiasedSignChar_product u a t).congr_deriv
  exact I_mul_centeredBiasedSignProductFirstMomentChar u a t

/--
After multiplication by `exp(t²/2)`, the product derivative is exactly the
zero-bias discrepancy.  This is the differential comparison used on the
near-Gaussian band.
-/
theorem hasDerivAt_gaussianRenormalized_centeredBiasedSignChar_product
    (u a : ι → ℝ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ =>
        Complex.exp (((s ^ 2 / 2 : ℝ) : ℂ)) *
          ∏ i, centeredBiasedSignChar (u i) (a i) s)
      (Complex.exp (((t ^ 2 / 2 : ℝ) : ℂ)) * (t : ℂ) *
        ((∏ i, centeredBiasedSignChar (u i) (a i) t) -
          centeredBiasedSignProductZeroBiasChar u a t)) t := by
  have hquad :
      HasDerivAt
        (fun s : ℝ => ((s ^ 2 / 2 : ℝ) : ℂ))
        (t : ℂ) t := by
    have hreal :
        HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
      simpa using (hasDerivAt_pow 2 t).div_const 2
    exact hreal.ofReal_comp
  have hexp := hquad.cexp
  have hprod :=
    hasDerivAt_centeredBiasedSignChar_product_eq_zeroBias u a t
  apply (hexp.mul hprod).congr_deriv
  ring

/--
At frequency zero, the zero-bias mixture has total mass equal to the total
variance.
-/
theorem centeredBiasedSignProductZeroBiasChar_zero
    (u a : ι → ℝ) :
    centeredBiasedSignProductZeroBiasChar u a 0 =
      ∑ i, biasedSignVarianceTerm (u i) (a i) := by
  unfold centeredBiasedSignProductZeroBiasChar
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  simp [centeredBiasedSignZeroBiasChar, centeredBiasedSignChar,
    biasedSignWeight, add_comm, ← Complex.ofReal_add]

end FiniteProduct

end Probability
end CertifiedJL
