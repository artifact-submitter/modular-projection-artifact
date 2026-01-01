/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.NormalApproximation.Rademacher.TiltedRademacherCharacteristic
import CertifiedJL.Probability.NormalApproximation.Rademacher.TiltedRademacherMoments
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# Product envelopes for tilted Rademacher characteristic functions

This file proves the distribution-specific analytic estimates used after the
Prawitz smoothing reduction.  The key low-frequency regime is

`4 * L * |t| ≤ 1`,

where `L` is the sum of the standardized third absolute moments.  Coordinates
with `|t aᵢ| > 1` then account for at most one quarter of the variance.  On the
remaining coordinates, an elementary sine estimate gives enough damping to
obtain the exact rational envelope `exp (-t² / 10)`.

No smoothing or Berry--Esseen statement is assumed here.
-/

open scoped BigOperators ComplexConjugate
open MeasureTheory Set

namespace CertifiedJL
namespace Probability

/-- Variance contribution of one centered biased sign with coefficient `a`. -/
noncomputable def biasedSignVarianceTerm (u a : ℝ) : ℝ :=
  a ^ 2 * (1 - Real.tanh u ^ 2)

/-- Third absolute centered moment of one biased sign with coefficient `a`. -/
noncomputable def biasedSignThirdMomentTerm (u a : ℝ) : ℝ :=
  |a| ^ 3 * (1 - Real.tanh u ^ 4)

theorem biasedSignVarianceTerm_nonneg (u a : ℝ) :
    0 ≤ biasedSignVarianceTerm u a :=
  mul_nonneg (sq_nonneg _)
    (sub_nonneg.mpr (Real.tanh_sq_lt_one u).le)

theorem biasedSignThirdMomentTerm_nonneg (u a : ℝ) :
    0 ≤ biasedSignThirdMomentTerm u a := by
  unfold biasedSignThirdMomentTerm
  apply mul_nonneg (by positivity)
  have ht := Real.tanh_sq_lt_one u
  nlinarith [sq_nonneg (Real.tanh u ^ 2)]

/--
The exact modulus identity in variance form:
`|φ(t)|² = 1 - (1-tanh² u) sin²(ta)`.
-/
theorem norm_centeredBiasedSignChar_sq_eq_one_sub
    (u a t : ℝ) :
    ‖centeredBiasedSignChar u a t‖ ^ 2 =
      1 - (1 - Real.tanh u ^ 2) * Real.sin (t * a) ^ 2 := by
  rw [norm_centeredBiasedSignChar_sq]
  nlinarith [Real.sin_sq_add_cos_sq (t * a)]

/-- A one-coordinate centered biased-sign characteristic function has norm at most one. -/
theorem norm_centeredBiasedSignChar_le_one
    (u a t : ℝ) :
    ‖centeredBiasedSignChar u a t‖ ≤ 1 := by
  have hsq :
      ‖centeredBiasedSignChar u a t‖ ^ 2 ≤ 1 := by
    rw [norm_centeredBiasedSignChar_sq_eq_one_sub]
    exact sub_le_self _ (mul_nonneg
      (sub_nonneg.mpr (Real.tanh_sq_lt_one u).le) (sq_nonneg _))
  exact (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using hsq)

/--
On `[-1,1]`, the sine has at least three quarters of the magnitude of its
argument.  This deliberately rational estimate is convenient for the later
exact damping constant.
-/
theorem three_quarters_mul_abs_le_abs_sin
    {z : ℝ} (hz : |z| ≤ 1) :
    (3 / 4 : ℝ) * |z| ≤ |Real.sin z| := by
  have hzπ : |z| ≤ Real.pi :=
    hz.trans (by linarith [Real.two_le_pi])
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hzπ]
  rcases eq_or_lt_of_le (abs_nonneg z) with hzero | hpos
  · have : |z| = 0 := hzero.symm
    simp [this]
  · have hsin :=
      Real.sin_gt_sub_cube hpos
    have hcubic : |z| ^ 3 ≤ |z| := by
      have hz0 : 0 ≤ |z| := abs_nonneg z
      nlinarith [mul_self_le_mul_self hz0 hz]
    linarith

/-- Squared form of `three_quarters_mul_abs_le_abs_sin`. -/
theorem nine_sixteenths_mul_sq_le_sin_sq
    {z : ℝ} (hz : |z| ≤ 1) :
    (9 / 16 : ℝ) * z ^ 2 ≤ Real.sin z ^ 2 := by
  have h := three_quarters_mul_abs_le_abs_sin hz
  have hsq := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ (3 / 4) * |z|) h
  nlinarith [sq_abs z, sq_abs (Real.sin z)]

/--
The exact rational cosine remainder used in the low-frequency product
analysis.  Mathlib's `5/96` fourth-order bound implies this simpler
`1/10` cubic envelope on `[-1,1]`.
-/
theorem abs_cos_sub_quadratic_le_one_tenth_mul_cube
    {z : ℝ} (hz : |z| ≤ 1) :
    |Real.cos z - (1 - z ^ 2 / 2)| ≤
      (1 / 10 : ℝ) * |z| ^ 3 := by
  have hcos := Real.cos_bound hz
  have hz0 : 0 ≤ |z| := abs_nonneg z
  have hpow : |z| ^ 4 ≤ |z| ^ 3 := by
    calc
      |z| ^ 4 = |z| ^ 3 * |z| := by ring
      _ ≤ |z| ^ 3 * 1 :=
        mul_le_mul_of_nonneg_left hz (pow_nonneg hz0 3)
      _ = |z| ^ 3 := by ring
  calc
    |Real.cos z - (1 - z ^ 2 / 2)|
        ≤ |z| ^ 4 * (5 / 96) := hcos
    _ ≤ |z| ^ 3 * (5 / 96) :=
      mul_le_mul_of_nonneg_right hpow (by norm_num)
    _ ≤ (1 / 10 : ℝ) * |z| ^ 3 := by
      nlinarith [pow_nonneg hz0 3]

/--
A matching rational cubic sine remainder on `[-1,1]`.  This is deliberately
slightly looser than the optimal `1/6`, but follows directly from Mathlib's
fourth-order trigonometric estimate.
-/
theorem abs_sin_sub_linear_le_one_quarter_mul_cube
    {z : ℝ} (hz : |z| ≤ 1) :
    |Real.sin z - z| ≤ (1 / 4 : ℝ) * |z| ^ 3 := by
  have hsin := Real.sin_bound hz
  have hz0 : 0 ≤ |z| := abs_nonneg z
  have hsin' :
      |Real.sin z - (z - z ^ 3 / 6)| ≤ |z| ^ 4 * (5 / 96) := by
    calc
      |Real.sin z - (z - z ^ 3 / 6)| ≤ |z| ^ 5 / 100 := hsin
      _ ≤ |z| ^ 4 * (5 / 96) := by
        have hpow' : |z| ^ 5 ≤ |z| ^ 4 := by
          calc
            |z| ^ 5 = |z| ^ 4 * |z| := by ring
            _ ≤ |z| ^ 4 * 1 :=
              mul_le_mul_of_nonneg_left hz (pow_nonneg hz0 4)
            _ = |z| ^ 4 := by ring
        calc
          |z| ^ 5 / 100 ≤ |z| ^ 4 / 100 :=
            div_le_div_of_nonneg_right hpow' (by norm_num)
          _ ≤ |z| ^ 4 * (5 / 96) := by
            calc
              |z| ^ 4 / 100 = |z| ^ 4 * (1 / 100) := by ring
              _ ≤ |z| ^ 4 * (5 / 96) :=
                mul_le_mul_of_nonneg_left (by norm_num) (pow_nonneg hz0 4)
  have hpow : |z| ^ 4 ≤ |z| ^ 3 := by
    calc
      |z| ^ 4 = |z| ^ 3 * |z| := by ring
      _ ≤ |z| ^ 3 * 1 :=
        mul_le_mul_of_nonneg_left hz (pow_nonneg hz0 3)
      _ = |z| ^ 3 := by ring
  have hid :
      Real.sin z - z =
        (Real.sin z - (z - z ^ 3 / 6)) - z ^ 3 / 6 := by ring
  rw [hid]
  calc
    |(Real.sin z - (z - z ^ 3 / 6)) - z ^ 3 / 6|
        ≤ |Real.sin z - (z - z ^ 3 / 6)| + |z ^ 3 / 6| :=
      abs_sub _ _
    _ ≤ |z| ^ 4 * (5 / 96) + |z ^ 3 / 6| :=
      add_le_add hsin' le_rfl
    _ = |z| ^ 4 * (5 / 96) + |z| ^ 3 / 6 := by
      rw [abs_div, abs_pow]
      norm_num
    _ ≤ |z| ^ 3 * (5 / 96) + |z| ^ 3 / 6 :=
      add_le_add
        (mul_le_mul_of_nonneg_right hpow (by norm_num)) le_rfl
    _ ≤ (1 / 4 : ℝ) * |z| ^ 3 := by
      nlinarith [pow_nonneg hz0 3]

/--
Sharp global third-order remainder for the oscillatory exponential.

Unlike the generic complex-exponential remainder, the third derivative along
the imaginary axis has constant norm.  The proof uses the integral form of
Taylor's theorem; the integral of `(1-s)²/2` on `[0,1]` gives the exact `1/6`.
-/
theorem norm_exp_mul_I_sub_quadratic_le_cube_div_six (y : ℝ) :
    ‖Complex.exp ((y : ℂ) * Complex.I) -
        (1 + (y : ℂ) * Complex.I - (y : ℂ) ^ 2 / 2)‖ ≤
      |y| ^ 3 / 6 := by
  let μ : Measure ℝ := Measure.dirac y
  have hmem : MemLp id (3 : ℕ) μ := by
    apply MemLp.of_bound (by fun_prop) |y|
    simp [μ]
  have hcont : ContDiff ℝ 3 (charFun μ) :=
    contDiff_charFun hmem
  have hrem := taylor_integral_remainder
    (f := charFun μ) (x₀ := 0) (x := 1) (n := 2)
    (by simpa [uIcc_of_le zero_le_one] using hcont.contDiffOn)
  have hderiv (k : ℕ) (hk : k ≤ 3) :
      iteratedDerivWithin k (charFun μ) (Icc 0 1) 0 =
        Complex.I ^ k * (y : ℂ) ^ k := by
    rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc zero_lt_one) (hcont.of_le (by norm_cast)).contDiffAt
      (show (0 : ℝ) ∈ Icc 0 1 by norm_num)]
    rw [iteratedDeriv_charFun (hmem.mono_exponent (by norm_cast))]
    simp [μ]
  have htaylor :
      taylorWithinEval (charFun μ) 2 (Icc 0 1) 0 1 =
        1 + (y : ℂ) * Complex.I - (y : ℂ) ^ 2 / 2 := by
    rw [taylor_within_apply]
    simp only [Nat.reduceAdd, Finset.sum_range_succ, Finset.range_one,
      Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one,
      sub_zero, one_pow, Nat.factorial_one, Nat.factorial_two,
      Nat.cast_ofNat]
    rw [hderiv 0 (by omega), hderiv 1 (by omega), hderiv 2 (by omega)]
    norm_num
    ring
  rw [uIcc_of_le zero_le_one, htaylor] at hrem
  have hnorm :
      ‖∫ s in (0 : ℝ)..1,
          (((1 - s) ^ 2 / (2 : ℝ)) •
            iteratedDerivWithin 3 (charFun μ) (Icc 0 1) s)‖ ≤
        ∫ s in (0 : ℝ)..1, ((1 - s) ^ 2 / 2) * |y| ^ 3 := by
    apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    · filter_upwards with s hs
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ (1 - s) ^ 2 / (2 : ℝ))]
      rw [iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc zero_lt_one) hcont.contDiffAt
        ⟨hs.1.le, hs.2⟩]
      rw [iteratedDeriv_charFun hmem]
      rw [show (∫ (x : ℝ), (x : ℂ) ^ 3 *
          Complex.exp (↑s * ↑x * Complex.I) ∂μ) =
          (y : ℂ) ^ 3 * Complex.exp ((s * y : ℝ) * Complex.I) by
        simp [μ]]
      rw [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul,
        norm_mul, Complex.norm_exp_ofReal_mul_I]
      simp only [Complex.norm_real, Real.norm_eq_abs, norm_pow]
      ring_nf
      exact le_rfl
    · have hc : Continuous (fun t : ℝ => (1 - t) ^ 2 / 2 * |y| ^ 3) := by
        fun_prop
      exact hc.intervalIntegrable _ _
  calc
    ‖Complex.exp ((y : ℂ) * Complex.I) -
        (1 + (y : ℂ) * Complex.I - (y : ℂ) ^ 2 / 2)‖ =
        ‖∫ s in (0 : ℝ)..1,
          (((1 - s) ^ 2 / (2 : ℝ)) •
            iteratedDerivWithin 3 (charFun μ) (Icc 0 1) s)‖ := by
      calc
        _ = ‖charFun μ 1 -
              (1 + (y : ℂ) * Complex.I - (y : ℂ) ^ 2 / 2)‖ := by
          simp [μ, mul_comm]
        _ = ‖∫ s in (0 : ℝ)..1,
              (((1 - s) ^ 2 / (2 : ℝ)) •
                iteratedDerivWithin 3 (charFun μ) (Icc 0 1) s)‖ := by
          rw [hrem]
          norm_num
    _ ≤ ∫ s in (0 : ℝ)..1, ((1 - s) ^ 2 / 2) * |y| ^ 3 := hnorm
    _ = |y| ^ 3 / 6 := by
      rw [intervalIntegral.integral_mul_const]
      rw [intervalIntegral.integral_div]
      have hpoly :
          (fun x : ℝ => (1 - x) ^ 2) =
            fun x : ℝ => 1 - 2 * x + x ^ 2 := by
        funext x
        ring
      change (∫ x in (0 : ℝ)..1, (1 - x) ^ 2) / 2 * |y| ^ 3 =
        |y| ^ 3 / 6
      rw [hpoly]
      have hi :
          (∫ x in (0 : ℝ)..1, (1 - 2 * x + x ^ 2)) = (1 / 3 : ℝ) := by
        rw [intervalIntegral.integral_add
          ((by fun_prop : Continuous (fun x : ℝ => 1 - 2 * x)).intervalIntegrable _ _)
          ((by fun_prop : Continuous (fun x : ℝ => x ^ 2)).intervalIntegrable _ _)]
        rw [intervalIntegral.integral_sub
          (continuous_const.intervalIntegrable _ _)
          ((by fun_prop : Continuous (fun x : ℝ => 2 * x)).intervalIntegrable _ _)]
        rw [intervalIntegral.integral_const_mul]
        norm_num [integral_pow]
      rw [hi]
      ring

/-- Nonnegativity of either biased-sign weight, in the Boolean-indexed API. -/
theorem biasedSignWeight_nonneg (u : ℝ) (e : Bool) :
    0 ≤ biasedSignWeight u e := by
  cases e <;>
    simp only [biasedSignWeight] <;>
    first | exact biasedSignNegWeight_nonneg u
          | exact biasedSignPosWeight_nonneg u

/--
Sharp one-coordinate characteristic-function remainder, expressed in the
exact third absolute centered moment of the biased sign.
-/
theorem norm_centeredBiasedSignChar_sub_quadratic_le
    (u a t : ℝ) :
    ‖centeredBiasedSignChar u a t -
        (1 - (biasedSignVarianceTerm u a * t ^ 2 : ℂ) / 2)‖ ≤
      biasedSignThirdMomentTerm u a * |t| ^ 3 / 6 := by
  let y : Bool → ℝ := fun e =>
    t * a * (biasedSignValue e - Real.tanh u)
  have hpoly :
      ∑ e : Bool, (biasedSignWeight u e : ℂ) *
          (1 + (y e : ℂ) * Complex.I - (y e : ℂ) ^ 2 / 2) =
        1 - (biasedSignVarianceTerm u a * t ^ 2 : ℂ) / 2 := by
    simp only [Fintype.sum_bool, biasedSignWeight]
    unfold biasedSignNegWeight biasedSignPosWeight biasedSignVarianceTerm
    dsimp only [y]
    push_cast
    simp [biasedSignValue]
    ring
  have hdiff :
      centeredBiasedSignChar u a t -
          (1 - (biasedSignVarianceTerm u a * t ^ 2 : ℂ) / 2) =
        ∑ e : Bool, (biasedSignWeight u e : ℂ) *
          (Complex.exp ((y e : ℂ) * Complex.I) -
            (1 + (y e : ℂ) * Complex.I - (y e : ℂ) ^ 2 / 2)) := by
    unfold centeredBiasedSignChar
    change
      (∑ e : Bool, (biasedSignWeight u e : ℂ) *
          Complex.exp ((y e : ℂ) * Complex.I)) -
          (1 - (biasedSignVarianceTerm u a * t ^ 2 : ℂ) / 2) =
        ∑ e : Bool, (biasedSignWeight u e : ℂ) *
          (Complex.exp ((y e : ℂ) * Complex.I) -
            (1 + (y e : ℂ) * Complex.I - (y e : ℂ) ^ 2 / 2))
    rw [← hpoly, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hdiff]
  calc
    ‖∑ e : Bool, (biasedSignWeight u e : ℂ) *
        (Complex.exp ((y e : ℂ) * Complex.I) -
          (1 + (y e : ℂ) * Complex.I - (y e : ℂ) ^ 2 / 2))‖
        ≤ ∑ e : Bool, ‖(biasedSignWeight u e : ℂ) *
          (Complex.exp ((y e : ℂ) * Complex.I) -
            (1 + (y e : ℂ) * Complex.I - (y e : ℂ) ^ 2 / 2))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ e : Bool, biasedSignWeight u e * (|y e| ^ 3 / 6) := by
      apply Finset.sum_le_sum
      intro e _
      rw [norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg]
      · exact mul_le_mul_of_nonneg_left
          (norm_exp_mul_I_sub_quadratic_le_cube_div_six (y e))
          (biasedSignWeight_nonneg u e)
      · exact biasedSignWeight_nonneg u e
    _ = biasedSignThirdMomentTerm u a * |t| ^ 3 / 6 := by
      unfold biasedSignThirdMomentTerm
      simp only [y, abs_mul, mul_pow]
      calc
        ∑ e : Bool, biasedSignWeight u e *
            (|t| ^ 3 * |a| ^ 3 *
              |biasedSignValue e - Real.tanh u| ^ 3 / 6) =
            (|t| ^ 3 * |a| ^ 3 / 6) *
              biasedSignExpectation u
                (fun z => |z - Real.tanh u| ^ 3) := by
          unfold biasedSignExpectation
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _
          ring
        _ = |a| ^ 3 * (1 - Real.tanh u ^ 4) * |t| ^ 3 / 6 := by
          rw [biasedSign_thirdAbsoluteCenteredMoment]
          ring

/--
Local one-coordinate damping.  The coefficient `1/5` is stronger than the
downstream product coefficient `1/10`; the loss pays for coordinates outside
the local range.
-/
theorem norm_centeredBiasedSignChar_le_exp_local
    (u a t : ℝ) (hlocal : |t * a| ≤ 1) :
    ‖centeredBiasedSignChar u a t‖ ≤
      Real.exp (-(biasedSignVarianceTerm u a * t ^ 2) / 5) := by
  let q : ℝ := 1 - Real.tanh u ^ 2
  let y : ℝ := q * (t * a) ^ 2
  have hq : 0 ≤ q :=
    sub_nonneg.mpr (Real.tanh_sq_lt_one u).le
  have hy : 0 ≤ y := mul_nonneg hq (sq_nonneg _)
  have hsin :
      (9 / 16 : ℝ) * (t * a) ^ 2 ≤ Real.sin (t * a) ^ 2 :=
    nine_sixteenths_mul_sq_le_sin_sq hlocal
  have hsq :
      ‖centeredBiasedSignChar u a t‖ ^ 2 ≤ 1 - (2 / 5 : ℝ) * y := by
    rw [norm_centeredBiasedSignChar_sq_eq_one_sub]
    dsimp only [q, y]
    nlinarith [mul_le_mul_of_nonneg_left hsin hq]
  have hexp_lower :
      1 - (2 / 5 : ℝ) * y ≤ Real.exp (-(2 / 5 : ℝ) * y) := by
    linarith [Real.add_one_le_exp (-(2 / 5 : ℝ) * y)]
  have hsq_exp :
      ‖centeredBiasedSignChar u a t‖ ^ 2 ≤
        (Real.exp (-(biasedSignVarianceTerm u a * t ^ 2) / 5)) ^ 2 := by
    calc
      ‖centeredBiasedSignChar u a t‖ ^ 2
          ≤ 1 - (2 / 5 : ℝ) * y := hsq
      _ ≤ Real.exp (-(2 / 5 : ℝ) * y) := hexp_lower
      _ = (Real.exp (-(biasedSignVarianceTerm u a * t ^ 2) / 5)) ^ 2 := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        unfold biasedSignVarianceTerm
        dsimp only [q, y]
        ring
  exact (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp hsq_exp

/-- Gaussian characteristic factor matching one coordinate variance. -/
noncomputable def biasedSignGaussianChar (u a t : ℝ) : ℂ :=
  (Real.exp (-(biasedSignVarianceTerm u a * t ^ 2) / 2) : ℝ)

theorem norm_biasedSignGaussianChar (u a t : ℝ) :
    ‖biasedSignGaussianChar u a t‖ =
      Real.exp (-(biasedSignVarianceTerm u a * t ^ 2) / 2) := by
  rw [biasedSignGaussianChar, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem norm_biasedSignGaussianChar_le_exp_local
    (u a t : ℝ) :
    ‖biasedSignGaussianChar u a t‖ ≤
      Real.exp (-(biasedSignVarianceTerm u a * t ^ 2) / 5) := by
  rw [norm_biasedSignGaussianChar]
  apply Real.exp_le_exp.mpr
  have hv := biasedSignVarianceTerm_nonneg u a
  have ht := sq_nonneg t
  nlinarith

/-- Outside the local range, `v t²` is charged to `β |t|³`. -/
theorem variance_mul_sq_le_thirdMoment_mul_abs_cube_of_one_lt
    (u a t : ℝ) (hlarge : 1 < |t * a|) :
    biasedSignVarianceTerm u a * t ^ 2 ≤
      biasedSignThirdMomentTerm u a * |t| ^ 3 := by
  let m : ℝ := Real.tanh u
  let q : ℝ := 1 - m ^ 2
  have hq : 0 ≤ q := sub_nonneg.mpr (Real.tanh_sq_lt_one u).le
  have habs : 1 < |t| * |a| := by simpa [abs_mul] using hlarge
  have ha3 : a ^ 2 ≤ |t| * |a| ^ 3 := by
    have ha2 : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
    rw [ha2]
    calc
      |a| ^ 2 = 1 * |a| ^ 2 := by ring
      _ ≤ (|t| * |a|) * |a| ^ 2 :=
        mul_le_mul_of_nonneg_right habs.le (sq_nonneg _)
      _ = |t| * |a| ^ 3 := by ring
  have hm : 1 ≤ 1 + m ^ 2 := by nlinarith [sq_nonneg m]
  have h :
      biasedSignVarianceTerm u a ≤
        |t| * biasedSignThirdMomentTerm u a := by
    unfold biasedSignVarianceTerm biasedSignThirdMomentTerm
    change a ^ 2 * q ≤ |t| * (|a| ^ 3 * (1 - m ^ 4))
    rw [show 1 - m ^ 4 = q * (1 + m ^ 2) by dsimp only [q]; ring]
    calc
      a ^ 2 * q ≤ (|t| * |a| ^ 3) * q :=
        mul_le_mul_of_nonneg_right ha3 hq
      _ ≤ (|t| * |a| ^ 3) * (q * (1 + m ^ 2)) := by
        have hqfactor : q ≤ q * (1 + m ^ 2) := by
          calc
            q = q * 1 := by ring
            _ ≤ q * (1 + m ^ 2) :=
              mul_le_mul_of_nonneg_left hm hq
        exact mul_le_mul_of_nonneg_left hqfactor (by positivity)
      _ = |t| * (|a| ^ 3 * (q * (1 + m ^ 2))) := by ring
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  calc
    biasedSignVarianceTerm u a * t ^ 2
        ≤ (|t| * biasedSignThirdMomentTerm u a) * t ^ 2 :=
      mul_le_mul_of_nonneg_right h ht2
    _ = biasedSignThirdMomentTerm u a * |t| ^ 3 := by
      rw [← sq_abs t]
      ring

/--
Local comparison with the matching Gaussian coordinate.  The exact
oscillatory `1/6` remainder and a `1/4` Gaussian remainder give `5/12`.
-/
theorem norm_centeredBiasedSignChar_sub_gaussian_le_local
    (u a t : ℝ) (hlocal : |t * a| ≤ 1) :
    ‖centeredBiasedSignChar u a t -
        biasedSignGaussianChar u a t‖ ≤
      (5 / 12 : ℝ) * biasedSignThirdMomentTerm u a * |t| ^ 3 := by
  let v : ℝ := biasedSignVarianceTerm u a
  let β : ℝ := biasedSignThirdMomentTerm u a
  let r : ℝ := v * t ^ 2 / 2
  have hv : 0 ≤ v := biasedSignVarianceTerm_nonneg u a
  have hβ : 0 ≤ β := biasedSignThirdMomentTerm_nonneg u a
  have hr : 0 ≤ r := by positivity
  have hq : 0 ≤ 1 - Real.tanh u ^ 2 :=
    sub_nonneg.mpr (Real.tanh_sq_lt_one u).le
  have hq_le : 1 - Real.tanh u ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (Real.tanh u)]
  have hrtop : r ≤ 1 := by
    unfold r v biasedSignVarianceTerm
    have hsquare : (t * a) ^ 2 ≤ 1 := by
      have := sq_le_sq.mpr (by simpa using hlocal : |t * a| ≤ |(1 : ℝ)|)
      simpa using this
    nlinarith [mul_le_mul_of_nonneg_right hsquare hq]
  have hgauss :
      ‖biasedSignGaussianChar u a t -
          (1 - (v * t ^ 2 : ℂ) / 2)‖ ≤ r ^ 2 := by
    rw [biasedSignGaussianChar]
    have hR :
        ‖Real.exp (-r) - 1 - (-r)‖ ≤ r ^ 2 :=
      by
        simpa [Real.norm_eq_abs, abs_of_nonneg hr] using
          (Real.norm_exp_sub_one_sub_id_le
            (x := -r) (by simpa [Real.norm_eq_abs, abs_of_nonneg hr] using hrtop))
    rw [show
        ((Real.exp (-(biasedSignVarianceTerm u a * t ^ 2) / 2) : ℝ) : ℂ) -
            (1 - (v * t ^ 2 : ℂ) / 2) =
          ((Real.exp (-r) - 1 - (-r) : ℝ) : ℂ) by
      dsimp only [r, v]
      push_cast
      ring_nf]
    rw [Complex.norm_real]
    exact hR
  have hfourth :
      r ^ 2 ≤ (1 / 4 : ℝ) * β * |t| ^ 3 := by
    unfold r v β biasedSignVarianceTerm biasedSignThirdMomentTerm
    have hm : 1 ≤ 1 + Real.tanh u ^ 2 := by
      nlinarith [sq_nonneg (Real.tanh u)]
    have habst : |t| * |a| ≤ 1 := by simpa [abs_mul] using hlocal
    have hcore :
        (1 - Real.tanh u ^ 2) * (|t| * |a|) ≤
          1 + Real.tanh u ^ 2 := by
      calc
        (1 - Real.tanh u ^ 2) * (|t| * |a|)
            ≤ 1 * 1 := mul_le_mul hq_le habst (by positivity) zero_le_one
        _ ≤ 1 + Real.tanh u ^ 2 := by simpa using hm
    rw [← sq_abs t, ← sq_abs a]
    nlinarith [mul_nonneg
      (mul_nonneg hq (by positivity : 0 ≤ |a| ^ 3))
      (by positivity : 0 ≤ |t| ^ 3)]
  calc
    ‖centeredBiasedSignChar u a t - biasedSignGaussianChar u a t‖
        ≤ ‖centeredBiasedSignChar u a t -
            (1 - (v * t ^ 2 : ℂ) / 2)‖ +
          ‖biasedSignGaussianChar u a t -
            (1 - (v * t ^ 2 : ℂ) / 2)‖ := by
      calc
        _ = ‖(centeredBiasedSignChar u a t -
              (1 - (v * t ^ 2 : ℂ) / 2)) +
            ((1 - (v * t ^ 2 : ℂ) / 2) -
              biasedSignGaussianChar u a t)‖ := by
          (congr 1; ring)
        _ ≤ ‖centeredBiasedSignChar u a t -
              (1 - (v * t ^ 2 : ℂ) / 2)‖ +
            ‖(1 - (v * t ^ 2 : ℂ) / 2) -
              biasedSignGaussianChar u a t‖ := norm_add_le _ _
        _ = _ := by rw [norm_sub_rev (biasedSignGaussianChar u a t)]
    _ ≤ β * |t| ^ 3 / 6 + r ^ 2 := by
      exact add_le_add
        (by simpa only [v, β] using
          norm_centeredBiasedSignChar_sub_quadratic_le u a t)
        hgauss
    _ ≤ β * |t| ^ 3 / 6 + (1 / 4 : ℝ) * β * |t| ^ 3 :=
      add_le_add_right hfourth _
    _ = (5 / 12 : ℝ) * β * |t| ^ 3 := by ring

/-- Coarse but global nonlocal coordinate comparison, with constant `7/6`. -/
theorem norm_centeredBiasedSignChar_sub_gaussian_le_nonlocal
    (u a t : ℝ) (hlarge : 1 < |t * a|) :
    ‖centeredBiasedSignChar u a t -
        biasedSignGaussianChar u a t‖ ≤
      (7 / 6 : ℝ) * biasedSignThirdMomentTerm u a * |t| ^ 3 := by
  let v : ℝ := biasedSignVarianceTerm u a
  let β : ℝ := biasedSignThirdMomentTerm u a
  have hvt :
      v * t ^ 2 ≤ β * |t| ^ 3 := by
    simpa only [v, β] using
      variance_mul_sq_le_thirdMoment_mul_abs_cube_of_one_lt u a t hlarge
  have hφ :
      ‖centeredBiasedSignChar u a t - 1‖ ≤
        β * |t| ^ 3 / 6 + v * t ^ 2 / 2 := by
    calc
      ‖centeredBiasedSignChar u a t - 1‖
          ≤ ‖centeredBiasedSignChar u a t -
              (1 - (v * t ^ 2 : ℂ) / 2)‖ +
            ‖(1 - (v * t ^ 2 : ℂ) / 2) - 1‖ := by
        calc
          _ = ‖(centeredBiasedSignChar u a t -
                (1 - (v * t ^ 2 : ℂ) / 2)) +
              ((1 - (v * t ^ 2 : ℂ) / 2) - 1)‖ := by
            (congr 1; ring)
          _ ≤ _ := norm_add_le _ _
      _ ≤ β * |t| ^ 3 / 6 + v * t ^ 2 / 2 := by
        apply add_le_add
        · simpa only [v, β] using
            norm_centeredBiasedSignChar_sub_quadratic_le u a t
        · rw [show (1 - (v * t ^ 2 : ℂ) / 2) - 1 =
              -((v * t ^ 2 / 2 : ℝ) : ℂ) by push_cast; ring]
          rw [norm_neg, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by
              exact div_nonneg (mul_nonneg
                (biasedSignVarianceTerm_nonneg u a) (sq_nonneg t)) zero_le_two)]
  have hg :
      ‖biasedSignGaussianChar u a t - 1‖ ≤ v * t ^ 2 / 2 := by
    have hr : 0 ≤ v * t ^ 2 / 2 :=
      div_nonneg (mul_nonneg (biasedSignVarianceTerm_nonneg u a) (sq_nonneg t))
        zero_le_two
    rw [biasedSignGaussianChar]
    change ‖((Real.exp (-(v * t ^ 2) / 2) : ℝ) : ℂ) - 1‖ ≤ _
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    have hexple : Real.exp (-(v * t ^ 2) / 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        dsimp only [v]
        have hnonneg := div_nonneg
          (mul_nonneg (biasedSignVarianceTerm_nonneg u a) (sq_nonneg t)) zero_le_two
        nlinarith)
    rw [abs_of_nonpos (sub_nonpos.mpr hexple)]
    linarith [Real.add_one_le_exp (-(v * t ^ 2) / 2)]
  calc
    ‖centeredBiasedSignChar u a t - biasedSignGaussianChar u a t‖
        ≤ ‖centeredBiasedSignChar u a t - 1‖ +
          ‖biasedSignGaussianChar u a t - 1‖ := by
      calc
        _ = ‖(centeredBiasedSignChar u a t - 1) +
            (1 - biasedSignGaussianChar u a t)‖ := by
          (congr 1; ring)
        _ ≤ ‖centeredBiasedSignChar u a t - 1‖ +
            ‖1 - biasedSignGaussianChar u a t‖ := norm_add_le _ _
        _ = _ := by rw [norm_sub_rev 1]
    _ ≤ (β * |t| ^ 3 / 6 + v * t ^ 2 / 2) + v * t ^ 2 / 2 :=
      add_le_add hφ hg
    _ ≤ (β * |t| ^ 3 / 6 + β * |t| ^ 3 / 2) +
          β * |t| ^ 3 / 2 := by
      gcongr
    _ = (7 / 6 : ℝ) * β * |t| ^ 3 := by ring

section Product

universe u_1

variable {ι : Type u_1} [Fintype ι]

omit [Fintype ι] in
/--
Order-independent normed telescoping bound for two finite products sharing
coordinate majorants.
-/
theorem norm_prod_sub_prod_le_sum_erase
    [DecidableEq ι] (s : Finset ι) (f g : ι → ℂ) (h : ι → ℝ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ h i)
    (hg : ∀ i ∈ s, ‖g i‖ ≤ h i)
    (hh : ∀ i ∈ s, 0 ≤ h i) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤
      ∑ i ∈ s, ‖f i - g i‖ * ∏ j ∈ s.erase i, h j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfs :
          ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, h i := by
        rw [norm_prod]
        exact Finset.prod_le_prod
          (fun i hi => norm_nonneg _)
          (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      have hga : ‖g a‖ ≤ h a := hg a (Finset.mem_insert_self _ _)
      have hha : 0 ≤ h a := hh a (Finset.mem_insert_self _ _)
      have hhs : ∀ i ∈ s, 0 ≤ h i :=
        fun i hi => hh i (Finset.mem_insert_of_mem hi)
      have hi := ih
        (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => hg i (Finset.mem_insert_of_mem hi))
        hhs
      calc
        ‖(∏ i ∈ insert a s, f i) - ∏ i ∈ insert a s, g i‖ =
            ‖(f a - g a) * (∏ i ∈ s, f i) +
              g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)‖ := by
          simp only [Finset.prod_insert ha]
          congr 1
          ring
        _ ≤ ‖(f a - g a) * (∏ i ∈ s, f i)‖ +
              ‖g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)‖ :=
          norm_add_le _ _
        _ = ‖f a - g a‖ * ‖∏ i ∈ s, f i‖ +
              ‖g a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ := by
          rw [norm_mul, norm_mul]
        _ ≤ ‖f a - g a‖ * (∏ i ∈ s, h i) +
              h a * (∑ i ∈ s,
                ‖f i - g i‖ * ∏ j ∈ s.erase i, h j) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hfs (norm_nonneg _))
            (mul_le_mul hga hi (norm_nonneg _) hha)
        _ = ∑ i ∈ insert a s,
              ‖f i - g i‖ * ∏ j ∈ (insert a s).erase i, h j := by
          rw [Finset.sum_insert ha]
          congr 1
          · simp [ha]
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi_mem
            rw [Finset.erase_insert_of_ne
              (Ne.symm (ne_of_mem_of_not_mem hi_mem ha))]
            rw [Finset.prod_insert]
            · ring
            · exact fun hai => ha (Finset.mem_of_mem_erase hai)

/-- Indices whose rescaled frequency is in the local analytic range. -/
noncomputable def tiltedRademacherLocalIndices
    (a : ι → ℝ) (t : ℝ) : Finset ι :=
  Finset.univ.filter fun i => |t * a i| ≤ 1

/-- Variance carried by coordinates in the local analytic range. -/
noncomputable def tiltedRademacherLocalVariance
    (u a : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ tiltedRademacherLocalIndices a t,
    biasedSignVarianceTerm (u i) (a i)

/-- Variance carried by coordinates outside the local analytic range. -/
noncomputable def tiltedRademacherNonlocalVariance
    (u a : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => ¬ |t * a i| ≤ 1),
    biasedSignVarianceTerm (u i) (a i)

theorem tiltedRademacherLocalVariance_nonneg
    (u a : ι → ℝ) (t : ℝ) :
    0 ≤ tiltedRademacherLocalVariance u a t := by
  unfold tiltedRademacherLocalVariance
  exact Finset.sum_nonneg fun i _ =>
    biasedSignVarianceTerm_nonneg (u i) (a i)

theorem tiltedRademacherNonlocalVariance_nonneg
    (u a : ι → ℝ) (t : ℝ) :
    0 ≤ tiltedRademacherNonlocalVariance u a t := by
  unfold tiltedRademacherNonlocalVariance
  exact Finset.sum_nonneg fun i _ =>
    biasedSignVarianceTerm_nonneg (u i) (a i)

/-- The local and nonlocal coordinate sets partition the total variance. -/
theorem tiltedRademacherLocalVariance_add_nonlocalVariance
    (u a : ι → ℝ) (t : ℝ) :
    tiltedRademacherLocalVariance u a t +
        tiltedRademacherNonlocalVariance u a t =
      tiltedRademacherVariance u a := by
  classical
  unfold tiltedRademacherLocalVariance tiltedRademacherNonlocalVariance
    tiltedRademacherLocalIndices tiltedRademacherVariance biasedSignVarianceTerm
  exact Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i => |t * a i| ≤ 1) (fun i => a i ^ 2 * (1 - Real.tanh (u i) ^ 2))

/--
A coordinate outside `|taᵢ| ≤ 1` has variance at most `|t|` times its third
absolute centered moment.
-/
theorem biasedSignVarianceTerm_le_abs_mul_thirdMoment_of_one_lt
    (u a t : ℝ) (hlarge : 1 < |t * a|) :
    biasedSignVarianceTerm u a ≤
      |t| * biasedSignThirdMomentTerm u a := by
  let m : ℝ := Real.tanh u
  let q : ℝ := 1 - m ^ 2
  have hq : 0 ≤ q := sub_nonneg.mpr (Real.tanh_sq_lt_one u).le
  have habs : 1 < |t| * |a| := by simpa [abs_mul] using hlarge
  have ha3 :
      a ^ 2 ≤ |t| * |a| ^ 3 := by
    have ha2 : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
    rw [ha2]
    calc
      |a| ^ 2 = 1 * |a| ^ 2 := by ring
      _ ≤ (|t| * |a|) * |a| ^ 2 :=
        mul_le_mul_of_nonneg_right habs.le (sq_nonneg _)
      _ = |t| * |a| ^ 3 := by ring
  have hm : 1 ≤ 1 + m ^ 2 := by nlinarith [sq_nonneg m]
  unfold biasedSignVarianceTerm biasedSignThirdMomentTerm
  change a ^ 2 * q ≤ |t| * (|a| ^ 3 * (1 - m ^ 4))
  have hfactor : 1 - m ^ 4 = q * (1 + m ^ 2) := by
    dsimp only [q]
    ring
  rw [hfactor]
  calc
    a ^ 2 * q ≤ (|t| * |a| ^ 3) * q :=
      mul_le_mul_of_nonneg_right ha3 hq
    _ ≤ (|t| * |a| ^ 3) * (q * (1 + m ^ 2)) := by
      have hqfactor : q ≤ q * (1 + m ^ 2) := by
        calc
          q = q * 1 := by ring
          _ ≤ q * (1 + m ^ 2) :=
            mul_le_mul_of_nonneg_left hm hq
      exact mul_le_mul_of_nonneg_left hqfactor (by positivity)
    _ = |t| * (|a| ^ 3 * (q * (1 + m ^ 2))) := by ring

/-- Nonlocal variance is bounded by `|t|` times the Lyapunov sum. -/
theorem tiltedRademacherNonlocalVariance_le
    (u a : ι → ℝ) (t : ℝ) :
    tiltedRademacherNonlocalVariance u a t ≤
      |t| * tiltedRademacherThirdMomentSum u a := by
  classical
  unfold tiltedRademacherNonlocalVariance
    tiltedRademacherThirdMomentSum
  calc
    ∑ i ∈ Finset.univ.filter (fun i => ¬ |t * a i| ≤ 1),
        biasedSignVarianceTerm (u i) (a i)
        ≤ ∑ i ∈ Finset.univ.filter (fun i => ¬ |t * a i| ≤ 1),
          |t| * biasedSignThirdMomentTerm (u i) (a i) := by
      apply Finset.sum_le_sum
      intro i hi
      apply biasedSignVarianceTerm_le_abs_mul_thirdMoment_of_one_lt
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi
      exact hi
    _ ≤ ∑ i, |t| * biasedSignThirdMomentTerm (u i) (a i) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro i _ _
      exact mul_nonneg (abs_nonneg _)
        (biasedSignThirdMomentTerm_nonneg (u i) (a i))
    _ = |t| * ∑ i, |a i| ^ 3 *
        (1 - Real.tanh (u i) ^ 4) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rfl

/--
Under the crossover condition `4 L |t| ≤ 1`, at least three quarters of the
unit variance lies in the local analytic range.
-/
theorem three_quarters_le_tiltedRademacherLocalVariance
    (u a : ι → ℝ) (t : ℝ)
    (hvariance :
      ∑ i, biasedSignVarianceTerm (u i) (a i) = 1)
    (hcrossover :
      4 * tiltedRademacherThirdMomentSum u a * |t| ≤ 1) :
    (3 / 4 : ℝ) ≤ tiltedRademacherLocalVariance u a t := by
  have hnonlocal :=
    tiltedRademacherNonlocalVariance_le u a t
  have htotal :
      tiltedRademacherLocalVariance u a t +
          tiltedRademacherNonlocalVariance u a t = 1 := by
    rw [tiltedRademacherLocalVariance_add_nonlocalVariance]
    simpa [tiltedRademacherVariance, biasedSignVarianceTerm] using hvariance
  have hL : |t| * tiltedRademacherThirdMomentSum u a ≤ 1 / 4 := by
    have hnonneg := tiltedRademacherThirdMomentSum_nonneg u a
    nlinarith
  nlinarith

/--
The common coordinate majorant used in the damped telescoping argument.
Local coordinates contribute their exponential variance damping; nonlocal
coordinates contribute the trivial bound one.
-/
noncomputable def tiltedRademacherCoordinateMajorant
    (u a : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  if |t * a i| ≤ 1 then
    Real.exp (-(biasedSignVarianceTerm (u i) (a i) * t ^ 2) / 5)
  else 1

omit [Fintype ι] in
theorem tiltedRademacherCoordinateMajorant_nonneg
    (u a : ι → ℝ) (t : ℝ) (i : ι) :
    0 ≤ tiltedRademacherCoordinateMajorant u a t i := by
  unfold tiltedRademacherCoordinateMajorant
  split_ifs <;> positivity

omit [Fintype ι] in
theorem norm_centeredBiasedSignChar_le_coordinateMajorant
    (u a : ι → ℝ) (t : ℝ) (i : ι) :
    ‖centeredBiasedSignChar (u i) (a i) t‖ ≤
      tiltedRademacherCoordinateMajorant u a t i := by
  unfold tiltedRademacherCoordinateMajorant
  split_ifs with hlocal
  · exact norm_centeredBiasedSignChar_le_exp_local _ _ _ hlocal
  · exact norm_centeredBiasedSignChar_le_one _ _ _

omit [Fintype ι] in
theorem norm_biasedSignGaussianChar_le_coordinateMajorant
    (u a : ι → ℝ) (t : ℝ) (i : ι) :
    ‖biasedSignGaussianChar (u i) (a i) t‖ ≤
      tiltedRademacherCoordinateMajorant u a t i := by
  unfold tiltedRademacherCoordinateMajorant
  split_ifs
  · exact norm_biasedSignGaussianChar_le_exp_local _ _ _
  · rw [norm_biasedSignGaussianChar]
    exact Real.exp_le_one_iff.mpr (by
      have hv := biasedSignVarianceTerm_nonneg (u i) (a i)
      have ht2 := sq_nonneg t
      nlinarith)

/-- A local coordinate has scaled variance at most one. -/
theorem biasedSignVarianceTerm_mul_sq_le_one_of_local
    (u a t : ℝ) (hlocal : |t * a| ≤ 1) :
    biasedSignVarianceTerm u a * t ^ 2 ≤ 1 := by
  have hq : 0 ≤ 1 - Real.tanh u ^ 2 :=
    sub_nonneg.mpr (Real.tanh_sq_lt_one u).le
  have hq_le : 1 - Real.tanh u ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (Real.tanh u)]
  have hsquare : (t * a) ^ 2 ≤ 1 := by
    have h := sq_le_sq.mpr (by simpa using hlocal : |t * a| ≤ |(1 : ℝ)|)
    simpa using h
  unfold biasedSignVarianceTerm
  nlinarith [mul_le_mul hq_le hsquare (sq_nonneg (t * a)) zero_le_one]

/--
Exact deleted-coordinate form of the common majorant product.  This is the
quantity retained by the sharp telescope before any uniform exponential
envelope is imposed.
-/
theorem prod_tiltedRademacherCoordinateMajorant_erase_eq
    [DecidableEq ι] (u a : ι → ℝ) (t : ℝ) (i : ι) :
    ∏ j ∈ Finset.univ.erase i,
        tiltedRademacherCoordinateMajorant u a t j =
      Real.exp
        (-((tiltedRademacherLocalVariance u a t -
            if |t * a i| ≤ 1 then
              biasedSignVarianceTerm (u i) (a i)
            else 0) * t ^ 2) / 5) := by
  classical
  let s : Finset ι := tiltedRademacherLocalIndices a t
  let v : ι → ℝ := fun j => biasedSignVarianceTerm (u j) (a j)
  have hprod :
      ∏ j ∈ Finset.univ.erase i,
          tiltedRademacherCoordinateMajorant u a t j =
        Real.exp
          (∑ j ∈ (Finset.univ.erase i) ∩ s,
            -(v j * t ^ 2) / 5) := by
    calc
      ∏ j ∈ Finset.univ.erase i,
          tiltedRademacherCoordinateMajorant u a t j =
          ∏ j ∈ Finset.univ.erase i,
            if j ∈ s then Real.exp (-(v j * t ^ 2) / 5) else 1 := by
        apply Finset.prod_congr rfl
        intro j _
        rw [tiltedRademacherCoordinateMajorant]
        congr 1
        simp [s, tiltedRademacherLocalIndices]
      _ = ∏ j ∈ (Finset.univ.erase i) ∩ s,
            Real.exp (-(v j * t ^ 2) / 5) := by
        rw [Finset.prod_ite_mem]
      _ = Real.exp
          (∑ j ∈ (Finset.univ.erase i) ∩ s,
            -(v j * t ^ 2) / 5) := by
        rw [← Real.exp_sum]
  rw [hprod]
  by_cases hi : |t * a i| ≤ 1
  · rw [if_pos hi]
    have his : i ∈ s := by
      simpa [s, tiltedRademacherLocalIndices, abs_mul] using hi
    rw [show (Finset.univ.erase i) ∩ s = s.erase i by
      rw [Finset.erase_inter, Finset.univ_inter]]
    rw [show
        (∑ j ∈ s.erase i, -(v j * t ^ 2) / 5) =
          -(((∑ j ∈ s, v j) - v i) * t ^ 2) / 5 by
      calc
        ∑ j ∈ s.erase i, -(v j * t ^ 2) / 5 =
            ∑ j ∈ s.erase i, v j * (-(t ^ 2) / 5) := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = (∑ j ∈ s.erase i, v j) * (-(t ^ 2) / 5) := by
          rw [Finset.sum_mul]
        _ = ((∑ j ∈ s, v j) - v i) * (-(t ^ 2) / 5) := by
          rw [show (∑ j ∈ s.erase i, v j) =
              (∑ j ∈ s, v j) - v i by
            rw [← Finset.sum_erase_add s v his]
            ring]
        _ = -(((∑ j ∈ s, v j) - v i) * t ^ 2) / 5 := by ring]
    congr 2
  · rw [if_neg hi]
    have hinot : i ∉ s := by
      simpa [s, tiltedRademacherLocalIndices] using hi
    rw [show (Finset.univ.erase i) ∩ s = s by
      rw [Finset.erase_inter, Finset.univ_inter,
        Finset.erase_eq_self.mpr hinot]]
    rw [show
        (∑ j ∈ s, -(v j * t ^ 2) / 5) =
          -((∑ j ∈ s, v j) * t ^ 2) / 5 by
      calc
        ∑ j ∈ s, -(v j * t ^ 2) / 5 =
            ∑ j ∈ s, v j * (-(t ^ 2) / 5) := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = (∑ j ∈ s, v j) * (-(t ^ 2) / 5) := by
          rw [Finset.sum_mul]
        _ = -((∑ j ∈ s, v j) * t ^ 2) / 5 := by ring]
    congr 2
    simp [s, v, tiltedRademacherLocalVariance]

/--
Removing one coordinate from the common majorant product preserves Gaussian
damping.  A removed local coordinate costs at most `exp(1/5) ≤ 5/4`; removing
a nonlocal coordinate costs nothing.
-/
theorem prod_tiltedRademacherCoordinateMajorant_erase_le
    [DecidableEq ι] (u a : ι → ℝ) (t : ℝ)
    (hvariance :
      ∑ i, biasedSignVarianceTerm (u i) (a i) = 1)
    (hcrossover :
      4 * tiltedRademacherThirdMomentSum u a * |t| ≤ 1)
    (i : ι) :
    ∏ j ∈ Finset.univ.erase i,
        tiltedRademacherCoordinateMajorant u a t j ≤
      if |t * a i| ≤ 1 then
        (5 / 4 : ℝ) * Real.exp (-(t ^ 2) / 10)
      else Real.exp (-(t ^ 2) / 10) := by
  have hlocal :
      (3 / 4 : ℝ) ≤ tiltedRademacherLocalVariance u a t :=
    three_quarters_le_tiltedRademacherLocalVariance
      u a t hvariance hcrossover
  have hexp_one_fifth :
      Real.exp (1 / 5 : ℝ) ≤ 5 / 4 := by
    calc
      Real.exp (1 / 5 : ℝ) ≤ 1 / (1 - (1 / 5 : ℝ)) :=
        Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
      _ = 5 / 4 := by norm_num
  rw [prod_tiltedRademacherCoordinateMajorant_erase_eq]
  by_cases hi : |t * a i| ≤ 1
  · simp only [if_pos hi]
    have hvi :
        biasedSignVarianceTerm (u i) (a i) * t ^ 2 ≤ 1 := by
      simpa using
        biasedSignVarianceTerm_mul_sq_le_one_of_local (u i) (a i) t hi
    calc
      Real.exp
          (-((tiltedRademacherLocalVariance u a t -
              biasedSignVarianceTerm (u i) (a i)) * t ^ 2) / 5)
          ≤ Real.exp (-(t ^ 2) / 10 + 1 / 5) := by
        apply Real.exp_le_exp.mpr
        have ht2 := sq_nonneg t
        nlinarith
      _ = Real.exp (1 / 5) * Real.exp (-(t ^ 2) / 10) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ (5 / 4 : ℝ) * Real.exp (-(t ^ 2) / 10) :=
        mul_le_mul_of_nonneg_right hexp_one_fifth (Real.exp_pos _).le
  · simp only [if_neg hi, sub_zero]
    apply Real.exp_le_exp.mpr
    have ht2 := sq_nonneg t
    nlinarith

/--
Sharp deleted-coordinate telescope before the uniform crossover envelope.

Each local coordinate carries the `5/12` Taylor remainder and is damped by
the variance of every *other* local coordinate.  Nonlocal coordinates use the
global `7/6` comparison but retain all local variance.  This form is intended
for the small-`L` quantitative integral, where replacing every deleted
variance by a common lower bound loses too much.
-/
theorem norm_prod_centeredBiasedSignChar_sub_prod_gaussian_le_deletedVariance
    (u a : ι → ℝ) (t : ℝ) :
    ‖(∏ i, centeredBiasedSignChar (u i) (a i) t) -
        ∏ i, biasedSignGaussianChar (u i) (a i) t‖ ≤
      ∑ i,
        (if |t * a i| ≤ 1 then (5 / 12 : ℝ) else 7 / 6) *
          biasedSignThirdMomentTerm (u i) (a i) * |t| ^ 3 *
          Real.exp
            (-((tiltedRademacherLocalVariance u a t -
                if |t * a i| ≤ 1 then
                  biasedSignVarianceTerm (u i) (a i)
                else 0) * t ^ 2) / 5) := by
  classical
  let h : ι → ℝ := tiltedRademacherCoordinateMajorant u a t
  calc
    ‖(∏ i, centeredBiasedSignChar (u i) (a i) t) -
        ∏ i, biasedSignGaussianChar (u i) (a i) t‖
        ≤ ∑ i ∈ Finset.univ,
            ‖centeredBiasedSignChar (u i) (a i) t -
                biasedSignGaussianChar (u i) (a i) t‖ *
              ∏ j ∈ Finset.univ.erase i, h j := by
      apply norm_prod_sub_prod_le_sum_erase
      · intro i _
        exact norm_centeredBiasedSignChar_le_coordinateMajorant u a t i
      · intro i _
        exact norm_biasedSignGaussianChar_le_coordinateMajorant u a t i
      · intro i _
        exact tiltedRademacherCoordinateMajorant_nonneg u a t i
    _ ≤ ∑ i,
        (if |t * a i| ≤ 1 then (5 / 12 : ℝ) else 7 / 6) *
          biasedSignThirdMomentTerm (u i) (a i) * |t| ^ 3 *
          Real.exp
            (-((tiltedRademacherLocalVariance u a t -
                if |t * a i| ≤ 1 then
                  biasedSignVarianceTerm (u i) (a i)
                else 0) * t ^ 2) / 5) := by
      apply Finset.sum_le_sum
      intro i _
      rw [show (∏ j ∈ Finset.univ.erase i, h j) =
          Real.exp
            (-((tiltedRademacherLocalVariance u a t -
                if |t * a i| ≤ 1 then
                  biasedSignVarianceTerm (u i) (a i)
                else 0) * t ^ 2) / 5) by
        exact prod_tiltedRademacherCoordinateMajorant_erase_eq u a t i]
      by_cases hlocal : |t * a i| ≤ 1
      · simp only [if_pos hlocal]
        exact mul_le_mul_of_nonneg_right
          (norm_centeredBiasedSignChar_sub_gaussian_le_local
            (u i) (a i) t hlocal)
          (Real.exp_pos _).le
      · simp only [if_neg hlocal]
        exact mul_le_mul_of_nonneg_right
          (norm_centeredBiasedSignChar_sub_gaussian_le_nonlocal
            (u i) (a i) t (lt_of_not_ge hlocal))
          (Real.exp_pos _).le

/--
Coarse damped product-to-Gaussian comparison on the Tyurin crossover band.

The proof retains the deleted-coordinate damping inside the telescope: a
local coordinate uses the sharp `5/12` remainder and pays only the factor
`exp(1/5) ≤ 5/4`, while a nonlocal coordinate uses the global `7/6`
comparison and retains the full local damping.  The common `7/6` coefficient
is convenient for outer-band estimates; it is not the sharp small-`L`
Berry--Esseen constant.
-/
theorem norm_prod_centeredBiasedSignChar_sub_prod_gaussian_le
    (u a : ι → ℝ) (t : ℝ)
    (hvariance :
      ∑ i, biasedSignVarianceTerm (u i) (a i) = 1)
    (hcrossover :
      4 * tiltedRademacherThirdMomentSum u a * |t| ≤ 1) :
    ‖(∏ i, centeredBiasedSignChar (u i) (a i) t) -
        ∏ i, biasedSignGaussianChar (u i) (a i) t‖ ≤
      (7 / 6 : ℝ) * tiltedRademacherThirdMomentSum u a *
        |t| ^ 3 * Real.exp (-(t ^ 2) / 10) := by
  classical
  let h : ι → ℝ := tiltedRademacherCoordinateMajorant u a t
  let β : ι → ℝ := fun i => biasedSignThirdMomentTerm (u i) (a i)
  have ht3 : 0 ≤ |t| ^ 3 := by positivity
  have hexp : 0 ≤ Real.exp (-(t ^ 2) / 10) := (Real.exp_pos _).le
  calc
    ‖(∏ i, centeredBiasedSignChar (u i) (a i) t) -
        ∏ i, biasedSignGaussianChar (u i) (a i) t‖
        ≤ ∑ i ∈ Finset.univ,
            ‖centeredBiasedSignChar (u i) (a i) t -
                biasedSignGaussianChar (u i) (a i) t‖ *
              ∏ j ∈ Finset.univ.erase i, h j := by
      apply norm_prod_sub_prod_le_sum_erase
      · intro i _
        exact norm_centeredBiasedSignChar_le_coordinateMajorant u a t i
      · intro i _
        exact norm_biasedSignGaussianChar_le_coordinateMajorant u a t i
      · intro i _
        exact tiltedRademacherCoordinateMajorant_nonneg u a t i
    _ ≤ ∑ i ∈ Finset.univ,
          (7 / 6 : ℝ) * β i * |t| ^ 3 *
            Real.exp (-(t ^ 2) / 10) := by
      apply Finset.sum_le_sum
      intro i _
      have hprod_nonneg :
          0 ≤ ∏ j ∈ Finset.univ.erase i, h j :=
        Finset.prod_nonneg fun j _ =>
          tiltedRademacherCoordinateMajorant_nonneg u a t j
      have hprod :=
        prod_tiltedRademacherCoordinateMajorant_erase_le
          u a t hvariance hcrossover i
      by_cases hlocal : |t * a i| ≤ 1
      · rw [if_pos hlocal] at hprod
        have hcoord :=
          norm_centeredBiasedSignChar_sub_gaussian_le_local
            (u i) (a i) t hlocal
        have hcoord_bound_nonneg :
            0 ≤ (5 / 12 : ℝ) * β i * |t| ^ 3 := by
          exact mul_nonneg
            (mul_nonneg (by norm_num)
              (biasedSignThirdMomentTerm_nonneg (u i) (a i))) ht3
        calc
          ‖centeredBiasedSignChar (u i) (a i) t -
              biasedSignGaussianChar (u i) (a i) t‖ *
                ∏ j ∈ Finset.univ.erase i, h j
              ≤ ((5 / 12 : ℝ) * β i * |t| ^ 3) *
                  ((5 / 4 : ℝ) * Real.exp (-(t ^ 2) / 10)) :=
            mul_le_mul hcoord hprod hprod_nonneg hcoord_bound_nonneg
          _ ≤ (7 / 6 : ℝ) * β i * |t| ^ 3 *
                Real.exp (-(t ^ 2) / 10) := by
            have hβ := biasedSignThirdMomentTerm_nonneg (u i) (a i)
            dsimp only [β] at hβ ⊢
            nlinarith [mul_nonneg (mul_nonneg hβ ht3) hexp]
      · rw [if_neg hlocal] at hprod
        have hlarge : 1 < |t * a i| := lt_of_not_ge hlocal
        have hcoord :=
          norm_centeredBiasedSignChar_sub_gaussian_le_nonlocal
            (u i) (a i) t hlarge
        have hcoord_bound_nonneg :
            0 ≤ (7 / 6 : ℝ) * β i * |t| ^ 3 := by
          exact mul_nonneg
            (mul_nonneg (by norm_num)
              (biasedSignThirdMomentTerm_nonneg (u i) (a i))) ht3
        calc
          ‖centeredBiasedSignChar (u i) (a i) t -
              biasedSignGaussianChar (u i) (a i) t‖ *
                ∏ j ∈ Finset.univ.erase i, h j
              ≤ ((7 / 6 : ℝ) * β i * |t| ^ 3) *
                  Real.exp (-(t ^ 2) / 10) :=
            mul_le_mul hcoord hprod hprod_nonneg hcoord_bound_nonneg
          _ = (7 / 6 : ℝ) * β i * |t| ^ 3 *
                Real.exp (-(t ^ 2) / 10) := rfl
    _ = (7 / 6 : ℝ) * tiltedRademacherThirdMomentSum u a *
          |t| ^ 3 * Real.exp (-(t ^ 2) / 10) := by
      calc
        ∑ i ∈ Finset.univ,
            (7 / 6 : ℝ) * β i * |t| ^ 3 *
              Real.exp (-(t ^ 2) / 10) =
            ∑ i ∈ Finset.univ,
              β i * ((7 / 6 : ℝ) * |t| ^ 3 *
                Real.exp (-(t ^ 2) / 10)) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = (∑ i ∈ Finset.univ, β i) *
              ((7 / 6 : ℝ) * |t| ^ 3 *
                Real.exp (-(t ^ 2) / 10)) := by
          rw [Finset.sum_mul]
        _ = (7 / 6 : ℝ) * tiltedRademacherThirdMomentSum u a *
              |t| ^ 3 * Real.exp (-(t ^ 2) / 10) := by
          rw [show (∑ i ∈ Finset.univ, β i) =
              tiltedRademacherThirdMomentSum u a by
            unfold tiltedRademacherThirdMomentSum
            dsimp only [β, biasedSignThirdMomentTerm]]
          ring

/-- The product of the matching coordinate Gaussians is the total-variance Gaussian. -/
theorem prod_biasedSignGaussianChar_eq
    (u a : ι → ℝ) (t : ℝ) :
    ∏ i, biasedSignGaussianChar (u i) (a i) t =
      ((Real.exp
        (-((∑ i, biasedSignVarianceTerm (u i) (a i)) * t ^ 2) / 2) : ℝ) : ℂ) := by
  classical
  simp only [biasedSignGaussianChar]
  rw [← Complex.ofReal_prod]
  congr 1
  rw [← Real.exp_sum]
  congr 1
  calc
    ∑ i, -(biasedSignVarianceTerm (u i) (a i) * t ^ 2) / 2 =
        ∑ i, biasedSignVarianceTerm (u i) (a i) * (-(t ^ 2) / 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, biasedSignVarianceTerm (u i) (a i)) *
        (-(t ^ 2) / 2) := by
      rw [Finset.sum_mul]
    _ = -((∑ i, biasedSignVarianceTerm (u i) (a i)) * t ^ 2) / 2 := by
      ring

/-- Total-variance-one form of the damped product-to-Gaussian comparison. -/
theorem norm_prod_centeredBiasedSignChar_sub_standardGaussian_le
    (u a : ι → ℝ) (t : ℝ)
    (hvariance :
      ∑ i, biasedSignVarianceTerm (u i) (a i) = 1)
    (hcrossover :
      4 * tiltedRademacherThirdMomentSum u a * |t| ≤ 1) :
    ‖(∏ i, centeredBiasedSignChar (u i) (a i) t) -
        ((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ)‖ ≤
      (7 / 6 : ℝ) * tiltedRademacherThirdMomentSum u a *
        |t| ^ 3 * Real.exp (-(t ^ 2) / 10) := by
  rw [← show
    (∏ i, biasedSignGaussianChar (u i) (a i) t) =
      ((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ) by
    rw [prod_biasedSignGaussianChar_eq, hvariance]
    congr 2
    ring]
  exact norm_prod_centeredBiasedSignChar_sub_prod_gaussian_le
    u a t hvariance hcrossover

/-- Product norm is controlled by the exponential of the local variance. -/
theorem norm_standardizedTiltedRademacherChar_le_exp_localVariance
    (u a : ι → ℝ) (t : ℝ) :
    ‖standardizedTiltedRademacherChar u a t‖ ≤
      Real.exp (-(tiltedRademacherLocalVariance
        u (fun i => a i / tiltedRademacherStdDev u a) t * t ^ 2) / 5) := by
  classical
  rw [standardizedTiltedRademacherChar_eq_prod, norm_prod]
  let c : ι → ℝ := fun i => a i / tiltedRademacherStdDev u a
  let s : Finset ι := tiltedRademacherLocalIndices c t
  have hpoint (i : ι) :
      ‖centeredBiasedSignChar (u i) (c i) t‖ ≤
        if i ∈ s then
          Real.exp (-(biasedSignVarianceTerm (u i) (c i) * t ^ 2) / 5)
        else 1 := by
    by_cases hi : i ∈ s
    · rw [if_pos hi]
      apply norm_centeredBiasedSignChar_le_exp_local
      simpa [s, tiltedRademacherLocalIndices] using hi
    · rw [if_neg hi]
      exact norm_centeredBiasedSignChar_le_one _ _ _
  calc
    ∏ i, ‖centeredBiasedSignChar (u i) (a i /
          tiltedRademacherStdDev u a) t‖
        ≤ ∏ i, if i ∈ s then
            Real.exp (-(biasedSignVarianceTerm (u i) (c i) * t ^ 2) / 5)
          else 1 := by
      apply Finset.prod_le_prod
      · intro i _
        exact norm_nonneg _
      · intro i _
        simpa only [c] using hpoint i
    _ = ∏ i ∈ s,
          Real.exp (-(biasedSignVarianceTerm (u i) (c i) * t ^ 2) / 5) := by
      simp only [Finset.prod_ite_mem, Finset.univ_inter]
    _ = Real.exp (∑ i ∈ s,
          -(biasedSignVarianceTerm (u i) (c i) * t ^ 2) / 5) := by
      rw [← Real.exp_sum]
    _ = Real.exp (-(tiltedRademacherLocalVariance u c t * t ^ 2) / 5) := by
      congr 1
      unfold tiltedRademacherLocalVariance
      dsimp only [s]
      calc
        ∑ i ∈ tiltedRademacherLocalIndices c t,
            -(biasedSignVarianceTerm (u i) (c i) * t ^ 2) / 5 =
            ∑ i ∈ tiltedRademacherLocalIndices c t,
              biasedSignVarianceTerm (u i) (c i) * (-(t ^ 2) / 5) := by
                apply Finset.sum_congr rfl
                intro i _
                ring
        _ = (∑ i ∈ tiltedRademacherLocalIndices c t,
              biasedSignVarianceTerm (u i) (c i)) * (-(t ^ 2) / 5) := by
                rw [Finset.sum_mul]
        _ = -((∑ i ∈ tiltedRademacherLocalIndices c t,
              biasedSignVarianceTerm (u i) (c i)) * t ^ 2) / 5 := by ring
    _ = Real.exp (-(tiltedRademacherLocalVariance
          u (fun i => a i / tiltedRademacherStdDev u a) t * t ^ 2) / 5) := rfl

/--
The exact low-frequency Tyurin damping envelope.  For a standardized finite
product, the crossover `4 L |t| ≤ 1` implies `|f(t)| ≤ exp (-t²/10)`.
-/
theorem norm_standardizedTiltedRademacherChar_le_exp_neg_sq_div_ten
    (u a : ι → ℝ) (t : ℝ)
    (ha : ∃ i, a i ≠ 0)
    (hcrossover :
      4 * tiltedRademacherThirdMomentSum u
          (fun i => a i / tiltedRademacherStdDev u a) * |t| ≤ 1) :
    ‖standardizedTiltedRademacherChar u a t‖ ≤
      Real.exp (-(t ^ 2) / 10) := by
  let c : ι → ℝ := fun i => a i / tiltedRademacherStdDev u a
  have hvariance :
      ∑ i, biasedSignVarianceTerm (u i) (c i) = 1 := by
    simpa [biasedSignVarianceTerm] using
      standardizedTiltedRademacherVariance_eq_one u a ha
  have hlocal :
      (3 / 4 : ℝ) ≤ tiltedRademacherLocalVariance u c t :=
    three_quarters_le_tiltedRademacherLocalVariance
      u c t hvariance hcrossover
  calc
    ‖standardizedTiltedRademacherChar u a t‖
        ≤ Real.exp (-(tiltedRademacherLocalVariance u c t * t ^ 2) / 5) := by
      simpa only [c] using
        norm_standardizedTiltedRademacherChar_le_exp_localVariance u a t
    _ ≤ Real.exp (-(t ^ 2) / 10) := by
      apply Real.exp_le_exp.mpr
      have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
      nlinarith

/--
Standardized tilted-Rademacher product-to-Gaussian comparison on the Tyurin
crossover band.
-/
theorem norm_standardizedTiltedRademacherChar_sub_standardGaussian_le
    (u a : ι → ℝ) (t : ℝ)
    (ha : ∃ i, a i ≠ 0)
    (hcrossover :
      4 * tiltedRademacherThirdMomentSum u
          (fun i => a i / tiltedRademacherStdDev u a) * |t| ≤ 1) :
    ‖standardizedTiltedRademacherChar u a t -
        ((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ)‖ ≤
      (7 / 6 : ℝ) *
        tiltedRademacherThirdMomentSum u
          (fun i => a i / tiltedRademacherStdDev u a) *
        |t| ^ 3 * Real.exp (-(t ^ 2) / 10) := by
  let c : ι → ℝ := fun i => a i / tiltedRademacherStdDev u a
  have hvariance :
      ∑ i, biasedSignVarianceTerm (u i) (c i) = 1 := by
    simpa [biasedSignVarianceTerm] using
      standardizedTiltedRademacherVariance_eq_one u a ha
  rw [standardizedTiltedRademacherChar_eq_prod]
  simpa only [c] using
    norm_prod_centeredBiasedSignChar_sub_standardGaussian_le
      u c t hvariance hcrossover

/--
Esscher-specialized form of the product damping theorem, stated using the
paper's Lyapunov ratio.
-/
theorem norm_rademacherTiltedStandardizedChar_le_exp_neg_sq_div_ten
    (b : ι → ℝ) (x t : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1)
    (hcrossover :
      4 * rademacherLyapunovRatio b x * |t| ≤ 1) :
    ‖charFun (rademacherTiltedStandardizedLaw b x) t‖ ≤
      Real.exp (-(t ^ 2) / 10) := by
  have ha : ∃ i, b i ≠ 0 := by
    by_contra h
    push Not at h
    have hb : b = 0 := funext h
    subst b
    simp at hnorm
  rw [← standardizedTiltedRademacherPMF_toMeasure_specialize b x,
    ← standardizedTiltedRademacherChar_eq_charFun]
  apply norm_standardizedTiltedRademacherChar_le_exp_neg_sq_div_ten
    (fun i => x * b i) b t ha
  rw [tiltedRademacherThirdMomentSum_standardized_specialize b x hnorm]
  exact hcrossover

/--
Esscher-specialized damped product-to-Gaussian discrepancy, in the exact
Lyapunov-ratio notation consumed by the smoothing argument.
-/
theorem norm_charFun_rademacherTiltedStandardizedLaw_sub_standardGaussian_le
    (b : ι → ℝ) (x t : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1)
    (hcrossover :
      4 * rademacherLyapunovRatio b x * |t| ≤ 1) :
    ‖charFun (rademacherTiltedStandardizedLaw b x) t -
        ((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ)‖ ≤
      (7 / 6 : ℝ) * rademacherLyapunovRatio b x *
        |t| ^ 3 * Real.exp (-(t ^ 2) / 10) := by
  have ha : ∃ i, b i ≠ 0 := by
    by_contra h
    push Not at h
    have hb : b = 0 := funext h
    subst b
    simp at hnorm
  rw [← standardizedTiltedRademacherPMF_toMeasure_specialize b x,
    ← standardizedTiltedRademacherChar_eq_charFun]
  have h :=
    norm_standardizedTiltedRademacherChar_sub_standardGaussian_le
      (fun i => x * b i) b t ha
  rw [tiltedRademacherThirdMomentSum_standardized_specialize b x hnorm] at h
  exact h hcrossover

end Product

end Probability
end CertifiedJL
