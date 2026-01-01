/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.NormalApproximation.Lyapunov.SmallLyapunovAnalytic
import CertifiedJL.Probability.NormalApproximation.Rademacher.BiasedSignZeroBias

/-!
# Core finite-band integral estimates for the small-Lyapunov regime

This file connects the sharp deleted-coordinate characteristic-function
majorant to the concrete Prawitz kernel.  The first layer proves that the
apparent `1 / |t|` singularity of the kernel is cancelled by the cubic
characteristic-function remainder.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace CertifiedJL
namespace Probability

universe u_1

variable {ι : Type u_1} [Fintype ι]

/--
Sharp local comparison with the matching Gaussian coordinate, retaining the
fourth-order Gaussian remainder instead of charging it to the third moment.

This is the split needed by Prawitz's `ε'` and `ε''` terms.
-/
theorem norm_centeredBiasedSignChar_sub_gaussian_le_third_add_fourth
    (u a t : ℝ) (hlocal : |t * a| ≤ 1) :
    ‖centeredBiasedSignChar u a t -
        biasedSignGaussianChar u a t‖ ≤
      biasedSignThirdMomentTerm u a * |t| ^ 3 / 6 +
        (biasedSignVarianceTerm u a * t ^ 2 / 2) ^ 2 := by
  let v : ℝ := biasedSignVarianceTerm u a
  let r : ℝ := v * t ^ 2 / 2
  have hv : 0 ≤ v := biasedSignVarianceTerm_nonneg u a
  have hr : 0 ≤ r := by positivity
  have hq : 0 ≤ 1 - Real.tanh u ^ 2 :=
    sub_nonneg.mpr (Real.tanh_sq_lt_one u).le
  have hq_le : 1 - Real.tanh u ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (Real.tanh u)]
  have hrtop : r ≤ 1 := by
    unfold r v biasedSignVarianceTerm
    have hsquare : (t * a) ^ 2 ≤ 1 := by
      have h := sq_le_sq.mpr
        (by simpa using hlocal : |t * a| ≤ |(1 : ℝ)|)
      simpa using h
    nlinarith [mul_le_mul_of_nonneg_right hsquare hq]
  have hgauss :
      ‖biasedSignGaussianChar u a t -
          (1 - (v * t ^ 2 : ℂ) / 2)‖ ≤ r ^ 2 := by
    rw [biasedSignGaussianChar]
    have hR :
        ‖Real.exp (-r) - 1 - (-r)‖ ≤ r ^ 2 := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hr] using
        (Real.norm_exp_sub_one_sub_id_le
          (x := -r)
          (by
            simpa [Real.norm_eq_abs, abs_of_nonneg hr] using hrtop))
    rw [show
        ((Real.exp (-(biasedSignVarianceTerm u a * t ^ 2) / 2) : ℝ) : ℂ) -
            (1 - (v * t ^ 2 : ℂ) / 2) =
          ((Real.exp (-r) - 1 - (-r) : ℝ) : ℂ) by
      dsimp only [r, v]
      push_cast
      ring_nf]
    rw [Complex.norm_real]
    exact hR
  calc
    ‖centeredBiasedSignChar u a t -
          biasedSignGaussianChar u a t‖
        ≤ ‖centeredBiasedSignChar u a t -
              (1 - (v * t ^ 2 : ℂ) / 2)‖ +
            ‖(1 - (v * t ^ 2 : ℂ) / 2) -
              biasedSignGaussianChar u a t‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ biasedSignThirdMomentTerm u a * |t| ^ 3 / 6 + r ^ 2 := by
      gcongr
      · simpa only [v] using
          norm_centeredBiasedSignChar_sub_quadratic_le u a t
      · rw [norm_sub_rev]
        exact hgauss
    _ = biasedSignThirdMomentTerm u a * |t| ^ 3 / 6 +
          (biasedSignVarianceTerm u a * t ^ 2 / 2) ^ 2 := by
      rfl

/--
Fourth-order lower bound for `sin²` on the local frequency band.
-/
theorem sq_sub_one_half_mul_fourth_le_sin_sq
    {z : ℝ} (hz : |z| ≤ 1) :
    z ^ 2 - z ^ 4 / 2 ≤ Real.sin z ^ 2 := by
  have hzπ : |z| ≤ Real.pi :=
    hz.trans (by linarith [Real.two_le_pi])
  rw [← sq_abs z, ← sq_abs (Real.sin z),
    Real.abs_sin_eq_sin_abs_of_abs_le_pi hzπ]
  by_cases hzero : |z| = 0
  · have hz' : z = 0 := abs_eq_zero.mp hzero
    simp [hz']
  have hpos : 0 < |z| := (abs_pos.mpr (abs_ne_zero.mp hzero))
  have hsin := Real.sin_gt_sub_cube hpos
  have hlower :
      |z| - |z| ^ 3 / 4 < Real.sin |z| := by
    linarith [pow_nonneg (abs_nonneg z) 3]
  have hbase : 0 ≤ |z| - |z| ^ 3 / 4 := by
    have hz0 : 0 ≤ |z| := abs_nonneg z
    nlinarith [mul_self_le_mul_self hz0 hz]
  have hsquare :=
    mul_self_le_mul_self hbase hlower.le
  nlinarith [sq_abs z, pow_nonneg (abs_nonneg z) 6]

/-- Global cubic Taylor remainder for cosine. -/
theorem abs_cos_sub_quadratic_le_cube_div_six (z : ℝ) :
    |Real.cos z - (1 - z ^ 2 / 2)| ≤ |z| ^ 3 / 6 := by
  let w : ℂ :=
    Complex.exp ((z : ℂ) * Complex.I) -
      (1 + (z : ℂ) * Complex.I - (z : ℂ) ^ 2 / 2)
  have hw :
      ‖w‖ ≤ |z| ^ 3 / 6 := by
    simpa only [w] using
      norm_exp_mul_I_sub_quadratic_le_cube_div_six z
  have hre : w.re = Real.cos z - (1 - z ^ 2 / 2) := by
    unfold w
    rw [Complex.exp_ofReal_mul_I]
    norm_num
    rw [Complex.cos_ofReal_re, ← Complex.ofReal_pow]
    norm_num
    norm_cast
  rw [← hre]
  exact (Complex.abs_re_le_norm w).trans hw

/-- Global cubic lower bound for `sin²`. -/
theorem sq_sub_two_thirds_mul_abs_cube_le_sin_sq (z : ℝ) :
    z ^ 2 - (2 / 3 : ℝ) * |z| ^ 3 ≤ Real.sin z ^ 2 := by
  have hcos := abs_cos_sub_quadratic_le_cube_div_six (2 * z)
  have hupper :
      Real.cos (2 * z) ≤
        1 - (2 * z) ^ 2 / 2 + |2 * z| ^ 3 / 6 := by
    linarith [le_abs_self
      (Real.cos (2 * z) - (1 - (2 * z) ^ 2 / 2))]
  rw [Real.sin_sq_eq_half_sub]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hupper
  nlinarith

/--
On the local band, the fourth-order correction is charged to the exact
third absolute centered moment.
-/
theorem biasedSignVarianceFrequencyFourth_le_thirdMomentFrequencyCube
    (u a t : ℝ) (hlocal : |t * a| ≤ 1) :
    (1 - Real.tanh u ^ 2) * (t * a) ^ 4 ≤
      biasedSignThirdMomentTerm u a * |t| ^ 3 := by
  let m : ℝ := Real.tanh u
  let q : ℝ := 1 - m ^ 2
  have hq : 0 ≤ q :=
    sub_nonneg.mpr (Real.tanh_sq_lt_one u).le
  have hone : 1 ≤ 1 + m ^ 2 := by
    nlinarith [sq_nonneg m]
  have hz0 : 0 ≤ |t * a| := abs_nonneg _
  have hpow : |t * a| ^ 4 ≤ |t * a| ^ 3 := by
    calc
      |t * a| ^ 4 = |t * a| ^ 3 * |t * a| := by ring
      _ ≤ |t * a| ^ 3 * 1 :=
        mul_le_mul_of_nonneg_left hlocal (pow_nonneg hz0 3)
      _ = |t * a| ^ 3 := by ring
  unfold biasedSignThirdMomentTerm
  dsimp only [m, q] at *
  have heven : (t * a) ^ 4 = |t * a| ^ 4 := by
    rw [← abs_pow]
    exact (abs_of_nonneg (by positivity)).symm
  rw [heven, abs_mul]
  calc
    (1 - Real.tanh u ^ 2) * (|t| * |a|) ^ 4
        ≤ (1 - Real.tanh u ^ 2) * (|t| * |a|) ^ 3 :=
      mul_le_mul_of_nonneg_left (by simpa [abs_mul] using hpow) hq
    _ ≤ (1 - Real.tanh u ^ 2) *
          (1 + Real.tanh u ^ 2) * (|t| * |a|) ^ 3 := by
      let A := (1 - Real.tanh u ^ 2) * (|t| * |a|) ^ 3
      have hA : 0 ≤ A :=
        mul_nonneg hq
          (pow_nonneg
            (mul_nonneg (abs_nonneg t) (abs_nonneg a)) 3)
      calc
        (1 - Real.tanh u ^ 2) * (|t| * |a|) ^ 3 =
            1 * A := by simp [A]
        _ ≤ (1 + Real.tanh u ^ 2) * A :=
          mul_le_mul_of_nonneg_right hone hA
        _ = (1 - Real.tanh u ^ 2) *
            (1 + Real.tanh u ^ 2) * (|t| * |a|) ^ 3 := by
          simp [A]
          ring
    _ = |a| ^ 3 * (1 - Real.tanh u ^ 4) * |t| ^ 3 := by
      ring

/--
Near-Gaussian local modulus for one centered biased-sign coordinate.

Unlike the coarse `exp(-v t²/5)` envelope, this keeps the Gaussian
coefficient `1/2` and pays only an exact third-moment cubic correction.
-/
theorem norm_centeredBiasedSignChar_le_exp_gaussian_cubic
    (u a t : ℝ) (hlocal : |t * a| ≤ 1) :
    ‖centeredBiasedSignChar u a t‖ ≤
      Real.exp
        (-(biasedSignVarianceTerm u a * t ^ 2) / 2 +
          biasedSignThirdMomentTerm u a * |t| ^ 3 / 4) := by
  let q : ℝ := 1 - Real.tanh u ^ 2
  let y : ℝ := biasedSignVarianceTerm u a * t ^ 2
  let c : ℝ := biasedSignThirdMomentTerm u a * |t| ^ 3 / 2
  have hq : 0 ≤ q :=
    sub_nonneg.mpr (Real.tanh_sq_lt_one u).le
  have hsin :
      (t * a) ^ 2 - (t * a) ^ 4 / 2 ≤
        Real.sin (t * a) ^ 2 :=
    sq_sub_one_half_mul_fourth_le_sin_sq hlocal
  have hfourth :
      q * (t * a) ^ 4 ≤
        biasedSignThirdMomentTerm u a * |t| ^ 3 := by
    simpa only [q] using
      biasedSignVarianceFrequencyFourth_le_thirdMomentFrequencyCube
        u a t hlocal
  have hsq :
      ‖centeredBiasedSignChar u a t‖ ^ 2 ≤ 1 - y + c := by
    rw [norm_centeredBiasedSignChar_sq_eq_one_sub]
    unfold y c biasedSignVarianceTerm
    dsimp only [q] at hq hfourth ⊢
    nlinarith [mul_le_mul_of_nonneg_left hsin hq]
  have hexpLower :
      1 - y + c ≤ Real.exp (-y + c) := by
    linarith [Real.add_one_le_exp (-y + c)]
  have hsqExp :
      ‖centeredBiasedSignChar u a t‖ ^ 2 ≤
        (Real.exp
          (-(biasedSignVarianceTerm u a * t ^ 2) / 2 +
            biasedSignThirdMomentTerm u a * |t| ^ 3 / 4)) ^ 2 := by
    calc
      ‖centeredBiasedSignChar u a t‖ ^ 2
          ≤ 1 - y + c := hsq
      _ ≤ Real.exp (-y + c) := hexpLower
      _ = (Real.exp
          (-(biasedSignVarianceTerm u a * t ^ 2) / 2 +
            biasedSignThirdMomentTerm u a * |t| ^ 3 / 4)) ^ 2 := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        unfold y c
        ring
  exact
    (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp hsqExp

/--
Global near-Gaussian modulus with a universal cubic correction.

The coefficient `1/3` is deliberately elementary; the optimized Prawitz
constant replaces it by approximately `0.198324`.
-/
theorem norm_centeredBiasedSignChar_le_exp_gaussian_cubic_global
    (u a t : ℝ) :
    ‖centeredBiasedSignChar u a t‖ ≤
      Real.exp
        (-(biasedSignVarianceTerm u a * t ^ 2) / 2 +
          biasedSignThirdMomentTerm u a * |t| ^ 3 / 3) := by
  let q : ℝ := 1 - Real.tanh u ^ 2
  let y : ℝ := biasedSignVarianceTerm u a * t ^ 2
  let c : ℝ := (2 / 3 : ℝ) *
    biasedSignThirdMomentTerm u a * |t| ^ 3
  have hq : 0 ≤ q :=
    sub_nonneg.mpr (Real.tanh_sq_lt_one u).le
  have hsin :=
    sq_sub_two_thirds_mul_abs_cube_le_sin_sq (t * a)
  have hcharge :
      q * |t * a| ^ 3 ≤
        biasedSignThirdMomentTerm u a * |t| ^ 3 := by
    unfold biasedSignThirdMomentTerm
    rw [abs_mul, mul_pow]
    have hone : 1 ≤ 1 + Real.tanh u ^ 2 := by
      nlinarith [sq_nonneg (Real.tanh u)]
    nlinarith [mul_nonneg
      (mul_nonneg hq (pow_nonneg (abs_nonneg a) 3))
      (pow_nonneg (abs_nonneg t) 3)]
  have hsq :
      ‖centeredBiasedSignChar u a t‖ ^ 2 ≤ 1 - y + c := by
    rw [norm_centeredBiasedSignChar_sq_eq_one_sub]
    unfold y c biasedSignVarianceTerm
    dsimp only [q] at hq hcharge ⊢
    nlinarith [mul_le_mul_of_nonneg_left hsin hq]
  have hexpLower :
      1 - y + c ≤ Real.exp (-y + c) := by
    linarith [Real.add_one_le_exp (-y + c)]
  have hsqExp :
      ‖centeredBiasedSignChar u a t‖ ^ 2 ≤
        (Real.exp
          (-(biasedSignVarianceTerm u a * t ^ 2) / 2 +
            biasedSignThirdMomentTerm u a * |t| ^ 3 / 3)) ^ 2 := by
    calc
      ‖centeredBiasedSignChar u a t‖ ^ 2
          ≤ 1 - y + c := hsq
      _ ≤ Real.exp (-y + c) := hexpLower
      _ = (Real.exp
          (-(biasedSignVarianceTerm u a * t ^ 2) / 2 +
            biasedSignThirdMomentTerm u a * |t| ^ 3 / 3)) ^ 2 := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        unfold y c
        ring
  exact
    (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp hsqExp

/--
Near-Gaussian zero-bias telescope with every deleted-coordinate cubic
modulus retained.  Unlike the outer-band `/5` envelope, this estimate
survives multiplication by `exp(t²/2)` in the differential argument.
-/
theorem norm_prod_centeredBiasedSignChar_sub_productZeroBiasChar_le_gaussianCubic
    [DecidableEq ι]
    (u a : ι → ℝ) (t : ℝ)
    (hvar : ∑ i, biasedSignVarianceTerm (u i) (a i) = 1) :
    ‖(∏ i, centeredBiasedSignChar (u i) (a i) t) -
        centeredBiasedSignProductZeroBiasChar u a t‖ ≤
      ∑ i,
        (biasedSignThirdMomentTerm (u i) (a i) * |t| / 2) *
          ∏ j ∈ Finset.univ.erase i,
            Real.exp
              (-(biasedSignVarianceTerm (u j) (a j) * t ^ 2) / 2 +
                biasedSignThirdMomentTerm (u j) (a j) * |t| ^ 3 / 3) := by
  rw [prod_centeredBiasedSignChar_sub_productZeroBiasChar_eq
    u a t hvar]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (biasedSignVarianceTerm_nonneg (u i) (a i))]
  have hdeleted :
      ‖∏ j ∈ Finset.univ.erase i,
          centeredBiasedSignChar (u j) (a j) t‖ ≤
        ∏ j ∈ Finset.univ.erase i,
          Real.exp
            (-(biasedSignVarianceTerm (u j) (a j) * t ^ 2) / 2 +
              biasedSignThirdMomentTerm (u j) (a j) * |t| ^ 3 / 3) := by
    calc
      ‖∏ j ∈ Finset.univ.erase i,
          centeredBiasedSignChar (u j) (a j) t‖ =
          ∏ j ∈ Finset.univ.erase i,
            ‖centeredBiasedSignChar (u j) (a j) t‖ := by
              simp only [norm_prod]
      _ ≤ ∏ j ∈ Finset.univ.erase i,
          Real.exp
            (-(biasedSignVarianceTerm (u j) (a j) * t ^ 2) / 2 +
              biasedSignThirdMomentTerm (u j) (a j) * |t| ^ 3 / 3) := by
            exact Finset.prod_le_prod
              (fun j _ =>
                norm_nonneg
                  (centeredBiasedSignChar (u j) (a j) t))
              (fun j _ =>
                norm_centeredBiasedSignChar_le_exp_gaussian_cubic_global
                  (u j) (a j) t)
  calc
    biasedSignVarianceTerm (u i) (a i) *
          ‖centeredBiasedSignChar (u i) (a i) t -
            centeredBiasedSignZeroBiasChar (u i) (a i) t‖ *
        ‖∏ j ∈ Finset.univ.erase i,
          centeredBiasedSignChar (u j) (a j) t‖
        ≤ (biasedSignVarianceTerm (u i) (a i) *
          ‖centeredBiasedSignChar (u i) (a i) t -
            centeredBiasedSignZeroBiasChar (u i) (a i) t‖) *
          ∏ j ∈ Finset.univ.erase i,
            Real.exp
              (-(biasedSignVarianceTerm (u j) (a j) * t ^ 2) / 2 +
                biasedSignThirdMomentTerm (u j) (a j) * |t| ^ 3 / 3) := by
      exact mul_le_mul_of_nonneg_left hdeleted
        (mul_nonneg (biasedSignVarianceTerm_nonneg (u i) (a i))
          (norm_nonneg _))
    _ ≤ (biasedSignThirdMomentTerm (u i) (a i) * |t| / 2) *
          ∏ j ∈ Finset.univ.erase i,
            Real.exp
              (-(biasedSignVarianceTerm (u j) (a j) * t ^ 2) / 2 +
                biasedSignThirdMomentTerm (u j) (a j) * |t| ^ 3 / 3) := by
      exact mul_le_mul_of_nonneg_right
        (biasedSignVariance_mul_norm_char_sub_zeroBiasChar_le
          (u i) (a i) t)
        (Finset.prod_nonneg fun j _ => (Real.exp_pos _).le)

/--
Multiplication by the Gaussian renormalization cancels the deleted
variance exactly, leaving only the omitted coordinate variance and the
deleted cubic correction.
-/
theorem exp_half_sq_mul_prod_gaussianCubic_erase_eq
    [DecidableEq ι]
    (u a : ι → ℝ) (t : ℝ) (i : ι)
    (hvar : ∑ j, biasedSignVarianceTerm (u j) (a j) = 1) :
    Real.exp (t ^ 2 / 2) *
        ∏ j ∈ Finset.univ.erase i,
          Real.exp
            (-(biasedSignVarianceTerm (u j) (a j) * t ^ 2) / 2 +
              biasedSignThirdMomentTerm (u j) (a j) * |t| ^ 3 / 3) =
      Real.exp
        (biasedSignVarianceTerm (u i) (a i) * t ^ 2 / 2 +
          (∑ j ∈ Finset.univ.erase i,
            biasedSignThirdMomentTerm (u j) (a j)) * |t| ^ 3 / 3) := by
  have hvarianceErase :
      ∑ j ∈ Finset.univ.erase i,
          biasedSignVarianceTerm (u j) (a j) =
        1 - biasedSignVarianceTerm (u i) (a i) := by
    have h :=
      Finset.sum_erase_add
        (s := Finset.univ)
        (f := fun j => biasedSignVarianceTerm (u j) (a j))
        (Finset.mem_univ i)
    rw [hvar] at h
    linarith
  rw [← Real.exp_sum, ← Real.exp_add]
  congr 1
  rw [Finset.sum_add_distrib]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  rw [Finset.sum_neg_distrib, ← Finset.sum_mul,
    ← Finset.sum_mul]
  rw [hvarianceErase]
  ring

/-- Coordinate Lyapunov inequality in the unbundled biased-sign notation. -/
theorem biasedSignVarianceTerm_cube_le_thirdMomentTerm_sq
    (u a : ℝ) :
    biasedSignVarianceTerm u a ^ 3 ≤
      biasedSignThirdMomentTerm u a ^ 2 := by
  let m : ℝ := Real.tanh u
  have hm : m ^ 2 ≤ 1 := (Real.tanh_sq_lt_one u).le
  have hcore :
      (1 - m ^ 2) ^ 3 ≤
        ((1 - m ^ 2) * (1 + m ^ 2)) ^ 2 := by
    have hbase : 1 - m ^ 2 ≤ (1 + m ^ 2) ^ 2 := by
      nlinarith [sq_nonneg (m ^ 2)]
    calc
      (1 - m ^ 2) ^ 3 =
          (1 - m ^ 2) ^ 2 * (1 - m ^ 2) := by ring
      _ ≤ (1 - m ^ 2) ^ 2 * (1 + m ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hbase (sq_nonneg _)
      _ = ((1 - m ^ 2) * (1 + m ^ 2)) ^ 2 := by ring
  have ha : 0 ≤ |a| ^ 6 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hcore ha
  unfold biasedSignVarianceTerm biasedSignThirdMomentTerm
  dsimp only [m] at hm hscaled ⊢
  rw [show 1 - Real.tanh u ^ 4 =
      (1 - Real.tanh u ^ 2) *
        (1 + Real.tanh u ^ 2) by ring]
  calc
    (a ^ 2 * (1 - Real.tanh u ^ 2)) ^ 3 =
        |a| ^ 6 * (1 - Real.tanh u ^ 2) ^ 3 := by
      rw [mul_pow]
      nth_rewrite 1 [← sq_abs a]
      ring
    _ ≤ |a| ^ 6 *
        ((1 - Real.tanh u ^ 2) *
          (1 + Real.tanh u ^ 2)) ^ 2 := hscaled
    _ = (|a| ^ 3 *
        ((1 - Real.tanh u ^ 2) *
          (1 + Real.tanh u ^ 2))) ^ 2 := by ring

/--
Any upper bound on a coordinate's third moment yields the usual
two-thirds-power upper bound on its variance.
-/
theorem biasedSignVarianceTerm_le_lyapunovVarianceCap
    {u a L : ℝ} (hL : 0 ≤ L)
    (hthird : biasedSignThirdMomentTerm u a ≤ L) :
    biasedSignVarianceTerm u a ≤ lyapunovVarianceCap L := by
  have hv := biasedSignVarianceTerm_nonneg u a
  have hbeta := biasedSignThirdMomentTerm_nonneg u a
  have hcubic :
      biasedSignVarianceTerm u a ^ 3 ≤ L ^ 2 := by
    calc
      biasedSignVarianceTerm u a ^ 3
          ≤ biasedSignThirdMomentTerm u a ^ 2 :=
        biasedSignVarianceTerm_cube_le_thirdMomentTerm_sq u a
      _ ≤ L ^ 2 := by nlinarith
  apply (pow_le_pow_iff_left₀ hv (lyapunovVarianceCap_nonneg hL)
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  rw [lyapunovVarianceCap_cube hL]
  exact hcubic

/--
One-variable envelope for the Gaussian-renormalized zero-bias
discrepancy.  `V` is any uniform coordinate-variance cap and `L` is the
total third absolute moment.
-/
theorem exp_half_sq_mul_norm_prod_sub_productZeroBiasChar_le_scalar
    [DecidableEq ι]
    (u a : ι → ℝ) (t V L : ℝ)
    (hvar : ∑ i, biasedSignVarianceTerm (u i) (a i) = 1)
    (hthird : ∑ i, biasedSignThirdMomentTerm (u i) (a i) = L)
    (hvarianceCap :
      ∀ i, biasedSignVarianceTerm (u i) (a i) ≤ V) :
    Real.exp (t ^ 2 / 2) *
        ‖(∏ i, centeredBiasedSignChar (u i) (a i) t) -
          centeredBiasedSignProductZeroBiasChar u a t‖ ≤
      L * |t| / 2 *
        Real.exp (V * t ^ 2 / 2 + L * |t| ^ 3 / 3) := by
  have hbase :=
    norm_prod_centeredBiasedSignChar_sub_productZeroBiasChar_le_gaussianCubic
      u a t hvar
  calc
    Real.exp (t ^ 2 / 2) *
        ‖(∏ i, centeredBiasedSignChar (u i) (a i) t) -
          centeredBiasedSignProductZeroBiasChar u a t‖
        ≤ Real.exp (t ^ 2 / 2) *
          ∑ i,
            (biasedSignThirdMomentTerm (u i) (a i) * |t| / 2) *
              ∏ j ∈ Finset.univ.erase i,
                Real.exp
                  (-(biasedSignVarianceTerm (u j) (a j) * t ^ 2) / 2 +
                    biasedSignThirdMomentTerm (u j) (a j) * |t| ^ 3 / 3) :=
      mul_le_mul_of_nonneg_left hbase (Real.exp_pos _).le
    _ = ∑ i,
          (biasedSignThirdMomentTerm (u i) (a i) * |t| / 2) *
            Real.exp
              (biasedSignVarianceTerm (u i) (a i) * t ^ 2 / 2 +
                (∑ j ∈ Finset.univ.erase i,
                  biasedSignThirdMomentTerm (u j) (a j)) *
                    |t| ^ 3 / 3) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [show Real.exp (t ^ 2 / 2) *
          ((biasedSignThirdMomentTerm (u i) (a i) * |t| / 2) *
            ∏ j ∈ Finset.univ.erase i,
              Real.exp
                (-(biasedSignVarianceTerm (u j) (a j) * t ^ 2) / 2 +
                  biasedSignThirdMomentTerm (u j) (a j) * |t| ^ 3 / 3)) =
        (biasedSignThirdMomentTerm (u i) (a i) * |t| / 2) *
          (Real.exp (t ^ 2 / 2) *
            ∏ j ∈ Finset.univ.erase i,
              Real.exp
                (-(biasedSignVarianceTerm (u j) (a j) * t ^ 2) / 2 +
                  biasedSignThirdMomentTerm (u j) (a j) * |t| ^ 3 / 3)) by ring]
      rw [exp_half_sq_mul_prod_gaussianCubic_erase_eq u a t i hvar]
    _ ≤ ∑ i,
          (biasedSignThirdMomentTerm (u i) (a i) * |t| / 2) *
            Real.exp (V * t ^ 2 / 2 + L * |t| ^ 3 / 3) := by
      apply Finset.sum_le_sum
      intro i _
      have hthirdErase :
          ∑ j ∈ Finset.univ.erase i,
              biasedSignThirdMomentTerm (u j) (a j) ≤ L := by
        have h :=
          Finset.sum_erase_add
            (s := Finset.univ)
            (f := fun j => biasedSignThirdMomentTerm (u j) (a j))
            (Finset.mem_univ i)
        rw [hthird] at h
        linarith [biasedSignThirdMomentTerm_nonneg (u i) (a i)]
      apply mul_le_mul_of_nonneg_left
      · apply Real.exp_le_exp.mpr
        have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
        have ht3 : 0 ≤ |t| ^ 3 := by positivity
        nlinarith [hvarianceCap i]
      · exact div_nonneg
          (mul_nonneg
            (biasedSignThirdMomentTerm_nonneg (u i) (a i))
            (abs_nonneg t))
          (by norm_num)
    _ = L * |t| / 2 *
          Real.exp (V * t ^ 2 / 2 + L * |t| ^ 3 / 3) := by
      have hsum :
          (∑ i, biasedSignThirdMomentTerm (u i) (a i) * |t| / 2) =
            (∑ i, biasedSignThirdMomentTerm (u i) (a i)) * |t| / 2 := by
        rw [← Finset.sum_div]
        rw [← Finset.sum_mul]
      rw [← Finset.sum_mul, hsum, hthird]

/-- Small-Lyapunov specialization of the scalar differential envelope. -/
theorem exp_half_sq_mul_norm_prod_sub_productZeroBiasChar_le_lyapunov
    [DecidableEq ι]
    (u a : ι → ℝ) (t L : ℝ)
    (hL : 0 ≤ L)
    (hvar : ∑ i, biasedSignVarianceTerm (u i) (a i) = 1)
    (hthird : ∑ i, biasedSignThirdMomentTerm (u i) (a i) = L) :
    Real.exp (t ^ 2 / 2) *
        ‖(∏ i, centeredBiasedSignChar (u i) (a i) t) -
          centeredBiasedSignProductZeroBiasChar u a t‖ ≤
      L * |t| / 2 *
        Real.exp
          (lyapunovVarianceCap L * t ^ 2 / 2 +
            L * |t| ^ 3 / 3) := by
  apply exp_half_sq_mul_norm_prod_sub_productZeroBiasChar_le_scalar
    u a t (lyapunovVarianceCap L) L hvar hthird
  intro i
  apply biasedSignVarianceTerm_le_lyapunovVarianceCap hL
  rw [← hthird]
  exact Finset.single_le_sum
    (fun j _ => biasedSignThirdMomentTerm_nonneg (u j) (a j))
    (Finset.mem_univ i)

/--
Integrated near-Gaussian comparison on a nonnegative frequency interval.
The right-hand side is a one-dimensional scalar integral parameterized by
`L`, suitable for certified interval evaluation.
-/
theorem norm_gaussianRenormalized_product_sub_one_le_integral
    (u a : ι → ℝ) {t L : ℝ}
    (ht : 0 ≤ t) (hL : 0 ≤ L)
    (hvar : ∑ i, biasedSignVarianceTerm (u i) (a i) = 1)
    (hthird : ∑ i, biasedSignThirdMomentTerm (u i) (a i) = L) :
    ‖Complex.exp (((t ^ 2 / 2 : ℝ) : ℂ)) *
          (∏ i, centeredBiasedSignChar (u i) (a i) t) - 1‖ ≤
      ∫ s : ℝ in 0..t,
        L * s ^ 2 / 2 *
          Real.exp
            (lyapunovVarianceCap L * s ^ 2 / 2 +
              L * s ^ 3 / 3) := by
  classical
  let F : ℝ → ℂ := fun s =>
    Complex.exp (((s ^ 2 / 2 : ℝ) : ℂ)) *
      ∏ i, centeredBiasedSignChar (u i) (a i) s
  let D : ℝ → ℂ := fun s =>
    Complex.exp (((s ^ 2 / 2 : ℝ) : ℂ)) * (s : ℂ) *
      ((∏ i, centeredBiasedSignChar (u i) (a i) s) -
        centeredBiasedSignProductZeroBiasChar u a s)
  have hderiv : ∀ s, HasDerivAt F (D s) s := by
    intro s
    exact
      hasDerivAt_gaussianRenormalized_centeredBiasedSignChar_product
        u a s
  have hcharCont (i : ι) :
      Continuous (centeredBiasedSignChar (u i) (a i)) := by
    rw [continuous_iff_continuousAt]
    intro s
    exact
      (hasDerivAt_centeredBiasedSignChar (u i) (a i) s).continuousAt
  have hzeroCont (i : ι) :
      Continuous (centeredBiasedSignZeroBiasChar (u i) (a i)) := by
    unfold centeredBiasedSignZeroBiasChar
    fun_prop
  have hprodCont :
      Continuous
        (fun s : ℝ =>
          ∏ i, centeredBiasedSignChar (u i) (a i) s) :=
    continuous_finsetProd Finset.univ fun i _ => hcharCont i
  have hzeroProductCont :
      Continuous (centeredBiasedSignProductZeroBiasChar u a) := by
    unfold centeredBiasedSignProductZeroBiasChar
    apply continuous_finsetSum Finset.univ
    intro i _
    exact ((continuous_const.mul (hzeroCont i)).mul
      (continuous_finsetProd (Finset.univ.erase i)
        fun j _ => hcharCont j))
  have hDcont : Continuous D := by
    dsimp [D]
    have hfront :
        Continuous (fun s : ℝ =>
          Complex.exp (((s ^ 2 / 2 : ℝ) : ℂ)) * (s : ℂ)) := by
      fun_prop
    exact hfront.mul (hprodCont.sub hzeroProductCont)
  have hFTC :
      (∫ s : ℝ in 0..t, D s) = F t - F 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hderiv s)
      (hDcont.intervalIntegrable 0 t)
  have hFzero : F 0 = 1 := by
    dsimp [F]
    rw [show Complex.exp (((0 ^ 2 / 2 : ℝ) : ℂ)) = 1 by norm_num,
      one_mul]
    apply Finset.prod_eq_one
    intro i _
    rw [centeredBiasedSignChar_eq]
    norm_num
  rw [← hFzero, ← hFTC]
  apply intervalIntegral.norm_integral_le_of_norm_le ht
  · filter_upwards with s hs
    have hs0 : 0 ≤ s := hs.1.le
    have hpoint :=
      exp_half_sq_mul_norm_prod_sub_productZeroBiasChar_le_lyapunov
        u a s L hL hvar hthird
    dsimp [D]
    rw [norm_mul, norm_mul, Complex.norm_exp,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
    have hexpReal :
        Real.exp ((↑((s ^ 2 / 2 : ℝ)) : ℂ).re) =
          Real.exp (s ^ 2 / 2) := by
      norm_cast
    rw [hexpReal]
    calc
      Real.exp (s ^ 2 / 2) * s *
          ‖(∏ i, centeredBiasedSignChar (u i) (a i) s) -
            centeredBiasedSignProductZeroBiasChar u a s‖
          = s * (Real.exp (s ^ 2 / 2) *
            ‖(∏ i, centeredBiasedSignChar (u i) (a i) s) -
              centeredBiasedSignProductZeroBiasChar u a s‖) := by ring
      _ ≤ s * (L * |s| / 2 *
          Real.exp
            (lyapunovVarianceCap L * s ^ 2 / 2 +
              L * |s| ^ 3 / 3)) :=
        mul_le_mul_of_nonneg_left hpoint hs0
      _ = L * s ^ 2 / 2 *
          Real.exp
            (lyapunovVarianceCap L * s ^ 2 / 2 +
              L * s ^ 3 / 3) := by
        rw [abs_of_nonneg hs0]
        ring
  · have hscalar :
        Continuous (fun s : ℝ =>
        L * s ^ 2 / 2 *
          Real.exp
            (lyapunovVarianceCap L * s ^ 2 / 2 +
              L * s ^ 3 / 3)) := by
      fun_prop
    exact hscalar.intervalIntegrable _ _

/--
Tyurin's first characteristic-function discrepancy bound, before restoring
the Gaussian factor.  This is the direct integral of the sharp zero-bias
coupling estimate; unlike the refined small-frequency bound above, it is
global in the frequency.
-/
theorem norm_gaussianRenormalized_product_sub_one_le_deltaOneIntegral
    (u a : ι → ℝ) {t L : ℝ}
    (ht : 0 ≤ t)
    (hvar : ∑ i, biasedSignVarianceTerm (u i) (a i) = 1)
    (hthird : ∑ i, biasedSignThirdMomentTerm (u i) (a i) = L) :
    ‖Complex.exp (((t ^ 2 / 2 : ℝ) : ℂ)) *
          (∏ i, centeredBiasedSignChar (u i) (a i) t) - 1‖ ≤
      ∫ s : ℝ in 0..t,
        L * s ^ 2 / 2 * Real.exp (s ^ 2 / 2) := by
  classical
  let F : ℝ → ℂ := fun s =>
    Complex.exp (((s ^ 2 / 2 : ℝ) : ℂ)) *
      ∏ i, centeredBiasedSignChar (u i) (a i) s
  let D : ℝ → ℂ := fun s =>
    Complex.exp (((s ^ 2 / 2 : ℝ) : ℂ)) * (s : ℂ) *
      ((∏ i, centeredBiasedSignChar (u i) (a i) s) -
        centeredBiasedSignProductZeroBiasChar u a s)
  have hderiv : ∀ s, HasDerivAt F (D s) s := by
    intro s
    exact
      hasDerivAt_gaussianRenormalized_centeredBiasedSignChar_product
        u a s
  have hcharCont (i : ι) :
      Continuous (centeredBiasedSignChar (u i) (a i)) := by
    rw [continuous_iff_continuousAt]
    intro s
    exact
      (hasDerivAt_centeredBiasedSignChar (u i) (a i) s).continuousAt
  have hzeroCont (i : ι) :
      Continuous (centeredBiasedSignZeroBiasChar (u i) (a i)) := by
    unfold centeredBiasedSignZeroBiasChar
    fun_prop
  have hprodCont :
      Continuous
        (fun s : ℝ =>
          ∏ i, centeredBiasedSignChar (u i) (a i) s) :=
    continuous_finsetProd Finset.univ fun i _ => hcharCont i
  have hzeroProductCont :
      Continuous (centeredBiasedSignProductZeroBiasChar u a) := by
    unfold centeredBiasedSignProductZeroBiasChar
    apply continuous_finsetSum Finset.univ
    intro i _
    exact ((continuous_const.mul (hzeroCont i)).mul
      (continuous_finsetProd (Finset.univ.erase i)
        fun j _ => hcharCont j))
  have hDcont : Continuous D := by
    dsimp [D]
    have hfront :
        Continuous (fun s : ℝ =>
          Complex.exp (((s ^ 2 / 2 : ℝ) : ℂ)) * (s : ℂ)) := by
      fun_prop
    exact hfront.mul (hprodCont.sub hzeroProductCont)
  have hFTC :
      (∫ s : ℝ in 0..t, D s) = F t - F 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hderiv s)
      (hDcont.intervalIntegrable 0 t)
  have hFzero : F 0 = 1 := by
    dsimp [F]
    rw [show Complex.exp (((0 ^ 2 / 2 : ℝ) : ℂ)) = 1 by norm_num,
      one_mul]
    apply Finset.prod_eq_one
    intro i _
    rw [centeredBiasedSignChar_eq]
    norm_num
  rw [← hFzero, ← hFTC]
  apply intervalIntegral.norm_integral_le_of_norm_le ht
  · filter_upwards with s hs
    have hs0 : 0 ≤ s := hs.1.le
    have hpoint :=
      norm_prod_centeredBiasedSignChar_sub_productZeroBiasChar_le
        u a s hvar
    have hsum :
        (∑ i, biasedSignThirdMomentTerm (u i) (a i) * |s| / 2) =
          L * |s| / 2 := by
      rw [← Finset.sum_div, ← Finset.sum_mul, hthird]
    rw [hsum] at hpoint
    dsimp [D]
    rw [norm_mul, norm_mul, Complex.norm_exp,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
    have hexpReal :
        Real.exp ((↑((s ^ 2 / 2 : ℝ)) : ℂ).re) =
          Real.exp (s ^ 2 / 2) := by
      norm_cast
    rw [hexpReal]
    calc
      Real.exp (s ^ 2 / 2) * s *
          ‖(∏ i, centeredBiasedSignChar (u i) (a i) s) -
            centeredBiasedSignProductZeroBiasChar u a s‖
          ≤ Real.exp (s ^ 2 / 2) * s * (L * |s| / 2) :=
        mul_le_mul_of_nonneg_left hpoint
          (mul_nonneg (Real.exp_nonneg _) hs0)
      _ = L * s ^ 2 / 2 * Real.exp (s ^ 2 / 2) := by
        rw [abs_of_nonneg hs0]
        ring
  · have hscalar :
        Continuous (fun s : ℝ =>
          L * s ^ 2 / 2 * Real.exp (s ^ 2 / 2)) := by
      fun_prop
    exact hscalar.intervalIntegrable _ _

/--
Tyurin's global `deltaOne` bound in the form consumed by the Prawitz core
integral.
-/
theorem norm_product_sub_standardGaussian_le_deltaOne
    (u a : ι → ℝ) {t L : ℝ}
    (ht : 0 ≤ t)
    (hvar : ∑ i, biasedSignVarianceTerm (u i) (a i) = 1)
    (hthird : ∑ i, biasedSignThirdMomentTerm (u i) (a i) = L) :
    ‖(∏ i, centeredBiasedSignChar (u i) (a i) t) -
        ((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ)‖ ≤
      L * Real.exp (-(t ^ 2) / 2) *
        (∫ s : ℝ in 0..t,
          s ^ 2 / 2 * Real.exp (s ^ 2 / 2)) := by
  have hrenorm :=
    norm_gaussianRenormalized_product_sub_one_le_deltaOneIntegral
      u a ht hvar hthird
  have hfactor :
      (∏ i, centeredBiasedSignChar (u i) (a i) t) -
          ((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ) =
        ((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ) *
          (Complex.exp (((t ^ 2 / 2 : ℝ) : ℂ)) *
            (∏ i, centeredBiasedSignChar (u i) (a i) t) - 1) := by
    have hcancel :
        ((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ) *
            Complex.exp (((t ^ 2 / 2 : ℝ) : ℂ)) = 1 := by
      rw [← Complex.ofReal_exp]
      push_cast
      rw [← Complex.exp_add]
      ring_nf
      simp
    symm
    calc
      ((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ) *
            (Complex.exp (((t ^ 2 / 2 : ℝ) : ℂ)) *
              (∏ i, centeredBiasedSignChar (u i) (a i) t) - 1)
          = (((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ) *
              Complex.exp (((t ^ 2 / 2 : ℝ) : ℂ))) *
                (∏ i, centeredBiasedSignChar (u i) (a i) t) -
              ((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ) := by ring
      _ = _ := by rw [hcancel, one_mul]
  rw [hfactor, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  calc
    Real.exp (-(t ^ 2) / 2) *
          ‖Complex.exp (((t ^ 2 / 2 : ℝ) : ℂ)) *
              (∏ i, centeredBiasedSignChar (u i) (a i) t) - 1‖
        ≤ Real.exp (-(t ^ 2) / 2) *
            (∫ s : ℝ in 0..t,
              L * s ^ 2 / 2 * Real.exp (s ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left hrenorm (Real.exp_nonneg _)
    _ = L * Real.exp (-(t ^ 2) / 2) *
          (∫ s : ℝ in 0..t,
            s ^ 2 / 2 * Real.exp (s ^ 2 / 2)) := by
      have hint :
          (∫ s : ℝ in 0..t,
              L * s ^ 2 / 2 * Real.exp (s ^ 2 / 2)) =
            L * (∫ s : ℝ in 0..t,
              s ^ 2 / 2 * Real.exp (s ^ 2 / 2)) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro s _
        ring
      rw [hint]
      ring

/--
Integrated near-Gaussian comparison for the actual standardized Esscher
tilt of a normalized Rademacher sum.
-/
theorem norm_gaussianRenormalized_rademacherTiltedCharFun_sub_one_le_integral
    (b : ι → ℝ) (x : ℝ) {t : ℝ}
    (hnorm : ∑ i, b i ^ 2 = 1) (ht : 0 ≤ t) :
    ‖Complex.exp (((t ^ 2 / 2 : ℝ) : ℂ)) *
          charFun (rademacherTiltedStandardizedLaw b x) t - 1‖ ≤
      ∫ s : ℝ in 0..t,
        rademacherLyapunovRatio b x * s ^ 2 / 2 *
          Real.exp
            (lyapunovVarianceCap (rademacherLyapunovRatio b x) *
                s ^ 2 / 2 +
              rademacherLyapunovRatio b x * s ^ 3 / 3) := by
  classical
  let u : ι → ℝ := fun i => x * b i
  let a : ι → ℝ := fun i =>
    b i / tiltedRademacherStdDev u b
  have hb : ∃ i, b i ≠ 0 := by
    by_contra h
    push Not at h
    have hbzero : b = 0 := by
      funext i
      exact h i
    subst b
    simp at hnorm
  have hvar :
      ∑ i, biasedSignVarianceTerm (u i) (a i) = 1 := by
    simpa only [biasedSignVarianceTerm, u, a] using
      standardizedTiltedRademacherVariance_eq_one u b hb
  have hthird :
      ∑ i, biasedSignThirdMomentTerm (u i) (a i) =
        rademacherLyapunovRatio b x := by
    change tiltedRademacherThirdMomentSum u a =
      rademacherLyapunovRatio b x
    exact tiltedRademacherThirdMomentSum_standardized_specialize
      b x hnorm
  have hchar :
      charFun (rademacherTiltedStandardizedLaw b x) t =
        ∏ i, centeredBiasedSignChar (u i) (a i) t := by
    rw [charFun_rademacherTiltedStandardizedLaw_eq_prod]
    apply Finset.prod_congr rfl
    intro i _
    dsimp [u, a]
    rw [tiltedRademacherStdDev_specialize]
  rw [hchar]
  exact norm_gaussianRenormalized_product_sub_one_le_integral
    u a ht (rademacherLyapunovRatio_nonneg b x) hvar hthird

/--
Tyurin's global `deltaOne` estimate for the standardized Esscher tilt of a
normalized Rademacher sum.
-/
theorem norm_rademacherTiltedCharFun_sub_standardGaussian_le_deltaOne
    (b : ι → ℝ) (x : ℝ) {t : ℝ}
    (hnorm : ∑ i, b i ^ 2 = 1) (ht : 0 ≤ t) :
    ‖charFun (rademacherTiltedStandardizedLaw b x) t -
        ((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ)‖ ≤
      rademacherLyapunovRatio b x * Real.exp (-(t ^ 2) / 2) *
        (∫ s : ℝ in 0..t,
          s ^ 2 / 2 * Real.exp (s ^ 2 / 2)) := by
  classical
  let u : ι → ℝ := fun i => x * b i
  let a : ι → ℝ := fun i =>
    b i / tiltedRademacherStdDev u b
  have hb : ∃ i, b i ≠ 0 := by
    by_contra h
    push Not at h
    have hbzero : b = 0 := by
      funext i
      exact h i
    subst b
    simp at hnorm
  have hvar :
      ∑ i, biasedSignVarianceTerm (u i) (a i) = 1 := by
    simpa only [biasedSignVarianceTerm, u, a] using
      standardizedTiltedRademacherVariance_eq_one u b hb
  have hthird :
      ∑ i, biasedSignThirdMomentTerm (u i) (a i) =
        rademacherLyapunovRatio b x := by
    change tiltedRademacherThirdMomentSum u a =
      rademacherLyapunovRatio b x
    exact tiltedRademacherThirdMomentSum_standardized_specialize
      b x hnorm
  have hchar :
      charFun (rademacherTiltedStandardizedLaw b x) t =
        ∏ i, centeredBiasedSignChar (u i) (a i) t := by
    rw [charFun_rademacherTiltedStandardizedLaw_eq_prod]
    apply Finset.prod_congr rfl
    intro i _
    dsimp [u, a]
    rw [tiltedRademacherStdDev_specialize]
  rw [hchar]
  exact norm_product_sub_standardGaussian_le_deltaOne
    u a ht hvar hthird

/-- Near-Gaussian modulus envelope for one local coordinate. -/
noncomputable def biasedSignGaussianCubicMajorant
    (u a t : ℝ) : ℝ :=
  Real.exp
    (-(biasedSignVarianceTerm u a * t ^ 2) / 2 +
      biasedSignThirdMomentTerm u a * |t| ^ 3 / 4)

/-- Third-plus-fourth-order local comparison remainder. -/
noncomputable def biasedSignThirdFourthRemainder
    (u a t : ℝ) : ℝ :=
  biasedSignThirdMomentTerm u a * |t| ^ 3 / 6 +
    (biasedSignVarianceTerm u a * t ^ 2 / 2) ^ 2

theorem biasedSignGaussianCubicMajorant_nonneg
    (u a t : ℝ) :
    0 ≤ biasedSignGaussianCubicMajorant u a t :=
  (Real.exp_pos _).le

theorem biasedSignThirdFourthRemainder_nonneg
    (u a t : ℝ) :
    0 ≤ biasedSignThirdFourthRemainder u a t := by
  unfold biasedSignThirdFourthRemainder
  exact add_nonneg
    (div_nonneg
      (mul_nonneg (biasedSignThirdMomentTerm_nonneg _ _)
        (by positivity))
      (by norm_num))
    (sq_nonneg _)

theorem norm_biasedSignGaussianChar_le_gaussianCubicMajorant
    (u a t : ℝ) :
    ‖biasedSignGaussianChar u a t‖ ≤
      biasedSignGaussianCubicMajorant u a t := by
  rw [norm_biasedSignGaussianChar]
  unfold biasedSignGaussianCubicMajorant
  apply Real.exp_le_exp.mpr
  have hthird := biasedSignThirdMomentTerm_nonneg u a
  have ht : 0 ≤ |t| ^ 3 := by positivity
  nlinarith

/--
Near-Gaussian product telescope on a fully local frequency band.

The comparison retains separately the exact third-moment and squared-
variance remainders and all deleted-coordinate Gaussian-cubic damping.
-/
theorem norm_prod_centeredBiasedSignChar_sub_prod_gaussian_le_sharpLocal
    [DecidableEq ι]
    (u a : ι → ℝ) (t : ℝ)
    (hlocal : ∀ i, |t * a i| ≤ 1) :
    ‖(∏ i, centeredBiasedSignChar (u i) (a i) t) -
        ∏ i, biasedSignGaussianChar (u i) (a i) t‖ ≤
      ∑ i,
        biasedSignThirdFourthRemainder (u i) (a i) t *
          ∏ j ∈ Finset.univ.erase i,
            biasedSignGaussianCubicMajorant (u j) (a j) t := by
  classical
  calc
    ‖(∏ i, centeredBiasedSignChar (u i) (a i) t) -
        ∏ i, biasedSignGaussianChar (u i) (a i) t‖
        ≤ ∑ i ∈ Finset.univ,
            ‖centeredBiasedSignChar (u i) (a i) t -
                biasedSignGaussianChar (u i) (a i) t‖ *
              ∏ j ∈ Finset.univ.erase i,
                biasedSignGaussianCubicMajorant (u j) (a j) t := by
      apply norm_prod_sub_prod_le_sum_erase
      · intro i _
        simpa only [biasedSignGaussianCubicMajorant] using
          norm_centeredBiasedSignChar_le_exp_gaussian_cubic
            (u i) (a i) t (hlocal i)
      · intro i _
        exact
          norm_biasedSignGaussianChar_le_gaussianCubicMajorant
            (u i) (a i) t
      · intro i _
        exact biasedSignGaussianCubicMajorant_nonneg _ _ _
    _ ≤ ∑ i,
        biasedSignThirdFourthRemainder (u i) (a i) t *
          ∏ j ∈ Finset.univ.erase i,
            biasedSignGaussianCubicMajorant (u j) (a j) t := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right
      · simpa only [biasedSignThirdFourthRemainder] using
          norm_centeredBiasedSignChar_sub_gaussian_le_third_add_fourth
            (u i) (a i) t (hlocal i)
      · exact Finset.prod_nonneg fun j _ =>
          biasedSignGaussianCubicMajorant_nonneg _ _ _

/--
Sharp fully local comparison for the actual standardized Esscher-tilted
Rademacher law.
-/
theorem norm_charFun_rademacherTiltedStandardizedLaw_sub_gaussian_le_sharpLocal
    [DecidableEq ι]
    (b : ι → ℝ) (x t : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1)
    (hlocal :
      ∀ i,
        |t * (b i /
          tiltedRademacherStdDev (fun j => x * b j) b)| ≤ 1) :
    ‖charFun (rademacherTiltedStandardizedLaw b x) t -
        ((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ)‖ ≤
      ∑ i,
        biasedSignThirdFourthRemainder
            (x * b i)
            (b i /
              tiltedRademacherStdDev (fun j => x * b j) b) t *
          ∏ j ∈ Finset.univ.erase i,
            biasedSignGaussianCubicMajorant
              (x * b j)
              (b j /
                tiltedRademacherStdDev (fun k => x * b k) b) t := by
  let u : ι → ℝ := fun i => x * b i
  let c : ι → ℝ := fun i =>
    b i / tiltedRademacherStdDev u b
  have ha : ∃ i, b i ≠ 0 := by
    by_contra h
    push Not at h
    have hb : b = 0 := funext h
    subst b
    simp at hnorm
  have hvariance :
      ∑ i, biasedSignVarianceTerm (u i) (c i) = 1 := by
    simpa [biasedSignVarianceTerm, u, c] using
      standardizedTiltedRademacherVariance_eq_one
        (fun i => x * b i) b ha
  rw [← standardizedTiltedRademacherPMF_toMeasure_specialize b x,
    ← standardizedTiltedRademacherChar_eq_charFun,
    standardizedTiltedRademacherChar_eq_prod]
  rw [← show
    (∏ i, biasedSignGaussianChar (u i) (c i) t) =
      ((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ) by
    rw [prod_biasedSignGaussianChar_eq, hvariance]
    congr 2
    ring]
  simpa only [u, c] using
    norm_prod_centeredBiasedSignChar_sub_prod_gaussian_le_sharpLocal
      (fun i => x * b i)
      (fun i =>
        b i / tiltedRademacherStdDev (fun j => x * b j) b)
      t hlocal

/-- One summand of the sharp deleted-coordinate majorant. -/
noncomputable def tiltedRademacherGaussianCFCoordinateMajorant
    (b : ι → ℝ) (x : ℝ) (i : ι) (t : ℝ) : ℝ :=
  let u : ι → ℝ := fun j => x * b j
  let c : ι → ℝ := fun j =>
    b j / tiltedRademacherStdDev u b
  (if |t * c i| ≤ 1 then (5 / 12 : ℝ) else 7 / 6) *
    biasedSignThirdMomentTerm (u i) (c i) * |t| ^ 3 *
    Real.exp
      (-((tiltedRademacherLocalVariance u c t -
          if |t * c i| ≤ 1 then
            biasedSignVarianceTerm (u i) (c i)
          else 0) * t ^ 2) / 5)

theorem tiltedRademacherGaussianCFMajorant_eq_sum_coordinate
    (b : ι → ℝ) (x t : ℝ) :
    tiltedRademacherGaussianCFMajorant b x t =
      ∑ i, tiltedRademacherGaussianCFCoordinateMajorant b x i t := by
  rfl

theorem tiltedRademacherGaussianCFCoordinateMajorant_nonneg
    (b : ι → ℝ) (x : ℝ) (i : ι) (t : ℝ) :
    0 ≤ tiltedRademacherGaussianCFCoordinateMajorant b x i t := by
  unfold tiltedRademacherGaussianCFCoordinateMajorant
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (by split_ifs <;> norm_num)
        (biasedSignThirdMomentTerm_nonneg _ _))
      (by positivity))
    (Real.exp_nonneg _)

theorem biasedSignVarianceTerm_le_tiltedRademacherLocalVariance_of_local
    (u a : ι → ℝ) (t : ℝ) (i : ι) (hi : |t * a i| ≤ 1) :
    biasedSignVarianceTerm (u i) (a i) ≤
      tiltedRademacherLocalVariance u a t := by
  classical
  unfold tiltedRademacherLocalVariance tiltedRademacherLocalIndices
  exact Finset.single_le_sum
    (fun j _ => biasedSignVarianceTerm_nonneg (u j) (a j))
    (by simpa [abs_mul] using hi)

theorem deletedLocalVariance_nonneg
    (u a : ι → ℝ) (t : ℝ) (i : ι) :
    0 ≤ tiltedRademacherLocalVariance u a t -
      if |t * a i| ≤ 1 then
        biasedSignVarianceTerm (u i) (a i)
      else 0 := by
  by_cases hi : |t * a i| ≤ 1
  · simp only [if_pos hi]
    exact sub_nonneg.mpr
      (biasedSignVarianceTerm_le_tiltedRademacherLocalVariance_of_local
        u a t i hi)
  · simp only [if_neg hi, sub_zero]
    exact tiltedRademacherLocalVariance_nonneg u a t

theorem tiltedRademacherGaussianCFMajorant_nonneg
    (b : ι → ℝ) (x t : ℝ) :
    0 ≤ tiltedRademacherGaussianCFMajorant b x t := by
  classical
  unfold tiltedRademacherGaussianCFMajorant
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (by split_ifs <;> norm_num)
        (biasedSignThirdMomentTerm_nonneg _ _))
      (by positivity))
    (Real.exp_nonneg _)

/--
A global cubic envelope used only to prove integrability.  The final
coefficient estimate must retain the sharper coordinate-wise exponential
damping.
-/
theorem tiltedRademacherGaussianCFMajorant_le_cubic
    (b : ι → ℝ) (x t : ℝ) :
    tiltedRademacherGaussianCFMajorant b x t ≤
      (7 / 6 : ℝ) *
        tiltedRademacherThirdMomentSum
          (fun i => x * b i)
          (fun i => b i /
            tiltedRademacherStdDev (fun j => x * b j) b) *
        |t| ^ 3 := by
  classical
  let u : ι → ℝ := fun i => x * b i
  let c : ι → ℝ := fun i =>
    b i / tiltedRademacherStdDev (fun j => x * b j) b
  unfold tiltedRademacherGaussianCFMajorant
  dsimp only
  rw [show
      (7 / 6 : ℝ) * tiltedRademacherThirdMomentSum u c * |t| ^ 3 =
        ∑ i, (7 / 6 : ℝ) *
          biasedSignThirdMomentTerm (u i) (c i) * |t| ^ 3 by
    unfold tiltedRademacherThirdMomentSum
    rw [Finset.mul_sum, Finset.sum_mul]
    simp only [biasedSignThirdMomentTerm]]
  apply Finset.sum_le_sum
  intro i _
  have hdeleted :
      0 ≤ tiltedRademacherLocalVariance u c t -
        if |t * c i| ≤ 1 then
          biasedSignVarianceTerm (u i) (c i)
        else 0 :=
    deletedLocalVariance_nonneg u c t i
  have hexp :
      Real.exp
          (-((tiltedRademacherLocalVariance u c t -
              if |t * c i| ≤ 1 then
                biasedSignVarianceTerm (u i) (c i)
              else 0) * t ^ 2) / 5) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg t]
  have hcoeff :
      (if |t * c i| ≤ 1 then (5 / 12 : ℝ) else 7 / 6) ≤ 7 / 6 := by
    split_ifs <;> norm_num
  have hm := biasedSignThirdMomentTerm_nonneg (u i) (c i)
  have ht : 0 ≤ |t| ^ 3 := by positivity
  calc
    (if |t * c i| ≤ 1 then (5 / 12 : ℝ) else 7 / 6) *
          biasedSignThirdMomentTerm (u i) (c i) * |t| ^ 3 *
          Real.exp
            (-((tiltedRademacherLocalVariance u c t -
                if |t * c i| ≤ 1 then
                  biasedSignVarianceTerm (u i) (c i)
                else 0) * t ^ 2) / 5)
        ≤ (if |t * c i| ≤ 1 then (5 / 12 : ℝ) else 7 / 6) *
            biasedSignThirdMomentTerm (u i) (c i) * |t| ^ 3 := by
          exact mul_le_of_le_one_right
            (mul_nonneg (mul_nonneg (by split_ifs <;> norm_num) hm) ht)
            hexp
    _ ≤ (7 / 6 : ℝ) *
          biasedSignThirdMomentTerm (u i) (c i) * |t| ^ 3 := by
      gcongr

theorem measurable_tiltedRademacherLocalVariance
    (u a : ι → ℝ) :
    Measurable (tiltedRademacherLocalVariance u a) := by
  classical
  unfold tiltedRademacherLocalVariance tiltedRademacherLocalIndices
  simp_rw [Finset.sum_filter]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite
  · exact measurableSet_le (by fun_prop) measurable_const
  · exact measurable_const
  · exact measurable_const

theorem measurable_tiltedRademacherGaussianCFCoordinateMajorant
    (b : ι → ℝ) (x : ℝ) (i : ι) :
    Measurable (tiltedRademacherGaussianCFCoordinateMajorant b x i) := by
  unfold tiltedRademacherGaussianCFCoordinateMajorant
  have hlocal :
      MeasurableSet {t : ℝ |
        |t * (b i /
          tiltedRademacherStdDev (fun j => x * b j) b)| ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  have hvariance :
      Measurable fun t : ℝ =>
        tiltedRademacherLocalVariance
          (fun j => x * b j)
          (fun j => b j /
            tiltedRademacherStdDev (fun k => x * b k) b) t :=
    measurable_tiltedRademacherLocalVariance _ _
  have hcoeff :
      Measurable fun t : ℝ =>
        if |t * (b i /
            tiltedRademacherStdDev (fun j => x * b j) b)| ≤ 1 then
          (5 / 12 : ℝ)
        else 7 / 6 :=
    Measurable.ite hlocal measurable_const measurable_const
  have hdeleted :
      Measurable fun t : ℝ =>
        if |t * (b i /
            tiltedRademacherStdDev (fun j => x * b j) b)| ≤ 1 then
          biasedSignVarianceTerm
            (x * b i)
            (b i / tiltedRademacherStdDev (fun j => x * b j) b)
        else 0 :=
    Measurable.ite hlocal measurable_const measurable_const
  have hsq : Measurable fun t : ℝ => t ^ 2 :=
    measurable_id.pow_const 2
  have hexponent :
      Measurable fun t : ℝ =>
        Real.exp
          (-((tiltedRademacherLocalVariance
                (fun j => x * b j)
                (fun j => b j /
                  tiltedRademacherStdDev (fun k => x * b k) b) t -
              if |t * (b i /
                  tiltedRademacherStdDev (fun j => x * b j) b)| ≤ 1 then
                biasedSignVarianceTerm
                  (x * b i)
                  (b i /
                    tiltedRademacherStdDev (fun j => x * b j) b)
              else 0) * t ^ 2) / 5) :=
    (((hvariance.sub hdeleted).mul hsq).neg.div
      (measurable_const :
        Measurable fun _ : ℝ => (5 : ℝ))).exp
  exact (((hcoeff.mul measurable_const).mul
    (continuous_abs.measurable.pow_const 3)).mul
      hexponent)

theorem measurable_tiltedRademacherGaussianCFMajorant
    (b : ι → ℝ) (x : ℝ) :
    Measurable (tiltedRademacherGaussianCFMajorant b x) := by
  classical
  rw [show
      tiltedRademacherGaussianCFMajorant b x =
        fun t =>
          ∑ i, tiltedRademacherGaussianCFCoordinateMajorant b x i t by
    funext t
    exact tiltedRademacherGaussianCFMajorant_eq_sum_coordinate b x t]
  exact Finset.measurable_sum _ fun i _ =>
    measurable_tiltedRademacherGaussianCFCoordinateMajorant b x i

/--
Multiplication by a cubic characteristic-function remainder removes the
Prawitz kernel's apparent singularity exactly.
-/
theorem norm_scaledPrawitzKernel_mul_abs_pow_three
    {U t : ℝ} (hU : 0 < U) (ht : |t| < U) :
    ‖scaledPrawitzKernel U t‖ * |t| ^ 3 =
      ‖regularizedPrawitzFrequencyKernel (t / U)‖ * |t| ^ 2 := by
  by_cases hzero : t = 0
  · subst t
    simp
  · have hratio : |t / U| < 1 := by
      rw [abs_div, abs_of_pos hU, div_lt_one hU]
      exact ht
    unfold scaledPrawitzKernel
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr hU),
      norm_prawitzKernel_eq_div hratio
        (div_ne_zero hzero hU.ne')]
    rw [abs_div, abs_of_pos hU]
    field_simp [hU.ne', abs_ne_zero.mpr hzero]

/--
The regularized frequency kernel is uniformly bounded on every compact
subinterval of its support.
-/
theorem exists_norm_regularizedPrawitzFrequencyKernel_bound
    {r : ℝ} (hr : r < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s ∈ Icc (-r) r,
        ‖regularizedPrawitzFrequencyKernel s‖ ≤ C := by
  have hcontinuous :
      ContinuousOn
        (fun s : ℝ => ‖regularizedPrawitzFrequencyKernel s‖)
        (Icc (-r) r) := by
    intro s hs
    have hsabs : |s| < 1 := by
      rw [abs_lt]
      constructor <;> linarith [hs.1, hs.2]
    exact
      (continuousAt_regularizedPrawitzFrequencyKernel_of_abs_lt_one
        hsabs).norm.continuousWithinAt
  obtain ⟨C, hC⟩ :=
    bddAbove_def.mp
      (IsCompact.bddAbove_image isCompact_Icc hcontinuous)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro s hs
  exact (hC _ ⟨s, hs, rfl⟩).trans (le_max_left _ _)

/--
The sharp core Prawitz majorant is integrable on every proper finite
sub-band `[-U₀,U₀] ⊂ (-U,U)`.

The proof uses a coarse cubic bound only to establish integrability.  The
value of the integral is subsequently bounded from the original sharp
coordinate-wise expression.
-/
theorem integrableOn_scaledPrawitzKernel_mul_tiltedMajorant
    (b : ι → ℝ) (x : ℝ) {U₀ U : ℝ}
    (hU₀ : 0 ≤ U₀) (hband : U₀ < U) :
    IntegrableOn
      (fun t =>
        ‖scaledPrawitzKernel U t‖ *
          tiltedRademacherGaussianCFMajorant b x t)
      (Icc (-U₀) U₀) volume := by
  have hU : 0 < U := hU₀.trans_lt hband
  let r : ℝ := U₀ / U
  have hr : r < 1 := by
    dsimp [r]
    exact (div_lt_one hU).mpr hband
  obtain ⟨C, hC0, hC⟩ :=
    exists_norm_regularizedPrawitzFrequencyKernel_bound hr
  let M : ℝ :=
    tiltedRademacherThirdMomentSum
      (fun i => x * b i)
      (fun i => b i /
        tiltedRademacherStdDev (fun j => x * b j) b)
  have hM : 0 ≤ M :=
    tiltedRademacherThirdMomentSum_nonneg _ _
  have hmeas :
      AEStronglyMeasurable
        (fun t =>
          ‖scaledPrawitzKernel U t‖ *
            tiltedRademacherGaussianCFMajorant b x t)
        volume :=
    ((measurable_scaledPrawitzKernel U).norm.mul
      (measurable_tiltedRademacherGaussianCFMajorant b x)).aestronglyMeasurable
  refine Measure.integrableOn_of_bounded (μ := volume)
      (M := (7 / 6 : ℝ) * M * C * U₀ ^ 2)
      measure_Icc_lt_top.ne hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (norm_nonneg _)
      (tiltedRademacherGaussianCFMajorant_nonneg b x t))]
  have htAbs : |t| ≤ U₀ := by
    rw [abs_le]
    exact ⟨ht.1, ht.2⟩
  have htInside : |t| < U := htAbs.trans_lt hband
  have htRatio : t / U ∈ Icc (-r) r := by
    constructor
    · dsimp [r]
      rw [← neg_div]
      exact div_le_div_of_nonneg_right ht.1 hU.le
    · dsimp [r]
      exact div_le_div_of_nonneg_right ht.2 hU.le
  have hmajorant :=
    tiltedRademacherGaussianCFMajorant_le_cubic b x t
  have hkernel := hC (t / U) htRatio
  have htSq : |t| ^ 2 ≤ U₀ ^ 2 := by
    exact pow_le_pow_left₀ (abs_nonneg t) htAbs 2
  have hcoef : 0 ≤ (7 / 6 : ℝ) * M :=
    mul_nonneg (by norm_num) hM
  calc
    ‖scaledPrawitzKernel U t‖ *
          tiltedRademacherGaussianCFMajorant b x t
        ≤ ‖scaledPrawitzKernel U t‖ *
            ((7 / 6 : ℝ) * M * |t| ^ 3) :=
      mul_le_mul_of_nonneg_left hmajorant (norm_nonneg _)
    _ = (7 / 6 : ℝ) * M *
          (‖scaledPrawitzKernel U t‖ * |t| ^ 3) := by ring
    _ = (7 / 6 : ℝ) * M *
          (‖regularizedPrawitzFrequencyKernel (t / U)‖ *
            |t| ^ 2) := by
      rw [norm_scaledPrawitzKernel_mul_abs_pow_three hU htInside]
    _ ≤ (7 / 6 : ℝ) * M * (C * |t| ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hkernel (sq_nonneg |t|))
        hcoef
    _ ≤ (7 / 6 : ℝ) * M * C * U₀ ^ 2 := by
      calc
        (7 / 6 : ℝ) * M * (C * |t| ^ 2) =
            ((7 / 6 : ℝ) * M * C) * |t| ^ 2 := by ring
        _ ≤ ((7 / 6 : ℝ) * M * C) * U₀ ^ 2 :=
          mul_le_mul_of_nonneg_left htSq
            (mul_nonneg hcoef hC0)
        _ = (7 / 6 : ℝ) * M * C * U₀ ^ 2 := by ring

end Probability
end CertifiedJL
