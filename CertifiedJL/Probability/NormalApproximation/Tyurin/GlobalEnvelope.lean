/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Fourier.Prawitz.KernelBounds
import CertifiedJL.Analysis.Fourier.Prawitz.GaussianIntegrals
import CertifiedJL.Probability.NormalApproximation.Lyapunov.SmallLyapunovIntegral
import CertifiedJL.Probability.NormalApproximation.Tyurin.CosineEnvelope
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Tyurin's global characteristic-function envelope

This file develops the distribution-specific form of the global product
estimate used in Tyurin's Prawitz proof.  We use the exact rational constant
`1 / 10` in place of the transcendental optimum `0.099162...`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace CertifiedJL
namespace Probability

universe u_1

variable {ι : Type u_1} [Fintype ι]

/-- Exact rational replacement for Tyurin's optimal cosine constant. -/
noncomputable def tyurinRationalA : ℝ := 1 / 10

/-- Rational switch point; the optimal point is `3.995895...`. -/
noncomputable def tyurinRationalM : ℝ := 4

/-- Exact lower-height constant in the second branch of `deltaTwo`. -/
noncomputable def tyurinRationalEll : ℝ :=
  Real.exp (-(25 / 54 : ℝ))

/-- The one-third Lyapunov scale used in Tyurin's deleted-product split. -/
noncomputable def lyapunovThirdRoot (L : ℝ) : ℝ :=
  L ^ (1 / 3 : ℝ)

theorem lyapunovThirdRoot_nonneg {L : ℝ} (hL : 0 ≤ L) :
    0 ≤ lyapunovThirdRoot L := by
  unfold lyapunovThirdRoot
  exact Real.rpow_nonneg hL _

theorem lyapunovThirdRoot_sq
    {L : ℝ} (hL : 0 ≤ L) :
    lyapunovThirdRoot L ^ 2 = lyapunovVarianceCap L := by
  unfold lyapunovThirdRoot lyapunovVarianceCap
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
  norm_num

theorem lyapunovThirdRoot_cube
    {L : ℝ} (hL : 0 ≤ L) :
    lyapunovThirdRoot L ^ 3 = L := by
  unfold lyapunovThirdRoot
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
  norm_num

private theorem tyurinCubicProfile_mono
    {y Y : ℝ} (hy : 0 ≤ y) (hyY : y ≤ Y)
    (hY : Y ≤ 5 / 3) :
    y ^ 2 / 2 - y ^ 3 / 5 ≤
      Y ^ 2 / 2 - Y ^ 3 / 5 := by
  have hY0 : 0 ≤ Y := hy.trans hyY
  have hsqCross : 2 * Y * y ≤ Y ^ 2 + y ^ 2 := by
    nlinarith [sq_nonneg (Y - y)]
  have hYsq : Y ^ 2 ≤ (5 / 3 : ℝ) * Y := by
    nlinarith [mul_nonneg hY0 (sub_nonneg.mpr hY)]
  have hysq : y ^ 2 ≤ (5 / 3 : ℝ) * y := by
    have : y ≤ 5 / 3 := hyY.trans hY
    nlinarith [mul_nonneg hy (sub_nonneg.mpr this)]
  have hbracket :
      0 ≤ (Y + y) / 2 - (Y ^ 2 + Y * y + y ^ 2) / 5 := by
    nlinarith
  have hfactor :
      Y ^ 2 / 2 - Y ^ 3 / 5 -
          (y ^ 2 / 2 - y ^ 3 / 5) =
        (Y - y) *
          ((Y + y) / 2 - (Y ^ 2 + Y * y + y ^ 2) / 5) := by
    ring
  rw [← sub_nonneg, hfactor]
  positivity

private theorem tyurinCubicProfile_le_max
    {y : ℝ} (hy : 0 ≤ y) :
    y ^ 2 / 2 - y ^ 3 / 5 ≤ 25 / 54 := by
  have hfactor :
      (25 / 54 : ℝ) - (y ^ 2 / 2 - y ^ 3 / 5) =
        (3 * y - 5) ^ 2 * (6 * y + 5) / 270 := by
    ring
  rw [← sub_nonneg, hfactor]
  positivity

private theorem tyurin_middle_cubic_nonneg
    {x : ℝ} (hx0 : (157 / 50 : ℝ) ≤ x)
    (hx1 : x ≤ 189 / 40) :
    0 ≤ 2 - x ^ 2 / 2 - (x - 157 / 50) ^ 2 / 2 +
      x ^ 3 / 10 := by
  rcases le_total x (19 / 5 : ℝ) with hx | hx
  · let z : ℝ := (x - 157 / 50) / (33 / 50)
    have hz0 : 0 ≤ z := by
      dsimp [z]
      positivity
    have hz1 : z ≤ 1 := by
      dsimp [z]
      norm_num at hx0 hx ⊢
      linarith
    have hrepr :
        2 - x ^ 2 / 2 - (x - 157 / 50) ^ 2 / 2 +
            x ^ 3 / 10 =
          (207643 / 1250000 : ℝ) * (1 - z) ^ 3 +
            3 * (3939 / 31250 : ℝ) * z * (1 - z) ^ 2 +
            3 * (1939 / 25000 : ℝ) * z ^ 2 * (1 - z) +
            (247 / 5000 : ℝ) * z ^ 3 := by
      dsimp [z]
      ring
    rw [hrepr]
    positivity
  · rcases le_total x (43 / 10 : ℝ) with hx' | hx'
    · let z : ℝ := (x - 19 / 5) / (1 / 2)
      have hz0 : 0 ≤ z := by
        dsimp [z]
        positivity
      have hz1 : z ≤ 1 := by
        dsimp [z]
        norm_num at hx hx' ⊢
        linarith
      have hrepr :
          2 - x ^ 2 / 2 - (x - 157 / 50) ^ 2 / 2 +
              x ^ 3 / 10 =
            (247 / 5000 : ℝ) * (1 - z) ^ 3 +
              3 * (421 / 15000 : ℝ) * z * (1 - z) ^ 2 +
              3 * (23 / 1250 : ℝ) * z ^ 2 * (1 - z) +
              (329 / 10000 : ℝ) * z ^ 3 := by
        dsimp [z]
        ring
      rw [hrepr]
      positivity
    · let z : ℝ := (x - 43 / 10) / (17 / 40)
      have hz0 : 0 ≤ z := by
        dsimp [z]
        positivity
      have hz1 : z ≤ 1 := by
        dsimp [z]
        norm_num at hx' hx1 ⊢
        linarith
      have hrepr :
          2 - x ^ 2 / 2 - (x - 157 / 50) ^ 2 / 2 +
              x ^ 3 / 10 =
            (329 / 10000 : ℝ) * (1 - z) ^ 3 +
              3 * (1809 / 40000 : ℝ) * z * (1 - z) ^ 2 +
              3 * (7201 / 96000 : ℝ) * z ^ 2 * (1 - z) +
              (83157 / 640000 : ℝ) * z ^ 3 := by
        dsimp [z]
        ring
      rw [hrepr]
      positivity

/--
The elementary global cosine remainder with the rational Tyurin constant.
The optimal coefficient is approximately `0.099162`; `1 / 10` retains useful
numerical margin while admitting an exact certificate.
-/
theorem cos_sub_one_add_half_sq_le_one_tenth_abs_cube (x : ℝ) :
    Real.cos x - 1 + x ^ 2 / 2 ≤ (1 / 10 : ℝ) * |x| ^ 3 := by
  wlog hx : 0 ≤ x generalizing x
  · have h := this (-x) (neg_nonneg.mpr (le_of_not_ge hx))
    simpa [Real.cos_neg] using h
  rw [abs_of_nonneg hx]
  rcases le_total x (Real.pi / 2) with hsmall | hsmall
  · have hcos := cos_le_taylor_four hx hsmall
    have hxBound : x ≤ 12 / 5 := by
      have hpi := Real.pi_lt_four
      linarith
    have hx3 : 0 ≤ x ^ 3 := by positivity
    nlinarith [mul_nonneg hx3 (sub_nonneg.mpr hxBound)]
  · rcases le_total x Real.pi with hpi | hpi
    · have hy0 : 0 ≤ Real.pi - x := sub_nonneg.mpr hpi
      have hy1 : Real.pi - x ≤ Real.pi / 2 := by linarith
      have hlinear :=
        Real.one_sub_mul_le_cos hy0 hy1
      rw [Real.cos_pi_sub] at hlinear
      have hrearrange :
          1 - 2 / Real.pi * (Real.pi - x) =
            -1 + 2 / Real.pi * x := by
        field_simp [Real.pi_ne_zero]
        ring
      rw [hrearrange] at hlinear
      have hcos : Real.cos x ≤ 1 - 2 / Real.pi * x := by
        linarith
      have hpiUpper := Real.pi_lt_d2
      have hconst : (5 / 8 : ℝ) < 2 / Real.pi := by
        rw [lt_div_iff₀ Real.pi_pos]
        nlinarith
      have hquad :
          0 ≤ 2 / Real.pi - x / 2 + x ^ 2 / 10 := by
        nlinarith [sq_nonneg (x - 5 / 2)]
      have hmul :
          0 ≤ x * (2 / Real.pi - x / 2 + x ^ 2 / 10) :=
        mul_nonneg hx hquad
      nlinarith
    · rcases le_total x (3 * Real.pi / 2) with hthreeHalf | hthreeHalf
      · let y : ℝ := x - Real.pi
        have hy0 : 0 ≤ y := by
          dsimp [y]
          linarith
        have hy1 : y ≤ Real.pi / 2 := by
          dsimp [y]
          linarith
        have hcosLower := Real.one_sub_sq_div_two_le_cos (x := y)
        have hcosShift : Real.cos x = -Real.cos y := by
          dsimp [y]
          linarith [Real.cos_sub_pi x]
        have hcos :
            Real.cos x ≤ -1 + y ^ 2 / 2 := by
          rw [hcosShift]
          linarith
        have hpiLower : (157 / 50 : ℝ) < Real.pi := by
          nlinarith [Real.pi_gt_d2]
        have hpiUpper : Real.pi < 63 / 20 := by
          nlinarith [Real.pi_lt_d2]
        have hxLower : (157 / 50 : ℝ) ≤ x :=
          hpiLower.le.trans hpi
        have hxUpper : x ≤ 189 / 40 := by
          nlinarith
        have hyDist :
            y ^ 2 ≤ (x - 157 / 50) ^ 2 := by
          have hleft : 0 ≤ y := hy0
          have hright : y ≤ x - 157 / 50 := by
            dsimp [y]
            linarith
          simpa only [pow_two] using
            mul_self_le_mul_self hleft hright
        have hpoly :=
          tyurin_middle_cubic_nonneg hxLower hxUpper
        dsimp [y] at hcos hyDist
        nlinarith
      · rcases le_total x 5 with hfive | hfive
        · let y : ℝ := x - 3 * Real.pi / 2
          have hy0 : 0 ≤ y := by
            dsimp [y]
            linarith
          have hy1 : y ≤ Real.pi / 2 := by
            dsimp [y]
            have hpiThree := Real.pi_gt_three
            nlinarith
          have hcosShift : Real.cos x = Real.sin y := by
            calc
              Real.cos x =
                  Real.cos ((y + Real.pi) + Real.pi / 2) := by
                    congr 1
                    dsimp [y]
                    ring
              _ = -Real.sin (y + Real.pi) :=
                Real.cos_add_pi_div_two _
              _ = Real.sin y := by
                rw [Real.sin_add_pi]
                ring
          have hcos : Real.cos x ≤ y := by
            rw [hcosShift]
            exact Real.sin_le hy0
          have hpiLower : (157 / 50 : ℝ) < Real.pi := by
            nlinarith [Real.pi_gt_d2]
          have hxLower : (9 / 2 : ℝ) ≤ x := by
            nlinarith
          have hbracket :
              0 ≤ x ^ 2 / 10 - x / 20 - 49 / 40 := by
            nlinarith [mul_nonneg
              (sub_nonneg.mpr hxLower)
              (by nlinarith : 0 ≤ x + 49 / 10)]
          have hdiff :
              0 ≤ (x - 9 / 2) *
                (x ^ 2 / 10 - x / 20 - 49 / 40) :=
            mul_nonneg (sub_nonneg.mpr hxLower) hbracket
          have hbase :
              0 <
                (1 : ℝ) - (9 / 2) ^ 2 / 2 + (9 / 2) ^ 3 / 10 -
                  (9 / 2 - 3 * (157 / 50) / 2) := by
            norm_num
          dsimp [y] at hcos
          nlinarith
        · have hcos := Real.cos_le_one x
          have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
          nlinarith [mul_nonneg hx2 (sub_nonneg.mpr hfive)]

/--
One-coordinate cubic modulus envelope.  The coefficient `1 / 5` is twice
the rational cosine-remainder constant because the squared modulus is the
characteristic function of the symmetrized coordinate.
-/
theorem norm_centeredBiasedSignChar_le_tyurinCubic
    (u a t : ℝ) :
    ‖centeredBiasedSignChar u a t‖ ≤
      Real.exp
        (-(biasedSignVarianceTerm u a * t ^ 2) / 2 +
          biasedSignThirdMomentTerm u a * |t| ^ 3 / 5) := by
  let q : ℝ := 1 - Real.tanh u ^ 2
  let z : ℝ := t * a
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact sub_nonneg.mpr (Real.tanh_sq_lt_one u).le
  have hrem :=
    cos_sub_one_add_half_sq_le_one_tenth_abs_cube (2 * z)
  rw [Real.cos_two_mul_eq_one_sub] at hrem
  have hsin :
      z ^ 2 - (2 / 5 : ℝ) * |z| ^ 3 ≤ Real.sin z ^ 2 := by
    rw [abs_mul] at hrem
    norm_num at hrem
    nlinarith
  have hweighted :
      q * z ^ 2 - (2 / 5 : ℝ) * q * |z| ^ 3 ≤
        q * Real.sin z ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsin hq0]
  have hthirdDom :
      q * |z| ^ 3 ≤
        biasedSignThirdMomentTerm u a * |t| ^ 3 := by
    have hm : 1 ≤ 1 + Real.tanh u ^ 2 := by
      nlinarith [sq_nonneg (Real.tanh u)]
    have hbase :
        q * |a| ^ 3 ≤ q * (1 + Real.tanh u ^ 2) * |a| ^ 3 := by
      nlinarith [mul_le_mul_of_nonneg_left hm hq0,
        pow_nonneg (abs_nonneg a) 3]
    dsimp [z]
    rw [abs_mul, mul_pow]
    unfold biasedSignThirdMomentTerm
    rw [show 1 - Real.tanh u ^ 4 =
        q * (1 + Real.tanh u ^ 2) by
      dsimp [q]
      ring]
    nlinarith [pow_nonneg (abs_nonneg t) 3]
  have hvz :
      biasedSignVarianceTerm u a * t ^ 2 = q * z ^ 2 := by
    dsimp [q, z, biasedSignVarianceTerm]
    ring
  have hlower :
      biasedSignVarianceTerm u a * t ^ 2 -
          (2 / 5 : ℝ) *
            biasedSignThirdMomentTerm u a * |t| ^ 3 ≤
        q * Real.sin z ^ 2 := by
    calc
      biasedSignVarianceTerm u a * t ^ 2 -
            (2 / 5 : ℝ) *
              biasedSignThirdMomentTerm u a * |t| ^ 3
          ≤ q * z ^ 2 - (2 / 5 : ℝ) * q * |z| ^ 3 := by
            rw [hvz]
            nlinarith
      _ ≤ q * Real.sin z ^ 2 := hweighted
  have hsq :
      ‖centeredBiasedSignChar u a t‖ ^ 2 ≤
        1 - biasedSignVarianceTerm u a * t ^ 2 +
          (2 / 5 : ℝ) *
            biasedSignThirdMomentTerm u a * |t| ^ 3 := by
    rw [norm_centeredBiasedSignChar_sq_eq_one_sub]
    dsimp [q, z] at hlower
    nlinarith
  let r : ℝ :=
    -(biasedSignVarianceTerm u a * t ^ 2) +
      (2 / 5 : ℝ) *
        biasedSignThirdMomentTerm u a * |t| ^ 3
  have honeExp : 1 + r ≤ Real.exp r := by
    simpa [add_comm] using Real.add_one_le_exp r
  have hsqExp :
      ‖centeredBiasedSignChar u a t‖ ^ 2 ≤ Real.exp r := by
    apply hsq.trans
    dsimp [r] at honeExp ⊢
    nlinarith
  have hexpSq :
      Real.exp r =
        Real.exp
          (-(biasedSignVarianceTerm u a * t ^ 2) / 2 +
            biasedSignThirdMomentTerm u a * |t| ^ 3 / 5) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    dsimp [r]
    ring
  rw [hexpSq] at hsqExp
  exact (sq_le_sq₀ (norm_nonneg _) (Real.exp_nonneg _)).mp hsqExp

/-- Unnormalized finite-product form of the cubic Tyurin envelope. -/
theorem norm_prod_centeredBiasedSignChar_le_tyurinCubicSum
    (u a : ι → ℝ) (t : ℝ) :
    ‖∏ i, centeredBiasedSignChar (u i) (a i) t‖ ≤
      Real.exp
        (-((∑ i, biasedSignVarianceTerm (u i) (a i)) * t ^ 2) / 2 +
          (∑ i, biasedSignThirdMomentTerm (u i) (a i)) *
            |t| ^ 3 / 5) := by
  classical
  rw [norm_prod]
  calc
    ∏ i, ‖centeredBiasedSignChar (u i) (a i) t‖
        ≤ ∏ i, Real.exp
            (-(biasedSignVarianceTerm (u i) (a i) * t ^ 2) / 2 +
              biasedSignThirdMomentTerm (u i) (a i) * |t| ^ 3 / 5) := by
          apply Finset.prod_le_prod
          · intro i _
            exact norm_nonneg _
          · intro i _
            exact norm_centeredBiasedSignChar_le_tyurinCubic
              (u i) (a i) t
    _ = Real.exp
          (∑ i,
            (-(biasedSignVarianceTerm (u i) (a i) * t ^ 2) / 2 +
              biasedSignThirdMomentTerm (u i) (a i) * |t| ^ 3 / 5)) := by
          rw [Real.exp_sum]
    _ = _ := by
          congr 1
          rw [Finset.sum_add_distrib, ← Finset.sum_div,
            ← Finset.sum_div]
          have hv :
              (∑ i, -(biasedSignVarianceTerm (u i) (a i) * t ^ 2)) =
                -(∑ i, biasedSignVarianceTerm (u i) (a i)) *
                  t ^ 2 := by
            rw [show (∑ i,
                -(biasedSignVarianceTerm (u i) (a i) * t ^ 2)) =
              -(∑ i, biasedSignVarianceTerm (u i) (a i)) *
                t ^ 2 by
              rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
              ring]
          have hβ :
              (∑ i,
                  biasedSignThirdMomentTerm (u i) (a i) * |t| ^ 3) =
                (∑ i, biasedSignThirdMomentTerm (u i) (a i)) *
                  |t| ^ 3 := by
            rw [← Finset.sum_mul]
          rw [hv, hβ]
          ring

/--
The normalized low-frequency branch of Tyurin's global product envelope.
It is valid for every frequency; the later cosine branch is what keeps the
estimate useful after this cubic exponent turns upward.
-/
theorem norm_prod_centeredBiasedSignChar_le_tyurinCubic
    (u a : ι → ℝ) (t L : ℝ)
    (hvar : ∑ i, biasedSignVarianceTerm (u i) (a i) = 1)
    (hthird : ∑ i, biasedSignThirdMomentTerm (u i) (a i) = L) :
    ‖∏ i, centeredBiasedSignChar (u i) (a i) t‖ ≤
      Real.exp (-(t ^ 2) / 2 + L * |t| ^ 3 / 5) := by
  simpa [hvar, hthird] using
    norm_prod_centeredBiasedSignChar_le_tyurinCubicSum u a t

/--
Actual-law specialization of the cubic branch of Tyurin's product envelope.
-/
theorem norm_rademacherTiltedCharFun_le_tyurinCubic
    (b : ι → ℝ) (x t : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1) :
    ‖charFun (rademacherTiltedStandardizedLaw b x) t‖ ≤
      Real.exp
        (-(t ^ 2) / 2 +
          rademacherLyapunovRatio b x * |t| ^ 3 / 5) := by
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
  exact norm_prod_centeredBiasedSignChar_le_tyurinCubic
    u a t (rademacherLyapunovRatio b x) hvar hthird

/--
Deleted-coordinate Tyurin envelope for the zero-bias product difference.
This is the exact finite-sum estimate from which the two branches of
`deltaTwo` are obtained.
-/
theorem norm_prod_sub_productZeroBiasChar_le_tyurinDeleted
    [DecidableEq ι]
    (u a : ι → ℝ) (t L : ℝ)
    (hvar : ∑ i, biasedSignVarianceTerm (u i) (a i) = 1)
    (hthird : ∑ i, biasedSignThirdMomentTerm (u i) (a i) = L) :
    ‖(∏ i, centeredBiasedSignChar (u i) (a i) t) -
        centeredBiasedSignProductZeroBiasChar u a t‖ ≤
      ∑ i,
        (biasedSignThirdMomentTerm (u i) (a i) * |t| / 2) *
          Real.exp
            (-((1 - biasedSignVarianceTerm (u i) (a i)) *
                t ^ 2) / 2 +
              (L - biasedSignThirdMomentTerm (u i) (a i)) *
                |t| ^ 3 / 5) := by
  rw [prod_centeredBiasedSignChar_sub_productZeroBiasChar_eq
    u a t hvar]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (biasedSignVarianceTerm_nonneg (u i) (a i))]
  have hdeleted :
      ‖∏ j ∈ Finset.univ.erase i,
          centeredBiasedSignChar (u j) (a j) t‖ ≤
        Real.exp
          (-((1 - biasedSignVarianceTerm (u i) (a i)) *
              t ^ 2) / 2 +
            (L - biasedSignThirdMomentTerm (u i) (a i)) *
              |t| ^ 3 / 5) := by
    rw [norm_prod]
    calc
      ∏ j ∈ Finset.univ.erase i,
          ‖centeredBiasedSignChar (u j) (a j) t‖
          ≤ ∏ j ∈ Finset.univ.erase i,
              Real.exp
                (-(biasedSignVarianceTerm (u j) (a j) * t ^ 2) / 2 +
                  biasedSignThirdMomentTerm (u j) (a j) *
                    |t| ^ 3 / 5) := by
            apply Finset.prod_le_prod
            · intro j _
              exact norm_nonneg _
            · intro j _
              exact norm_centeredBiasedSignChar_le_tyurinCubic
                (u j) (a j) t
      _ = Real.exp
            (∑ j ∈ Finset.univ.erase i,
              (-(biasedSignVarianceTerm (u j) (a j) * t ^ 2) / 2 +
                biasedSignThirdMomentTerm (u j) (a j) *
                  |t| ^ 3 / 5)) := by
            rw [Real.exp_sum]
      _ = _ := by
            congr 1
            have hiv :
                ∑ j ∈ Finset.univ.erase i,
                    biasedSignVarianceTerm (u j) (a j) =
                  1 - biasedSignVarianceTerm (u i) (a i) := by
              have h :=
                Finset.sum_erase_add
                  (s := Finset.univ)
                  (f := fun j =>
                    biasedSignVarianceTerm (u j) (a j))
                  (Finset.mem_univ i)
              rw [hvar] at h
              linarith
            have hiβ :
                ∑ j ∈ Finset.univ.erase i,
                    biasedSignThirdMomentTerm (u j) (a j) =
                  L - biasedSignThirdMomentTerm (u i) (a i) := by
              have h :=
                Finset.sum_erase_add
                  (s := Finset.univ)
                  (f := fun j =>
                    biasedSignThirdMomentTerm (u j) (a j))
                  (Finset.mem_univ i)
              rw [hthird] at h
              linarith
            rw [Finset.sum_add_distrib, ← Finset.sum_div,
              ← Finset.sum_div]
            have hv :
                (∑ j ∈ Finset.univ.erase i,
                    -(biasedSignVarianceTerm (u j) (a j) * t ^ 2)) =
                  -(1 - biasedSignVarianceTerm (u i) (a i)) *
                    t ^ 2 := by
              rw [show (∑ j ∈ Finset.univ.erase i,
                    -(biasedSignVarianceTerm (u j) (a j) * t ^ 2)) =
                  -(∑ j ∈ Finset.univ.erase i,
                      biasedSignVarianceTerm (u j) (a j)) *
                    t ^ 2 by
                rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
                ring]
              rw [hiv]
            have hβ :
                (∑ j ∈ Finset.univ.erase i,
                    biasedSignThirdMomentTerm (u j) (a j) *
                      |t| ^ 3) =
                  (L - biasedSignThirdMomentTerm (u i) (a i)) *
                    |t| ^ 3 := by
              rw [← Finset.sum_mul, hiβ]
            rw [hv, hβ]
            ring
  calc
    biasedSignVarianceTerm (u i) (a i) *
          ‖centeredBiasedSignChar (u i) (a i) t -
            centeredBiasedSignZeroBiasChar (u i) (a i) t‖ *
        ‖∏ j ∈ Finset.univ.erase i,
          centeredBiasedSignChar (u j) (a j) t‖
        ≤ (biasedSignThirdMomentTerm (u i) (a i) * |t| / 2) *
            ‖∏ j ∈ Finset.univ.erase i,
              centeredBiasedSignChar (u j) (a j) t‖ := by
          gcongr
          exact biasedSignVariance_mul_norm_char_sub_zeroBiasChar_le
            (u i) (a i) t
    _ ≤ (biasedSignThirdMomentTerm (u i) (a i) * |t| / 2) *
          Real.exp
            (-((1 - biasedSignVarianceTerm (u i) (a i)) *
                t ^ 2) / 2 +
              (L - biasedSignThirdMomentTerm (u i) (a i)) *
                |t| ^ 3 / 5) := by
          exact mul_le_mul_of_nonneg_left hdeleted
            (div_nonneg
              (mul_nonneg
                (biasedSignThirdMomentTerm_nonneg (u i) (a i))
                (abs_nonneg t))
              (by norm_num))

/--
Endpoint domination for the deleted-coordinate cubic exponent on Tyurin's
first branch.
-/
theorem biasedSignDeletedExponent_le_tyurinEndpoint
    {u a t L : ℝ} (ht : 0 ≤ t) (hL : 0 ≤ L)
    (hthird : biasedSignThirdMomentTerm u a ≤ L)
    (hcut : t * lyapunovThirdRoot L ≤ 5 / 3) :
    biasedSignVarianceTerm u a * t ^ 2 / 2 -
          biasedSignThirdMomentTerm u a * t ^ 3 / 5 ≤
      lyapunovVarianceCap L * t ^ 2 / 2 -
          L * t ^ 3 / 5 := by
  let v := biasedSignVarianceTerm u a
  let β := biasedSignThirdMomentTerm u a
  let r := Real.sqrt v
  let R := lyapunovThirdRoot L
  have hv0 : 0 ≤ v := biasedSignVarianceTerm_nonneg u a
  have hβ0 : 0 ≤ β := biasedSignThirdMomentTerm_nonneg u a
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hR0 : 0 ≤ R := lyapunovThirdRoot_nonneg hL
  have hrSq : r ^ 2 = v := by
    dsimp [r]
    exact Real.sq_sqrt hv0
  have hRSq : R ^ 2 = lyapunovVarianceCap L := by
    exact lyapunovThirdRoot_sq hL
  have hRCube : R ^ 3 = L := lyapunovThirdRoot_cube hL
  have hvβ :
      v ^ 3 ≤ β ^ 2 :=
    biasedSignVarianceTerm_cube_le_thirdMomentTerm_sq u a
  have hvrβ : v * r ≤ β := by
    apply (sq_le_sq₀ (mul_nonneg hv0 hr0) hβ0).mp
    rw [show (v * r) ^ 2 = v ^ 3 by
      rw [mul_pow, hrSq]
      ring]
    exact hvβ
  have hvCap :
      v ≤ lyapunovVarianceCap L := by
    exact biasedSignVarianceTerm_le_lyapunovVarianceCap hL hthird
  have hrR : r ≤ R := by
    apply (sq_le_sq₀ hr0 hR0).mp
    rw [hrSq, hRSq]
    exact hvCap
  let y := t * r
  let Y := t * R
  have hy0 : 0 ≤ y := mul_nonneg ht hr0
  have hyY : y ≤ Y :=
    mul_le_mul_of_nonneg_left hrR ht
  have hprofile :=
    tyurinCubicProfile_mono hy0 hyY hcut
  have hlocal :
      v * t ^ 2 / 2 - β * t ^ 3 / 5 ≤
        y ^ 2 / 2 - y ^ 3 / 5 := by
    have ht3 : 0 ≤ t ^ 3 := by positivity
    have hthirdScaled :
        v * r * t ^ 3 ≤ β * t ^ 3 :=
      mul_le_mul_of_nonneg_right hvrβ ht3
    dsimp [y]
    rw [show (t * r) ^ 2 = v * t ^ 2 by
      rw [mul_pow, hrSq]
      ring]
    rw [show (t * r) ^ 3 = v * r * t ^ 3 by
      rw [mul_pow]
      rw [show r ^ 3 = r * r ^ 2 by ring, hrSq]
      ring]
    nlinarith
  calc
    v * t ^ 2 / 2 - β * t ^ 3 / 5
        ≤ y ^ 2 / 2 - y ^ 3 / 5 := hlocal
    _ ≤ Y ^ 2 / 2 - Y ^ 3 / 5 := hprofile
    _ = lyapunovVarianceCap L * t ^ 2 / 2 -
          L * t ^ 3 / 5 := by
      dsimp [Y]
      rw [mul_pow, mul_pow, hRSq, hRCube]
      ring

/-- Global maximum of one deleted-coordinate cubic exponent. -/
theorem biasedSignDeletedExponent_le_tyurinMaximum
    (u a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    biasedSignVarianceTerm u a * t ^ 2 / 2 -
        biasedSignThirdMomentTerm u a * t ^ 3 / 5 ≤
      25 / 54 := by
  let v := biasedSignVarianceTerm u a
  let β := biasedSignThirdMomentTerm u a
  let r := Real.sqrt v
  let y := t * r
  have hv0 : 0 ≤ v := biasedSignVarianceTerm_nonneg u a
  have hβ0 : 0 ≤ β := biasedSignThirdMomentTerm_nonneg u a
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrSq : r ^ 2 = v := by
    dsimp [r]
    exact Real.sq_sqrt hv0
  have hvβ :
      v ^ 3 ≤ β ^ 2 :=
    biasedSignVarianceTerm_cube_le_thirdMomentTerm_sq u a
  have hvrβ : v * r ≤ β := by
    apply (sq_le_sq₀ (mul_nonneg hv0 hr0) hβ0).mp
    rw [show (v * r) ^ 2 = v ^ 3 by
      rw [mul_pow, hrSq]
      ring]
    exact hvβ
  have hy0 : 0 ≤ y := mul_nonneg ht hr0
  have hlocal :
      v * t ^ 2 / 2 - β * t ^ 3 / 5 ≤
        y ^ 2 / 2 - y ^ 3 / 5 := by
    have ht3 : 0 ≤ t ^ 3 := by positivity
    have hthirdScaled :
        v * r * t ^ 3 ≤ β * t ^ 3 :=
      mul_le_mul_of_nonneg_right hvrβ ht3
    dsimp [y]
    rw [show (t * r) ^ 2 = v * t ^ 2 by
      rw [mul_pow, hrSq]
      ring]
    rw [show (t * r) ^ 3 = v * r * t ^ 3 by
      rw [mul_pow]
      rw [show r ^ 3 = r * r ^ 2 by ring, hrSq]
      ring]
    nlinarith
  exact hlocal.trans (tyurinCubicProfile_le_max hy0)

/--
First branch of Tyurin's deleted-product estimate.  The cubic terms cancel
at the endpoint, leaving only the two-thirds-power variance correction.
-/
theorem norm_prod_sub_productZeroBiasChar_le_tyurinFirstBranch
    [DecidableEq ι]
    (u a : ι → ℝ) {t L : ℝ}
    (ht : 0 ≤ t) (hL : 0 ≤ L)
    (hvar : ∑ i, biasedSignVarianceTerm (u i) (a i) = 1)
    (hthird : ∑ i, biasedSignThirdMomentTerm (u i) (a i) = L)
    (hcut : t * lyapunovThirdRoot L ≤ 5 / 3) :
    ‖(∏ i, centeredBiasedSignChar (u i) (a i) t) -
        centeredBiasedSignProductZeroBiasChar u a t‖ ≤
      L * t / 2 *
        Real.exp
          (-(t ^ 2) / 2 +
            lyapunovVarianceCap L * t ^ 2 / 2) := by
  have hdeleted :=
    norm_prod_sub_productZeroBiasChar_le_tyurinDeleted
      u a t L hvar hthird
  calc
    ‖(∏ i, centeredBiasedSignChar (u i) (a i) t) -
          centeredBiasedSignProductZeroBiasChar u a t‖
        ≤ ∑ i,
            (biasedSignThirdMomentTerm (u i) (a i) * |t| / 2) *
              Real.exp
                (-((1 - biasedSignVarianceTerm (u i) (a i)) *
                    t ^ 2) / 2 +
                  (L - biasedSignThirdMomentTerm (u i) (a i)) *
                    |t| ^ 3 / 5) := hdeleted
    _ ≤ ∑ i,
          (biasedSignThirdMomentTerm (u i) (a i) * t / 2) *
            Real.exp
              (-(t ^ 2) / 2 +
                lyapunovVarianceCap L * t ^ 2 / 2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_of_nonneg ht]
      apply mul_le_mul_of_nonneg_left
      · apply Real.exp_le_exp.mpr
        have hβi :
            biasedSignThirdMomentTerm (u i) (a i) ≤ L := by
          rw [← hthird]
          exact Finset.single_le_sum
            (fun j _ => biasedSignThirdMomentTerm_nonneg (u j) (a j))
            (Finset.mem_univ i)
        have hi :=
          biasedSignDeletedExponent_le_tyurinEndpoint
            (u := u i) (a := a i) ht hL hβi hcut
        nlinarith
      · exact div_nonneg
          (mul_nonneg
            (biasedSignThirdMomentTerm_nonneg (u i) (a i)) ht)
          (by norm_num)
    _ = L * t / 2 *
          Real.exp
            (-(t ^ 2) / 2 +
              lyapunovVarianceCap L * t ^ 2 / 2) := by
      rw [← Finset.sum_mul, ← Finset.sum_div,
        ← Finset.sum_mul, hthird]

/--
Second branch of Tyurin's deleted-product estimate, using the exact rational
height `ell = exp(-25/54)`.
-/
theorem norm_prod_sub_productZeroBiasChar_le_tyurinSecondBranch
    [DecidableEq ι]
    (u a : ι → ℝ) {t L : ℝ}
    (ht : 0 ≤ t)
    (hvar : ∑ i, biasedSignVarianceTerm (u i) (a i) = 1)
    (hthird : ∑ i, biasedSignThirdMomentTerm (u i) (a i) = L) :
    ‖(∏ i, centeredBiasedSignChar (u i) (a i) t) -
        centeredBiasedSignProductZeroBiasChar u a t‖ ≤
      L * t / (2 * tyurinRationalEll) *
        Real.exp (-(t ^ 2) / 2 + L * t ^ 3 / 5) := by
  have hdeleted :=
    norm_prod_sub_productZeroBiasChar_le_tyurinDeleted
      u a t L hvar hthird
  have hell : 0 < tyurinRationalEll := by
    unfold tyurinRationalEll
    positivity
  calc
    ‖(∏ i, centeredBiasedSignChar (u i) (a i) t) -
          centeredBiasedSignProductZeroBiasChar u a t‖
        ≤ ∑ i,
            (biasedSignThirdMomentTerm (u i) (a i) * |t| / 2) *
              Real.exp
                (-((1 - biasedSignVarianceTerm (u i) (a i)) *
                    t ^ 2) / 2 +
                  (L - biasedSignThirdMomentTerm (u i) (a i)) *
                    |t| ^ 3 / 5) := hdeleted
    _ ≤ ∑ i,
          (biasedSignThirdMomentTerm (u i) (a i) * t /
              (2 * tyurinRationalEll)) *
            Real.exp (-(t ^ 2) / 2 + L * t ^ 3 / 5) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_of_nonneg ht]
      have hexp :
          Real.exp
              (-((1 - biasedSignVarianceTerm (u i) (a i)) *
                  t ^ 2) / 2 +
                (L - biasedSignThirdMomentTerm (u i) (a i)) *
                  t ^ 3 / 5) ≤
            (1 / tyurinRationalEll) *
              Real.exp (-(t ^ 2) / 2 + L * t ^ 3 / 5) := by
        rw [show (1 / tyurinRationalEll) =
            Real.exp (25 / 54 : ℝ) by
          unfold tyurinRationalEll
          rw [one_div, ← Real.exp_neg]
          congr 1
          ring]
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hi :=
          biasedSignDeletedExponent_le_tyurinMaximum
            (u i) (a i) ht
        nlinarith
      calc
        (biasedSignThirdMomentTerm (u i) (a i) * t / 2) *
              Real.exp
                (-((1 - biasedSignVarianceTerm (u i) (a i)) *
                    t ^ 2) / 2 +
                  (L - biasedSignThirdMomentTerm (u i) (a i)) *
                    t ^ 3 / 5)
            ≤ (biasedSignThirdMomentTerm (u i) (a i) * t / 2) *
                ((1 / tyurinRationalEll) *
                  Real.exp (-(t ^ 2) / 2 + L * t ^ 3 / 5)) := by
              exact mul_le_mul_of_nonneg_left hexp
                (div_nonneg
                  (mul_nonneg
                    (biasedSignThirdMomentTerm_nonneg (u i) (a i)) ht)
                  (by norm_num))
        _ = (biasedSignThirdMomentTerm (u i) (a i) * t /
                (2 * tyurinRationalEll)) *
              Real.exp (-(t ^ 2) / 2 + L * t ^ 3 / 5) := by
              field_simp [hell.ne']
    _ = L * t / (2 * tyurinRationalEll) *
          Real.exp (-(t ^ 2) / 2 + L * t ^ 3 / 5) := by
      rw [← Finset.sum_mul, ← Finset.sum_div,
        ← Finset.sum_mul, hthird]

/--
Integrated first branch of Tyurin's `deltaTwo` estimate, before restoring
the Gaussian factor.
-/
theorem norm_gaussianRenormalized_product_sub_one_le_tyurinFirstBranch
    (u a : ι → ℝ) {t L : ℝ}
    (ht : 0 ≤ t) (hL : 0 ≤ L)
    (hvar : ∑ i, biasedSignVarianceTerm (u i) (a i) = 1)
    (hthird : ∑ i, biasedSignThirdMomentTerm (u i) (a i) = L)
    (hcut : t * lyapunovThirdRoot L ≤ 5 / 3) :
    ‖Complex.exp (((t ^ 2 / 2 : ℝ) : ℂ)) *
          (∏ i, centeredBiasedSignChar (u i) (a i) t) - 1‖ ≤
      ∫ s : ℝ in 0..t,
        L * s ^ 2 / 2 *
          Real.exp (lyapunovVarianceCap L * s ^ 2 / 2) := by
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
    have hst : s ≤ t := hs.2
    have hroot0 : 0 ≤ lyapunovThirdRoot L :=
      lyapunovThirdRoot_nonneg hL
    have hcutS : s * lyapunovThirdRoot L ≤ 5 / 3 :=
      (mul_le_mul_of_nonneg_right hst hroot0).trans hcut
    have hpoint :=
      norm_prod_sub_productZeroBiasChar_le_tyurinFirstBranch
        u a hs0 hL hvar hthird hcutS
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
          ≤ Real.exp (s ^ 2 / 2) * s *
              (L * s / 2 *
                Real.exp
                  (-(s ^ 2) / 2 +
                    lyapunovVarianceCap L * s ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left hpoint
          (mul_nonneg (Real.exp_nonneg _) hs0)
      _ = L * s ^ 2 / 2 *
          Real.exp (lyapunovVarianceCap L * s ^ 2 / 2) := by
        rw [show
            Real.exp (s ^ 2 / 2) * s *
                (L * s / 2 *
                  Real.exp
                    (-(s ^ 2) / 2 +
                      lyapunovVarianceCap L * s ^ 2 / 2)) =
              L * s ^ 2 / 2 *
                (Real.exp (s ^ 2 / 2) *
                  Real.exp
                    (-(s ^ 2) / 2 +
                      lyapunovVarianceCap L * s ^ 2 / 2)) by ring]
        rw [← Real.exp_add]
        congr 1
        ring_nf
  · have hscalar :
        Continuous (fun s : ℝ =>
          L * s ^ 2 / 2 *
            Real.exp (lyapunovVarianceCap L * s ^ 2 / 2)) := by
      fun_prop
    exact hscalar.intervalIntegrable _ _

/-! ## Reusable scalar envelopes -/

/--
Rationalized piecewise exponent in Tyurin's global product envelope.
-/
noncomputable def tyurinB (t gamma : ℝ) : ℝ :=
  if gamma * |t| < tyurinRationalM then
    -(t ^ 2) + 2 * gamma * tyurinRationalA * |t| ^ 3
  else if gamma * |t| ≤ 2 * Real.pi then
    -2 * tyurinCosineLoss / gamma ^ 2 *
      (1 - Real.cos (gamma * t))
  else
    0

/-- Tyurin's global product-modulus envelope. -/
noncomputable def tyurinProductEnvelope (L t : ℝ) : ℝ :=
  Real.exp (tyurinB t (2 * L) / 2)

/-- Tyurin's first characteristic-function discrepancy envelope. -/
noncomputable def tyurinDeltaOne (L t : ℝ) : ℝ :=
  L * Real.exp (-(|t| ^ 2) / 2) *
    (∫ s : ℝ in 0..|t|,
      s ^ 2 / 2 * Real.exp (s ^ 2 / 2))

/--
Tyurin's rationalized `deltaTwo` envelope.  The branch condition is written
without division, so it remains total at `L = 0`.
-/
noncomputable def tyurinDeltaTwo (L t : ℝ) : ℝ :=
  let T := |t|
  let R := lyapunovThirdRoot L
  let A := 5 / (3 * R)
  if T * R ≤ 5 / 3 then
    L * Real.exp (-(T ^ 2) / 2) *
      (∫ s : ℝ in 0..T,
        s ^ 2 / 2 *
          Real.exp (lyapunovVarianceCap L * s ^ 2 / 2))
  else
    L * Real.exp (-(T ^ 2) / 2) *
      ((∫ s : ℝ in 0..A,
          s ^ 2 / 2 *
            Real.exp (lyapunovVarianceCap L * s ^ 2 / 2)) +
        ∫ s : ℝ in A..T,
          s ^ 2 / (2 * tyurinRationalEll) *
            Real.exp (L * s ^ 3 / 5))

theorem tyurinB_firstBranch
    {t gamma : ℝ}
    (h : gamma * |t| < tyurinRationalM) :
    tyurinB t gamma =
      -(t ^ 2) + 2 * gamma * tyurinRationalA * |t| ^ 3 := by
  simp [tyurinB, h]

/-- Direct boundary canary: equality at the rational switch uses the cosine branch. -/
theorem tyurinB_switchBoundary
    {t gamma : ℝ} (h : gamma * |t| = tyurinRationalM) :
    tyurinB t gamma =
      -2 * tyurinCosineLoss / gamma ^ 2 *
        (1 - Real.cos (gamma * t)) := by
  have hMpi : tyurinRationalM ≤ 2 * Real.pi := by
    unfold tyurinRationalM
    nlinarith [Real.pi_gt_three]
  simp [tyurinB, h, hMpi]

/--
The complete certified global product envelope: the cubic branch below the
rational switch, the `49 / 50` cosine branch up to `2π`, and the trivial
unit envelope thereafter.
-/
theorem norm_prod_centeredBiasedSignChar_le_tyurinProductEnvelope
    (u a : ι → ℝ) {t L : ℝ}
    (hL : 0 ≤ L)
    (hvar : ∑ i, biasedSignVarianceTerm (u i) (a i) = 1)
    (hthird : ∑ i, biasedSignThirdMomentTerm (u i) (a i) = L) :
    ‖∏ i, centeredBiasedSignChar (u i) (a i) t‖ ≤
      tyurinProductEnvelope L t := by
  classical
  by_cases hfirst : 2 * L * |t| < 4
  · have hbranch :
        (2 * L) * |t| < tyurinRationalM := by
      unfold tyurinRationalM
      linarith
    have hcubic :=
      norm_prod_centeredBiasedSignChar_le_tyurinCubic
        u a t L hvar hthird
    rw [tyurinProductEnvelope, tyurinB, if_pos hbranch]
    convert hcubic using 1
    congr 1
    unfold tyurinRationalA
    ring
  · have hfreq0 : 4 ≤ 2 * L * |t| := le_of_not_gt hfirst
    have hbranch0 :
        ¬((2 * L) * |t| < tyurinRationalM) := by
      unfold tyurinRationalM
      simpa [mul_assoc] using hfirst
    by_cases hsecond : 2 * L * |t| ≤ 2 * Real.pi
    · have hLpos : 0 < L := by
        by_contra h
        have hLzero : L = 0 := le_antisymm (le_of_not_gt h) hL
        rw [hLzero] at hfreq0
        norm_num at hfreq0
      have hbranch1 :
          (2 * L) * |t| ≤ 2 * Real.pi := by
        simpa [mul_assoc] using hsecond
      have hcosine :=
        norm_prod_centeredBiasedSignChar_le_tyurinCosine
          u a hLpos hvar hthird hfreq0 hsecond
      rw [tyurinProductEnvelope, tyurinB, if_neg hbranch0,
        if_pos hbranch1]
      convert hcosine using 1
      congr 1
      have hcos :
          Real.cos ((2 * L) * t) =
            Real.cos (2 * L * |t|) := by
        rw [← Real.cos_abs ((2 * L) * t)]
        congr 1
        rw [abs_mul, abs_mul, abs_of_nonneg hL, abs_of_nonneg
          (by norm_num : (0 : ℝ) ≤ 2)]
      rw [hcos]
      field_simp [hLpos.ne']
      ring
    · have hbranch1 :
          ¬((2 * L) * |t| ≤ 2 * Real.pi) := by
        simpa [mul_assoc] using hsecond
      rw [tyurinProductEnvelope, tyurinB, if_neg hbranch0,
        if_neg hbranch1]
      norm_num
      calc
        ∏ i, ‖centeredBiasedSignChar (u i) (a i) t‖
            ≤ ∏ _i : ι, (1 : ℝ) := by
              apply Finset.prod_le_prod
              · intro i _
                exact norm_nonneg _
              · intro i _
                exact norm_centeredBiasedSignChar_le_one _ _ _
        _ = 1 := by simp

/--
The two distribution-independent Gaussian terms in Tyurin's actual
`D*` functional.  We retain the exact Gaussian core-correction integral:
replacing it by the global weighted envelope loses too much in the
moderate-Lyapunov regime.  Only the reference tail is closed analytically.
-/
noncomputable def tyurinGaussianActualBudget
    (U₀ U : ℝ) : ℝ :=
  2 * (∫ u : ℝ in 0..U₀,
      ‖scaledPrawitzKernel U u - principalCDFKernel u‖ *
        Real.exp (-(u ^ 2) / 2)) +
    Real.exp (-(U₀ ^ 2) / 2) /
      (Real.pi * U₀ ^ 2)

/--
The mathematical `D*` functional with the actual Gaussian correction
integral retained.  This is the reference definition against which closed
certificate budgets are checked.
-/
noncomputable def tyurinActualDStar
    (L U₀ U : ℝ) : ℝ :=
  (2 * (∫ u : ℝ in 0..U₀,
      ‖scaledPrawitzKernel U u‖ *
        min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)) +
    2 * (∫ u : ℝ in U₀..U,
      ‖scaledPrawitzKernel U u‖ *
        tyurinProductEnvelope L u) +
    tyurinGaussianActualBudget U₀ U) / L

/--
The canonical certificate-facing rationalized Prawitz functional.  Its
Gaussian term uses the sharp I.30 budget, retaining the negative first
Gaussian moment that is essential in the moderate-Lyapunov regime.
-/
noncomputable def tyurinRationalDStar
    (L U₀ U : ℝ) : ℝ :=
  (2 * (∫ u : ℝ in 0..U₀,
      ‖scaledPrawitzKernel U u‖ *
        min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)) +
    2 * (∫ u : ℝ in U₀..U,
      ‖scaledPrawitzKernel U u‖ *
        tyurinProductEnvelope L u) +
    prawitzGaussianSharpClosedBudget U₀ U) / L

/--
The cheaper closed-budget variant used only in the all-the-way-to-zero
Lyapunov branch.  It is deliberately separate from `tyurinRationalDStar`:
the weighted closed envelope is too coarse to certify the moderate regime.
-/
noncomputable def tyurinSmallRationalDStar
    (L U₀ U : ℝ) : ℝ :=
  (2 * (∫ u : ℝ in 0..U₀,
      ‖scaledPrawitzKernel U u‖ *
        min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)) +
    2 * (∫ u : ℝ in U₀..U,
      ‖scaledPrawitzKernel U u‖ *
        tyurinProductEnvelope L u) +
    prawitzGaussianWeightedClosedBudget U₀ U) / L

/-- The logarithmic small-L core cutoff; unlike a fixed cutoff, this sends
the normalized Gaussian reference tail to zero as `L → 0+`. -/
noncomputable def tyurinSmallCutoff (L : ℝ) : ℝ :=
  2 * Real.sqrt (Real.log (1 / L))

/-- The scaled bandwidth used in the all-the-way-to-zero branch. -/
noncomputable def tyurinScaledBandwidth (L : ℝ) : ℝ :=
  (157 / 50 : ℝ) / L

/-! ## The all-the-way-to-zero cutoff geometry -/

theorem one_lt_log_inv_of_le_one_fiftieth
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ 1 / 50) :
    1 < Real.log (1 / L) := by
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  calc
    Real.exp 1 < 3 := Real.exp_one_lt_three
    _ ≤ 1 / L := by
      rw [le_div_iff₀ hL]
      nlinarith

theorem tyurinSmallCutoff_pos
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ 1 / 50) :
    0 < tyurinSmallCutoff L := by
  unfold tyurinSmallCutoff
  have hlog := one_lt_log_inv_of_le_one_fiftieth hL hsmall
  positivity

theorem tyurinSmallCutoff_sq
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ 1 / 50) :
    tyurinSmallCutoff L ^ 2 = 4 * Real.log (1 / L) := by
  unfold tyurinSmallCutoff
  rw [mul_pow, Real.sq_sqrt
    (zero_le_one.trans
      (one_lt_log_inv_of_le_one_fiftieth hL hsmall).le)]
  ring

theorem exp_neg_tyurinSmallCutoff_sq_div_two
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ 1 / 50) :
    Real.exp (-(tyurinSmallCutoff L ^ 2) / 2) = L ^ 2 := by
  rw [tyurinSmallCutoff_sq hL hsmall]
  have hlog :
      -(4 * Real.log (1 / L)) / 2 =
        Real.log (L ^ 2) := by
    rw [Real.log_pow, one_div, Real.log_inv]
    ring
  rw [hlog, Real.exp_log]
  positivity

theorem sqrt_log_inv_le_scaled
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ 1 / 50) :
    Real.sqrt (Real.log (1 / L)) ≤
      (157 / 315 : ℝ) / L := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have hinvPos : 0 < 1 / L := by positivity
    have hlogLe :
        Real.log (1 / L) ≤ 1 / L :=
      (Real.log_le_sub_one_of_pos hinvPos).trans (by linarith)
    have hcap : L ≤ (157 / 315 : ℝ) ^ 2 := by
      exact hsmall.trans (by norm_num)
    have hrecip :
        1 / L ≤ ((157 / 315 : ℝ) / L) ^ 2 := by
      rw [show 1 / L = L / L ^ 2 by
        field_simp [hL.ne']]
      rw [div_pow]
      rw [div_le_div_iff₀ (sq_pos_of_pos hL) (sq_pos_of_pos hL)]
      exact mul_le_mul_of_nonneg_right hcap (sq_nonneg L)
    exact hlogLe.trans hrecip

theorem tyurinSmallCutoff_pi_le_scaledBandwidth
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ 1 / 50) :
    Real.pi * tyurinSmallCutoff L ≤
      tyurinScaledBandwidth L := by
  have hsqrt := sqrt_log_inv_le_scaled hL hsmall
  have hpi : Real.pi ≤ 63 / 20 := by
    nlinarith [Real.pi_lt_d2]
  unfold tyurinSmallCutoff tyurinScaledBandwidth
  have hnonneg : 0 ≤ Real.sqrt (Real.log (1 / L)) :=
    Real.sqrt_nonneg _
  calc
    Real.pi * (2 * Real.sqrt (Real.log (1 / L)))
        ≤ (63 / 20 : ℝ) *
            (2 * Real.sqrt (Real.log (1 / L))) := by
          gcongr
    _ ≤ (63 / 20 : ℝ) *
            (2 * ((157 / 315 : ℝ) / L)) := by
          gcongr
    _ = (157 / 50 : ℝ) / L := by ring

theorem tyurinScaledBandwidth_lt_pi_div
    {L : ℝ} (hL : 0 < L) :
    tyurinScaledBandwidth L < Real.pi / L := by
  unfold tyurinScaledBandwidth
  apply div_lt_div_of_pos_right _ hL
  nlinarith [Real.pi_gt_d2]

end Probability
end CertifiedJL
