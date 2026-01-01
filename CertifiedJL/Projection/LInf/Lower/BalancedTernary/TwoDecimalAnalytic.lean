/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Interval.Reflection
import CertifiedJL.Arithmetic.Transcendental.Trigonometric.Trig
import CertifiedJL.Analysis.Fourier.ElementaryCosineSmallBall

/-!
# Analytic constants for the two-decimal sparse `L∞` lower bounds

This module proves the common normalized-cosine estimates and the endpoint
cosine floors used by the generated trigonometric majorants.  Every decimal
appearing below is an exact rational number.  Transcendental comparisons are
discharged by theorem-backed interval arithmetic or elementary alternating
Taylor bounds.
-/

open scoped BigOperators ENNReal

namespace CertifiedJL
namespace SparseLInfLowerTwoDecimal

open Probability

private theorem exp_neg_lt {x u : ℚ} (hx : 0 ≤ x)
    (hcheck : Interval.upperLTCheck (Exp.negUpper 64 x 32) u = true) :
    Real.exp (-(x : ℝ)) < (u : ℝ) := by
  exact Interval.lt_of_contains_of_upperLTCheck
    (Exp.negUpper_contains (p := 64) (k := 32) (x := x) hx) hcheck

theorem exp_neg_lambda_sq_div_two_lt :
    Real.exp (-(12321 / 20000 : ℝ)) < 5401 / 10000 := by
  simpa using exp_neg_lt (x := 12321 / 20000) (u := 5401 / 10000)
    (by norm_num) (by decide +kernel)

theorem exp_neg_two_lambda_sq_lt :
    Real.exp (-(12321 / 5000 : ℝ)) < 851 / 10000 := by
  simpa using exp_neg_lt (x := 12321 / 5000) (u := 851 / 10000)
    (by norm_num) (by decide +kernel)

private theorem piLower_lt_pi : (392699 / 125000 : ℝ) < Real.pi := by
  nlinarith [Real.pi_gt_d6]

private theorem exp_neg_pi_sq_mul_lt
    {s x u : ℚ} (hs : 0 < s)
    (hx : x = (392699 / 125000) ^ 2 * s ^ 2)
    (hcheck : Interval.upperLTCheck (Exp.negUpper 64 x 32) u = true) :
    Real.exp (-(Real.pi ^ 2 * (s : ℝ) ^ 2)) < (u : ℝ) := by
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hpiLower0 : (0 : ℝ) < 392699 / 125000 := by norm_num
  have hpiSq : (392699 / 125000 : ℝ) ^ 2 < Real.pi ^ 2 := by
    nlinarith [piLower_lt_pi]
  have hsSq : (0 : ℝ) < (s : ℝ) ^ 2 := sq_pos_of_pos hsR
  have harg : (x : ℝ) < Real.pi ^ 2 * (s : ℝ) ^ 2 := by
    rw [hx]
    push_cast
    exact mul_lt_mul_of_pos_right hpiSq hsSq
  have hr := exp_neg_lt (x := x) (u := u) (by
    rw [hx]
    positivity) hcheck
  exact (Real.exp_lt_exp.mpr (by linarith)).trans hr

theorem exp_neg_diffuse24_lt :
    Real.exp (-(Real.pi ^ 2 * (113 / 250 : ℝ) ^ 2)) < 333 / 2500 := by
  have h := exp_neg_pi_sq_mul_lt (s := 113 / 250)
      (x := (392699 / 125000 : ℚ) ^ 2 * (113 / 250) ^ 2)
      (u := 333 / 2500)
      (by norm_num) rfl (by decide +kernel)
  convert h using 1 <;> norm_num

theorem exp_neg_diffuse34_lt :
    Real.exp (-(Real.pi ^ 2 * (111 / 250 : ℝ) ^ 2)) < 71447 / 500000 := by
  have h := exp_neg_pi_sq_mul_lt (s := 111 / 250)
      (x := (392699 / 125000 : ℚ) ^ 2 * (111 / 250) ^ 2)
      (u := 71447 / 500000)
      (by norm_num) rfl (by decide +kernel)
  convert h using 1 <;> norm_num

theorem exp_neg_diffuse42_lt :
    Real.exp (-(Real.pi ^ 2 * (929 / 2000 : ℝ) ^ 2)) < 119 / 1000 := by
  have h := exp_neg_pi_sq_mul_lt (s := 929 / 2000)
      (x := (392699 / 125000 : ℚ) ^ 2 * (929 / 2000) ^ 2)
      (u := 119 / 1000)
      (by norm_num) rfl (by decide +kernel)
  convert h using 1 <;> norm_num

set_option maxRecDepth 1000000 in
theorem exp_neg_diffuse47_lt :
    Real.exp (-(Real.pi ^ 2 * (4679 / 10000 : ℝ) ^ 2)) < 2881 / 25000 := by
  have h := exp_neg_pi_sq_mul_lt (s := 4679 / 10000)
      (x := (392699 / 125000 : ℚ) ^ 2 * (4679 / 10000) ^ 2)
      (u := 2881 / 25000)
      (by norm_num) rfl (by decide +kernel)
  convert h using 1 <;> norm_num

private theorem central_cos_lower
    {cap endpoint : ℚ}
    (hcap0 : 0 ≤ cap) (hcapHalf : cap ≤ 1 / 2)
    (hcheck : endpoint <
      1 - (2 * (111 / 100 : ℚ) ^ 2 * cap ^ 2) / 2 +
        (2 * (111 / 100 : ℚ) ^ 2 * cap ^ 2) ^ 2 / 24 -
        (2 * (111 / 100 : ℚ) ^ 2 * cap ^ 2) ^ 3 / 720) :
    (endpoint : ℝ) <
      Real.cos ((111 / 100 : ℝ) * (cap : ℝ) * Real.sqrt 2) := by
  let x : ℝ := (111 / 100 : ℝ) * (cap : ℝ) * Real.sqrt 2
  have hcap0R : (0 : ℝ) ≤ (cap : ℝ) := by exact_mod_cast hcap0
  have hx0 : 0 ≤ x := by positivity
  have hxpi : x ≤ Real.pi / 2 := by
    have hcapHalf : (cap : ℝ) ≤ 1 / 2 := by
      rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num]
      exact_mod_cast hcapHalf
    have hsqrt : Real.sqrt 2 < 3 / 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_nonneg 2]
    dsimp [x]
    nlinarith [Real.pi_gt_three]
  have ht := Probability.elementary_cos_taylor_six_le hx0 hxpi
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hx2 : x ^ 2 =
      (2 * (111 / 100 : ℚ) ^ 2 * cap ^ 2 : ℚ) := by
    dsimp [x]
    push_cast
    rw [mul_pow, mul_pow, hs2]
    ring
  have hx4 : x ^ 4 =
      ((2 * (111 / 100 : ℚ) ^ 2 * cap ^ 2 : ℚ) : ℝ) ^ 2 := by
    rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, hx2]
  have hx6 : x ^ 6 =
      ((2 * (111 / 100 : ℚ) ^ 2 * cap ^ 2 : ℚ) : ℝ) ^ 3 := by
    rw [show x ^ 6 = (x ^ 2) ^ 3 by ring, hx2]
  rw [hx2, hx4, hx6] at ht
  have hcheckR :
      (endpoint : ℝ) <
        1 - (((2 * (111 / 100 : ℚ) ^ 2 * cap ^ 2 : ℚ) : ℝ)) / 2 +
          (((2 * (111 / 100 : ℚ) ^ 2 * cap ^ 2 : ℚ) : ℝ)) ^ 2 / 24 -
          (((2 * (111 / 100 : ℚ) ^ 2 * cap ^ 2 : ℚ) : ℝ)) ^ 3 / 720 := by
    exact_mod_cast hcheck
  linarith

theorem cos_central24_lower :
    (1859733 / 2000000 : ℝ) <
      Real.cos ((111 / 100 : ℝ) * (6 / 25 : ℝ) * Real.sqrt 2) := by
  have h := central_cos_lower (cap := 6 / 25)
    (endpoint := 1859733 / 2000000) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem cos_central34_lower :
    (43045911 / 50000000 : ℝ) <
      Real.cos ((111 / 100 : ℝ) * (17 / 50 : ℝ) * Real.sqrt 2) := by
  have h := central_cos_lower (cap := 17 / 50)
    (endpoint := 43045911 / 50000000) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem cos_central42_lower :
    (19760411 / 25000000 : ℝ) <
      Real.cos ((111 / 100 : ℝ) * (21 / 50 : ℝ) * Real.sqrt 2) := by
  have h := central_cos_lower (cap := 21 / 50)
    (endpoint := 19760411 / 25000000) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

theorem cos_central47_lower :
    (591961 / 800000 : ℝ) <
      Real.cos ((111 / 100 : ℝ) * (47 / 100 : ℝ) * Real.sqrt 2) := by
  have h := central_cos_lower (cap := 47 / 100)
    (endpoint := 591961 / 800000) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

private theorem diffuse_cos_lower {cap endpoint : ℚ}
    (hcap0 : 0 ≤ cap) (hcapHalf : cap ≤ 1 / 2)
    (hcheck : Interval.lowerGTCheck
      (TrigInterval.cosPiHalf (p := 64) cap 2) endpoint = true) :
    (endpoint : ℝ) < Real.cos (Real.pi * (cap : ℝ)) := by
  exact Interval.lt_of_lowerGTCheck_of_contains hcheck
    (TrigInterval.cosPiHalf_contains (p := 64) hcap0 hcapHalf 2)

theorem cos_diffuse24_lower :
    (72896857 / 100000000 : ℝ) < Real.cos (Real.pi * (6 / 25 : ℝ)) := by
  have h := diffuse_cos_lower (cap := 6 / 25)
    (endpoint := 72896857 / 100000000) (by norm_num) (by norm_num)
    (by decide +kernel)
  convert h using 1 <;> norm_num

theorem cos_diffuse34_lower :
    (12043839 / 25000000 : ℝ) < Real.cos (Real.pi * (17 / 50 : ℝ)) := by
  have h := diffuse_cos_lower (cap := 17 / 50)
    (endpoint := 12043839 / 25000000) (by norm_num) (by norm_num)
    (by decide +kernel)
  convert h using 1 <;> norm_num

theorem cos_diffuse42_lower :
    (3108621 / 12500000 : ℝ) < Real.cos (Real.pi * (21 / 50 : ℝ)) := by
  have h := diffuse_cos_lower (cap := 21 / 50)
    (endpoint := 3108621 / 12500000) (by norm_num) (by norm_num)
    (by decide +kernel)
  convert h using 1 <;> norm_num

theorem cos_diffuse47_lower :
    (1176349 / 12500000 : ℝ) < Real.cos (Real.pi * (47 / 100 : ℝ)) := by
  have h := diffuse_cos_lower (cap := 47 / 100)
    (endpoint := 1176349 / 12500000) (by norm_num) (by norm_num)
    (by decide +kernel)
  convert h using 1 <;> norm_num

end SparseLInfLowerTwoDecimal
end CertifiedJL
