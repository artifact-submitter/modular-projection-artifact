/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# Fourth-order cosine--Gaussian comparison

This file proves the scalar comparison (S2) used by Gaussian replacement for
signed-Rademacher remainders.  It is certificate-independent owner theory.
-/

namespace CertifiedJL

open Set

private theorem exp_neg_le_taylor_four {y : ℝ} (hy : 0 ≤ y) :
    Real.exp (-y) ≤ 1 - y + y ^ 2 / 2 - y ^ 3 / 6 + y ^ 4 / 24 := by
  rcases eq_or_lt_of_le hy with rfl | hy
  · norm_num
  · obtain ⟨z, hz, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
      (f := fun t : ℝ => Real.exp (-t)) (x₀ := 0) (x := y) (n := 4)
      hy.ne'.symm (by fun_prop)
    have hzpos : 0 < z := by simpa [uIoo, hy.le] using hz.1
    have hderiv : iteratedDeriv 5 (fun t : ℝ => Real.exp (-t)) z =
        -Real.exp (-z) := by
      rw [show (fun t : ℝ => Real.exp (-t)) =
          fun t : ℝ => Real.exp ((-1) * t) by
        funext t
        congr 1
        ring]
      rw [iteratedDeriv_exp_const_mul]
      norm_num
    rw [uIcc_of_lt hy] at hrem
    have htaylor :
        taylorWithinEval (fun t : ℝ => Real.exp (-t)) 4 (Icc 0 y) 0 y =
          1 - y + y ^ 2 / 2 - y ^ 3 / 6 + y ^ 4 / 24 := by
      have hwithin (k : ℕ) :
          iteratedDerivWithin k (fun t : ℝ => Real.exp (-t)) (Icc 0 y) 0 =
            iteratedDeriv k (fun t : ℝ => Real.exp (-t)) 0 :=
        iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hy)
          (by fun_prop) ⟨le_rfl, hy.le⟩
      rw [taylor_within_apply]
      simp_rw [hwithin]
      rw [show (fun t : ℝ => Real.exp (-t)) =
          fun t : ℝ => Real.exp ((-1) * t) by
        funext t
        congr 1
        ring]
      simp_rw [iteratedDeriv_exp_const_mul]
      norm_num [Finset.sum_range_succ]
      ring
    rw [hderiv] at hrem
    rw [htaylor] at hrem
    norm_num at hrem
    have hnonpos : -Real.exp (-z) * y ^ 5 / 120 ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (Real.exp_pos (-z)).le) (pow_nonneg hy.le 5))
        (by norm_num)
    linarith

private theorem cos_taylor_six_le_of_nonneg_of_le_pi {x : ℝ}
    (hx : 0 ≤ x) (hxpi : x ≤ Real.pi) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · norm_num
  · obtain ⟨z, hz, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
      (f := Real.cos) (x₀ := 0) (x := x) (n := 6)
      hx.ne'.symm (by fun_prop)
    have hzmem : z ∈ Set.Ioo 0 Real.pi := by
      have hz' : z ∈ Set.Ioo 0 x := by simpa [uIoo, hx.le] using hz
      exact ⟨hz'.1, hz'.2.trans_le hxpi⟩
    have hsin : 0 ≤ Real.sin z :=
      (Real.sin_pos_of_pos_of_lt_pi hzmem.1 hzmem.2).le
    have hderiv : iteratedDeriv 7 Real.cos z = Real.sin z := by
      rw [show (7 : ℕ) = 2 * 3 + 1 by norm_num,
        Real.iteratedDeriv_odd_cos]
      norm_num
    rw [uIcc_of_lt hx] at hrem
    have htaylor : taylorWithinEval Real.cos 6 (Icc 0 x) 0 x =
        1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 := by
      have hwithin (k : ℕ) :
          iteratedDerivWithin k Real.cos (Icc 0 x) 0 =
            iteratedDeriv k Real.cos 0 :=
        iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx)
          (by fun_prop) ⟨le_rfl, hx.le⟩
      rw [taylor_within_apply]
      simp_rw [hwithin]
      norm_num [Finset.sum_range_succ]
      ring
    rw [hderiv] at hrem
    rw [htaylor] at hrem
    norm_num at hrem
    have hnonneg : 0 ≤ Real.sin z * x ^ 7 / 5040 := by positivity
    linarith

private theorem cos_le_taylor_four_of_nonneg_of_le_pi {x : ℝ}
    (hx : 0 ≤ x) (hxpi : x ≤ Real.pi) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · norm_num
  · obtain ⟨z, hz, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
      (f := Real.cos) (x₀ := 0) (x := x) (n := 4)
      hx.ne'.symm (by fun_prop)
    have hzmem : z ∈ Set.Ioo 0 Real.pi := by
      have hz' : z ∈ Set.Ioo 0 x := by simpa [uIoo, hx.le] using hz
      exact ⟨hz'.1, hz'.2.trans_le hxpi⟩
    have hsin : 0 ≤ Real.sin z :=
      (Real.sin_pos_of_pos_of_lt_pi hzmem.1 hzmem.2).le
    have hderiv : iteratedDeriv 5 Real.cos z = -Real.sin z := by
      rw [show (5 : ℕ) = 2 * 2 + 1 by norm_num,
        Real.iteratedDeriv_odd_cos]
      norm_num
    rw [uIcc_of_lt hx] at hrem
    have htaylor : taylorWithinEval Real.cos 4 (Icc 0 x) 0 x =
        1 - x ^ 2 / 2 + x ^ 4 / 24 := by
      have hwithin (k : ℕ) :
          iteratedDerivWithin k Real.cos (Icc 0 x) 0 =
            iteratedDeriv k Real.cos 0 :=
        iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx)
          (by fun_prop) ⟨le_rfl, hx.le⟩
      rw [taylor_within_apply]
      simp_rw [hwithin]
      norm_num [Finset.sum_range_succ]
      ring
    rw [hderiv, htaylor] at hrem
    norm_num at hrem
    have hnonpos : -Real.sin z * x ^ 5 / 120 ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hsin) (pow_nonneg hx.le 5))
        (by norm_num)
    linarith

/-- **Cosine--Gaussian comparison (S2).**  The characteristic function of a
standard sign differs from the matching centered Gaussian characteristic
function by at most the fourth-order term used in the replacement argument. -/
theorem abs_cos_sub_exp_neg_half_sq_le (x : ℝ) :
    |Real.cos x - Real.exp (-(x ^ 2) / 2)| ≤ x ^ 4 / 12 := by
  let r := |x|
  have hr : 0 ≤ r := abs_nonneg x
  have hx2 : x ^ 2 = r ^ 2 := by simp [r, sq_abs]
  have hx4 : x ^ 4 = r ^ 4 := by
    rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, hx2]
    ring
  have hcos : Real.cos x = Real.cos r := by
    rcases le_total 0 x with hx | hx
    · simp [r, abs_of_nonneg hx]
    · rw [show r = -x by simp [r, abs_of_nonpos hx], Real.cos_neg]
  rw [hcos, hx2, hx4]
  rw [show -(r ^ 2) / 2 = -(r ^ 2 / 2) by ring]
  by_cases hlarge : 24 ≤ r ^ 4
  · have habs :
        |Real.cos r - Real.exp (-(r ^ 2 / 2))| ≤ 2 := by
      calc
        |Real.cos r - Real.exp (-(r ^ 2 / 2))| ≤
            |Real.cos r| + |Real.exp (-(r ^ 2 / 2))| := abs_sub _ _
        _ ≤ 1 + 1 := by
          gcongr
          · exact Real.abs_cos_le_one r
          · rw [abs_of_pos (Real.exp_pos _)]
            exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg r])
        _ = 2 := by norm_num
    exact habs.trans (show (2 : ℝ) ≤ r ^ 4 / 12 by nlinarith)
  · have hr4 : r ^ 4 < 24 := lt_of_not_ge hlarge
    have hpi : r ≤ Real.pi := by
      have hpi3 := Real.pi_gt_three
      by_contra h
      have hr3 : 3 < r := hpi3.trans_le (le_of_not_ge h)
      have hr2 : 9 < r ^ 2 := by nlinarith [sq_nonneg (r - 3)]
      have hr4gt : 81 < r ^ 4 := by
        nlinarith [show r ^ 4 = (r ^ 2) ^ 2 by ring, sq_nonneg (r ^ 2 - 9)]
      linarith
    have hcosLower := cos_taylor_six_le_of_nonneg_of_le_pi hr hpi
    have hcosUpper := cos_le_taylor_four_of_nonneg_of_le_pi hr hpi
    have hexpUpper := exp_neg_le_taylor_four (y := r ^ 2 / 2) (by positivity)
    have hexpLower : 1 - r ^ 2 / 2 ≤ Real.exp (-(r ^ 2 / 2)) := by
      linarith [Real.add_one_le_exp (-(r ^ 2 / 2))]
    rw [abs_le]
    constructor
    · have hr2lt : r ^ 2 < 5 := by
        nlinarith [show r ^ 4 = (r ^ 2) ^ 2 by ring, sq_nonneg (r ^ 2 - 5)]
      have hpower : r ^ 8 ≤ 5 * r ^ 6 := by
        calc
          r ^ 8 = r ^ 6 * r ^ 2 := by ring
          _ ≤ r ^ 6 * 5 :=
            mul_le_mul_of_nonneg_left hr2lt.le (pow_nonneg hr 6)
          _ = 5 * r ^ 6 := by ring
      have hexpUpper' : Real.exp (-(r ^ 2 / 2)) ≤
          1 - r ^ 2 / 2 + r ^ 4 / 8 - r ^ 6 / 48 + r ^ 8 / 384 := by
        calc
          Real.exp (-(r ^ 2 / 2)) ≤
              1 - r ^ 2 / 2 + (r ^ 2 / 2) ^ 2 / 2 -
                (r ^ 2 / 2) ^ 3 / 6 + (r ^ 2 / 2) ^ 4 / 24 := hexpUpper
          _ = 1 - r ^ 2 / 2 + r ^ 4 / 8 - r ^ 6 / 48 + r ^ 8 / 384 := by
            ring
      have hec : Real.exp (-(r ^ 2 / 2)) - Real.cos r ≤ r ^ 4 / 12 := by
        linarith
      linarith
    · nlinarith [pow_nonneg hr 4]

end CertifiedJL
