/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Diffuse.LowScalar

/-! # Low-mass scalar envelope for the floor-73 diffuse profile -/

open scoped BigOperators

open MeasureTheory ProbabilityTheory

namespace CertifiedJL
namespace ThresholdDiffuseFloor73Scalar

open ThresholdDiffuseLowScalar

private theorem moving_lt {x C : ℝ}
    (hx0 : 1 ≤ x) (hx1 : x ≤ 11 / 10) (hxC :
      ((4 - (32 / 9 : ℝ) * x) / 2) *
          ((1 / 2 : ℝ) + (1 / 2) * (247 / 1000 : ℝ)) +
        (((32 / 9 : ℝ) * x - 2) / 2) *
          ((3 / 8 : ℝ) + (1 / 2) * (247 / 1000 : ℝ) +
            (1 / 8) * (4 / 1000 : ℝ)) < C) :
    sparseScalarF ((5 / 2) * x) ((32 / 9) * x) < C := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx0
  have hp2 : (2 : ℝ) ≤ (32 / 9) * x := by nlinarith
  have hp4 : (32 / 9 : ℝ) * x ≤ 4 := by nlinarith
  have hratio : ((5 / 2 : ℝ) * x) / ((32 / 9) * x) = 45 / 64 := by
    field_simp [hxpos.ne']
    ring
  have hbase := sparseScalarF_between_two_four_le hp2 hp4
    (by norm_num : (0 : ℝ) ≤ 45 / 64) hratio
  have h2 := exp_neg_lt (x := (45 / 32 : ℚ))
    (u := (247 / 1000 : ℚ)) (by norm_num) (by decide +kernel)
  have h8 := exp_neg_lt (x := (45 / 8 : ℚ))
    (u := (4 / 1000 : ℚ)) (by norm_num) (by decide +kernel)
  apply hbase.trans_lt
  have hw2 : 0 ≤ (4 - (32 / 9 : ℝ) * x) / 2 := by positivity
  have hw4 : 0 ≤ ((32 / 9 : ℝ) * x - 2) / 2 := by positivity
  have hm2 :
      (1 / 2 : ℝ) + (1 / 2) * Real.exp (-2 * (45 / 64)) <
        (1 / 2 : ℝ) + (1 / 2) * (247 / 1000) := by
    norm_num at h2 ⊢
    linarith
  have hm4 :
      (3 / 8 : ℝ) + (1 / 2) * Real.exp (-2 * (45 / 64)) +
          (1 / 8) * Real.exp (-8 * (45 / 64)) <
        (3 / 8 : ℝ) + (1 / 2) * (247 / 1000) + (1 / 8) * (4 / 1000) := by
    norm_num at h2 h8 ⊢
    nlinarith
  have hweighted :
      ((4 - (32 / 9 : ℝ) * x) / 2) *
            ((1 / 2 : ℝ) + (1 / 2) * Real.exp (-2 * (45 / 64))) +
          (((32 / 9 : ℝ) * x - 2) / 2) *
            ((3 / 8 : ℝ) + (1 / 2) * Real.exp (-2 * (45 / 64)) +
              (1 / 8) * Real.exp (-8 * (45 / 64))) <
        ((4 - (32 / 9 : ℝ) * x) / 2) *
            ((1 / 2 : ℝ) + (1 / 2) * (247 / 1000)) +
          (((32 / 9 : ℝ) * x - 2) / 2) *
            ((3 / 8 : ℝ) + (1 / 2) * (247 / 1000) +
              (1 / 8) * (4 / 1000)) := by
    have hsum :
        (4 - (32 / 9 : ℝ) * x) / 2 +
          ((32 / 9 : ℝ) * x - 2) / 2 = 1 := by ring
    by_cases hw4pos : 0 < ((32 / 9 : ℝ) * x - 2) / 2
    · exact add_lt_add_of_le_of_lt
        (mul_le_mul_of_nonneg_left hm2.le hw2)
        (mul_lt_mul_of_pos_left hm4 hw4pos)
    · have hw4zero : ((32 / 9 : ℝ) * x - 2) / 2 = 0 := by
        exact le_antisymm (le_of_not_gt hw4pos) hw4
      have hw2pos : 0 < (4 - (32 / 9 : ℝ) * x) / 2 := by linarith
      exact add_lt_add_of_lt_of_le
        (mul_lt_mul_of_pos_left hm2 hw2pos)
        (mul_le_mul_of_nonneg_left hm4.le hw4)
  exact hweighted.trans hxC

private theorem moving_all_lt {x : ℝ}
    (hx0 : 1 ≤ x) (hx1 : x ≤ 11 / 10) :
    sparseScalarF ((5 / 2) * x) ((32 / 9) * x) < (527 / 1000 : ℝ) := by
  apply moving_lt hx0 hx1
  norm_num at hx0 hx1 ⊢
  nlinarith

private theorem moving_third_lt {x : ℝ}
    (hx0 : (26 / 25 : ℝ) ≤ x) (hx1 : x ≤ 11 / 10) :
    sparseScalarF ((5 / 2) * x) ((32 / 9) * x) < (518 / 1000 : ℝ) := by
  apply moving_lt (by nlinarith) hx1
  norm_num at hx0 hx1 ⊢
  nlinarith

private theorem four_lt {s : ℝ} (hs : (5 / 2 : ℝ) ≤ s) :
    sparseScalarF s 4 < (520 / 1000 : ℝ) := by
  rw [sparseScalarF_four_exact (le_trans (by norm_num) hs)]
  have h1mono : Real.exp (-s / 2) ≤ Real.exp (-(5 / 4 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h4mono : Real.exp (-2 * s) ≤ Real.exp (-(5 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h1 := exp_neg_lt (x := (5 / 4 : ℚ))
    (u := (287 / 1000 : ℚ)) (by norm_num) (by decide +kernel)
  have h4 := exp_neg_lt (x := (5 : ℚ))
    (u := (7 / 1000 : ℚ)) (by norm_num) (by decide +kernel)
  nlinarith

private theorem six_lt {s : ℝ} (hs : (5 / 2 : ℝ) ≤ s) :
    sparseScalarF s 6 < (524 / 1000 : ℝ) := by
  rw [sparseScalarF_six_exact (le_trans (by norm_num) hs)]
  have h1mono : Real.exp (-s / 3) ≤ Real.exp (-(5 / 6 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h4mono : Real.exp (-4 * s / 3) ≤ Real.exp (-(10 / 3 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h9mono : Real.exp (-3 * s) ≤ Real.exp (-(15 / 2 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h1 := exp_neg_lt (x := (5 / 6 : ℚ))
    (u := (435 / 1000 : ℚ)) (by norm_num) (by decide +kernel)
  have h4 := exp_neg_lt (x := (10 / 3 : ℚ))
    (u := (36 / 1000 : ℚ)) (by norm_num) (by decide +kernel)
  have h9 := exp_neg_lt (x := (15 / 2 : ℚ))
    (u := (1 / 1000 : ℚ)) (by norm_num) (by decide +kernel)
  nlinarith

private theorem eight_lt {s : ℝ} (hs : (5 / 2 : ℝ) ≤ s) :
    sparseScalarF s 8 < (526 / 1000 : ℝ) := by
  rw [sparseScalarF_eight_exact (le_trans (by norm_num) hs)]
  have h1mono : Real.exp (-s / 4) ≤ Real.exp (-(5 / 8 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h4mono : Real.exp (-s) ≤ Real.exp (-(5 / 2 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h9mono : Real.exp (-9 * s / 4) ≤ Real.exp (-(45 / 8 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h16mono : Real.exp (-4 * s) ≤ Real.exp (-(10 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h1 := exp_neg_lt (x := (5 / 8 : ℚ))
    (u := (5355 / 10000 : ℚ)) (by norm_num) (by decide +kernel)
  have h4 := exp_neg_lt (x := (5 / 2 : ℚ))
    (u := (822 / 10000 : ℚ)) (by norm_num) (by decide +kernel)
  have h9 := exp_neg_lt (x := (45 / 8 : ℚ))
    (u := (37 / 10000 : ℚ)) (by norm_num) (by decide +kernel)
  have h16 := exp_neg_lt (x := (10 : ℚ))
    (u := (1 / 20000 : ℚ)) (by norm_num) (by decide +kernel)
  nlinarith

private theorem four_third_lt {s : ℝ} (hs : (13 / 5 : ℝ) ≤ s) :
    sparseScalarF s 4 < (512 / 1000 : ℝ) := by
  rw [sparseScalarF_four_exact (le_trans (by norm_num) hs)]
  have h1mono : Real.exp (-s / 2) ≤ Real.exp (-(13 / 10 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h4mono : Real.exp (-2 * s) ≤ Real.exp (-(26 / 5 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h1 := exp_neg_lt (x := (13 / 10 : ℚ))
    (u := (2726 / 10000 : ℚ)) (by norm_num) (by decide +kernel)
  have h4 := exp_neg_lt (x := (26 / 5 : ℚ))
    (u := (56 / 10000 : ℚ)) (by norm_num) (by decide +kernel)
  nlinarith

private theorem six_third_lt {s : ℝ} (hs : (13 / 5 : ℝ) ≤ s) :
    sparseScalarF s 6 < (516 / 1000 : ℝ) := by
  rw [sparseScalarF_six_exact (le_trans (by norm_num) hs)]
  have h1mono : Real.exp (-s / 3) ≤ Real.exp (-(13 / 15 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h4mono : Real.exp (-4 * s / 3) ≤ Real.exp (-(52 / 15 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h9mono : Real.exp (-3 * s) ≤ Real.exp (-(39 / 5 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h1 := exp_neg_lt (x := (13 / 15 : ℚ))
    (u := (421 / 1000 : ℚ)) (by norm_num) (by decide +kernel)
  have h4 := exp_neg_lt (x := (52 / 15 : ℚ))
    (u := (313 / 10000 : ℚ)) (by norm_num) (by decide +kernel)
  have h9 := exp_neg_lt (x := (39 / 5 : ℚ))
    (u := (5 / 10000 : ℚ)) (by norm_num) (by decide +kernel)
  nlinarith

private theorem eight_third_lt {s : ℝ} (hs : (13 / 5 : ℝ) ≤ s) :
    sparseScalarF s 8 < (519 / 1000 : ℝ) := by
  rw [sparseScalarF_eight_exact (le_trans (by norm_num) hs)]
  have h1mono : Real.exp (-s / 4) ≤ Real.exp (-(13 / 20 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h4mono : Real.exp (-s) ≤ Real.exp (-(13 / 5 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h9mono : Real.exp (-9 * s / 4) ≤ Real.exp (-(117 / 20 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h16mono : Real.exp (-4 * s) ≤ Real.exp (-(52 / 5 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h1 := exp_neg_lt (x := (13 / 20 : ℚ))
    (u := (523 / 1000 : ℚ)) (by norm_num) (by decide +kernel)
  have h4 := exp_neg_lt (x := (13 / 5 : ℚ))
    (u := (75 / 1000 : ℚ)) (by norm_num) (by decide +kernel)
  have h9 := exp_neg_lt (x := (117 / 20 : ℚ))
    (u := (3 / 1000 : ℚ)) (by norm_num) (by decide +kernel)
  have h16 := exp_neg_lt (x := (52 / 5 : ℚ))
    (u := (4 / 100000 : ℚ)) (by norm_num) (by decide +kernel)
  nlinarith

private theorem lobe_lt_of_bounds
    {s r c y L C : ℝ} (hs : 0 < s) (_hr : 0 < r)
    (hc : c < r * s * Real.pi ^ 2 / (2 * (1 + s)))
    (hy : Real.exp (-c) < y) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hL : 0 < L) (hsqrt : L < Real.sqrt (1 + s))
    (harith : (1 / L) * (1 + 2 * y / (1 - y ^ 3)) < C) :
    1 / Real.sqrt (1 + s) *
        (1 + 2 * Real.exp (-(r * s * Real.pi ^ 2 / (2 * (1 + s)))) /
          (1 - Real.exp (-(r * s * Real.pi ^ 2 / (2 * (1 + s)))) ^ 3)) < C := by
  let z := Real.exp (-(r * s * Real.pi ^ 2 / (2 * (1 + s))))
  have hz : z < y := (Real.exp_lt_exp.mpr (by linarith)).trans hy
  have hz0 : 0 ≤ z := (Real.exp_pos _).le
  have hz3 : z ^ 3 < y ^ 3 := pow_lt_pow_left₀ hz hz0 (by norm_num)
  have hdenz : 0 < 1 - z ^ 3 := by
    have : z < 1 := hz.trans hy1
    nlinarith [pow_lt_one₀ hz0 this (by norm_num : 3 ≠ 0)]
  have hdeny : 0 < 1 - y ^ 3 := by
    nlinarith [pow_lt_one₀ hy0 hy1 (by norm_num : 3 ≠ 0)]
  have htail : 2 * z / (1 - z ^ 3) < 2 * y / (1 - y ^ 3) := by
    rw [div_lt_div_iff₀ hdenz hdeny]
    nlinarith
  have hsqrtPos : 0 < Real.sqrt (1 + s) := by positivity
  have hinv : 1 / Real.sqrt (1 + s) < 1 / L :=
    one_div_lt_one_div_of_lt hL hsqrt
  have hfactor : 0 < 1 + 2 * z / (1 - z ^ 3) := by positivity
  dsimp [z] at htail hfactor ⊢
  exact (mul_lt_mul_of_pos_right hinv hfactor).trans
    ((mul_lt_mul_of_pos_left (by linarith) (by positivity)).trans harith)

private theorem lobe_first_lt :
    1 / Real.sqrt (1 + (5 / 2 : ℝ)) *
        (1 + 2 * Real.exp
            (-((320 / 101 : ℝ) * (5 / 2) * Real.pi ^ 2 /
              (2 * (1 + (5 / 2))))) /
          (1 - (Real.exp
            (-((320 / 101 : ℝ) * (5 / 2) * Real.pi ^ 2 /
              (2 * (1 + (5 / 2)))))) ^ 3)) <
      (107 / 200 : ℝ) := by
  apply lobe_lt_of_bounds (s := (5 / 2 : ℝ))
    (r := (320 / 101 : ℝ)) (c := (111 / 10 : ℝ))
    (y := (1 / 65000 : ℝ)) (L := (187 / 100 : ℝ))
  · norm_num
  · norm_num
  · calc
      (111 / 10 : ℝ) < (800 / 707) * (986 / 100) := by norm_num
      _ < (800 / 707) * Real.pi ^ 2 :=
        mul_lt_mul_of_pos_left pi_sq_gt_986_over_100 (by norm_num)
      _ = _ := by ring
  · convert exp_neg_lt (x := (111 / 10 : ℚ)) (u := (1 / 65000 : ℚ))
      (by norm_num) (by decide +kernel) using 1 <;> norm_num
  · norm_num
  · norm_num
  · norm_num
  · have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 + 5 / 2)
    have hn := Real.sqrt_nonneg (1 + (5 / 2 : ℝ))
    nlinarith
  · norm_num

private theorem lobe_second_lt :
    1 / Real.sqrt (1 + (101 / 40 : ℝ)) *
        (1 + 2 * Real.exp
            (-((40 / 13 : ℝ) * (101 / 40) * Real.pi ^ 2 /
              (2 * (1 + (101 / 40))))) /
          (1 - (Real.exp
            (-((40 / 13 : ℝ) * (101 / 40) * Real.pi ^ 2 /
              (2 * (1 + (101 / 40)))))) ^ 3)) <
      (533 / 1000 : ℝ) := by
  apply lobe_lt_of_bounds (s := (101 / 40 : ℝ))
    (r := (40 / 13 : ℝ)) (c := (54 / 5 : ℝ))
    (y := (1 / 48000 : ℝ)) (L := (1877 / 1000 : ℝ))
  · norm_num
  · norm_num
  · calc
      (54 / 5 : ℝ) < (2020 / 1833) * (986 / 100) := by norm_num
      _ < (2020 / 1833) * Real.pi ^ 2 :=
        mul_lt_mul_of_pos_left pi_sq_gt_986_over_100 (by norm_num)
      _ = _ := by ring
  · convert exp_neg_lt (x := (54 / 5 : ℚ)) (u := (1 / 48000 : ℚ))
      (by norm_num) (by decide +kernel) using 1 <;> norm_num
  · norm_num
  · norm_num
  · norm_num
  · have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 + 101 / 40)
    have hn := Real.sqrt_nonneg (1 + (101 / 40 : ℝ))
    nlinarith
  · norm_num

private theorem lobe_third_lt :
    1 / Real.sqrt (1 + (13 / 5 : ℝ)) *
        (1 + 2 * Real.exp
            (-((32 / 11 : ℝ) * (13 / 5) * Real.pi ^ 2 /
              (2 * (1 + (13 / 5))))) /
          (1 - (Real.exp
            (-((32 / 11 : ℝ) * (13 / 5) * Real.pi ^ 2 /
              (2 * (1 + (13 / 5)))))) ^ 3)) <
      (66 / 125 : ℝ) := by
  apply lobe_lt_of_bounds (s := (13 / 5 : ℝ))
    (r := (32 / 11 : ℝ)) (c := (103 / 10 : ℝ))
    (y := (1 / 29000 : ℝ)) (L := (1897 / 1000 : ℝ))
  · norm_num
  · norm_num
  · calc
      (103 / 10 : ℝ) < (104 / 99) * (986 / 100) := by norm_num
      _ < (104 / 99) * Real.pi ^ 2 :=
        mul_lt_mul_of_pos_left pi_sq_gt_986_over_100 (by norm_num)
      _ = _ := by ring
  · convert exp_neg_lt (x := (103 / 10 : ℚ)) (u := (1 / 29000 : ℚ))
      (by norm_num) (by decide +kernel) using 1 <;> norm_num
  · norm_num
  · norm_num
  · norm_num
  · have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 + 13 / 5)
    have hn := Real.sqrt_nonneg (1 + (13 / 5 : ℝ))
    nlinarith
  · norm_num

private theorem to_eight_lt {x p : ℝ}
    (hx0 : 1 ≤ x) (hx1 : x ≤ 11 / 10)
    (hp0 : (32 / 9) * x ≤ p) (hp1 : p ≤ 8) :
    sparseScalarF ((5 / 2) * x) p < (107 / 200 : ℝ) := by
  let s : ℝ := (5 / 2) * x
  let a : ℝ := (32 / 9) * x
  have hs : 0 < s := by dsimp [s]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have ha0 : (32 / 9 : ℝ) ≤ a := by dsimp [a]; nlinarith
  have ha4 : a < 4 := by dsimp [a]; nlinarith
  have hp_pos : 0 < p := lt_of_lt_of_le ha hp0
  have hs_base : (5 / 2 : ℝ) ≤ s := by dsimp [s]; nlinarith
  have hFa : sparseScalarF s a ≤ (527 / 1000 : ℝ) :=
    (moving_all_lt hx0 hx1).le
  by_cases hp4 : p ≤ 4
  · let theta : ℝ := (p - a) / (4 - a)
    have htheta0 : 0 ≤ theta := by dsimp [theta]; positivity
    have htheta1 : theta ≤ 1 := by
      dsimp [theta]
      rw [div_le_one (sub_pos.mpr ha4)]
      linarith
    have hp : p = (1 - theta) * a + theta * 4 := by
      dsimp [theta]
      field_simp [ne_of_gt (sub_pos.mpr ha4)]
      ring
    have hH0 : 0 ≤ p * ((1 - theta) / a + theta / 4) := by positivity
    have hHD := variable_harmonic_le ha0 ha4.le htheta0 htheta1 hp
    exact interpolation_segment_lt (M := (527 / 1000 : ℝ))
      (D := (289 / 288 : ℝ)) (C := (107 / 200 : ℝ))
      hs ha (by norm_num) ha4 hp_pos htheta0 htheta1 hp
      hFa (four_lt hs_base).le (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hH0 hHD (by norm_num) (by norm_num) (by norm_num)
  · have hp4' : 4 ≤ p := le_of_not_ge hp4
    by_cases hp6 : p ≤ 6
    · let theta : ℝ := (p - 4) / 2
      have htheta0 : 0 ≤ theta := by dsimp [theta]; linarith
      have htheta1 : theta ≤ 1 := by dsimp [theta]; linarith
      have hp : p = (1 - theta) * 4 + theta * 6 := by dsimp [theta]; ring
      have hH0 : 0 ≤ p * ((1 - theta) / 4 + theta / 6) := by positivity
      have hHD := four_six_harmonic_le htheta0 htheta1 hp
      exact interpolation_segment_lt (M := (524 / 1000 : ℝ))
        (D := (25 / 24 : ℝ)) (C := (107 / 200 : ℝ))
        hs (by norm_num) (by norm_num) (by norm_num)
        hp_pos htheta0 htheta1 hp (four_lt hs_base).le (six_lt hs_base).le
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        hH0 hHD (by norm_num) (by norm_num) (by norm_num)
    · have hp6' : 6 ≤ p := le_of_not_ge hp6
      let theta : ℝ := (p - 6) / 2
      have htheta0 : 0 ≤ theta := by dsimp [theta]; linarith
      have htheta1 : theta ≤ 1 := by dsimp [theta]; linarith
      have hp : p = (1 - theta) * 6 + theta * 8 := by dsimp [theta]; ring
      have hH0 : 0 ≤ p * ((1 - theta) / 6 + theta / 8) := by positivity
      have hHD := six_eight_harmonic_le htheta0 htheta1 hp
      exact interpolation_segment_lt (M := (526 / 1000 : ℝ))
        (D := (49 / 48 : ℝ)) (C := (107 / 200 : ℝ))
        hs (by norm_num) (by norm_num) (by norm_num)
        hp_pos htheta0 htheta1 hp (six_lt hs_base).le (eight_lt hs_base).le
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        hH0 hHD (by norm_num) (by norm_num) (by norm_num)

private theorem third_to_eight_lt {x p : ℝ}
    (hx0 : (26 / 25 : ℝ) ≤ x) (hx1 : x ≤ 11 / 10)
    (hp0 : (32 / 9) * x ≤ p) (hp1 : p ≤ 8) :
    sparseScalarF ((5 / 2) * x) p < (267 / 500 : ℝ) := by
  let s : ℝ := (5 / 2) * x
  let a : ℝ := (32 / 9) * x
  have hs : 0 < s := by dsimp [s]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have ha0 : (32 / 9 : ℝ) ≤ a := by dsimp [a]; nlinarith
  have ha4 : a < 4 := by dsimp [a]; nlinarith
  have hp_pos : 0 < p := lt_of_lt_of_le ha hp0
  have hs_base : (13 / 5 : ℝ) ≤ s := by dsimp [s]; nlinarith
  have hFa : sparseScalarF s a ≤ (518 / 1000 : ℝ) :=
    (moving_third_lt hx0 hx1).le
  by_cases hp4 : p ≤ 4
  · let theta : ℝ := (p - a) / (4 - a)
    have htheta0 : 0 ≤ theta := by dsimp [theta]; positivity
    have htheta1 : theta ≤ 1 := by
      dsimp [theta]
      rw [div_le_one (sub_pos.mpr ha4)]
      linarith
    have hp : p = (1 - theta) * a + theta * 4 := by
      dsimp [theta]
      field_simp [ne_of_gt (sub_pos.mpr ha4)]
      ring
    have hH0 : 0 ≤ p * ((1 - theta) / a + theta / 4) := by positivity
    have hHD := variable_harmonic_le ha0 ha4.le htheta0 htheta1 hp
    exact interpolation_segment_lt (M := (518 / 1000 : ℝ))
      (D := (289 / 288 : ℝ)) (C := (267 / 500 : ℝ))
      hs ha (by norm_num) ha4 hp_pos htheta0 htheta1 hp
      hFa (four_third_lt hs_base).le (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hH0 hHD (by norm_num) (by norm_num) (by norm_num)
  · have hp4' : 4 ≤ p := le_of_not_ge hp4
    by_cases hp6 : p ≤ 6
    · let theta : ℝ := (p - 4) / 2
      have htheta0 : 0 ≤ theta := by dsimp [theta]; linarith
      have htheta1 : theta ≤ 1 := by dsimp [theta]; linarith
      have hp : p = (1 - theta) * 4 + theta * 6 := by dsimp [theta]; ring
      have hH0 : 0 ≤ p * ((1 - theta) / 4 + theta / 6) := by positivity
      have hHD := four_six_harmonic_le htheta0 htheta1 hp
      exact interpolation_segment_lt (M := (516 / 1000 : ℝ))
        (D := (25 / 24 : ℝ)) (C := (267 / 500 : ℝ))
        hs (by norm_num) (by norm_num) (by norm_num)
        hp_pos htheta0 htheta1 hp
        (four_third_lt hs_base).le (six_third_lt hs_base).le
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        hH0 hHD (by norm_num) (by norm_num) (by norm_num)
    · have hp6' : 6 ≤ p := le_of_not_ge hp6
      let theta : ℝ := (p - 6) / 2
      have htheta0 : 0 ≤ theta := by dsimp [theta]; linarith
      have htheta1 : theta ≤ 1 := by dsimp [theta]; linarith
      have hp : p = (1 - theta) * 6 + theta * 8 := by dsimp [theta]; ring
      have hH0 : 0 ≤ p * ((1 - theta) / 6 + theta / 8) := by positivity
      have hHD := six_eight_harmonic_le htheta0 htheta1 hp
      exact interpolation_segment_lt (M := (519 / 1000 : ℝ))
        (D := (49 / 48 : ℝ)) (C := (267 / 500 : ℝ))
        hs (by norm_num) (by norm_num) (by norm_num)
        hp_pos htheta0 htheta1 hp
        (six_third_lt hs_base).le (eight_third_lt hs_base).le
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        hH0 hHD (by norm_num) (by norm_num) (by norm_num)

/-- First low-mass scalar band for the floor-73 diffuse profile. -/
theorem first_lt {x p : ℝ}
    (hx0 : 1 ≤ x) (hx1 : x ≤ 101 / 100) (hp0 : (32 / 9) * x ≤ p) :
    sparseScalarF ((5 / 2) * x) p < (107 / 200 : ℝ) := by
  by_cases hp8 : p ≤ 8
  · exact to_eight_lt hx0 (hx1.trans (by norm_num)) hp0 hp8
  · have hs : (5 / 2 : ℝ) ≤ (5 / 2) * x := by nlinarith
    have hratio : (320 / 101 : ℝ) * ((5 / 2) * x) ≤ p := by
      calc
        _ ≤ 8 := by nlinarith
        _ ≤ p := le_of_not_ge hp8
    exact (sparseScalarF_lobe_periodization_of_tilt_ratio
      (sLower := (5 / 2 : ℝ)) (r := (320 / 101 : ℝ))
      (by norm_num) hs (by norm_num) hratio).trans_lt lobe_first_lt

/-- Second low-mass scalar band for the floor-73 diffuse profile. -/
theorem second_lt {x p : ℝ}
    (hx0 : (101 / 100 : ℝ) ≤ x) (hx1 : x ≤ 26 / 25)
    (hp0 : (32 / 9) * x ≤ p) :
    sparseScalarF ((5 / 2) * x) p < (107 / 200 : ℝ) := by
  by_cases hp8 : p ≤ 8
  · exact to_eight_lt (by nlinarith) (hx1.trans (by norm_num)) hp0 hp8
  · have hs : (101 / 40 : ℝ) ≤ (5 / 2) * x := by nlinarith
    have hratio : (40 / 13 : ℝ) * ((5 / 2) * x) ≤ p := by
      calc
        _ ≤ 8 := by nlinarith
        _ ≤ p := le_of_not_ge hp8
    exact (sparseScalarF_lobe_periodization_of_tilt_ratio
      (sLower := (101 / 40 : ℝ)) (r := (40 / 13 : ℝ))
      (by norm_num) hs (by norm_num) hratio).trans_lt
        (lobe_second_lt.trans_le (by norm_num))

/-- Third low-mass scalar band for the floor-73 diffuse profile. -/
theorem third_lt {x p : ℝ}
    (hx0 : (26 / 25 : ℝ) ≤ x) (hx1 : x ≤ 11 / 10)
    (hp0 : (32 / 9) * x ≤ p) :
    sparseScalarF ((5 / 2) * x) p < (267 / 500 : ℝ) := by
  by_cases hp8 : p ≤ 8
  · exact third_to_eight_lt hx0 hx1 hp0 hp8
  · have hs : (13 / 5 : ℝ) ≤ (5 / 2) * x := by nlinarith
    have hratio : (32 / 11 : ℝ) * ((5 / 2) * x) ≤ p := by
      calc
        _ ≤ 8 := by nlinarith
        _ ≤ p := le_of_not_ge hp8
    exact (sparseScalarF_lobe_periodization_of_tilt_ratio
      (sLower := (13 / 5 : ℝ)) (r := (32 / 11 : ℝ))
      (by norm_num) hs (by norm_num) hratio).trans_lt
        (lobe_third_lt.trans_le (by norm_num))

end ThresholdDiffuseFloor73Scalar
end CertifiedJL
