/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Interval.Reflection
import CertifiedJL.Analysis.Fourier.ElementaryCosineSmallBall
import CertifiedJL.Projection.LInf.Lower.BalancedTernary.TwentyOneFiftiethTail
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Seven-frequency cosine majorants for the sparse `21/50` endpoint

The two exact trigonometric polynomials in this module control the central and
diffuse one-row regimes.  Bernstein-basis decompositions prove nonnegativity
and event domination over rational intervals.  Exponential estimates use only
kernel-checked interval reflection.
-/

open scoped BigOperators ENNReal

namespace CertifiedJL.SparseLInfLower21Over50

open Probability

private theorem exp_neg_lt {x u : ℚ} (hx : 0 ≤ x)
    (hcheck : Interval.upperLTCheck (Exp.negUpper 48 x 32) u = true) :
    Real.exp (-(x : ℝ)) < (u : ℝ) := by
  exact Interval.lt_of_contains_of_upperLTCheck
    (Exp.negUpper_contains (p := 48) (k := 32) (x := x) hx) hcheck

theorem exp_neg_lambda_sq_div_two_lt :
    Real.exp (-(12321 / 20000 : ℝ)) < 5401 / 10000 := by
  simpa using exp_neg_lt (x := 12321 / 20000) (u := 5401 / 10000)
    (by norm_num) (by decide +kernel)

theorem exp_neg_two_lambda_sq_lt :
    Real.exp (-(12321 / 5000 : ℝ)) < 851 / 10000 := by
  simpa using exp_neg_lt (x := 12321 / 5000) (u := 851 / 10000)
    (by norm_num) (by decide +kernel)

theorem exp_neg_diffuse42_lt :
    Real.exp (-(Real.pi ^ 2 * (400 / 867 : ℝ) ^ 2)) < 1224 / 10000 := by
  have harg : (21007 / 10000 : ℝ) < Real.pi ^ 2 * (400 / 867 : ℝ) ^ 2 := by
    nlinarith [Real.pi_gt_d6, Real.pi_pos]
  have hr := exp_neg_lt (x := 21007 / 10000) (u := 1224 / 10000)
    (by norm_num) (by decide +kernel)
  have hr' : Real.exp (-(21007 / 10000 : ℝ)) < (1224 / 10000 : ℝ) := by
    convert hr using 1 <;> norm_num
  exact (Real.exp_lt_exp.mpr (by linarith)).trans hr'

theorem cos_central42_lower :
    (7904 / 10000 : ℝ) < Real.cos (2331 * Real.sqrt 2 / 5000) := by
  let x : ℝ := 2331 * Real.sqrt 2 / 5000
  have hx0 : 0 ≤ x := by positivity
  have hxpi : x ≤ Real.pi / 2 := by
    have hslt : Real.sqrt 2 < 3 / 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    dsimp [x]
    nlinarith [Real.pi_gt_three]
  have ht := Probability.elementary_cos_taylor_six_le hx0 hxpi
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hx2 : x ^ 2 = (5433561 / 12500000 : ℝ) := by
    dsimp [x]
    rw [div_pow, mul_pow, hs2]
    norm_num
  have hx4 : x ^ 4 = (5433561 / 12500000 : ℝ) ^ 2 := by
    rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, hx2]
  have hx6 : x ^ 6 = (5433561 / 12500000 : ℝ) ^ 3 := by
    rw [show x ^ 6 = (x ^ 2) ^ 3 by ring, hx2]
  rw [hx2, hx4, hx6] at ht
  norm_num at ht ⊢
  linarith

theorem cos_diffuse42_lower :
    (2484 / 10000 : ℝ) < Real.cos (21 * Real.pi / 50) := by
  let x : ℝ := 21 * Real.pi / 50
  have hx0 : 0 ≤ x := by positivity
  have hxpi : x ≤ Real.pi / 2 := by
    dsimp [x]
    nlinarith [Real.pi_pos]
  have ht := Probability.elementary_cos_taylor_six_le hx0 hxpi
  have hpiSq : Real.pi ^ 2 < (31416 / 10000 : ℝ) ^ 2 := by
    nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have hxSq : x ^ 2 < (21 / 50 : ℝ) ^ 2 * (31416 / 10000 : ℝ) ^ 2 := by
    dsimp [x]
    nlinarith
  have hmono : 1 - ((21 / 50 : ℝ) ^ 2 * (31416 / 10000 : ℝ) ^ 2) / 2 +
        (((21 / 50 : ℝ) ^ 2 * (31416 / 10000 : ℝ) ^ 2) ^ 2) / 24 -
        (((21 / 50 : ℝ) ^ 2 * (31416 / 10000 : ℝ) ^ 2) ^ 3) / 720 <
      1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 := by
    nlinarith [sq_nonneg (x ^ 2),
      sq_nonneg ((21 / 50 : ℝ) ^ 2 * (31416 / 10000 : ℝ) ^ 2)]
  norm_num at hmono ⊢
  linarith

noncomputable def centralRawTwentyOneFiftieth (y : ℝ) : ℝ :=
  575661 / 100000000 - (2496777 / 50000000) * y -
    (2566109 / 25000000) * y ^ 2 + (20669139 / 25000000) * y ^ 3 +
    (1015209 / 390625) * y ^ 4 + (5496927 / 3125000) * y ^ 5 -
    (676806 / 390625) * y ^ 6 - (3601829 / 1562500) * y ^ 7

noncomputable def centralMajorantTwentyOneFiftieth (x : ℝ) : ℝ :=
  38759027 / 100000000 + (40888388 / 100000000) * Real.cos x +
    (43597814 / 100000000) * Real.cos (2 * x) -
    (14218949 / 100000000) * Real.cos (5 * x) -
    (5414448 / 100000000) * Real.cos (6 * x) -
    (3601829 / 100000000) * Real.cos (7 * x)

noncomputable def diffuseRawTwentyOneFiftieth (y : ℝ) : ℝ :=
  7145003 / 10000000 + (158963127 / 100000000) * y -
    (12446319 / 10000000) * y ^ 2 - (78860691 / 25000000) * y ^ 3 +
    (19554303 / 6250000) * y ^ 4 + (29928381 / 6250000) * y ^ 5 -
    (6518101 / 3125000) * y ^ 6 - (4275483 / 1562500) * y ^ 7

noncomputable def diffuseMajorantTwentyOneFiftieth (x : ℝ) : ℝ :=
  61363243 / 100000000 + (72022959 / 100000000) * Real.cos x -
    (3568686 / 100000000) * Real.cos (2 * x) -
    (19003929 / 100000000) * Real.cos (3 * x) -
    (6518101 / 100000000) * Real.cos (6 * x) -
    (4275483 / 100000000) * Real.cos (7 * x)

lemma cos_four_mul (x : ℝ) :
    Real.cos (4 * x) = 8 * Real.cos x ^ 4 - 8 * Real.cos x ^ 2 + 1 := by
  rw [show 4 * x = 2 * (2 * x) by ring, Real.cos_two_mul,
    Real.cos_two_mul]
  ring

lemma cos_five_mul (x : ℝ) :
    Real.cos (5 * x) = 16 * Real.cos x ^ 5 - 20 * Real.cos x ^ 3 +
      5 * Real.cos x := by
  have h := Real.two_mul_cos_mul_cos x (4 * x)
  rw [show x - 4 * x = -(3 * x) by ring, Real.cos_neg,
    show x + 4 * x = 5 * x by ring, Real.cos_three_mul, cos_four_mul] at h
  nlinarith

lemma cos_six_mul (x : ℝ) :
    Real.cos (6 * x) = 32 * Real.cos x ^ 6 - 48 * Real.cos x ^ 4 +
      18 * Real.cos x ^ 2 - 1 := by
  have h := Real.two_mul_cos_mul_cos x (5 * x)
  rw [show x - 5 * x = -(4 * x) by ring, Real.cos_neg,
    show x + 5 * x = 6 * x by ring, cos_four_mul, cos_five_mul] at h
  nlinarith

lemma cos_seven_mul (x : ℝ) :
    Real.cos (7 * x) = 64 * Real.cos x ^ 7 - 112 * Real.cos x ^ 5 +
      56 * Real.cos x ^ 3 - 7 * Real.cos x := by
  have h := Real.two_mul_cos_mul_cos x (6 * x)
  rw [show x - 6 * x = -(5 * x) by ring, Real.cos_neg,
    show x + 6 * x = 7 * x by ring, cos_five_mul, cos_six_mul] at h
  nlinarith

lemma centralMajorantTwentyOneFiftieth_eq_raw (x : ℝ) :
    centralMajorantTwentyOneFiftieth x = centralRawTwentyOneFiftieth (Real.cos x) := by
  unfold centralMajorantTwentyOneFiftieth centralRawTwentyOneFiftieth
  rw [Real.cos_two_mul, cos_five_mul, cos_six_mul, cos_seven_mul]
  ring

lemma diffuseMajorantTwentyOneFiftieth_eq_raw (x : ℝ) :
    diffuseMajorantTwentyOneFiftieth x = diffuseRawTwentyOneFiftieth (Real.cos x) := by
  unfold diffuseMajorantTwentyOneFiftieth diffuseRawTwentyOneFiftieth
  rw [Real.cos_two_mul, Real.cos_three_mul, cos_six_mul, cos_seven_mul]
  ring

noncomputable def bernstein7 (c0 c1 c2 c3 c4 c5 c6 c7 t : ℝ) : ℝ :=
  c0 * (1 - t) ^ 7 + 7 * c1 * t * (1 - t) ^ 6 +
    21 * c2 * t ^ 2 * (1 - t) ^ 5 +
    35 * c3 * t ^ 3 * (1 - t) ^ 4 +
    35 * c4 * t ^ 4 * (1 - t) ^ 3 +
    21 * c5 * t ^ 5 * (1 - t) ^ 2 +
    7 * c6 * t ^ 6 * (1 - t) + c7 * t ^ 7

lemma nonneg_on_interval_of_bernstein7
    (F : ℝ → ℝ) (a b c0 c1 c2 c3 c4 c5 c6 c7 : ℝ)
    (hab : 0 < b - a) {y : ℝ} (hya : a ≤ y) (hyb : y ≤ b)
    (hid : ∀ t, F (a + (b - a) * t) =
      bernstein7 c0 c1 c2 c3 c4 c5 c6 c7 t)
    (hc : 0 ≤ c0 ∧ 0 ≤ c1 ∧ 0 ≤ c2 ∧ 0 ≤ c3 ∧
      0 ≤ c4 ∧ 0 ≤ c5 ∧ 0 ≤ c6 ∧ 0 ≤ c7) : 0 ≤ F y := by
  let t : ℝ := (y - a) / (b - a)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_one hab).2
    linarith
  have hrep : y = a + (b - a) * t := by
    dsimp [t]
    field_simp [hab.ne']
    ring
  rw [hrep, hid]
  rcases hc with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩
  unfold bernstein7
  have h1t : 0 ≤ 1 - t := by linarith
  positivity

set_option maxHeartbeats 4000000 in
theorem centralRawTwentyOneFiftieth_nonneg {y : ℝ} (hlo : -1 ≤ y) (hhi : y ≤ 1) :
    0 ≤ centralRawTwentyOneFiftieth y := by
  by_cases h1 : y ≤ -1 / 2
  · exact nonneg_on_interval_of_bernstein7 centralRawTwentyOneFiftieth (-1) (-1 / 2)
      (53874783 / 100000000) (70925219 / 350000000)
      (23675077 / 300000000) (44558859 / 1400000000)
      (42821249 / 3500000000) (546923 / 150000000)
      (147859 / 350000000) (11867 / 100000000)
      (by norm_num) hlo h1 (by intro t; unfold centralRawTwentyOneFiftieth bernstein7; ring)
      (by norm_num)
  · have h1' : -1 / 2 ≤ y := le_of_not_ge h1
    by_cases h2 : y ≤ -3 / 8
    · exact nonneg_on_interval_of_bernstein7 centralRawTwentyOneFiftieth (-1 / 2) (-3 / 8)
        (11867 / 100000000) (119627 / 2800000000)
        (5015557 / 33600000000) (3200917 / 8000000000)
        (275799317 / 358400000000) (759889271 / 614400000000)
        (10219756971 / 5734400000000) (7815997239 / 3276800000000)
        (by norm_num) h1' h2 (by intro t; unfold centralRawTwentyOneFiftieth bernstein7; ring)
        (by norm_num)
    · have h2' : -3 / 8 ≤ y := le_of_not_ge h2
      by_cases h3 : y ≤ -1 / 4
      · exact nonneg_on_interval_of_bernstein7 centralRawTwentyOneFiftieth (-3 / 8) (-1 / 4)
          (7815997239 / 3276800000000) (34272466731 / 11468800000000)
          (12555151591 / 3440640000000) (12463943899 / 2867200000000)
          (36278751317 / 7168000000000) (12403461937 / 2150400000000)
          (2308890097 / 358400000000) (180710493 / 25600000000)
          (by norm_num) h2' h3 (by intro t; unfold centralRawTwentyOneFiftieth bernstein7; ring)
          (by norm_num)
      · have h3' : -1 / 4 ≤ y := le_of_not_ge h3
        by_cases h4 : y ≤ 0
        · exact nonneg_on_interval_of_bernstein7 centralRawTwentyOneFiftieth (-1 / 4) 0
            (180710493 / 25600000000) (92876891 / 11200000000)
            (624715421 / 67200000000) (138194227 / 14000000000)
            (549992081 / 56000000000) (75750739 / 8400000000)
            (10556031 / 1400000000) (575661 / 100000000)
            (by norm_num) h3' h4 (by intro t; unfold centralRawTwentyOneFiftieth bernstein7; ring)
            (by norm_num)
        · have h4' : 0 ≤ y := le_of_not_ge h4
          by_cases h5 : y ≤ 1 / 8
          · exact nonneg_on_interval_of_bernstein7 centralRawTwentyOneFiftieth 0 (1 / 8)
              (575661 / 100000000) (13621731 / 2800000000)
              (130933339 / 33600000000) (1298533099 / 448000000000)
              (216633377 / 112000000000) (334516633 / 307200000000)
              (8419583 / 17920000000) (675360891 / 3276800000000)
              (by norm_num) h4' h5 (by intro t; unfold centralRawTwentyOneFiftieth bernstein7; ring)
              (by norm_num)
          · have h5' : 1 / 8 ≤ y := le_of_not_ge h5
            by_cases h6 : y ≤ 3 / 16
            · exact nonneg_on_interval_of_bernstein7 centralRawTwentyOneFiftieth (1 / 8) (3 / 16)
                (675360891 / 3276800000000) (3405512471 / 45875200000000)
                (8587741871 / 275251200000000) (85455408427 / 917504000000000)
                (509321214433 / 1835008000000000) (37957333607 / 62914560000000)
                (1600975696437 / 1468006400000000) (738505402473 / 419430400000000)
                (by norm_num) h5' h6
                (by intro t; unfold centralRawTwentyOneFiftieth bernstein7; ring) (by norm_num)
            · have h6' : 3 / 16 ≤ y := le_of_not_ge h6
              by_cases h7 : y ≤ 1 / 4
              · exact nonneg_on_interval_of_bernstein7 centralRawTwentyOneFiftieth (3 / 16) (1 / 4)
                  (738505402473 / 419430400000000) (1784281060437 / 734003200000000)
                  (1807816487389 / 550502400000000) (995783225849 / 229376000000000)
                  (64517655887 / 11468800000000) (12318099779 / 1720320000000)
                  (6430131503 / 716800000000) (283695203 / 25600000000)
                  (by norm_num) h6' h7
                  (by intro t; unfold centralRawTwentyOneFiftieth bernstein7; ring) (by norm_num)
              · have h7' : 1 / 4 ≤ y := le_of_not_ge h7
                by_cases h8 : y ≤ 1 / 2
                · exact nonneg_on_interval_of_bernstein7 centralRawTwentyOneFiftieth (1 / 4) (1 / 2)
                    (283695203 / 25600000000) (1749600301 / 89600000000)
                    (881326769 / 26880000000) (168004973 / 3200000000)
                    (1127283891 / 14000000000) (997319689 / 8400000000)
                    (236129699 / 1400000000) (23079477 / 100000000)
                    (by norm_num) h7' h8
                    (by intro t; unfold centralRawTwentyOneFiftieth bernstein7; ring) (by norm_num)
                · have h8' : 1 / 2 ≤ y := le_of_not_ge h8
                  exact nonneg_on_interval_of_bernstein7 centralRawTwentyOneFiftieth (1 / 2) 1
                    (23079477 / 100000000) (124269659 / 350000000)
                    (55450313 / 105000000) (2637823953 / 3500000000)
                    (1018378711 / 1000000000) (2664108973 / 2100000000)
                    (14935499 / 10937500) (100010003 / 100000000)
                    (by norm_num) h8' hhi
                    (by intro t; unfold centralRawTwentyOneFiftieth bernstein7; ring) (by norm_num)

theorem centralRawTwentyOneFiftieth_domination {y : ℝ}
    (hlo : (494 / 625 : ℝ) ≤ y) (hhi : y ≤ 1) : 1 ≤ centralRawTwentyOneFiftieth y := by
  rw [← sub_nonneg]
  exact nonneg_on_interval_of_bernstein7 (fun z => centralRawTwentyOneFiftieth z - 1)
    (494 / 625) 1
    (2477895948957962871393041 / 3725290298461914062500000000)
    (3478210188256897342203057 / 41723251342773437500000000)
    (31250195408518561338853 / 200271606445312500000000)
    (112779658003807644529 / 534057617187500000000)
    (203959153849506963 / 854492187500000000)
    (36952022841071 / 164062500000000)
    (13412772971 / 87500000000) (10003 / 100000000)
    (by norm_num) hlo hhi
    (by intro t; unfold centralRawTwentyOneFiftieth bernstein7; ring) (by norm_num)

set_option maxHeartbeats 4000000 in
theorem diffuseRawTwentyOneFiftieth_nonneg {y : ℝ} (hlo : -1 ≤ y) (hhi : y ≤ 1) :
    0 ≤ diffuseRawTwentyOneFiftieth y := by
  by_cases h1 : y ≤ -7 / 8
  · exact nonneg_on_interval_of_bernstein7 diffuseRawTwentyOneFiftieth (-1) (-7 / 8)
      (2532909 / 100000000) (16451643 / 1120000000)
      (178710421 / 22400000000) (1782117361 / 448000000000)
      (397441949 / 224000000000) (1002659487 / 1433600000000)
      (1620824973 / 5734400000000) (686729289 / 3276800000000)
      (by norm_num) hlo h1 (by intro t; unfold diffuseRawTwentyOneFiftieth bernstein7; ring)
      (by norm_num)
  · have h1' : -7 / 8 ≤ y := le_of_not_ge h1
    by_cases h2 : y ≤ -3 / 4
    · exact nonneg_on_interval_of_bernstein7 diffuseRawTwentyOneFiftieth (-7 / 8) (-3 / 4)
        (686729289 / 3276800000000) (1565455077 / 11468800000000)
        (2334443079 / 5734400000000) (10134060409 / 14336000000000)
        (6290403467 / 7168000000000) (125561921 / 143360000000)
        (265393879 / 358400000000) (14486867 / 25600000000)
        (by norm_num) h1' h2 (by intro t; unfold diffuseRawTwentyOneFiftieth bernstein7; ring)
        (by norm_num)
    · have h2' : -3 / 4 ≤ y := le_of_not_ge h2
      by_cases h3 : y ≤ -5 / 8
      · exact nonneg_on_interval_of_bernstein7 diffuseRawTwentyOneFiftieth (-3 / 4) (-5 / 8)
          (14486867 / 25600000000) (140238397 / 358400000000)
          (127187677 / 716800000000) (134223953 / 7168000000000)
          (934378537 / 14336000000000) (2844732349 / 5734400000000)
          (17206774509 / 11468800000000) (2137801791 / 655360000000)
          (by norm_num) h2' h3 (by intro t; unfold diffuseRawTwentyOneFiftieth bernstein7; ring)
          (by norm_num)
      · have h3' : -5 / 8 ≤ y := le_of_not_ge h3
        by_cases h4 : y ≤ -1 / 2
        · exact nonneg_on_interval_of_bernstein7 diffuseRawTwentyOneFiftieth (-5 / 8) (-1 / 2)
            (2137801791 / 655360000000) (3601018011 / 716800000000)
            (337923797 / 44800000000) (19718787811 / 1792000000000)
            (698240647 / 44800000000) (17159367 / 800000000)
            (80434929 / 2800000000) (1875909 / 50000000)
            (by norm_num) h3' h4 (by intro t; unfold diffuseRawTwentyOneFiftieth bernstein7; ring)
            (by norm_num)
        · have h4' : -1 / 2 ≤ y := le_of_not_ge h4
          by_cases h5 : y ≤ 0
          · exact nonneg_on_interval_of_bernstein7 diffuseRawTwentyOneFiftieth (-1 / 2) 0
              (1875909 / 50000000) (50878701 / 700000000)
              (46224999 / 350000000) (77723749 / 350000000)
              (2384757911 / 7000000000) (661630301 / 1400000000)
              (841337293 / 1400000000) (7145003 / 10000000)
              (by norm_num) h4' h5 (by intro t; unfold diffuseRawTwentyOneFiftieth bernstein7; ring)
              (by norm_num)
          · have h5' : 0 ≤ y := le_of_not_ge h5
            exact nonneg_on_interval_of_bernstein7 diffuseRawTwentyOneFiftieth 0 1
              (7145003 / 10000000) (659113337 / 700000000)
              (388294367 / 350000000) (3947439241 / 3500000000)
              (1743239741 / 1750000000) (721689897 / 700000000)
              (125757747 / 70000000) (100020003 / 100000000)
              (by norm_num) h5' hhi
              (by intro t; unfold diffuseRawTwentyOneFiftieth bernstein7; ring) (by norm_num)

theorem diffuseRawTwentyOneFiftieth_domination {y : ℝ}
    (hlo : (621 / 2500 : ℝ) ≤ y) (hhi : y ≤ 1) : 1 ≤ diffuseRawTwentyOneFiftieth y := by
  rw [← sub_nonneg]
  exact nonneg_on_interval_of_bernstein7 (fun z => diffuseRawTwentyOneFiftieth z - 1)
    (621 / 2500) 1
    (10074873678891727130705347 / 953674316406250000000000000000)
    (375089080362978630961684277 / 5340576171875000000000000000)
    (384426525545741929615599 / 4272460937500000000000000)
    (50262738293135604757 / 610351562500000000000)
    (1671069815067416927 / 13671875000000000000)
    (98418701114707 / 312500000000000)
    (1047775019171 / 1750000000000) (20003 / 100000000)
    (by norm_num) hlo hhi
    (by intro t; unfold diffuseRawTwentyOneFiftieth bernstein7; ring) (by norm_num)

theorem centralMajorantTwentyOneFiftieth_nonneg (x : ℝ) : 0 ≤ centralMajorantTwentyOneFiftieth x := by
  rw [centralMajorantTwentyOneFiftieth_eq_raw]
  exact centralRawTwentyOneFiftieth_nonneg (Real.neg_one_le_cos x) (Real.cos_le_one x)

theorem diffuseMajorantTwentyOneFiftieth_nonneg (x : ℝ) : 0 ≤ diffuseMajorantTwentyOneFiftieth x := by
  rw [diffuseMajorantTwentyOneFiftieth_eq_raw]
  exact diffuseRawTwentyOneFiftieth_nonneg (Real.neg_one_le_cos x) (Real.cos_le_one x)

theorem centralMajorantTwentyOneFiftieth_domination {x : ℝ}
    (hx : |x| ≤ 2331 * Real.sqrt 2 / 5000) : 1 ≤ centralMajorantTwentyOneFiftieth x := by
  have hbpi : (2331 * Real.sqrt 2 / 5000 : ℝ) ≤ Real.pi := by
    have hslt : Real.sqrt 2 < 3 / 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    nlinarith [Real.pi_gt_three]
  have hcos : Real.cos (2331 * Real.sqrt 2 / 5000) ≤ Real.cos x := by
    rw [← Real.cos_abs x]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hbpi hx
  rw [centralMajorantTwentyOneFiftieth_eq_raw]
  apply centralRawTwentyOneFiftieth_domination _ (Real.cos_le_one x)
  have hc := cos_central42_lower
  norm_num at hc ⊢
  exact hc.le.trans hcos

theorem diffuseMajorantTwentyOneFiftieth_domination {x : ℝ}
    (hx : |x| ≤ 21 * Real.pi / 50) : 1 ≤ diffuseMajorantTwentyOneFiftieth x := by
  have hbpi : (21 * Real.pi / 50 : ℝ) ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hcos : Real.cos (21 * Real.pi / 50) ≤ Real.cos x := by
    rw [← Real.cos_abs x]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hbpi hx
  rw [diffuseMajorantTwentyOneFiftieth_eq_raw]
  apply diffuseRawTwentyOneFiftieth_domination _ (Real.cos_le_one x)
  have hc := cos_diffuse42_lower
  norm_num at hc ⊢
  exact hc.le.trans hcos

theorem centralExpectationTwentyOneFiftieth {φ1 φ2 φ5 φ6 φ7 : ℝ}
    (h1 : φ1 < 5401 / 10000) (h2 : φ2 < 851 / 10000)
    (h5 : 0 ≤ φ5) (h6 : 0 ≤ φ6) (h7 : 0 ≤ φ7) :
    38759027 / 100000000 + (40888388 / 100000000) * φ1 +
      (43597814 / 100000000) * φ2 - (14218949 / 100000000) * φ5 -
      (5414448 / 100000000) * φ6 - (3601829 / 100000000) * φ7 <
        323 / 500 := by
  norm_num at *
  linarith

theorem diffuseExpectationTwentyOneFiftieth {φ1 φ2 φ3 φ6 φ7 : ℝ}
    (h1 : φ1 < 1224 / 10000) (h2 : 0 ≤ φ2) (h3 : 0 ≤ φ3)
    (h6 : 0 ≤ φ6) (h7 : 0 ≤ φ7) :
    61363243 / 100000000 + (72022959 / 100000000) * φ1 -
      (3568686 / 100000000) * φ2 - (19003929 / 100000000) * φ3 -
      (6518101 / 100000000) * φ6 - (4275483 / 100000000) * φ7 <
        703 / 1000 := by
  norm_num at *
  linarith

set_option exponentiation.threshold 1024 in
theorem final703 : (703 / 1000 : ℝ) ^ 256 < (2 : ℝ) ^ (-130 : ℤ) := by
  norm_num [zpow_neg]

set_option exponentiation.threshold 1024 in
/-- The uniform `703/1000` row cap cannot by itself certify 131 bits. -/
theorem final703_not_bits131 :
    ¬(703 / 1000 : ℝ) ^ 256 < (2 : ℝ) ^ (-131 : ℤ) := by
  norm_num [zpow_neg]

end CertifiedJL.SparseLInfLower21Over50
