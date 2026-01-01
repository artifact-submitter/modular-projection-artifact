/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Interval.Reflection
import CertifiedJL.Certificates.Families.L2Lower.Shared.Spec
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Diffuse.Floor73Scalar
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.NormNum

/-! # Reflected endpoints for the floor-73 diffuse profile -/

namespace CertifiedJL.CertificateProviders.SparseThresholdDiffuseFloor73

private theorem exp_neg_lt {x u : ℚ} (hx : 0 ≤ x)
    (hcheck : Interval.upperLTCheck (Exp.negUpper 48 x 32) u = true) :
    Real.exp (-(x : ℝ)) < (u : ℝ) := by
  have hcontains := Exp.negUpper_contains (p := 48) (k := 32) (x := x) hx
  exact Interval.lt_of_contains_of_upperLTCheck hcontains hcheck

private theorem tail_lt_of_exp_bound {c c₀ y C : ℝ}
    (hc : c₀ ≤ c) (hy : Real.exp (-c₀) < y)
    (hy0 : 0 ≤ y) (hy1 : y < 1)
    (harith : 2 * y / (1 - y ^ 3) < C) :
    2 * Real.exp (-c) / (1 - Real.exp (-c) ^ 3) < C := by
  let z := Real.exp (-c)
  have hz : z < y :=
    (Real.exp_le_exp.mpr (by linarith)).trans_lt hy
  have hz0 : 0 ≤ z := (Real.exp_pos _).le
  have hz1 : z < 1 := hz.trans hy1
  have hdenz : 0 < 1 - z ^ 3 := by
    nlinarith [pow_lt_one₀ hz0 hz1 (by norm_num : 3 ≠ 0)]
  have hdeny : 0 < 1 - y ^ 3 := by
    nlinarith [pow_lt_one₀ hy0 hy1 (by norm_num : 3 ≠ 0)]
  change 2 * z / (1 - z ^ 3) < C
  apply (show 2 * z / (1 - z ^ 3) < 2 * y / (1 - y ^ 3) by
    rw [div_lt_div_iff₀ hdenz hdeny]
    have hdiff :
        0 < 2 * y * (1 - z ^ 3) - 2 * z * (1 - y ^ 3) := by
      rw [show 2 * y * (1 - z ^ 3) - 2 * z * (1 - y ^ 3) =
        2 * (y - z) * (1 + y * z * (y + z)) by ring]
      positivity
    linarith).trans harith

private theorem lobe_lt_of_bounds
    {s r c y L C : ℝ} (hs : 0 < s)
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
  have hz1 : z < 1 := hz.trans hy1
  have hdenz : 0 < 1 - z ^ 3 := by
    nlinarith [pow_lt_one₀ hz0 hz1 (by norm_num : 3 ≠ 0)]
  have hdeny : 0 < 1 - y ^ 3 := by
    nlinarith [pow_lt_one₀ hy0 hy1 (by norm_num : 3 ≠ 0)]
  have htail : 2 * z / (1 - z ^ 3) < 2 * y / (1 - y ^ 3) := by
    rw [div_lt_div_iff₀ hdenz hdeny]
    have hdiff :
        0 < 2 * y * (1 - z ^ 3) - 2 * z * (1 - y ^ 3) := by
      rw [show 2 * y * (1 - z ^ 3) - 2 * z * (1 - y ^ 3) =
        2 * (y - z) * (1 + y * z * (y + z)) by ring]
      positivity
    linarith
  have hsqrtPos : 0 < Real.sqrt (1 + s) := by positivity
  have hinv : 1 / Real.sqrt (1 + s) < 1 / L :=
    one_div_lt_one_div_of_lt hL hsqrt
  have hfactor : 0 < 1 + 2 * z / (1 - z ^ 3) := by positivity
  dsimp [z] at htail hfactor ⊢
  exact (mul_lt_mul_of_pos_right hinv hfactor).trans
    ((mul_lt_mul_of_pos_left (by linarith) (by positivity)).trans harith)

private theorem lowTailFirst {c : ℝ} (hc : (300 / 47 : ℝ) ≤ c) :
    2 * Real.exp (-c) / (1 - Real.exp (-c) ^ 3) < (7 / 2000 : ℝ) := by
  apply tail_lt_of_exp_bound hc
  · convert exp_neg_lt (x := (300 / 47 : ℚ)) (u := (1 / 590 : ℚ))
      (by norm_num) (by decide +kernel) using 1 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

private theorem lowTailSecond {c : ℝ} (hc : (25 / 4 : ℝ) ≤ c) :
    2 * Real.exp (-c) / (1 - Real.exp (-c) ^ 3) < (1 / 250 : ℝ) := by
  apply tail_lt_of_exp_bound hc
  · convert exp_neg_lt (x := (25 / 4 : ℚ)) (u := (1 / 515 : ℚ))
      (by norm_num) (by decide +kernel) using 1 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

private theorem lowTailThird {c : ℝ} (hc : (6 : ℝ) ≤ c) :
    2 * Real.exp (-c) / (1 - Real.exp (-c) ^ 3) < (1 / 200 : ℝ) := by
  apply tail_lt_of_exp_bound hc
  · convert exp_neg_lt (x := (6 : ℚ)) (u := (1 / 403 : ℚ))
      (by norm_num) (by decide +kernel) using 1 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

private theorem highFirstLobe :
    1 / Real.sqrt (1 + (11 / 4 : ℝ)) *
        (1 + 2 * Real.exp
            (-((64 / 45 : ℝ) * (11 / 4) * Real.pi ^ 2 /
              (2 * (1 + (11 / 4))))) /
          (1 - (Real.exp
            (-((64 / 45 : ℝ) * (11 / 4) * Real.pi ^ 2 /
              (2 * (1 + (11 / 4)))))) ^ 3)) < (523 / 1000 : ℝ) := by
  apply lobe_lt_of_bounds (s := (11 / 4 : ℝ)) (r := (64 / 45 : ℝ))
    (c := (51 / 10 : ℝ)) (y := (61 / 10000 : ℝ))
    (L := (1936 / 1000 : ℝ))
  · norm_num
  · have hpi : (986 / 100 : ℝ) < Real.pi ^ 2 := by
      nlinarith [Real.pi_gt_d4, Real.pi_pos]
    calc
      (51 / 10 : ℝ) < (352 / 675) * (986 / 100) := by norm_num
      _ < (352 / 675) * Real.pi ^ 2 :=
        mul_lt_mul_of_pos_left hpi (by norm_num)
      _ = _ := by ring
  · convert exp_neg_lt (x := (51 / 10 : ℚ)) (u := (61 / 10000 : ℚ))
      (by norm_num) (by decide +kernel) using 1 <;> norm_num
  · norm_num
  · norm_num
  · norm_num
  · have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 + 11 / 4)
    have hn := Real.sqrt_nonneg (1 + (11 / 4 : ℝ))
    nlinarith
  · norm_num

private theorem highFirstTail {c : ℝ} (hc : (45 / 8 : ℝ) ≤ c) :
    2 * Real.exp (-c) / (1 - Real.exp (-c) ^ 3) < (3 / 400 : ℝ) := by
  apply tail_lt_of_exp_bound hc
  · convert exp_neg_lt (x := (45 / 8 : ℚ)) (u := (1 / 275 : ℚ))
      (by norm_num) (by decide +kernel) using 1 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

private theorem highSecondLobe :
    1 / Real.sqrt (1 + (3 : ℝ)) *
        (1 + 2 * Real.exp
            (-((64 / 45 : ℝ) * 3 * Real.pi ^ 2 / (2 * (1 + 3)))) /
          (1 - (Real.exp
            (-((64 / 45 : ℝ) * 3 * Real.pi ^ 2 / (2 * (1 + 3))))) ^ 3)) <
      (253 / 500 : ℝ) := by
  apply lobe_lt_of_bounds (s := (3 : ℝ)) (r := (64 / 45 : ℝ))
    (c := (26 / 5 : ℝ)) (y := (56 / 10000 : ℝ))
    (L := (1999 / 1000 : ℝ))
  · norm_num
  · have hpi : (986 / 100 : ℝ) < Real.pi ^ 2 := by
      nlinarith [Real.pi_gt_d4, Real.pi_pos]
    calc
      (26 / 5 : ℝ) < (8 / 15) * (986 / 100) := by norm_num
      _ < (8 / 15) * Real.pi ^ 2 :=
        mul_lt_mul_of_pos_left hpi (by norm_num)
      _ = _ := by ring
  · convert exp_neg_lt (x := (26 / 5 : ℚ)) (u := (56 / 10000 : ℚ))
      (by norm_num) (by decide +kernel) using 1 <;> norm_num
  · norm_num
  · norm_num
  · norm_num
  · have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4)
    have hn := Real.sqrt_nonneg (4 : ℝ)
    nlinarith
  · norm_num

private theorem highSecondTail {c : ℝ} (hc : (720 / 157 : ℝ) ≤ c) :
    2 * Real.exp (-c) / (1 - Real.exp (-c) ^ 3) < (21 / 1000 : ℝ) := by
  apply tail_lt_of_exp_bound hc
  · convert exp_neg_lt (x := (720 / 157 : ℚ)) (u := (1 / 98 : ℚ))
      (by norm_num) (by decide +kernel) using 1 <;> norm_num
  · norm_num
  · norm_num
  · norm_num

theorem verified :
    CertificateContracts.SparseL2ThresholdDiffuseFloor73Endpoints where
  lowScalarFirst := ThresholdDiffuseFloor73Scalar.first_lt
  lowScalarSecond := ThresholdDiffuseFloor73Scalar.second_lt
  lowScalarThird := ThresholdDiffuseFloor73Scalar.third_lt
  lowTailFirst := lowTailFirst
  lowTailSecond := lowTailSecond
  lowTailThird := lowTailThird
  highFirstLobe := highFirstLobe
  highFirstTail := highFirstTail
  highSecondLobe := highSecondLobe
  highSecondTail := highSecondTail

end CertifiedJL.CertificateProviders.SparseThresholdDiffuseFloor73
