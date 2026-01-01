/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Interval.Reflection
import CertifiedJL.Certificates.Families.L2Lower.Shared.Spec
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.NormNum

/-! # Reflected endpoint replay for the high-mass diffuse profile -/

namespace CertifiedJL.CertificateProviders.SparseThresholdDiffuseHighNumeric128

private theorem thresholdDiffuse_exp_neg_lt {x u : ℚ} (hx : 0 ≤ x)
    (hcheck : Interval.upperLTCheck
      (Exp.negUpper 48 x 32) u = true) :
    Real.exp (-(x : ℝ)) < (u : ℝ) := by
  have hcontains := Exp.negUpper_contains (p := 48) (k := 32) (x := x) hx
  exact Interval.lt_of_contains_of_upperLTCheck hcontains hcheck

private theorem thresholdDiffuse_pi_sq_gt :
    (986 / 100 : ℝ) < Real.pi ^ 2 := by
  nlinarith [Real.pi_gt_d4, Real.pi_pos]

private theorem firstLobe :
    1 / Real.sqrt (1 + (363 / 100 : ℝ)) *
        (1 + 2 * Real.exp
            (-((320 / 297 : ℝ) * (363 / 100) * Real.pi ^ 2 /
              (2 * (1 + (363 / 100))))) /
          (1 - (Real.exp
            (-((320 / 297 : ℝ) * (363 / 100) * Real.pi ^ 2 /
              (2 * (1 + (363 / 100)))))) ^ 3)) <
      (2399 / 5000 : ℝ) := by
  let c : ℝ := (320 / 297 : ℝ) * (363 / 100) * Real.pi ^ 2 /
    (2 * (1 + (363 / 100)))
  let x : ℝ := Real.exp (-c)
  have hc0 : (86768 / 20835 : ℝ) < c := by
    calc
      (86768 / 20835 : ℝ) = (1760 / 4167) * (986 / 100) := by norm_num
      _ < (1760 / 4167) * Real.pi ^ 2 :=
        mul_lt_mul_of_pos_left thresholdDiffuse_pi_sq_gt (by norm_num)
      _ = c := by dsimp [c]; ring
  have hx : x < (1 / 64 : ℝ) := by
    have hmono : x < Real.exp (-(86768 / 20835 : ℝ)) := by
      dsimp [x]
      exact Real.exp_lt_exp.mpr (by linarith)
    have hcert : Real.exp (-(86768 / 20835 : ℝ)) < (1 / 64 : ℝ) := by
      convert thresholdDiffuse_exp_neg_lt
        (x := (86768 / 20835 : ℚ)) (u := (1 / 64 : ℚ))
        (by norm_num) (by decide +kernel) using 1 <;> norm_num
    exact hmono.trans hcert
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx3 : x ^ 3 < (1 / 64 : ℝ) ^ 3 := by
    exact pow_lt_pow_left₀ hx hx0 (by norm_num)
  have hden : 0 < 1 - x ^ 3 := by nlinarith
  have htail :
      2 * x / (1 - x ^ 3) <
        2 * (1 / 64 : ℝ) / (1 - (1 / 64 : ℝ) ^ 3) := by
    rw [div_lt_div_iff₀ hden (by norm_num)]
    nlinarith
  have hsqrt : (43 / 20 : ℝ) < Real.sqrt (1 + (363 / 100 : ℝ)) := by
    have hsqrt0 := Real.sqrt_nonneg (1 + (363 / 100 : ℝ))
    have hsqrtSq := Real.sq_sqrt
      (by norm_num : (0 : ℝ) ≤ 1 + (363 / 100 : ℝ))
    nlinarith
  have hinv : 1 / Real.sqrt (1 + (363 / 100 : ℝ)) < (20 / 43 : ℝ) := by
    have hsqrtPos : 0 < Real.sqrt (1 + (363 / 100 : ℝ)) := by positivity
    apply (div_lt_iff₀ hsqrtPos).2
    nlinarith
  have hfactor : 0 < 1 + 2 * x / (1 - x ^ 3) := by positivity
  calc
    1 / Real.sqrt (1 + (363 / 100 : ℝ)) *
        (1 + 2 * Real.exp (-((320 / 297 : ℝ) * (363 / 100) *
          Real.pi ^ 2 / (2 * (1 + (363 / 100))))) /
          (1 - (Real.exp (-((320 / 297 : ℝ) * (363 / 100) *
            Real.pi ^ 2 / (2 * (1 + (363 / 100)))))) ^ 3)) =
        1 / Real.sqrt (1 + (363 / 100 : ℝ)) *
          (1 + 2 * x / (1 - x ^ 3)) := by rfl
    _ < (20 / 43 : ℝ) * (1 + 2 * x / (1 - x ^ 3)) :=
      mul_lt_mul_of_pos_right hinv hfactor
    _ < (20 / 43 : ℝ) *
        (1 + 2 * (1 / 64 : ℝ) / (1 - (1 / 64 : ℝ) ^ 3)) := by
      exact mul_lt_mul_of_pos_left (by linarith) (by norm_num)
    _ < (2399 / 5000 : ℝ) := by norm_num

private theorem firstTail {c : ℝ}
    (hc : (1485 / 248 : ℝ) ≤ c) :
    2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) <
      (1 / 198 : ℝ) := by
  let x : ℝ := Real.exp (-c)
  have hx : x < (1 / 398 : ℝ) := by
    have hmono : x ≤ Real.exp (-(1485 / 248 : ℝ)) := by
      dsimp [x]
      exact Real.exp_le_exp.mpr (by linarith)
    have hcert : Real.exp (-(1485 / 248 : ℝ)) < (1 / 398 : ℝ) := by
      convert thresholdDiffuse_exp_neg_lt
        (x := (1485 / 248 : ℚ)) (u := (1 / 398 : ℚ))
        (by norm_num) (by decide +kernel) using 1 <;> norm_num
    exact hmono.trans_lt hcert
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x < 1 := by linarith
  have hx3 : x ^ 3 < 1 := pow_lt_one₀ hx0 hx1 (by norm_num)
  have hden : 0 < 1 - x ^ 3 := by linarith
  change 2 * x / (1 - x ^ 3) < (1 / 198 : ℝ)
  rw [div_lt_iff₀ hden]
  have hxCube : x ^ 3 < (1 / 398 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hx hx0 (by norm_num)
  nlinarith

private theorem secondLobe :
    1 / Real.sqrt (1 + (99 / 25 : ℝ)) *
        (1 + 2 * Real.exp
            (-((320 / 297 : ℝ) * (99 / 25) * Real.pi ^ 2 /
              (2 * (1 + (99 / 25))))) /
          (1 - (Real.exp
            (-((320 / 297 : ℝ) * (99 / 25) * Real.pi ^ 2 /
              (2 * (1 + (99 / 25)))))) ^ 3)) <
      (58 / 125 : ℝ) := by
  let c : ℝ := (320 / 297 : ℝ) * (99 / 25) * Real.pi ^ 2 /
    (2 * (1 + (99 / 25)))
  let x : ℝ := Real.exp (-c)
  have hc0 : (1972 / 465 : ℝ) < c := by
    calc
      (1972 / 465 : ℝ) = (40 / 93) * (986 / 100) := by norm_num
      _ < (40 / 93) * Real.pi ^ 2 :=
        mul_lt_mul_of_pos_left thresholdDiffuse_pi_sq_gt (by norm_num)
      _ = c := by dsimp [c]; ring
  have hx : x < (3 / 200 : ℝ) := by
    have hmono : x < Real.exp (-(1972 / 465 : ℝ)) := by
      dsimp [x]
      exact Real.exp_lt_exp.mpr (by linarith)
    have hcert : Real.exp (-(1972 / 465 : ℝ)) < (3 / 200 : ℝ) := by
      convert thresholdDiffuse_exp_neg_lt
        (x := (1972 / 465 : ℚ)) (u := (3 / 200 : ℚ))
        (by norm_num) (by decide +kernel) using 1 <;> norm_num
    exact hmono.trans hcert
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx3 : x ^ 3 < (3 / 200 : ℝ) ^ 3 := by
    exact pow_lt_pow_left₀ hx hx0 (by norm_num)
  have hden : 0 < 1 - x ^ 3 := by nlinarith
  have htail :
      2 * x / (1 - x ^ 3) <
        2 * (3 / 200 : ℝ) / (1 - (3 / 200 : ℝ) ^ 3) := by
    rw [div_lt_div_iff₀ hden (by norm_num)]
    nlinarith
  have hsqrt : (20 / 9 : ℝ) < Real.sqrt (1 + (99 / 25 : ℝ)) := by
    have hsqrt0 := Real.sqrt_nonneg (1 + (99 / 25 : ℝ))
    have hsqrtSq := Real.sq_sqrt
      (by norm_num : (0 : ℝ) ≤ 1 + (99 / 25 : ℝ))
    nlinarith
  have hinv : 1 / Real.sqrt (1 + (99 / 25 : ℝ)) < (9 / 20 : ℝ) := by
    have hsqrtPos : 0 < Real.sqrt (1 + (99 / 25 : ℝ)) := by positivity
    apply (div_lt_iff₀ hsqrtPos).2
    nlinarith
  have hfactor : 0 < 1 + 2 * x / (1 - x ^ 3) := by positivity
  calc
    1 / Real.sqrt (1 + (99 / 25 : ℝ)) *
        (1 + 2 * Real.exp (-((320 / 297 : ℝ) * (99 / 25) *
          Real.pi ^ 2 / (2 * (1 + (99 / 25))))) /
          (1 - (Real.exp (-((320 / 297 : ℝ) * (99 / 25) *
            Real.pi ^ 2 / (2 * (1 + (99 / 25)))))) ^ 3)) =
        1 / Real.sqrt (1 + (99 / 25 : ℝ)) *
          (1 + 2 * x / (1 - x ^ 3)) := by rfl
    _ < (9 / 20 : ℝ) * (1 + 2 * x / (1 - x ^ 3)) :=
      mul_lt_mul_of_pos_right hinv hfactor
    _ < (9 / 20 : ℝ) *
        (1 + 2 * (3 / 200 : ℝ) / (1 - (3 / 200 : ℝ) ^ 3)) := by
      exact mul_lt_mul_of_pos_left (by linarith) (by norm_num)
    _ < (58 / 125 : ℝ) := by norm_num

private theorem secondTail {c : ℝ}
    (hc : (4752 / 985 : ℝ) ≤ c) :
    2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) <
      (1 / 59 : ℝ) := by
  let x : ℝ := Real.exp (-c)
  have hx : x < (1 / 120 : ℝ) := by
    have hmono : x ≤ Real.exp (-(4752 / 985 : ℝ)) := by
      dsimp [x]
      exact Real.exp_le_exp.mpr (by linarith)
    have hcert : Real.exp (-(4752 / 985 : ℝ)) < (1 / 120 : ℝ) := by
      convert thresholdDiffuse_exp_neg_lt
        (x := (4752 / 985 : ℚ)) (u := (1 / 120 : ℚ))
        (by norm_num) (by decide +kernel) using 1 <;> norm_num
    exact hmono.trans_lt hcert
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x < 1 := by linarith
  have hx3 : x ^ 3 < 1 := pow_lt_one₀ hx0 hx1 (by norm_num)
  have hden : 0 < 1 - x ^ 3 := by linarith
  change 2 * x / (1 - x ^ 3) < (1 / 59 : ℝ)
  rw [div_lt_iff₀ hden]
  have hxCube : x ^ 3 < (1 / 120 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hx hx0 (by norm_num)
  nlinarith

theorem verified :
    CertificateContracts.SparseL2ThresholdDiffuseHighEndpoints128 where
  firstLobe := firstLobe
  firstTail := firstTail
  secondLobe := secondLobe
  secondTail := secondTail

end CertifiedJL.CertificateProviders.SparseThresholdDiffuseHighNumeric128
