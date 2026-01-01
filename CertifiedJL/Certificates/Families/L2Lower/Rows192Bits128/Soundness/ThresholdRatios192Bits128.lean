/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Interval.Reflection
import Mathlib.Tactic.NormNum

/-! # Final scalar ratios for 192 rows, floor 12, and 128 bits -/

namespace CertifiedJL.ThresholdRatios192Bits128

def precision : ℕ := 256
def squarings : ℕ := 32

private theorem exp_mul_rat_lt_one {x factor : ℚ}
    (hx : 0 ≤ x) (hsmall : x < 2 ^ squarings)
    (hbase : 0 < Dyadic.roundDown precision (1 - x / 2 ^ squarings))
    (hcheck : Interval.upperLTCheck
      (Exp.posUpper precision x squarings *
        Interval.ofRat precision factor) 1 = true) :
    Real.exp (x : ℝ) * (factor : ℝ) < 1 := by
  have hexp :
      (Exp.posUpper precision x squarings).Contains (Real.exp (x : ℝ)) := by
    simpa using Exp.posUpper_contains
      (p := precision) (k := squarings) (x := x) hx hsmall hbase
  have hrat := Interval.contains_ofRat precision factor
  simpa using Interval.lt_of_contains_of_upperLTCheck
    (Interval.contains_mul hexp hrat) hcheck

private def nearEnclosure : Interval precision :=
  Exp.posUpper precision (138 / 5) squarings *
    Interval.ofRat precision ((681 / 1250 : ℚ) ^ 192 * 2 ^ 128)

private theorem nearCheck : Interval.upperLTCheck nearEnclosure 1 = true := by
  set_option maxRecDepth 1000000 in
    decide +kernel

theorem nearFinalRatio :
    Real.exp ((23 / 10 : ℝ) * 12) * (681 / 1250 : ℝ) ^ 192 <
      (2 : ℝ)⁻¹ ^ 128 := by
  have hlt := exp_mul_rat_lt_one
    (x := (138 / 5 : ℚ))
    (factor := (681 / 1250 : ℚ) ^ 192 * 2 ^ 128)
    (by norm_num) (by norm_num [squarings]) (by
      rw [Dyadic.roundDown, Int.floor_pos]
      norm_num [precision, squarings, Dyadic.scale]) (by
      simpa [nearEnclosure] using nearCheck)
  rw [show (23 / 10 : ℝ) * 12 = 138 / 5 by norm_num,
    inv_pow, inv_eq_one_div]
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 128)).2
  simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat,
    Nat.cast_ofNat, Nat.cast_pow, mul_assoc] using hlt

private def diffuseEnclosure : Interval precision :=
  Exp.posUpper precision (198 / 5) squarings *
    Interval.ofRat precision ((97 / 200 : ℚ) ^ 192 * 2 ^ 128)

private theorem diffuseCheck :
    Interval.upperLTCheck diffuseEnclosure 1 = true := by
  set_option maxRecDepth 1000000 in
    decide +kernel

theorem diffuseFinalRatio :
    Real.exp ((33 / 10 : ℝ) * 12) * (97 / 200 : ℝ) ^ 192 <
      (2 : ℝ)⁻¹ ^ 128 := by
  have hlt := exp_mul_rat_lt_one
    (x := (198 / 5 : ℚ))
    (factor := (97 / 200 : ℚ) ^ 192 * 2 ^ 128)
    (by norm_num) (by norm_num [squarings]) (by
      rw [Dyadic.roundDown, Int.floor_pos]
      norm_num [precision, squarings, Dyadic.scale]) (by
      simpa [diffuseEnclosure] using diffuseCheck)
  rw [show (33 / 10 : ℝ) * 12 = 198 / 5 by norm_num,
    inv_pow, inv_eq_one_div]
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 128)).2
  simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat,
    Nat.cast_ofNat, Nat.cast_pow, mul_assoc] using hlt

private def retainedEnclosure : Interval precision :=
  Exp.posUpper precision (69000 / 2401) squarings *
    Interval.ofRat precision
      ((53 / 100 : ℚ) ^ 192 * 2 ^ 128 * 20 / 19)

private theorem retainedCheck :
    Interval.upperLTCheck retainedEnclosure 1 = true := by
  set_option maxRecDepth 1000000 in
    decide +kernel

theorem retainedFinalRatio :
    Real.exp ((23 / 10 : ℝ) * 12 * (2500 / 2401)) *
        (53 / 100 : ℝ) ^ 192 <
      ((19 / (20 * 2 ^ 128) : ℚ) : ℝ) := by
  have hlt := exp_mul_rat_lt_one
    (x := (69000 / 2401 : ℚ))
    (factor := (53 / 100 : ℚ) ^ 192 * 2 ^ 128 * 20 / 19)
    (by norm_num) (by norm_num [squarings]) (by
      rw [Dyadic.roundDown, Int.floor_pos]
      norm_num [precision, squarings, Dyadic.scale]) (by
      simpa [retainedEnclosure] using retainedCheck)
  rw [show (23 / 10 : ℝ) * 12 * (2500 / 2401) =
      69000 / 2401 by norm_num]
  have hscaled : Real.exp (69000 / 2401 : ℝ) *
      (53 / 100 : ℝ) ^ 192 * (2 : ℝ) ^ 128 * 20 / 19 < 1 := by
    simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_inv,
      Rat.cast_ofNat, Nat.cast_ofNat, Nat.cast_pow, div_eq_mul_inv,
      mul_assoc] using hlt
  have htarget : ((19 / (20 * 2 ^ 128) : ℚ) : ℝ) =
      19 / (20 * (2 : ℝ) ^ 128) := by norm_num
  rw [htarget]
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 20 * 2 ^ 128)).2
  have hhigh : Real.exp (69000 / 2401 : ℝ) *
      (53 / 100 : ℝ) ^ 192 * (2 : ℝ) ^ 128 * 20 < 19 :=
    (div_lt_one (by norm_num : (0 : ℝ) < 19)).mp hscaled
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hhigh

end CertifiedJL.ThresholdRatios192Bits128
