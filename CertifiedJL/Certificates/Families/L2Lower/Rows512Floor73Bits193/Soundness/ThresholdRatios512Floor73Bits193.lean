/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Interval.Reflection
import Mathlib.Tactic.NormNum

/-! # Final scalar ratios for the 512-row, floor-73, 193-bit endpoint -/

namespace CertifiedJL.ThresholdRatios512Floor73Bits193

def precision : ℕ := 256
def squarings : ℕ := 32

private theorem exp_pos_contains {x : ℚ} (hx : 0 ≤ x)
    (hupper : x < 2 ^ squarings)
    (hbase : 0 < Dyadic.roundDown precision (1 - x / 2 ^ squarings)) :
    (Exp.posUpper precision x squarings).Contains (Real.exp (x : ℝ)) := by
  simpa using Exp.posUpper_contains
    (p := precision) (k := squarings) (x := x) hx hupper hbase

private def nearEnclosure : Interval precision :=
  Exp.posUpper precision (1679 / 10) squarings *
    Interval.ofRat precision (((681 / 1250 : ℚ) ^ 256) ^ 2 * 2 ^ 193)

private theorem nearCheck : Interval.upperLTCheck nearEnclosure 1 = true := by
  set_option maxRecDepth 1000000 in
    decide +kernel

theorem nearFinalRatio :
    Real.exp ((23 / 10 : ℝ) * 73) * (681 / 1250 : ℝ) ^ 512 <
      (2 : ℝ)⁻¹ ^ 193 := by
  have hexp := exp_pos_contains (x := (1679 / 10 : ℚ)) (by norm_num)
    (by norm_num [squarings]) (by
      rw [Dyadic.roundDown, Int.floor_pos]
      norm_num [precision, squarings, Dyadic.scale])
  have hrat := Interval.contains_ofRat precision
    (((681 / 1250 : ℚ) ^ 256) ^ 2 * 2 ^ 193)
  have hlt : Real.exp (1679 / 10 : ℝ) *
      (((((681 / 1250 : ℚ) ^ 256) ^ 2 * 2 ^ 193) : ℚ) : ℝ) < 1 := by
    simpa [nearEnclosure] using Interval.lt_of_contains_of_upperLTCheck
      (Interval.contains_mul hexp hrat) nearCheck
  rw [show (23 / 10 : ℝ) * 73 = 1679 / 10 by norm_num, inv_pow,
    inv_eq_one_div]
  rw [show (681 / 1250 : ℝ) ^ 512 = ((681 / 1250 : ℝ) ^ 256) ^ 2 by
    rw [← pow_mul]]
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 193)).2
  simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat,
    Nat.cast_ofNat, Nat.cast_pow, mul_assoc] using hlt

private def diffuseEnclosure : Interval precision :=
  Exp.posUpper precision (365 / 2) squarings *
    Interval.ofRat precision ((539 / 1000 : ℚ) ^ 256 * 2 ^ 96) *
    Interval.ofRat precision ((539 / 1000 : ℚ) ^ 256 * 2 ^ 97)

private theorem diffuseCheck : Interval.upperLTCheck diffuseEnclosure 1 = true := by
  set_option maxRecDepth 1000000 in
    decide +kernel

theorem diffuseFinalRatio :
    Real.exp ((5 / 2 : ℝ) * 73) * (539 / 1000 : ℝ) ^ 512 <
      (2 : ℝ)⁻¹ ^ 193 := by
  have hexp := exp_pos_contains (x := (365 / 2 : ℚ)) (by norm_num)
    (by norm_num [squarings]) (by
      rw [Dyadic.roundDown, Int.floor_pos]
      norm_num [precision, squarings, Dyadic.scale])
  have hleft := Interval.contains_ofRat precision
    ((539 / 1000 : ℚ) ^ 256 * 2 ^ 96)
  have hright := Interval.contains_ofRat precision
    ((539 / 1000 : ℚ) ^ 256 * 2 ^ 97)
  have hlt : Real.exp (365 / 2 : ℝ) *
      ((((539 / 1000 : ℚ) ^ 256 * 2 ^ 96) : ℚ) : ℝ) *
      ((((539 / 1000 : ℚ) ^ 256 * 2 ^ 97) : ℚ) : ℝ) < 1 := by
    simpa [diffuseEnclosure] using Interval.lt_of_contains_of_upperLTCheck
      (Interval.contains_mul (Interval.contains_mul hexp hleft) hright)
      diffuseCheck
  rw [show (5 / 2 : ℝ) * 73 = 365 / 2 by norm_num, inv_pow, inv_eq_one_div]
  rw [show (539 / 1000 : ℝ) ^ 512 = ((539 / 1000 : ℝ) ^ 256) ^ 2 by
    rw [← pow_mul]]
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 193)).2
  rw [show (2 : ℝ) ^ 193 = 2 ^ 96 * 2 ^ 97 by rw [← pow_add]]
  calc
    _ = Real.exp (365 / 2 : ℝ) *
        ((539 / 1000 : ℝ) ^ 256 * 2 ^ 96) *
        ((539 / 1000 : ℝ) ^ 256 * 2 ^ 97) := by ring
    _ = Real.exp (365 / 2 : ℝ) *
        ((((539 / 1000 : ℚ) ^ 256 * 2 ^ 96) : ℚ) : ℝ) *
        ((((539 / 1000 : ℚ) ^ 256 * 2 ^ 97) : ℚ) : ℝ) := by norm_num
    _ < 1 := hlt

private def retainedEnclosure : Interval precision :=
  Exp.posUpper precision (419750 / 2401) squarings *
    Interval.ofRat precision
      (((53 / 100 : ℚ) ^ 256) ^ 2 * 2 ^ 193 * 100000 / 99999)

private theorem retainedCheck : Interval.upperLTCheck retainedEnclosure 1 = true := by
  set_option maxRecDepth 1000000 in
    decide +kernel

theorem retainedFinalRatio :
    Real.exp ((23 / 10 : ℝ) * 73 * (2500 / 2401)) *
        (53 / 100 : ℝ) ^ 512 <
      ((99999 / (100000 * 2 ^ 193) : ℚ) : ℝ) := by
  have hexp := exp_pos_contains (x := (419750 / 2401 : ℚ)) (by norm_num)
    (by norm_num [squarings]) (by
      rw [Dyadic.roundDown, Int.floor_pos]
      norm_num [precision, squarings, Dyadic.scale])
  have hrat := Interval.contains_ofRat precision
    (((53 / 100 : ℚ) ^ 256) ^ 2 * 2 ^ 193 * 100000 / 99999)
  have hlt : Real.exp (419750 / 2401 : ℝ) *
      (((((53 / 100 : ℚ) ^ 256) ^ 2 * 2 ^ 193 * 100000 / 99999) : ℚ) : ℝ) <
      1 := by
    simpa [retainedEnclosure] using Interval.lt_of_contains_of_upperLTCheck
      (Interval.contains_mul hexp hrat) retainedCheck
  rw [show (23 / 10 : ℝ) * 73 * (2500 / 2401) = 419750 / 2401 by norm_num]
  rw [show (53 / 100 : ℝ) ^ 512 = ((53 / 100 : ℝ) ^ 256) ^ 2 by
    rw [← pow_mul]]
  have hscaled : Real.exp (419750 / 2401 : ℝ) * ((53 / 100 : ℝ) ^ 256) ^ 2 *
      (2 : ℝ) ^ 193 * 100000 / 99999 < 1 := by
    set_option maxRecDepth 100000 in
      simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_inv,
        Rat.cast_ofNat, Nat.cast_ofNat, Nat.cast_pow, div_eq_mul_inv,
        mul_assoc] using hlt
  have htarget : ((99999 / (100000 * 2 ^ 193) : ℚ) : ℝ) =
      99999 / (100000 * (2 : ℝ) ^ 193) := by norm_num
  rw [htarget]
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 100000 * 2 ^ 193)).2
  have hhigh : Real.exp (419750 / 2401 : ℝ) * ((53 / 100 : ℝ) ^ 256) ^ 2 *
      (2 : ℝ) ^ 193 * 100000 < 99999 :=
    (div_lt_one (by norm_num : (0 : ℝ) < 99999)).mp hscaled
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hhigh

end CertifiedJL.ThresholdRatios512Floor73Bits193
