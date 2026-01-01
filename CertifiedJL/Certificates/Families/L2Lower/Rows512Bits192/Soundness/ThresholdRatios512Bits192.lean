/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Interval.Reflection
import Mathlib.Tactic.NormNum

/-! # Final scalar ratios for the 512-row, floor-71, 192-bit endpoint -/

namespace CertifiedJL.ThresholdRatios512Bits192

def precision : ℕ := 256
def squarings : ℕ := 32

private def nearEnclosure : Interval precision :=
  Exp.posUpper precision (1633 / 10) squarings *
    Interval.ofRat precision (((681 / 1250 : ℚ) ^ 256) ^ 2 * 2 ^ 192)

private theorem nearCheck : Interval.upperLTCheck nearEnclosure 1 = true := by
  set_option maxRecDepth 1000000 in
    decide +kernel

theorem nearFinalRatio :
    Real.exp ((23 / 10 : ℝ) * 71) * (681 / 1250 : ℝ) ^ 512 <
      (2 : ℝ)⁻¹ ^ 192 := by
  have hexp :
      (Exp.posUpper precision (1633 / 10) squarings).Contains
        (Real.exp (1633 / 10 : ℝ)) := by
    simpa using Exp.posUpper_contains
      (p := precision) (k := squarings) (x := (1633 / 10 : ℚ))
      (by norm_num) (by norm_num [squarings]) (by
        change 0 < Dyadic.roundDown precision
          (1 - (1633 / 10) / 2 ^ squarings)
        rw [Dyadic.roundDown, Int.floor_pos]
        norm_num [precision, squarings, Dyadic.scale])
  have hrat := Interval.contains_ofRat precision
    (((681 / 1250 : ℚ) ^ 256) ^ 2 * 2 ^ 192)
  have hlt :
      Real.exp (1633 / 10 : ℝ) *
          ((((681 / 1250 : ℚ) ^ 256) ^ 2 * 2 ^ 192 : ℚ) : ℝ) < 1 := by
    simpa [nearEnclosure] using Interval.lt_of_contains_of_upperLTCheck
      (Interval.contains_mul hexp hrat) nearCheck
  rw [show (23 / 10 : ℝ) * 71 = 1633 / 10 by norm_num,
    inv_pow, inv_eq_one_div]
  rw [show (681 / 1250 : ℝ) ^ 512 =
      ((681 / 1250 : ℝ) ^ 256) ^ 2 by
    rw [← pow_mul]]
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 192)).2
  simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div,
    Rat.cast_ofNat, Nat.cast_ofNat, Nat.cast_pow, mul_assoc] using hlt

private def diffuseChunk : Interval precision :=
  Interval.ofRat precision ((97 / 200 : ℚ) ^ 256 * 2 ^ 96)

private def diffuseEnclosure : Interval precision :=
  Exp.posUpper precision (2343 / 10) squarings * diffuseChunk * diffuseChunk

private theorem diffuseCheck :
    Interval.upperLTCheck diffuseEnclosure 1 = true := by
  set_option maxRecDepth 1000000 in
    decide +kernel

theorem diffuseFinalRatio :
    Real.exp ((33 / 10 : ℝ) * 71) * (97 / 200 : ℝ) ^ 512 <
      (2 : ℝ)⁻¹ ^ 192 := by
  have hexp :
      (Exp.posUpper precision (2343 / 10) squarings).Contains
        (Real.exp (2343 / 10 : ℝ)) := by
    simpa using Exp.posUpper_contains
      (p := precision) (k := squarings) (x := (2343 / 10 : ℚ))
      (by norm_num) (by norm_num [squarings]) (by
        change 0 < Dyadic.roundDown precision
          (1 - (2343 / 10) / 2 ^ squarings)
        rw [Dyadic.roundDown, Int.floor_pos]
        norm_num [precision, squarings, Dyadic.scale])
  have hchunk := Interval.contains_ofRat precision
    ((97 / 200 : ℚ) ^ 256 * 2 ^ 96)
  have hlt :
      Real.exp (2343 / 10 : ℝ) *
          (((97 / 200 : ℚ) ^ 256 * 2 ^ 96 : ℚ) : ℝ) *
          (((97 / 200 : ℚ) ^ 256 * 2 ^ 96 : ℚ) : ℝ) < 1 := by
    simpa [diffuseEnclosure] using Interval.lt_of_contains_of_upperLTCheck
      (Interval.contains_mul (Interval.contains_mul hexp hchunk) hchunk)
      diffuseCheck
  rw [show (33 / 10 : ℝ) * 71 = 2343 / 10 by norm_num,
    inv_pow, inv_eq_one_div]
  rw [show (97 / 200 : ℝ) ^ 512 =
      ((97 / 200 : ℝ) ^ 256) ^ 2 by
    rw [← pow_mul]]
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 192)).2
  rw [show (2 : ℝ) ^ 192 = 2 ^ 96 * 2 ^ 96 by rw [← pow_add]]
  calc
    Real.exp (2343 / 10 : ℝ) * ((97 / 200 : ℝ) ^ 256) ^ 2 *
        (2 ^ 96 * 2 ^ 96) =
      Real.exp (2343 / 10 : ℝ) *
        ((97 / 200 : ℝ) ^ 256 * 2 ^ 96) *
        ((97 / 200 : ℝ) ^ 256 * 2 ^ 96) := by ring
    _ = Real.exp (2343 / 10 : ℝ) *
          (((97 / 200 : ℚ) ^ 256 * 2 ^ 96 : ℚ) : ℝ) *
          (((97 / 200 : ℚ) ^ 256 * 2 ^ 96 : ℚ) : ℝ) := by
      norm_num only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div,
        Rat.cast_ofNat, Nat.cast_ofNat, Nat.cast_pow]
    _ < 1 := hlt

private def retainedEnclosure : Interval precision :=
  Exp.posUpper precision (408250 / 2401) squarings *
    Interval.ofRat precision
      (((53 / 100 : ℚ) ^ 256) ^ 2 * 2 ^ 192 * 100 / 99)

private theorem retainedCheck :
    Interval.upperLTCheck retainedEnclosure 1 = true := by
  set_option maxRecDepth 1000000 in
    decide +kernel

theorem retainedFinalRatio :
    Real.exp ((23 / 10 : ℝ) * 71 * (2500 / 2401)) *
        (53 / 100 : ℝ) ^ 512 <
      ((99 / (100 * 2 ^ 192) : ℚ) : ℝ) := by
  have hexp :
      (Exp.posUpper precision (408250 / 2401) squarings).Contains
        (Real.exp (408250 / 2401 : ℝ)) := by
    simpa using Exp.posUpper_contains
      (p := precision) (k := squarings) (x := (408250 / 2401 : ℚ))
      (by norm_num) (by norm_num [squarings]) (by
        change 0 < Dyadic.roundDown precision
          (1 - (408250 / 2401) / 2 ^ squarings)
        rw [Dyadic.roundDown, Int.floor_pos]
        norm_num [precision, squarings, Dyadic.scale])
  have hrat := Interval.contains_ofRat precision
    (((53 / 100 : ℚ) ^ 256) ^ 2 * 2 ^ 192 * 100 / 99)
  have hlt :
      Real.exp (408250 / 2401 : ℝ) *
          (((((53 / 100 : ℚ) ^ 256) ^ 2 * 2 ^ 192 * 100 / 99) : ℚ) : ℝ) < 1 := by
    simpa [retainedEnclosure] using Interval.lt_of_contains_of_upperLTCheck
      (Interval.contains_mul hexp hrat) retainedCheck
  rw [show (23 / 10 : ℝ) * 71 * (2500 / 2401) =
      408250 / 2401 by norm_num]
  rw [show (53 / 100 : ℝ) ^ 512 =
      ((53 / 100 : ℝ) ^ 256) ^ 2 by
    rw [← pow_mul]]
  have hscaled :
      Real.exp (408250 / 2401 : ℝ) * ((53 / 100 : ℝ) ^ 256) ^ 2 *
          (2 : ℝ) ^ 192 * 100 / 99 < 1 := by
    have hbase : (53 / 100 : ℝ) = ((53 / 100 : ℚ) : ℝ) := by norm_num
    have h2 : (2 : ℝ) = ((2 : ℚ) : ℝ) := by norm_num
    have h100 : (100 : ℝ) = ((100 : ℚ) : ℝ) := by norm_num
    have h99 : (99 : ℝ) = ((99 : ℚ) : ℝ) := by norm_num
    rw [hbase, h2, h100, h99]
    set_option maxRecDepth 100000 in
      simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_inv,
        div_eq_mul_inv, mul_assoc] using hlt
  have htarget :
      ((99 / (100 * 2 ^ 192) : ℚ) : ℝ) =
        99 / (100 * (2 : ℝ) ^ 192) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_pow]
  rw [htarget]
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 100 * 2 ^ 192)).2
  have hhigh :
      Real.exp (408250 / 2401 : ℝ) * ((53 / 100 : ℝ) ^ 256) ^ 2 *
          (2 : ℝ) ^ 192 * 100 < 99 :=
    (div_lt_one (by norm_num : (0 : ℝ) < 99)).mp hscaled
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hhigh

end CertifiedJL.ThresholdRatios512Bits192
