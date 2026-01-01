/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Interval.Reflection
import Mathlib.Tactic.NormNum

/-! # Final scalar ratios for the 512-row, floor-57, 256-bit endpoint -/

namespace CertifiedJL.ThresholdRatios512Bits256

def precision : ℕ := 256
def squarings : ℕ := 32

private def nearEnclosure : Interval precision :=
  Exp.posUpper precision (1311 / 10) squarings *
    Interval.ofRat precision ((681 / 1250 : ℚ) ^ 512 * 2 ^ 256)

private theorem nearCheck : Interval.upperLTCheck nearEnclosure 1 = true := by
  set_option maxRecDepth 1000000 in
    decide +kernel

theorem nearFinalRatio :
    Real.exp ((23 / 10 : ℝ) * 57) * (681 / 1250 : ℝ) ^ 512 <
      (2 : ℝ)⁻¹ ^ 256 := by
  have hexp :
      (Exp.posUpper precision (1311 / 10) squarings).Contains
        (Real.exp (1311 / 10 : ℝ)) := by
    simpa using Exp.posUpper_contains
      (p := precision) (k := squarings) (x := (1311 / 10 : ℚ))
      (by norm_num) (by norm_num [squarings]) (by
        change 0 < Dyadic.roundDown precision
          (1 - (1311 / 10) / 2 ^ squarings)
        rw [Dyadic.roundDown, Int.floor_pos]
        norm_num [precision, squarings, Dyadic.scale])
  have hrat := Interval.contains_ofRat precision
    ((681 / 1250 : ℚ) ^ 512 * 2 ^ 256)
  have hlt :
      Real.exp (1311 / 10 : ℝ) *
          (((681 / 1250 : ℚ) ^ 512 * 2 ^ 256 : ℚ) : ℝ) < 1 := by
    simpa [nearEnclosure] using Interval.lt_of_contains_of_upperLTCheck
      (Interval.contains_mul hexp hrat) nearCheck
  rw [show (23 / 10 : ℝ) * 57 = 1311 / 10 by norm_num,
    inv_pow, inv_eq_one_div]
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 256)).2
  simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div,
    Rat.cast_ofNat, Nat.cast_ofNat, Nat.cast_pow, mul_assoc] using hlt

private def diffuseChunk : Interval precision :=
  Interval.ofRat precision ((97 / 200 : ℚ) ^ 256 * 2 ^ 128)

private def diffuseEnclosure : Interval precision :=
  Exp.posUpper precision (1881 / 10) squarings * diffuseChunk * diffuseChunk

private theorem diffuseCheck :
    Interval.upperLTCheck diffuseEnclosure 1 = true := by
  set_option maxRecDepth 1000000 in
    decide +kernel

theorem diffuseFinalRatio :
    Real.exp ((33 / 10 : ℝ) * 57) * (97 / 200 : ℝ) ^ 512 <
      (2 : ℝ)⁻¹ ^ 256 := by
  have hexp :
      (Exp.posUpper precision (1881 / 10) squarings).Contains
        (Real.exp (1881 / 10 : ℝ)) := by
    simpa using Exp.posUpper_contains
      (p := precision) (k := squarings) (x := (1881 / 10 : ℚ))
      (by norm_num) (by norm_num [squarings]) (by
        change 0 < Dyadic.roundDown precision
          (1 - (1881 / 10) / 2 ^ squarings)
        rw [Dyadic.roundDown, Int.floor_pos]
        norm_num [precision, squarings, Dyadic.scale])
  have hchunk := Interval.contains_ofRat precision
    ((97 / 200 : ℚ) ^ 256 * 2 ^ 128)
  have hlt :
      Real.exp (1881 / 10 : ℝ) *
          (((97 / 200 : ℚ) ^ 256 * 2 ^ 128 : ℚ) : ℝ) *
          (((97 / 200 : ℚ) ^ 256 * 2 ^ 128 : ℚ) : ℝ) < 1 := by
    simpa [diffuseEnclosure] using Interval.lt_of_contains_of_upperLTCheck
      (Interval.contains_mul (Interval.contains_mul hexp hchunk) hchunk)
      diffuseCheck
  rw [show (33 / 10 : ℝ) * 57 = 1881 / 10 by norm_num,
    inv_pow, inv_eq_one_div]
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 256)).2
  rw [show (97 / 200 : ℝ) ^ 512 =
      ((97 / 200 : ℝ) ^ 256) ^ 2 by rw [← pow_mul]]
  rw [show (2 : ℝ) ^ 256 = 2 ^ 128 * 2 ^ 128 by rw [← pow_add]]
  calc
    Real.exp (1881 / 10 : ℝ) * ((97 / 200 : ℝ) ^ 256) ^ 2 *
        (2 ^ 128 * 2 ^ 128) =
      Real.exp (1881 / 10 : ℝ) *
        ((97 / 200 : ℝ) ^ 256 * 2 ^ 128) *
        ((97 / 200 : ℝ) ^ 256 * 2 ^ 128) := by ring
    _ = Real.exp (1881 / 10 : ℝ) *
          (((97 / 200 : ℚ) ^ 256 * 2 ^ 128 : ℚ) : ℝ) *
          (((97 / 200 : ℚ) ^ 256 * 2 ^ 128 : ℚ) : ℝ) := by
      norm_num only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div,
        Rat.cast_ofNat, Nat.cast_ofNat, Nat.cast_pow]
    _ < 1 := hlt

private def retainedEnclosure : Interval precision :=
  Exp.posUpper precision (327750 / 2401) squarings *
    Interval.ofRat precision
      ((53 / 100 : ℚ) ^ 512 * 2 ^ 256 * 25 / 24)

private theorem retainedCheck :
    Interval.upperLTCheck retainedEnclosure 1 = true := by
  set_option maxRecDepth 1000000 in
    decide +kernel

theorem retainedFinalRatio :
    Real.exp ((23 / 10 : ℝ) * 57 * (2500 / 2401)) *
        (53 / 100 : ℝ) ^ 512 <
      ((24 / (25 * 2 ^ 256) : ℚ) : ℝ) := by
  have hexp :
      (Exp.posUpper precision (327750 / 2401) squarings).Contains
        (Real.exp (327750 / 2401 : ℝ)) := by
    simpa using Exp.posUpper_contains
      (p := precision) (k := squarings) (x := (327750 / 2401 : ℚ))
      (by norm_num) (by norm_num [squarings]) (by
        change 0 < Dyadic.roundDown precision
          (1 - (327750 / 2401) / 2 ^ squarings)
        rw [Dyadic.roundDown, Int.floor_pos]
        norm_num [precision, squarings, Dyadic.scale])
  have hrat := Interval.contains_ofRat precision
    ((53 / 100 : ℚ) ^ 512 * 2 ^ 256 * 25 / 24)
  have hlt :
      Real.exp (327750 / 2401 : ℝ) *
          ((((53 / 100 : ℚ) ^ 512 * 2 ^ 256 * 25 / 24) : ℚ) : ℝ) < 1 := by
    simpa [retainedEnclosure] using Interval.lt_of_contains_of_upperLTCheck
      (Interval.contains_mul hexp hrat) retainedCheck
  rw [show (23 / 10 : ℝ) * 57 * (2500 / 2401) =
      327750 / 2401 by norm_num]
  have hscaled :
      Real.exp (327750 / 2401 : ℝ) * (53 / 100 : ℝ) ^ 512 *
          (2 : ℝ) ^ 256 * 25 / 24 < 1 := by
    have hbase : (53 / 100 : ℝ) = ((53 / 100 : ℚ) : ℝ) := by norm_num
    have h2 : (2 : ℝ) = ((2 : ℚ) : ℝ) := by norm_num
    have h25 : (25 : ℝ) = ((25 : ℚ) : ℝ) := by norm_num
    have h24 : (24 : ℝ) = ((24 : ℚ) : ℝ) := by norm_num
    rw [hbase, h2, h25, h24]
    set_option maxRecDepth 100000 in
      simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_inv,
        div_eq_mul_inv, mul_assoc] using hlt
  have htarget :
      ((24 / (25 * 2 ^ 256) : ℚ) : ℝ) =
        24 / (25 * (2 : ℝ) ^ 256) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_pow]
  rw [htarget]
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 25 * 2 ^ 256)).2
  have hhigh :
      Real.exp (327750 / 2401 : ℝ) * (53 / 100 : ℝ) ^ 512 *
          (2 : ℝ) ^ 256 * 25 < 24 :=
    (div_lt_one (by norm_num : (0 : ℝ) < 24)).mp hscaled
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hhigh

end CertifiedJL.ThresholdRatios512Bits256
