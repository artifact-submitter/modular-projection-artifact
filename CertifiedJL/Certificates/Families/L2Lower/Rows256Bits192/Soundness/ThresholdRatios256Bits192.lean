/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Interval.Reflection
import Mathlib.Tactic.NormNum

/-! # Final scalar ratios for the 256-row, floor-9, 192-bit endpoint -/

namespace CertifiedJL.ThresholdRatios256Bits192

def precision : ℕ := 256
def squarings : ℕ := 32

private def nearEnclosure : Interval precision :=
  Exp.posUpper precision (207 / 10) squarings *
    Interval.ofRat precision ((681 / 1250 : ℚ) ^ 256 * 2 ^ 192)

private theorem nearCheck : Interval.upperLTCheck nearEnclosure 1 = true := by
  set_option maxRecDepth 1000000 in
    decide +kernel

theorem nearFinalRatio :
    Real.exp ((23 / 10 : ℝ) * 9) * (681 / 1250 : ℝ) ^ 256 <
      (2 : ℝ)⁻¹ ^ 192 := by
  have hexp :
      (Exp.posUpper precision (207 / 10) squarings).Contains
        (Real.exp (207 / 10 : ℝ)) := by
    simpa using Exp.posUpper_contains
      (p := precision) (k := squarings) (x := (207 / 10 : ℚ))
      (by norm_num) (by norm_num [squarings]) (by
        change 0 < Dyadic.roundDown precision
          (1 - (207 / 10) / 2 ^ squarings)
        rw [Dyadic.roundDown, Int.floor_pos]
        norm_num [precision, squarings, Dyadic.scale])
  have hrat := Interval.contains_ofRat precision
    ((681 / 1250 : ℚ) ^ 256 * 2 ^ 192)
  have hlt :
      Real.exp (207 / 10 : ℝ) *
          (((681 / 1250 : ℚ) ^ 256 * 2 ^ 192 : ℚ) : ℝ) < 1 := by
    simpa [nearEnclosure] using Interval.lt_of_contains_of_upperLTCheck
      (Interval.contains_mul hexp hrat) nearCheck
  rw [show (23 / 10 : ℝ) * 9 = 207 / 10 by norm_num,
    inv_pow, inv_eq_one_div]
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 192)).2
  calc
    Real.exp (207 / 10 : ℝ) * (681 / 1250 : ℝ) ^ 256 * 2 ^ 192 =
        Real.exp (207 / 10 : ℝ) *
          (((681 / 1250 : ℚ) ^ 256 * 2 ^ 192 : ℚ) : ℝ) := by
      push_cast
      ring
    _ < 1 := hlt

private def diffuseEnclosure : Interval precision :=
  Exp.posUpper precision (297 / 10) squarings *
    Interval.ofRat precision ((97 / 200 : ℚ) ^ 256 * 2 ^ 192)

private theorem diffuseCheck :
    Interval.upperLTCheck diffuseEnclosure 1 = true := by
  set_option maxRecDepth 1000000 in
    decide +kernel

theorem diffuseFinalRatio :
    Real.exp ((33 / 10 : ℝ) * 9) * (97 / 200 : ℝ) ^ 256 <
      (2 : ℝ)⁻¹ ^ 192 := by
  have hexp :
      (Exp.posUpper precision (297 / 10) squarings).Contains
        (Real.exp (297 / 10 : ℝ)) := by
    simpa using Exp.posUpper_contains
      (p := precision) (k := squarings) (x := (297 / 10 : ℚ))
      (by norm_num) (by norm_num [squarings]) (by
        change 0 < Dyadic.roundDown precision
          (1 - (297 / 10) / 2 ^ squarings)
        rw [Dyadic.roundDown, Int.floor_pos]
        norm_num [precision, squarings, Dyadic.scale])
  have hrat := Interval.contains_ofRat precision
    ((97 / 200 : ℚ) ^ 256 * 2 ^ 192)
  have hlt :
      Real.exp (297 / 10 : ℝ) *
          (((97 / 200 : ℚ) ^ 256 * 2 ^ 192 : ℚ) : ℝ) < 1 := by
    simpa [diffuseEnclosure] using Interval.lt_of_contains_of_upperLTCheck
      (Interval.contains_mul hexp hrat) diffuseCheck
  rw [show (33 / 10 : ℝ) * 9 = 297 / 10 by norm_num,
    inv_pow, inv_eq_one_div]
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 192)).2
  calc
    Real.exp (297 / 10 : ℝ) * (97 / 200 : ℝ) ^ 256 * 2 ^ 192 =
        Real.exp (297 / 10 : ℝ) *
          (((97 / 200 : ℚ) ^ 256 * 2 ^ 192 : ℚ) : ℝ) := by
      push_cast
      ring
    _ < 1 := hlt

private def retainedEnclosure : Interval precision :=
  Exp.posUpper precision (51750 / 2401) squarings *
    Interval.ofRat precision
      ((53 / 100 : ℚ) ^ 256 * 2 ^ 192 * 100 / 99)

private theorem retainedCheck :
    Interval.upperLTCheck retainedEnclosure 1 = true := by
  set_option maxRecDepth 1000000 in
    decide +kernel

theorem retainedFinalRatio :
    Real.exp ((23 / 10 : ℝ) * 9 * (2500 / 2401)) *
        (53 / 100 : ℝ) ^ 256 <
      ((99 / (100 * 2 ^ 192) : ℚ) : ℝ) := by
  have hexp :
      (Exp.posUpper precision (51750 / 2401) squarings).Contains
        (Real.exp (51750 / 2401 : ℝ)) := by
    simpa using Exp.posUpper_contains
      (p := precision) (k := squarings) (x := (51750 / 2401 : ℚ))
      (by norm_num) (by norm_num [squarings]) (by
        change 0 < Dyadic.roundDown precision
          (1 - (51750 / 2401) / 2 ^ squarings)
        rw [Dyadic.roundDown, Int.floor_pos]
        norm_num [precision, squarings, Dyadic.scale])
  have hrat := Interval.contains_ofRat precision
    ((53 / 100 : ℚ) ^ 256 * 2 ^ 192 * 100 / 99)
  have hlt :
      Real.exp (51750 / 2401 : ℝ) *
          ((((53 / 100 : ℚ) ^ 256 * 2 ^ 192 * 100 / 99) : ℚ) : ℝ) < 1 := by
    simpa [retainedEnclosure] using Interval.lt_of_contains_of_upperLTCheck
      (Interval.contains_mul hexp hrat) retainedCheck
  rw [show (23 / 10 : ℝ) * 9 * (2500 / 2401) =
      51750 / 2401 by norm_num]
  have hscaled :
      Real.exp (51750 / 2401 : ℝ) * (53 / 100 : ℝ) ^ 256 *
          (2 : ℝ) ^ 192 * 100 / 99 < 1 := by
    calc
      _ = Real.exp (51750 / 2401 : ℝ) *
          ((((53 / 100 : ℚ) ^ 256 * 2 ^ 192 * 100 / 99) : ℚ) : ℝ) := by
        push_cast
        ring
    _ < 1 := hlt
  have htarget :
      ((99 / (100 * 2 ^ 192) : ℚ) : ℝ) =
        99 / (100 * (2 : ℝ) ^ 192) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_pow]
  rw [htarget]
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 100 * 2 ^ 192)).2
  have hnineteen :
      Real.exp (51750 / 2401 : ℝ) * (53 / 100 : ℝ) ^ 256 *
          (2 : ℝ) ^ 192 * 100 < 99 :=
    (div_lt_one (by norm_num : (0 : ℝ) < 99)).mp hscaled
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hnineteen

end CertifiedJL.ThresholdRatios256Bits192
