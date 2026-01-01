/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Interval.Reflection
import Mathlib.Tactic.NormNum

/-!
# Final scalar ratios for sparse protocol-threshold branches

The near-dominant branch uses tilt `23/10` and row cap `681/1250`.
The diffuse branch uses tilt `33/10` and row cap `97/200`.
-/

namespace CertifiedJL

namespace ThresholdNearDominantRatio128

def precision : ℕ := 256
def squarings : ℕ := 32

private def enclosure : Interval precision :=
  Exp.posUpper precision (667 / 10) squarings *
    Interval.ofRat precision ((681 / 1250 : ℚ) ^ 256 * 2 ^ 128)

private def check : Bool := Interval.upperLTCheck enclosure 1

private theorem check_eq_true : check = true := by
  set_option maxRecDepth 1000000 in
    decide +kernel

/-- The relaxed near-dominant row cap gives a strict 128-bit ratio. -/
theorem finalRatio :
    Real.exp ((23 / 10 : ℝ) * 29) * (681 / 1250 : ℝ) ^ 256 <
      (2 : ℝ)⁻¹ ^ 128 := by
  have hexp :
      (Exp.posUpper precision (667 / 10) squarings).Contains
      (Real.exp (667 / 10 : ℝ)) := by
    simpa using Exp.posUpper_contains
      (p := precision) (k := squarings) (x := (667 / 10 : ℚ))
      (by norm_num) (by norm_num [squarings]) (by
        change 0 < Dyadic.roundDown precision
          (1 - (667 / 10) / 2 ^ squarings)
        rw [Dyadic.roundDown, Int.floor_pos]
        norm_num [precision, squarings, Dyadic.scale])
  have hrat := Interval.contains_ofRat precision
      ((681 / 1250 : ℚ) ^ 256 * 2 ^ 128)
  have hproduct := Interval.contains_mul hexp hrat
  have hlt :
      Real.exp (667 / 10 : ℝ) *
          (((681 / 1250 : ℚ) ^ 256 * 2 ^ 128 : ℚ) : ℝ) < 1 := by
    simpa [enclosure] using
      Interval.lt_of_contains_of_upperLTCheck hproduct check_eq_true
  have htwoPos : (0 : ℝ) < 2 ^ 128 := by positivity
  have hscaled :
      Real.exp (667 / 10 : ℝ) * (681 / 1250 : ℝ) ^ 256 * 2 ^ 128 < 1 := by
    calc
      _ = Real.exp (667 / 10 : ℝ) *
          (((681 / 1250 : ℚ) ^ 256 * 2 ^ 128 : ℚ) : ℝ) := by
        norm_num
        ring
      _ < 1 := hlt
  rw [show (23 / 10 : ℝ) * 29 = 667 / 10 by norm_num,
    inv_pow, inv_eq_one_div]
  exact (lt_div_iff₀ htwoPos).2 hscaled

end ThresholdNearDominantRatio128

namespace ThresholdDiffuseRatio

def precision : ℕ := 256
def squarings : ℕ := 32

private def enclosure : Interval precision :=
  Exp.posUpper precision (957 / 10) squarings *
    Interval.ofRat precision ((97 / 200 : ℚ) ^ 256 * 2 ^ 128)

private def check : Bool := Interval.upperLTCheck enclosure 1

private theorem check_eq_true : check = true := by
  set_option maxRecDepth 1000000 in
    decide +kernel

/-- The diffuse rational row cap leaves a strict 128-bit final ratio. -/
theorem finalRatio128 :
    Real.exp ((33 / 10 : ℝ) * 29) * (97 / 200 : ℝ) ^ 256 <
      (2 : ℝ)⁻¹ ^ 128 := by
  have hexp :
      (Exp.posUpper precision (957 / 10) squarings).Contains
      (Real.exp (957 / 10 : ℝ)) := by
    simpa using Exp.posUpper_contains
      (p := precision) (k := squarings) (x := (957 / 10 : ℚ))
      (by norm_num) (by norm_num [squarings]) (by
        change 0 < Dyadic.roundDown precision
          (1 - (957 / 10) / 2 ^ squarings)
        rw [Dyadic.roundDown, Int.floor_pos]
        norm_num [precision, squarings, Dyadic.scale])
  have hrat := Interval.contains_ofRat precision
      ((97 / 200 : ℚ) ^ 256 * 2 ^ 128)
  have hproduct := Interval.contains_mul hexp hrat
  have hlt :
      Real.exp (957 / 10 : ℝ) *
          (((97 / 200 : ℚ) ^ 256 * 2 ^ 128 : ℚ) : ℝ) < 1 := by
    simpa [enclosure] using
      Interval.lt_of_contains_of_upperLTCheck hproduct check_eq_true
  have htwoPos : (0 : ℝ) < 2 ^ 128 := by positivity
  have hscaled :
      Real.exp (957 / 10 : ℝ) * (97 / 200 : ℝ) ^ 256 * 2 ^ 128 < 1 := by
    calc
      _ = Real.exp (957 / 10 : ℝ) *
          (((97 / 200 : ℚ) ^ 256 * 2 ^ 128 : ℚ) : ℝ) := by
        norm_num
        ring
      _ < 1 := hlt
  rw [show (33 / 10 : ℝ) * 29 = 957 / 10 by norm_num,
    inv_pow, inv_eq_one_div]
  exact (lt_div_iff₀ htwoPos).2 hscaled

end ThresholdDiffuseRatio
end CertifiedJL
