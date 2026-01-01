/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Transcendental.Trigonometric.TrigData
import CertifiedJL.Analysis.Fourier.Prawitz.KernelBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Executable interval enclosures for rational multiples of pi

The Prawitz certificate evaluates trigonometric functions only at rational
multiples of `pi`.  This module combines the twenty-decimal theorem-backed
interval for `pi` with arbitrary-order alternating Taylor sums on
`[0, pi / 2]`.  Every executable operation is integer or rational interval
arithmetic.
-/

namespace CertifiedJL
namespace TrigInterval

open Probability

theorem pow_contains {p : ℕ} {I : Interval p} {x : ℝ}
    (hx : I.Contains x) (n : ℕ) :
    (pow I n).Contains (x ^ n) := by
  induction n with
  | zero => simpa [pow] using Interval.contains_ofRat p 1
  | succ n ih =>
      simpa [pow, _root_.pow_succ] using Interval.contains_mul ih hx

private theorem sinTerm_contains {p : ℕ} {X : Interval p} {x : ℝ}
    (hx : X.Contains x) (i : ℕ) :
    (sinTerm X i).Contains
      ((-1 : ℝ) ^ i *
        (x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ))) := by
  have hpow := pow_contains hx (2 * i + 1)
  have hcoeff := Interval.contains_ofRat p
    (((-1 : ℚ) ^ i) / ((2 * i + 1).factorial : ℚ))
  have hmul := Interval.contains_mul hpow hcoeff
  simpa [sinTerm, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul

theorem sinPartial_contains {p : ℕ} {X : Interval p} {x : ℝ}
    (hx : X.Contains x) (n : ℕ) :
    (sinPartial X n).Contains
      (∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i *
          (x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ))) := by
  induction n with
  | zero => simpa [sinPartial] using Interval.contains_ofRat p 0
  | succ n ih =>
      rw [Finset.sum_range_succ]
      simpa [sinPartial] using
        Interval.contains_add ih (sinTerm_contains hx n)

theorem sinTaylor_contains {p : ℕ} {X : Interval p} {x : ℝ}
    (hx : X.Contains x) (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi / 2)
    (k : ℕ) :
    (sinTaylor X k).Contains (Real.sin x) := by
  have hl := sinPartial_contains hx (2 * k)
  have hu := sinPartial_contains hx (2 * k + 1)
  exact ⟨hl.1.trans (sin_taylor_evenSum_le hx0 hxpi k),
    (sin_le_taylor_oddSum hx0 hxpi k).trans hu.2⟩

private theorem cosTailTerm_contains {p : ℕ}
    {X : Interval p} {x : ℝ} (hx : X.Contains x) (i : ℕ) :
    (cosTailTerm X i).Contains
      ((-1 : ℝ) ^ i *
        (x ^ (2 * (i + 1)) /
          ((2 * (i + 1)).factorial : ℝ))) := by
  have hpow := pow_contains hx (2 * (i + 1))
  have hcoeff := Interval.contains_ofRat p
    (((-1 : ℚ) ^ i) / ((2 * (i + 1)).factorial : ℚ))
  have hmul := Interval.contains_mul hpow hcoeff
  simpa [cosTailTerm, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul

theorem cosTailPartial_contains {p : ℕ}
    {X : Interval p} {x : ℝ} (hx : X.Contains x) (n : ℕ) :
    (cosTailPartial X n).Contains
      (∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i *
          (x ^ (2 * (i + 1)) /
            ((2 * (i + 1)).factorial : ℝ))) := by
  induction n with
  | zero => simpa [cosTailPartial] using Interval.contains_ofRat p 0
  | succ n ih =>
      rw [Finset.sum_range_succ]
      simpa [cosTailPartial] using
        Interval.contains_add ih (cosTailTerm_contains hx n)

theorem cosTaylor_contains {p : ℕ} {X : Interval p} {x : ℝ}
    (hx : X.Contains x) (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi / 2)
    (k : ℕ) :
    (cosTaylor X k).Contains (Real.cos x) := by
  have hone : (Interval.ofRat p 1).Contains (1 : ℝ) :=
    by simpa using Interval.contains_ofRat p (1 : ℚ)
  have hlTail := cosTailPartial_contains hx (2 * k + 1)
  have huTail := cosTailPartial_contains hx (2 * k)
  have hl := Interval.contains_sub hone hlTail
  have hu := Interval.contains_sub hone huTail
  exact ⟨hl.1.trans (cos_taylor_lowerSum_le hx0 hxpi k),
    (cos_le_taylor_upperSum hx0 hxpi k).trans hu.2⟩

theorem piMul_contains {p : ℕ} {s : ℚ} (hs : 0 ≤ s) :
    (piMul (p := p) s).Contains (Real.pi * (s : ℝ)) := by
  apply Interval.contains_enclose
  have hl : (piLower : ℝ) < Real.pi := by
    have h := Real.pi_gt_d20
    norm_num [piLower] at h ⊢
    exact h
  have hu : Real.pi < (piUpper : ℝ) := by
    have h := Real.pi_lt_d20
    norm_num [piUpper] at h ⊢
    exact h
  have hsReal : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  constructor
  · simpa only [Rat.cast_mul] using
      mul_le_mul_of_nonneg_right hl.le hsReal
  · simpa only [Rat.cast_mul] using
      mul_le_mul_of_nonneg_right hu.le hsReal

theorem piRange_contains {p : ℕ} {lower upper : ℚ} {s : ℝ}
    (hlower : 0 ≤ lower)
    (hs : (lower : ℝ) ≤ s ∧ s ≤ (upper : ℝ)) :
    (piRange (p := p) lower upper).Contains (Real.pi * s) := by
  apply Interval.contains_enclose
  have hpiLower : (piLower : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d20
    norm_num [piLower] at h ⊢
    exact h.le
  have hpiUpper : Real.pi ≤ (piUpper : ℝ) := by
    have h := Real.pi_lt_d20
    norm_num [piUpper] at h ⊢
    exact h.le
  have hlowerReal : (0 : ℝ) ≤ (lower : ℝ) := by exact_mod_cast hlower
  have hupperReal : (0 : ℝ) ≤ (upper : ℝ) :=
    hlowerReal.trans (hs.1.trans hs.2)
  constructor
  · calc
      ((piLower * lower : ℚ) : ℝ) =
          (piLower : ℝ) * (lower : ℝ) := by norm_num
      _ ≤ Real.pi * (lower : ℝ) :=
        mul_le_mul_of_nonneg_right hpiLower hlowerReal
      _ ≤ Real.pi * s := mul_le_mul_of_nonneg_left hs.1 Real.pi_pos.le
  · calc
      Real.pi * s ≤ Real.pi * (upper : ℝ) :=
        mul_le_mul_of_nonneg_left hs.2 Real.pi_pos.le
      _ ≤ (piUpper : ℝ) * (upper : ℝ) :=
        mul_le_mul_of_nonneg_right hpiUpper hupperReal
      _ = ((piUpper * upper : ℚ) : ℝ) := by norm_num

theorem sinPiRange_contains {p : ℕ} {lower upper : ℚ} {s : ℝ}
    (hlower : 0 ≤ lower) (hupper : upper ≤ 1 / 2)
    (hs : (lower : ℝ) ≤ s ∧ s ≤ (upper : ℝ)) (k : ℕ) :
    (sinPiRange (p := p) lower upper k).Contains
      (Real.sin (Real.pi * s)) := by
  apply sinTaylor_contains (piRange_contains hlower hs)
  · have hs0 : 0 ≤ s := by
      have hlowerReal : (0 : ℝ) ≤ (lower : ℝ) := by exact_mod_cast hlower
      exact hlowerReal.trans hs.1
    exact mul_nonneg Real.pi_pos.le hs0
  · have hupperReal : (upper : ℝ) ≤ 1 / 2 := by
      rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num]
      exact_mod_cast hupper
    nlinarith [Real.pi_pos]

theorem cosPiRange_contains {p : ℕ} {lower upper : ℚ} {s : ℝ}
    (hlower : 0 ≤ lower) (hupper : upper ≤ 1 / 2)
    (hs : (lower : ℝ) ≤ s ∧ s ≤ (upper : ℝ)) (k : ℕ) :
    (cosPiRange (p := p) lower upper k).Contains
      (Real.cos (Real.pi * s)) := by
  apply cosTaylor_contains (piRange_contains hlower hs)
  · have hs0 : 0 ≤ s := by
      have hlowerReal : (0 : ℝ) ≤ (lower : ℝ) := by exact_mod_cast hlower
      exact hlowerReal.trans hs.1
    exact mul_nonneg Real.pi_pos.le hs0
  · have hupperReal : (upper : ℝ) ≤ 1 / 2 := by
      rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num]
      exact_mod_cast hupper
    nlinarith [Real.pi_pos]

theorem sinPiHalf_contains {p : ℕ} {s : ℚ}
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2) (k : ℕ) :
    (sinPiHalf (p := p) s k).Contains
      (Real.sin (Real.pi * (s : ℝ))) := by
  apply sinTaylor_contains (piMul_contains hs0)
  · exact mul_nonneg Real.pi_pos.le (by exact_mod_cast hs0)
  · have hsReal : (s : ℝ) ≤ 1 / 2 := by
      rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num]
      exact_mod_cast hs
    nlinarith [Real.pi_pos]

theorem cosPiHalf_contains {p : ℕ} {s : ℚ}
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2) (k : ℕ) :
    (cosPiHalf (p := p) s k).Contains
      (Real.cos (Real.pi * (s : ℝ))) := by
  apply cosTaylor_contains (piMul_contains hs0)
  · exact mul_nonneg Real.pi_pos.le (by exact_mod_cast hs0)
  · have hsReal : (s : ℝ) ≤ 1 / 2 := by
      rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num]
      exact_mod_cast hs
    nlinarith [Real.pi_pos]

end TrigInterval
end CertifiedJL
