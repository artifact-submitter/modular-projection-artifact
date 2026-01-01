/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Transcendental.Exponential.DyadicExpData
import CertifiedJL.Arithmetic.Transcendental.Exponential.Exp

/-!
# Integer-only evaluation of the scaled exponential enclosure

The logical exponential enclosure in `CertifiedJL.Arithmetic.Transcendental.Exponential.Exp` first
decodes a dyadic endpoint as a rational and then rounds the scaled base back
to the same dyadic grid.  This file proves an extensionally equal evaluator
that performs that round trip directly with integer floor and ceiling
division.  Numerical certificates may therefore reduce the executable term
without repeatedly normalizing large rational expressions.
-/

namespace CertifiedJL
namespace DyadicExp

private theorem roundDown_one_sub_upper
    (p : ℕ) (upper : ℤ) (k : ℕ) :
    Dyadic.roundDown p
        (1 - Dyadic.toRat p upper / (2 ^ k : ℕ)) =
      (Dyadic.scale p : ℤ) +
        Dyadic.floorDivBy (-upper) (2 ^ k : ℤ) := by
  rw [Dyadic.roundDown]
  have hscale : (Dyadic.scale p : ℚ) ≠ 0 := by
    exact_mod_cast Dyadic.scale_ne_zero p
  have hpow : ((2 ^ k : ℕ) : ℚ) ≠ 0 := by positivity
  have hrewrite :
      (1 - Dyadic.toRat p upper / (2 ^ k : ℕ)) *
          Dyadic.scale p =
        (Dyadic.scale p : ℚ) +
          ((-upper : ℤ) : ℚ) / (2 ^ k : ℕ) := by
    unfold Dyadic.toRat
    field_simp
    simp only [Int.cast_neg]
    ring
  rw [hrewrite, add_comm]
  change
    ⌊(((-upper : ℤ) : ℚ) / (2 ^ k : ℕ)) +
        (((Dyadic.scale p : ℕ) : ℤ) : ℚ)⌋ =
      (Dyadic.scale p : ℤ) +
        Dyadic.floorDivBy (-upper) (2 ^ k : ℤ)
  rw [Int.floor_add_intCast,
    Rat.floor_intCast_div_natCast]
  simp [Dyadic.floorDivBy, add_comm]

private theorem roundUp_one_sub_upper
    (p : ℕ) (upper : ℤ) (k : ℕ) :
    Dyadic.roundUp p
        (1 - Dyadic.toRat p upper / (2 ^ k : ℕ)) =
      (Dyadic.scale p : ℤ) +
        Dyadic.ceilDivBy (-upper) (2 ^ k : ℤ) := by
  rw [Dyadic.roundUp]
  have hscale : (Dyadic.scale p : ℚ) ≠ 0 := by
    exact_mod_cast Dyadic.scale_ne_zero p
  have hpow : ((2 ^ k : ℕ) : ℚ) ≠ 0 := by positivity
  have hrewrite :
      (1 - Dyadic.toRat p upper / (2 ^ k : ℕ)) *
          Dyadic.scale p =
        (Dyadic.scale p : ℚ) +
          ((-upper : ℤ) : ℚ) / (2 ^ k : ℕ) := by
    unfold Dyadic.toRat
    field_simp
    simp only [Int.cast_neg]
    ring
  rw [hrewrite, add_comm]
  change
    ⌈(((-upper : ℤ) : ℚ) / (2 ^ k : ℕ)) +
        (((Dyadic.scale p : ℕ) : ℤ) : ℚ)⌉ =
      (Dyadic.scale p : ℤ) +
        Dyadic.ceilDivBy (-upper) (2 ^ k : ℤ)
  rw [Int.ceil_add_intCast,
    Rat.ceil_intCast_div_natCast]
  simp [Dyadic.ceilDivBy, add_comm]

private theorem interval_eq
    {p : ℕ} {I J : Interval p}
    (hlo : I.lo = J.lo) (hhi : I.hi = J.hi) :
    I = J := by
  cases I
  cases J
  simp_all

theorem base_eq_ofRat
    (p : ℕ) (upper : ℤ) (k : ℕ) :
    base p upper k =
      Interval.ofRat p
        (1 - Dyadic.toRat p upper / (2 ^ k : ℕ)) := by
  apply interval_eq
  · simpa only [base, Interval.ofRat, Interval.enclose,
      Nat.cast_ofNat, Nat.cast_pow] using
      (roundDown_one_sub_upper p upper k).symm
  · simpa only [base, Interval.ofRat, Interval.enclose,
      Nat.cast_ofNat, Nat.cast_pow] using
      (roundUp_one_sub_upper p upper k).symm

theorem ofIntervalUpper_eq
    (p : ℕ) (I : Interval p) (k : ℕ) :
    ofIntervalUpper p I k = Exp.ofIntervalUpper p I k := by
  unfold ofIntervalUpper Exp.ofIntervalUpper Exp.upper
  by_cases h : 0 ≤ I.upperRat
  · rw [if_pos h]
    unfold Exp.posUpper Exp.posBase
    change Exp.upperHull ((base p I.hi k).reciprocal.squareN k) =
      Exp.upperHull
        ((Interval.ofRat p
          (1 - Dyadic.toRat p I.hi / (2 ^ k : ℕ))).reciprocal.squareN k)
    rw [base_eq_ofRat]
  · rw [if_neg h]
    unfold Exp.negUpper Exp.negBase
    have hneg :
        Interval.ofRat p
              (1 - I.upperRat / (2 ^ k : ℕ)) =
            Interval.ofRat p 1 +
              Interval.ofRat p
                (-I.upperRat / (2 ^ k : ℕ)) := by
      apply interval_eq
      · change
          Dyadic.roundDown p
              (1 - I.upperRat / (2 ^ k : ℕ)) =
            Dyadic.roundDown p 1 +
              Dyadic.roundDown p
                (-I.upperRat / (2 ^ k : ℕ))
        simp [Dyadic.roundDown, sub_eq_add_neg, add_mul]
        congr 1
        ring
      · change
          Dyadic.roundUp p
              (1 - I.upperRat / (2 ^ k : ℕ)) =
            Dyadic.roundUp p 1 +
              Dyadic.roundUp p
                (-I.upperRat / (2 ^ k : ℕ))
        simp [Dyadic.roundUp, sub_eq_add_neg, add_mul]
        congr 1
        ring
    change Exp.upperHull ((base p I.hi k).reciprocal.squareN k) =
      Exp.upperHull
        ((Interval.ofRat p 1 +
          Interval.ofRat p
            (-Dyadic.toRat p I.hi / (2 ^ k : ℕ))).reciprocal.squareN k)
    rw [base_eq_ofRat]
    rw [show
      Interval.ofRat p
          (1 - Dyadic.toRat p I.hi / (2 ^ k : ℕ)) =
        Interval.ofRat p 1 +
          Interval.ofRat p
            (-Dyadic.toRat p I.hi / (2 ^ k : ℕ)) by
      simpa only [Interval.upperRat] using hneg]

theorem ofIntervalUpper_contains
    {p k : ℕ} {I : Interval p} {x : ℝ}
    (hx : I.Contains x)
    (hupper : 0 ≤ I.upperRat →
      I.upperRat < (2 ^ k : ℕ))
    (hbase : 0 ≤ I.upperRat →
      0 < (Interval.ofRat p
        (1 - I.upperRat / (2 ^ k : ℕ))).lo) :
    (ofIntervalUpper p I k).Contains (Real.exp x) := by
  rw [ofIntervalUpper_eq]
  exact Exp.ofIntervalUpper_contains hx hupper hbase

/--
For a dyadic scale and a scaling power both at least two, an exponent upper
endpoint at most one automatically satisfies every reciprocal-base side
condition.  This is the inexpensive safety interface used by the moderate
Prawitz certificate.
-/
theorem ofIntervalUpper_contains_of_upperRat_le_one
    {p k : ℕ} {I : Interval p} {x : ℝ}
    (hscale : (2 : ℚ) ≤ Dyadic.scale p)
    (hpow : (2 : ℚ) ≤ (2 ^ k : ℕ))
    (hx : I.Contains x)
    (hupperOne : I.upperRat ≤ 1) :
    (ofIntervalUpper p I k).Contains (Real.exp x) := by
  apply ofIntervalUpper_contains hx
  · intro _hupperNonneg
    exact hupperOne.trans_lt (lt_of_lt_of_le (by norm_num) hpow)
  · intro _hupperNonneg
    apply Dyadic.roundDown_pos
    have hpowPos : (0 : ℚ) < (2 ^ k : ℕ) := by positivity
    have hquotient :
        I.upperRat / (2 ^ k : ℕ) ≤ (1 : ℚ) / 2 := by
      calc
        I.upperRat / (2 ^ k : ℕ) ≤
            (1 : ℚ) / (2 ^ k : ℕ) :=
          div_le_div_of_nonneg_right hupperOne hpowPos.le
        _ ≤ (1 : ℚ) / 2 := by
          exact one_div_le_one_div_of_le (by norm_num) hpow
    have hbaseHalf :
        (1 : ℚ) / 2 ≤
          1 - I.upperRat / (2 ^ k : ℕ) := by
      linarith
    calc
      (1 : ℚ) = (1 / 2 : ℚ) * 2 := by norm_num
      _ ≤ (1 / 2 : ℚ) * Dyadic.scale p :=
        mul_le_mul_of_nonneg_left hscale (by norm_num)
      _ ≤
          (1 - I.upperRat / (2 ^ k : ℕ)) *
            Dyadic.scale p :=
        mul_le_mul_of_nonneg_right hbaseHalf (by positivity)

end DyadicExp
end CertifiedJL
