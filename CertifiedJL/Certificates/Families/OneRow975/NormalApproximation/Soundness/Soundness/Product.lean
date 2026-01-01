/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Soundness.Soundness.Core

/-!
# Product-envelope soundness for moderate Lyapunov cells
-/

namespace CertifiedJL
namespace TyurinModerate

open Probability

private theorem toRat_max (p : ℕ) (a b : ℤ) :
    Dyadic.toRat p (max a b) =
      max (Dyadic.toRat p a) (Dyadic.toRat p b) := by
  unfold Dyadic.toRat
  rw [Int.cast_max, max_div_div_right]
  positivity

private theorem cell_endpoint_contains
    (C : Cell) :
    C.lyapunovInterval.Contains (C.hi : ℝ) := by
  simpa [Cell.lyapunovInterval] using contains_rat C.hi

private theorem actualX_contains
    {C : Cell} {XI : DInterval} {x : ℝ}
    (hx : XI.Contains x) (hgeometry : geometryCheck C = true) :
    (div (C.lyapunovInterval * XI) (rat C.hi)).Contains x := by
  rcases geometryCheck_sound hgeometry with
    ⟨_hlo, _hlohi, _hratio, _hcutoff, _hcut, _hUlo,
      _hrlo, _hrlo3, _hrhi, _hrhi3, _hswitch,
      hhiLo, _⟩
  have hnum :
      (C.lyapunovInterval * XI).Contains
        ((C.hi : ℝ) * x) :=
    Interval.contains_mul (cell_endpoint_contains C) hx
  have hden : (rat C.hi).Contains (C.hi : ℝ) :=
    contains_rat C.hi
  have hquot :=
    contains_div hhiLo hnum hden
  have hhi : (C.hi : ℝ) ≠ 0 := by
    have : 0 < C.hi :=
      (geometryCheck_sound hgeometry).1.trans_le
        (geometryCheck_sound hgeometry).2.1
    exact_mod_cast this.ne'
  convert hquot using 1
  field_simp

private theorem ucoord_contains
    {C : Cell} {XI : DInterval} {u : ℝ}
    (hx : XI.Contains (2 * (C.hi : ℝ) * u))
    (hgeometry : geometryCheck C = true) :
    (div XI (rat 2 * rat C.hi)).Contains u := by
  rcases geometryCheck_sound hgeometry with
    ⟨_hlo, _hlohi, _hratio, _hcutoff, _hcut, _hUlo,
      _hrlo, _hrlo3, _hrhi, _hrhi3, _hswitch,
      _hhiLo, htwoHi, _⟩
  have hden :
      (rat 2 * rat C.hi).Contains
        (2 * (C.hi : ℝ)) :=
    Interval.contains_mul
      (by simpa using contains_rat (2 : ℚ))
      (contains_rat C.hi)
  have hquot := contains_div htwoHi hx hden
  have hhi : (C.hi : ℝ) ≠ 0 := by
    have : 0 < C.hi :=
      (geometryCheck_sound hgeometry).1.trans_le
        (geometryCheck_sound hgeometry).2.1
    exact_mod_cast this.ne'
  convert hquot using 1
  field_simp

private theorem cubicProduct_upper
    {C : Cell} {XI : DInterval} {u : ℝ}
    (hx : XI.Contains (2 * (C.hi : ℝ) * u))
    (hgeometry : geometryCheck C = true)
    (hsafe : expSafe (cubicProductExponent C XI) = true) :
    Real.exp (-(u ^ 2) / 2 + (C.hi : ℝ) * u ^ 3 / 5) ≤
      ((expUpper (cubicProductExponent C XI)).upperRat : ℝ) := by
  have hu := ucoord_contains hx hgeometry
  have huSq := Interval.contains_square hu
  have huCube := contains_powNat hu 3
  have hL := cell_endpoint_contains C
  have hexponent :
      (cubicProductExponent C XI).Contains
        (-(u ^ 2) / 2 + (C.hi : ℝ) * u ^ 3 / 5) := by
    unfold cubicProductExponent
    have hcubic :
        (rat (2 / 5) * C.lyapunovInterval *
            powNat (div XI (rat 2 * rat C.hi)) 3).Contains
          ((2 / 5 : ℝ) * (C.hi : ℝ) * u ^ 3) :=
      Interval.contains_mul
        (Interval.contains_mul
          (by simpa using contains_rat (2 / 5)) hL)
        huCube
    have hinside :=
      Interval.contains_add
        (Interval.contains_neg huSq) hcubic
    convert
      Interval.contains_mul hinside
        (by simpa using contains_rat (1 / 2)) using 1 <;>
      ring
  exact le_upperRat
    (contains_expUpper hexponent hsafe)

private theorem cosineProduct_upper
    {C : Cell} {XI : DInterval} {u : ℝ}
    (hx : XI.Contains (2 * (C.hi : ℝ) * u))
    (hx4 : 4 ≤ 2 * (C.hi : ℝ) * u)
    (hxBand : 2 * (C.hi : ℝ) * u ≤ 157 / 25)
    (hgeometry : geometryCheck C = true)
    (hsafe : expSafe (cosineProductExponent C XI) = true) :
    Real.exp
        (-(tyurinCosineLoss / (4 * (C.hi : ℝ) ^ 2) *
          tyurinRationalCosineLower
            (2 * (C.hi : ℝ) * u))) ≤
      ((expUpper (cosineProductExponent C XI)).upperRat : ℝ) := by
  let x : ℝ := 2 * (C.hi : ℝ) * u
  have hactualX :
      (div (C.lyapunovInterval * XI) (rat C.hi)).Contains x := by
    exact actualX_contains (by simpa [x] using hx) hgeometry
  obtain ⟨q, hq, hqle⟩ :=
    rationalCosineLower_surrogate hactualX
      (by simpa [x] using hx4) (by simpa [x] using hxBand)
  rcases geometryCheck_sound hgeometry with
    ⟨_hlo, _hlohi, _hratio, _hcutoff, _hcut, _hUlo,
      _hrlo, _hrlo3, _hrhi, _hrhi3, _hswitch,
      _hhiLo, _htwoHi, _htwoExact, hfourL, _⟩
  have hL := cell_endpoint_contains C
  have hLSq := Interval.contains_square hL
  have hden :
      (rat 4 * C.lyapunovInterval.square).Contains
        (4 * (C.hi : ℝ) ^ 2) :=
    Interval.contains_mul
      (by simpa using contains_rat (4 : ℚ)) hLSq
  have hinv :
      (div (rat 1)
          (rat 4 * C.lyapunovInterval.square)).Contains
        (1 / (4 * (C.hi : ℝ) ^ 2)) :=
    contains_div hfourL
      (by simpa using contains_rat (1 : ℚ)) hden
  have hloss :
      (rat cosineLoss).Contains tyurinCosineLoss := by
    simpa [cosineLoss, tyurinCosineLoss] using
      contains_rat cosineLoss
  have hsurrogateExponent :
      (cosineProductExponent C XI).Contains
        (-(tyurinCosineLoss * q *
          (1 / (4 * (C.hi : ℝ) ^ 2)))) := by
    unfold cosineProductExponent
    exact Interval.contains_neg
      (Interval.contains_mul
        (Interval.contains_mul hloss hq) hinv)
  have hsurrogateExp :=
    contains_expUpper hsurrogateExponent hsafe
  have hfactor :
      0 ≤ tyurinCosineLoss /
        (4 * (C.hi : ℝ) ^ 2) := by
    have hhi : (0 : ℝ) < C.hi := by
      exact_mod_cast
        (geometryCheck_sound hgeometry).1.trans_le
          (geometryCheck_sound hgeometry).2.1
    unfold tyurinCosineLoss
    positivity
  have hexponent :
      -(tyurinCosineLoss /
          (4 * (C.hi : ℝ) ^ 2) *
            tyurinRationalCosineLower x) ≤
        -(tyurinCosineLoss * q *
          (1 / (4 * (C.hi : ℝ) ^ 2))) := by
    have := neg_le_neg (mul_le_mul_of_nonneg_left hqle hfactor)
    dsimp only [x] at this ⊢
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm] using this
  exact (Real.exp_le_exp.mpr hexponent).trans
    (le_upperRat hsurrogateExp)

/--
The executable product-envelope upper endpoint dominates the sharp analytic
endpoint envelope on one Lyapunov cell.
-/
theorem productEnvelope_upper
    {C : Cell} {XI : DInterval} {u : ℝ}
    (hx : XI.Contains (2 * (C.hi : ℝ) * u))
    (hband : 2 * (C.hi : ℝ) * u ≤ 157 / 25)
    (hgeometry : geometryCheck C = true)
    (hsafe : productEnvelopeSafe C XI = true) :
    tyurinCellProductEnvelope (C.hi : ℝ) u ≤
      ((productEnvelope C XI).upperRat : ℝ) := by
  let actualXI :=
    div (C.lyapunovInterval * XI) (rat C.hi)
  let x : ℝ := 2 * (C.hi : ℝ) * u
  have hxActual : actualXI.Contains x := by
    dsimp only [actualXI, x]
    exact actualX_contains hx hgeometry
  by_cases hfirst : actualXI.upperRat < 4
  · have hx4 : x < 4 := by
      have hcast :
          (actualXI.upperRat : ℝ) < (4 : ℝ) := by
        exact_mod_cast hfirst
      exact (le_upperRat_of_contains hxActual).trans_lt hcast
    unfold productEnvelopeSafe at hsafe
    unfold productEnvelope
    dsimp only [actualXI] at hfirst
    rw [if_pos hfirst] at hsafe ⊢
    unfold tyurinCellProductEnvelope
    rw [if_pos (by simpa [x] using hx4)]
    exact cubicProduct_upper hx hgeometry hsafe
  · by_cases hsecond : 4 ≤ actualXI.lowerRat
    · have hx4 : 4 ≤ x := by
        have hcast :
            (4 : ℝ) ≤ (actualXI.lowerRat : ℝ) := by
          exact_mod_cast hsecond
        exact hcast.trans (lowerRat_le_of_contains hxActual)
      unfold productEnvelopeSafe at hsafe
      unfold productEnvelope
      dsimp only [actualXI] at hfirst hsecond
      rw [if_neg hfirst, if_pos hsecond] at hsafe ⊢
      unfold tyurinCellProductEnvelope
      rw [if_neg (by simpa [x] using not_lt.mpr hx4)]
      exact cosineProduct_upper hx hx4 hband
        hgeometry hsafe
    · unfold productEnvelopeSafe at hsafe
      unfold productEnvelope
      dsimp only [actualXI] at hfirst hsecond
      rw [if_neg hfirst, if_neg hsecond] at hsafe ⊢
      rw [Bool.and_eq_true] at hsafe
      unfold tyurinCellProductEnvelope
      by_cases hx4 : x < 4
      · rw [if_pos (by simpa [x] using hx4)]
        have hcubic :=
          cubicProduct_upper hx hgeometry hsafe.1
        unfold hull Interval.upperRat
        rw [toRat_max]
        unfold Interval.upperRat at hcubic
        have hmax :
            (Dyadic.toRat precision
                (expUpper (cubicProductExponent C XI)).hi : ℝ) ≤
              (max
                (Dyadic.toRat precision
                  (expUpper (cubicProductExponent C XI)).hi)
                (Dyadic.toRat precision
                  (expUpper (cosineProductExponent C XI)).hi) : ℚ) := by
          exact_mod_cast
            (le_max_left
              (Dyadic.toRat precision
                (expUpper (cubicProductExponent C XI)).hi)
              (Dyadic.toRat precision
                (expUpper (cosineProductExponent C XI)).hi))
        exact hcubic.trans hmax
      · have hx4' : 4 ≤ x := le_of_not_gt hx4
        rw [if_neg (by simpa [x] using hx4)]
        have hcosine :=
          cosineProduct_upper hx hx4' hband
            hgeometry hsafe.2
        unfold hull Interval.upperRat
        rw [toRat_max]
        unfold Interval.upperRat at hcosine
        have hmax :
            (Dyadic.toRat precision
                (expUpper (cosineProductExponent C XI)).hi : ℝ) ≤
              (max
                (Dyadic.toRat precision
                  (expUpper (cubicProductExponent C XI)).hi)
                (Dyadic.toRat precision
                  (expUpper (cosineProductExponent C XI)).hi) : ℚ) := by
          exact_mod_cast
            (le_max_right
              (Dyadic.toRat precision
                (expUpper (cubicProductExponent C XI)).hi)
              (Dyadic.toRat precision
                (expUpper (cosineProductExponent C XI)).hi))
        exact hcosine.trans hmax

end TyurinModerate
end CertifiedJL
