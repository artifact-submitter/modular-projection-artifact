/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Numeric.OuterPlan
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Soundness.CrossingCore

/-!
# Soundness of the switch-aligned Tyurin outer certificate
-/

open MeasureTheory Set
open scoped BigOperators

namespace CertifiedJL.TyurinModerate
open Probability

private theorem toRat_min_outer (p : ℕ) (a b : ℤ) :
    Dyadic.toRat p (min a b) =
      min (Dyadic.toRat p a) (Dyadic.toRat p b) := by
  unfold Dyadic.toRat
  rw [Int.cast_min, min_div_div_right]
  positivity

private theorem toRat_max_outer (p : ℕ) (a b : ℤ) :
    Dyadic.toRat p (max a b) =
      max (Dyadic.toRat p a) (Dyadic.toRat p b) := by
  unfold Dyadic.toRat
  rw [Int.cast_max, max_div_div_right]
  positivity

private theorem upperRat_le_hull_left (I J : DInterval) :
    (I.upperRat : ℝ) ≤ ((hull I J).upperRat : ℝ) := by
  unfold hull Interval.upperRat
  rw [toRat_max_outer]
  exact_mod_cast le_max_left (Dyadic.toRat precision I.hi)
    (Dyadic.toRat precision J.hi)

private theorem upperRat_le_hull_right (I J : DInterval) :
    (J.upperRat : ℝ) ≤ ((hull I J).upperRat : ℝ) := by
  unfold hull Interval.upperRat
  rw [toRat_max_outer]
  exact_mod_cast le_max_right (Dyadic.toRat precision I.hi)
    (Dyadic.toRat precision J.hi)

private theorem mul_le_intervalUpper_outer
    {I J : DInterval} {x y : ℝ}
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hx : x ≤ (I.upperRat : ℝ))
    (hy : y ≤ (J.upperRat : ℝ)) :
    x * y ≤ ((I * J).upperRat : ℝ) := by
  have hI0 : 0 ≤ (I.upperRat : ℝ) := hx0.trans hx
  have hJ0 : 0 ≤ (J.upperRat : ℝ) := hy0.trans hy
  exact (mul_le_mul hx hy hy0 hI0).trans
    (Interval.upperRat_mul_upperRat_le I J)

private theorem outerPlanCosineLower_nonneg
    {x : ℝ} (hx0 : 4 ≤ x) (hx1 : x ≤ 157 / 25) :
    0 ≤ tyurinRationalCosineLower x := by
  unfold tyurinRationalCosineLower
  split_ifs with hleft hmiddle
  · have hgap0 : 0 ≤ x - 157 / 50 := by nlinarith
    have hgap1 : x - 157 / 50 ≤ 157 / 50 := by nlinarith
    nlinarith [sq_nonneg (x - 157 / 50),
      sq_le_sq₀ hgap0 (by norm_num : (0 : ℝ) ≤ 157 / 50) |>.2 hgap1]
  · norm_num
  · have hr0 : 0 ≤ 157 / 25 - x := by linarith
    have hr1 : 157 / 25 - x ≤ 313 / 200 := by
      have : 189 / 40 ≤ x := le_of_not_gt hmiddle
      linarith
    have hrsq :
        (157 / 25 - x) ^ 2 ≤ (313 / 200 : ℝ) ^ 2 :=
      (sq_le_sq₀ hr0 (by norm_num)).2 hr1
    have hfactor :
        (157 / 25 - x) ^ 2 / 2 -
            (157 / 25 - x) ^ 4 / 24 =
          (157 / 25 - x) ^ 2 *
            (1 / 2 - (157 / 25 - x) ^ 2 / 24) := by ring
    rw [hfactor]
    apply mul_nonneg (sq_nonneg _)
    nlinarith

private theorem outerPlanCosineLower_ge_two_fifths
    {x : ℝ} (hx0 : 4 ≤ x) (hx1 : x ≤ 189 / 40) :
    (2 / 5 : ℝ) ≤ tyurinRationalCosineLower x := by
  unfold tyurinRationalCosineLower
  split_ifs with hleft hmiddle
  · have hgap0 : 0 ≤ x - 157 / 50 := by nlinarith
    have hgap1 : x - 157 / 50 ≤ 317 / 200 := by linarith
    have hrsq :
        (x - 157 / 50) ^ 2 ≤ (317 / 200 : ℝ) ^ 2 :=
      (sq_le_sq₀ hgap0 (by norm_num)).2 hgap1
    nlinarith
  · exact le_rfl
  · have hx : x = 189 / 40 := by
      exact le_antisymm hx1 (le_of_not_gt hmiddle)
    subst x
    norm_num

/-- Exact rational branch selection gives a cosine surrogate no larger than
the analytic envelope throughout the whole plan cell. -/
theorem outerPlanCosineLower_surrogate
    {lo hi : ℚ} {XI : DInterval} {x : ℝ}
    (hx : XI.Contains x) (hlo : (lo : ℝ) ≤ x)
    (hhi : x ≤ (hi : ℝ)) (hx0 : 4 ≤ x)
    (hx1 : x ≤ 157 / 25) :
    ∃ q : ℝ, (outerPlanCosineLower lo hi XI).Contains q ∧
      q ≤ tyurinRationalCosineLower x := by
  unfold outerPlanCosineLower
  by_cases hleft : hi ≤ outerPlanCosineLeftEnd
  · rw [if_pos hleft]
    let q : ℝ := 2 - (x - 157 / 50) ^ 2 / 2
    have hshift := Interval.contains_sub hx
      (by simpa using contains_rat (157 / 50))
    refine ⟨q, ?_, ?_⟩
    · dsimp only [q]
      simpa [div_eq_mul_inv] using
        Interval.contains_sub (by simpa using contains_rat (2 : ℚ))
          (Interval.contains_mul (Interval.contains_square hshift)
            (by simpa using contains_rat (1 / 2)))
    · unfold tyurinRationalCosineLower
      have hxleft : x ≤ (471 / 100 : ℝ) := by
        have : (hi : ℝ) ≤ (471 / 100 : ℝ) := by
          simpa [outerPlanCosineLeftEnd] using
            (Rat.cast_le (K := ℝ)).mpr hleft
        exact hhi.trans this
      rw [if_pos hxleft]
  · rw [if_neg hleft]
    by_cases hright : outerPlanCosineRightStart ≤ lo
    · rw [if_pos hright]
      let r : ℝ := 157 / 25 - x
      let q : ℝ := r ^ 2 / 2 - r ^ 4 / 24
      have hr : (rat (157 / 25) - XI).Contains r := by
        dsimp only [r]
        exact Interval.contains_sub
          (by simpa using contains_rat (157 / 25)) hx
      refine ⟨q, ?_, ?_⟩
      · dsimp only [q]
        have hhalf :
            ((rat (157 / 25) - XI).square * rat (1 / 2)).Contains
              (r ^ 2 / 2) := by
          simpa [div_eq_mul_inv] using
            Interval.contains_mul (Interval.contains_square hr)
              (by simpa using contains_rat (1 / 2))
        have htwentyFour :
            (powNat (rat (157 / 25) - XI) 4 * rat (1 / 24)).Contains
              (r ^ 4 / 24) := by
          simpa [div_eq_mul_inv] using
            Interval.contains_mul (contains_powNat hr 4)
              (by simpa using contains_rat (1 / 24))
        exact Interval.contains_sub hhalf htwentyFour
      · unfold tyurinRationalCosineLower
        have hxRight : (189 / 40 : ℝ) ≤ x := by
          have : (189 / 40 : ℝ) ≤ (lo : ℝ) := by
            simpa [outerPlanCosineRightStart] using
              (Rat.cast_le (K := ℝ)).mpr hright
          exact this.trans hlo
        rw [if_neg (by linarith : ¬x ≤ (471 / 100 : ℝ)),
          if_neg (not_lt.mpr hxRight)]
    · rw [if_neg hright]
      by_cases hmiddle : hi ≤ outerPlanCosineRightStart
      · rw [if_pos hmiddle]
        refine ⟨2 / 5, by simpa using contains_rat (2 / 5), ?_⟩
        apply outerPlanCosineLower_ge_two_fifths hx0
        have : (hi : ℝ) ≤ (189 / 40 : ℝ) := by
          simpa [outerPlanCosineRightStart] using
            (Rat.cast_le (K := ℝ)).mpr hmiddle
        exact hhi.trans this
      · rw [if_neg hmiddle]
        exact ⟨0, by simpa using contains_rat (0 : ℚ),
          outerPlanCosineLower_nonneg hx0 hx1⟩

private theorem outerPlanCubicProduct_upper
    {C : Cell} {XI : DInterval} {x u : ℝ}
    (hx : XI.Contains x) (hxu : x = 2 * (C.hi : ℝ) * u)
    (hgeometry : geometryCheck C = true)
    (hden : 0 < (rat 40 * (rat C.hi).square).lo)
    (hsafe : expSafe (outerPlanCubicExponent C XI) = true) :
    Real.exp (-(u ^ 2) / 2 + (C.hi : ℝ) * u ^ 3 / 5) ≤
      ((expUpper (outerPlanCubicExponent C XI)).upperRat : ℝ) := by
  have hb : (0 : ℝ) < C.hi := by
    rcases geometryCheck_sound hgeometry with ⟨hlo, hlohi, _⟩
    exact_mod_cast hlo.trans_le hlohi
  have hbI : (rat C.hi).Contains (C.hi : ℝ) := contains_rat C.hi
  have hdenContains :
      (rat 40 * (rat C.hi).square).Contains
        (40 * (C.hi : ℝ) ^ 2) :=
    Interval.contains_mul (by simpa using contains_rat (40 : ℚ))
      (Interval.contains_square hbI)
  have hinv := contains_div hden
    (by simpa using contains_rat (1 : ℚ)) hdenContains
  have hexponent :
      (outerPlanCubicExponent C XI).Contains
        (x ^ 2 * (x - 5) / (40 * (C.hi : ℝ) ^ 2)) := by
    unfold outerPlanCubicExponent
    simpa [div_eq_mul_inv, mul_assoc] using
      Interval.contains_mul
        (Interval.contains_mul (Interval.contains_square hx)
          (Interval.contains_sub hx (by simpa using contains_rat (5 : ℚ))))
        hinv
  have heq :
      x ^ 2 * (x - 5) / (40 * (C.hi : ℝ) ^ 2) =
        -(u ^ 2) / 2 + (C.hi : ℝ) * u ^ 3 / 5 := by
    rw [hxu]
    field_simp [hb.ne']
    ring
  exact le_upperRat (contains_expUpper (heq ▸ hexponent) hsafe)

private theorem outerPlanCosineProduct_upper
    {C : Cell} {lo hi : ℚ} {XI : DInterval} {x : ℝ}
    (hx : XI.Contains x) (hlo : (lo : ℝ) ≤ x)
    (hhi : x ≤ (hi : ℝ))
    (hx4 : 4 ≤ x) (hxBand : x ≤ 157 / 25)
    (hgeometry : geometryCheck C = true)
    (hsafe : expSafe (outerPlanCosineExponent C lo hi XI) = true) :
    Real.exp (-(tyurinCosineLoss / (4 * (C.hi : ℝ) ^ 2) *
        tyurinRationalCosineLower x)) ≤
      ((expUpper (outerPlanCosineExponent C lo hi XI)).upperRat : ℝ) := by
  obtain ⟨q, hq, hqle⟩ :=
    outerPlanCosineLower_surrogate hx hlo hhi hx4 hxBand
  rcases geometryCheck_sound hgeometry with
    ⟨_hlo, _hlohi, _hratio, _hcutoff, _hcut, _hUlo,
      _hrlo, _hrlo3, _hrhi, _hrhi3, _hswitch,
      _hhiLo, _htwoHi, _htwoExact, hfourL, _⟩
  have hbI : (rat C.hi).Contains (C.hi : ℝ) := contains_rat C.hi
  have hden :
      (rat 4 * (rat C.hi).square).Contains
        (4 * (C.hi : ℝ) ^ 2) :=
    Interval.contains_mul (by simpa using contains_rat (4 : ℚ))
      (Interval.contains_square hbI)
  have hinv := contains_div hfourL
    (by simpa using contains_rat (1 : ℚ)) hden
  have hloss : (rat cosineLoss).Contains tyurinCosineLoss := by
    simpa [cosineLoss, tyurinCosineLoss] using contains_rat cosineLoss
  have hsurrogate :
      (outerPlanCosineExponent C lo hi XI).Contains
        (-(tyurinCosineLoss * q * (1 / (4 * (C.hi : ℝ) ^ 2)))) := by
    unfold outerPlanCosineExponent
    exact Interval.contains_neg
      (Interval.contains_mul (Interval.contains_mul hloss hq) hinv)
  have hb : (0 : ℝ) < C.hi := by
    rcases geometryCheck_sound hgeometry with ⟨hlo', hlohi', _⟩
    exact_mod_cast hlo'.trans_le hlohi'
  have hfactor : 0 ≤ tyurinCosineLoss / (4 * (C.hi : ℝ) ^ 2) := by
    unfold tyurinCosineLoss
    positivity
  have hexponent :
      -(tyurinCosineLoss / (4 * (C.hi : ℝ) ^ 2) *
          tyurinRationalCosineLower x) ≤
        -(tyurinCosineLoss * q * (1 / (4 * (C.hi : ℝ) ^ 2))) := by
    have := neg_le_neg (mul_le_mul_of_nonneg_left hqle hfactor)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  exact (Real.exp_le_exp.mpr hexponent).trans
    (le_upperRat (contains_expUpper hsurrogate hsafe))

/-- The new product evaluator bounds the same endpoint product envelope as
the original 500-cell checker. -/
theorem outerPlanProductEnvelope_upper
    {C : Cell} {lo hi : ℚ} {x u : ℝ}
    (hx : (Interval.enclose precision lo hi).Contains x)
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ))
    (hxu : x = 2 * (C.hi : ℝ) * u)
    (hband : x ≤ 157 / 25)
    (hgeometry : geometryCheck C = true)
    (hsafe : outerPlanProductSafe C lo hi = true) :
    tyurinCellProductEnvelope (C.hi : ℝ) u ≤
      ((outerPlanProductEnvelope C lo hi).upperRat : ℝ) := by
  unfold outerPlanProductSafe at hsafe
  unfold outerPlanProductEnvelope
  dsimp only
  by_cases hfirst : hi < 4
  · rw [if_pos hfirst] at hsafe ⊢
    rw [Bool.and_eq_true] at hsafe
    have hx4 : x < 4 := hhi.trans_lt (by exact_mod_cast hfirst)
    unfold tyurinCellProductEnvelope
    rw [if_pos (by simpa [hxu] using hx4)]
    exact outerPlanCubicProduct_upper hx hxu hgeometry
      (of_decide_eq_true hsafe.1) hsafe.2
  · rw [if_neg hfirst] at hsafe ⊢
    by_cases hsecond : 4 ≤ lo
    · rw [if_pos hsecond] at hsafe ⊢
      have hx4 : 4 ≤ x := (by exact_mod_cast hsecond : (4 : ℝ) ≤ lo).trans hlo
      unfold tyurinCellProductEnvelope
      rw [if_neg (by simpa [hxu] using not_lt.mpr hx4)]
      rw [← hxu]
      exact outerPlanCosineProduct_upper hx hlo hhi hx4 hband
        hgeometry hsafe
    · rw [if_neg hsecond] at hsafe ⊢
      rw [Bool.and_eq_true, Bool.and_eq_true] at hsafe
      unfold tyurinCellProductEnvelope
      by_cases hx4 : x < 4
      · rw [if_pos (by simpa [hxu] using hx4)]
        exact (outerPlanCubicProduct_upper hx hxu hgeometry
          (of_decide_eq_true hsafe.1.1) hsafe.1.2).trans
          (upperRat_le_hull_left _ _)
      · have hx4' : 4 ≤ x := le_of_not_gt hx4
        rw [if_neg (by simpa [hxu] using hx4)]
        rw [← hxu]
        exact (outerPlanCosineProduct_upper hx hlo hhi hx4' hband
          hgeometry hsafe.2).trans (upperRat_le_hull_right _ _)

private theorem scaledEndpoint_le_rational_outer
    {U t : ℝ} (hU : 0 < U) (ht0 : 0 ≤ t) (htU : t ≤ U) :
    scaledPrawitzEndpointEnvelope U t ≤
      (1 / U) * ((1 - t / U) / 2 +
        (piUpper : ℝ) * (1 - t / U) ^ 2 / 4) := by
  have hpi : Real.pi ≤ (piUpper : ℝ) := by
    simpa [piUpper] using pi_lt_3141593_div_1000000.le
  have hgap : 0 ≤ 1 - t / U := by
    rw [sub_nonneg, div_le_one hU]
    exact htU
  unfold scaledPrawitzEndpointEnvelope
  rw [abs_of_nonneg ht0]
  gcongr

private theorem outerPlanI29Scaled_upper
    {C : Cell} {XI : DInterval} {x u : ℝ}
    (hx : XI.Contains x) (hxu : x = 2 * (C.hi : ℝ) * u)
    (hu : 0 < u) (hgeometry : geometryCheck C = true)
    (hsafe : 0 < (rat (2 * piLower) * XI).lo) :
    scaledPrawitzI29Envelope u / (2 * (C.hi : ℝ)) ≤
      ((outerPlanI29Scaled XI).upperRat : ℝ) := by
  have hb : (0 : ℝ) < C.hi := by
    rcases geometryCheck_sound hgeometry with ⟨hlo, hlohi, _⟩
    exact_mod_cast hlo.trans_le hlohi
  have hxpos : 0 < x := by rw [hxu]; positivity
  have heq :
      scaledPrawitzI29Envelope u / (2 * (C.hi : ℝ)) =
        scaledPrawitzI29Envelope x := by
    unfold scaledPrawitzI29Envelope
    rw [abs_of_pos hu, abs_of_pos hxpos, hxu]
    field_simp [hb.ne', hu.ne', Real.pi_ne_zero]
  rw [heq]
  simpa [outerPlanI29Scaled, kernelI29] using
    kernelI29_upper hx hxpos hsafe

private theorem outerPlanEndpointScaled_upper
    {C : Cell} {XI : DInterval} {x u : ℝ}
    (hx : XI.Contains x) (hxu : x = 2 * (C.hi : ℝ) * u)
    (hu0 : 0 ≤ u) (huU : u ≤ (C.bandwidth : ℝ))
    (hgeometry : geometryCheck C = true)
    (hsafe : 0 < (rat 2 * rat (C.hi * C.bandwidth)).lo) :
    scaledPrawitzEndpointEnvelope (C.bandwidth : ℝ) u /
        (2 * (C.hi : ℝ)) ≤
      ((outerPlanEndpointScaled C XI).upperRat : ℝ) := by
  rcases geometryCheck_sound hgeometry with
    ⟨hlo, hlohi, _hratio, hcutoff, hcut, _⟩
  have hb : (0 : ℝ) < C.hi := by exact_mod_cast hlo.trans_le hlohi
  have hU : (0 : ℝ) < C.bandwidth := by
    exact_mod_cast hcutoff.trans_le hcut
  let S : ℝ := (C.hi : ℝ) * (C.bandwidth : ℝ)
  have hS : 0 < S := by dsimp [S]; positivity
  have hSI : (rat (C.hi * C.bandwidth)).Contains S := by
    dsimp only [S]
    simpa using contains_rat (C.hi * C.bandwidth)
  have hden :
      (rat 2 * rat (C.hi * C.bandwidth)).Contains (2 * S) := by
    exact Interval.contains_mul (by simpa using contains_rat (2 : ℚ)) hSI
  have hquot :
      (div XI (rat 2 * rat (C.hi * C.bandwidth))).Contains
        (x / (2 * S)) :=
    contains_div hsafe hx hden
  have hgap :
      (rat 1 - div XI (rat 2 * rat (C.hi * C.bandwidth))).Contains
        (1 - x / (2 * S)) :=
    Interval.contains_sub (by simpa using contains_rat (1 : ℚ)) hquot
  have hinv :
      (div (rat 1) (rat 2 * rat (C.hi * C.bandwidth))).Contains
        (1 / (2 * S)) :=
    contains_div hsafe (by simpa using contains_rat (1 : ℚ)) hden
  have hhalf :
      ((rat 1 - div XI (rat 2 * rat (C.hi * C.bandwidth))) *
          rat (1 / 2)).Contains ((1 - x / (2 * S)) / 2) := by
    simpa [div_eq_mul_inv] using
      Interval.contains_mul hgap (by simpa using contains_rat (1 / 2))
  have hquarter :
      (rat piUpper *
          (rat 1 - div XI (rat 2 * rat (C.hi * C.bandwidth))).square *
          rat (1 / 4)).Contains
        ((piUpper : ℝ) * (1 - x / (2 * S)) ^ 2 / 4) := by
    simpa [div_eq_mul_inv, mul_assoc] using
      Interval.contains_mul
        (Interval.contains_mul (contains_rat piUpper)
          (Interval.contains_square hgap))
        (contains_rat (1 / 4))
  have hrational :
      (outerPlanEndpointScaled C XI).Contains
        ((1 / (2 * S)) * ((1 - x / (2 * S)) / 2 +
          (piUpper : ℝ) * (1 - x / (2 * S)) ^ 2 / 4)) := by
    unfold outerPlanEndpointScaled
    dsimp only
    exact Interval.contains_mul hinv (Interval.contains_add hhalf hquarter)
  have hanalytic := scaledEndpoint_le_rational_outer hU hu0 huU
  have hdiv := div_le_div_of_nonneg_right hanalytic (by positivity :
    0 ≤ 2 * (C.hi : ℝ))
  calc
    scaledPrawitzEndpointEnvelope (C.bandwidth : ℝ) u /
          (2 * (C.hi : ℝ)) ≤
        ((1 / (C.bandwidth : ℝ)) *
          ((1 - u / (C.bandwidth : ℝ)) / 2 +
            (piUpper : ℝ) * (1 - u / (C.bandwidth : ℝ)) ^ 2 / 4)) /
            (2 * (C.hi : ℝ)) := hdiv
    _ =
        (1 / (2 * S)) * ((1 - x / (2 * S)) / 2 +
          (piUpper : ℝ) * (1 - x / (2 * S)) ^ 2 / 4) := by
      dsimp only [S]
      rw [hxu]
      field_simp [hb.ne', hU.ne']
    _ ≤ ((outerPlanEndpointScaled C XI).upperRat : ℝ) :=
      le_upperRat hrational

/-- The scaled kernel checker includes the change-of-variables Jacobian and
bounds the original certificate envelope on every plan cell. -/
theorem outerPlanKernel_upper
    {C : Cell} {XI : DInterval} {x u : ℝ}
    (hx : XI.Contains x) (hxu : x = 2 * (C.hi : ℝ) * u)
    (hu : 0 < u) (huU : u ≤ (C.bandwidth : ℝ))
    (hgeometry : geometryCheck C = true)
    (hsafe : outerPlanKernelSafe C XI = true) :
    scaledPrawitzCertificateEnvelope (C.bandwidth : ℝ) u /
        (2 * (C.hi : ℝ)) ≤
      ((outerPlanKernel C XI).upperRat : ℝ) := by
  unfold outerPlanKernelSafe at hsafe
  rw [Bool.and_eq_true] at hsafe
  have hi29 := outerPlanI29Scaled_upper hx hxu hu hgeometry
    (of_decide_eq_true hsafe.1)
  have hend := outerPlanEndpointScaled_upper hx hxu hu.le huU hgeometry
    (of_decide_eq_true hsafe.2)
  have hb : (0 : ℝ) < C.hi := by
    rcases geometryCheck_sound hgeometry with ⟨hlo, hlohi, _⟩
    exact_mod_cast hlo.trans_le hlohi
  by_cases hhalfCheck :
      C.hi * C.bandwidth ≤ XI.lowerRat
  · have hhalf : (C.bandwidth : ℝ) / 2 ≤ u := by
      have hscale :
          (C.hi : ℝ) * (C.bandwidth : ℝ) ≤ x := by
        have hcast :
            ((C.hi * C.bandwidth : ℚ) : ℝ) ≤ (XI.lowerRat : ℝ) := by
          exact_mod_cast hhalfCheck
        simpa using hcast.trans (lowerRat_le_of_contains hx)
      rw [hxu] at hscale
      nlinarith
    unfold outerPlanKernel
    rw [if_pos hhalfCheck]
    unfold scaledPrawitzCertificateEnvelope
    rw [abs_of_pos hu, if_pos hhalf]
    rw [← min_div_div_right (by positivity : 0 ≤ 2 * (C.hi : ℝ))]
    unfold minInterval Interval.upperRat
    rw [toRat_min_outer]
    unfold Interval.upperRat at hi29 hend
    have hcast (a b : ℚ) :
        ((min a b : ℚ) : ℝ) = min (a : ℝ) (b : ℝ) := by
      by_cases hab : a ≤ b
      · rw [min_eq_left hab, min_eq_left]
        exact_mod_cast hab
      · have hba : b ≤ a := le_of_not_ge hab
        rw [min_eq_right hba, min_eq_right]
        exact_mod_cast hba
    rw [hcast]
    exact min_le_min hi29 hend
  · have henvelope :
        scaledPrawitzCertificateEnvelope (C.bandwidth : ℝ) u ≤
          scaledPrawitzI29Envelope u := by
      unfold scaledPrawitzCertificateEnvelope
      split_ifs
      · exact min_le_left _ _
      · exact le_rfl
    unfold outerPlanKernel
    rw [if_neg hhalfCheck]
    exact (div_le_div_of_nonneg_right henvelope (by positivity)).trans hi29

/-- Pointwise soundness of one complete scaled-coordinate plan cell. -/
theorem outerPlanIntegrand_upper
    {C : Cell} {lo hi : ℚ} {L u : ℝ}
    (hgeometry : geometryCheck C = true)
    (hL : (C.lo : ℝ) ≤ L) (hLb : L ≤ (C.hi : ℝ))
    (hu : (lo : ℝ) / (2 * (C.hi : ℝ)) ≤ u ∧
      u ≤ (hi : ℝ) / (2 * (C.hi : ℝ)))
    (hsafe : outerPlanCellSafe C lo hi = true) :
    ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
        tyurinProductEnvelope L u / (2 * (C.hi : ℝ)) ≤
      ((outerPlanIntegrand C lo hi).upperRat : ℝ) := by
  unfold outerPlanCellSafe at hsafe
  rw [Bool.and_eq_true, Bool.and_eq_true] at hsafe
  have hbounds := of_decide_eq_true hsafe.1.1
  rcases hbounds with ⟨houterLo, hlohi, houterHi⟩
  have hxBounds :
      (lo : ℝ) ≤ 2 * (C.hi : ℝ) * u ∧
        2 * (C.hi : ℝ) * u ≤ (hi : ℝ) := by
    have hb : (0 : ℝ) < C.hi := by
      rcases geometryCheck_sound hgeometry with ⟨ha, hab, _⟩
      exact_mod_cast ha.trans_le hab
    constructor
    · have h := (div_le_iff₀
          (by positivity : 0 < 2 * (C.hi : ℝ))).mp hu.1
      nlinarith
    · have h := (le_div_iff₀
          (by positivity : 0 < 2 * (C.hi : ℝ))).mp hu.2
      nlinarith
  have hx :
      (Interval.enclose precision lo hi).Contains
        (2 * (C.hi : ℝ) * u) :=
    Interval.contains_enclose hxBounds
  rcases geometryCheck_sound hgeometry with
    ⟨hlo, _hlohi, hratio, hcutoff, hcut, _hUlo,
      _hrlo, _hrlo3, _hrhi, _hrhi3, _hswitch,
      _hhiLo, _htwoHi, _htwoExact, _hfourL,
      _hcore, _houter, hbandGeom⟩
  have hb : (0 : ℝ) < C.hi := by
    have : (0 : ℝ) < C.lo := by exact_mod_cast hlo
    exact (this.trans_le hL).trans_le hLb
  have hLpos : 0 < L := (by exact_mod_cast hlo : (0 : ℝ) < C.lo).trans_le hL
  have hcutReal : (0 : ℝ) < C.cutoff := by exact_mod_cast hcutoff
  have huCut : (C.cutoff : ℝ) ≤ u := by
    have hcast :
        2 * (C.hi : ℝ) * (C.cutoff : ℝ) ≤ (lo : ℝ) := by
      exact_mod_cast houterLo
    have := hcast.trans hxBounds.1
    nlinarith
  have hu0 : 0 < u := hcutReal.trans_le huCut
  have huU : u ≤ (C.bandwidth : ℝ) := by
    have hcast :
        (hi : ℝ) ≤ 2 * (C.hi : ℝ) * (C.bandwidth : ℝ) := by
      exact_mod_cast houterHi
    have := hxBounds.2.trans hcast
    nlinarith
  have hband :
      2 * (C.hi : ℝ) * u ≤ 157 / 25 := by
    have hcast :
        2 * (C.hi : ℝ) * (C.bandwidth : ℝ) ≤ (157 / 25 : ℝ) := by
      have hcast := (Rat.cast_le (K := ℝ)).mpr hbandGeom
      norm_num at hcast ⊢
      exact hcast
    exact (mul_le_mul_of_nonneg_left huU (by positivity)).trans hcast
  have hUpos : (0 : ℝ) < C.bandwidth := by
    exact_mod_cast hcutoff.trans_le hcut
  have hkernelCert :=
    norm_scaledPrawitzKernel_le_certificateEnvelope
      hUpos hu0.ne' (by simpa [abs_of_pos hu0] using huU)
  have hkernel :
      ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ /
          (2 * (C.hi : ℝ)) ≤
        ((outerPlanKernel C (Interval.enclose precision lo hi)).upperRat : ℝ) :=
    (div_le_div_of_nonneg_right hkernelCert (by positivity)).trans
      (outerPlanKernel_upper hx rfl hu0 huU hgeometry hsafe.1.2)
  have hproductCell :=
    tyurinProductEnvelope_le_cellEndpoint
      (by exact_mod_cast hlo) hL hLb hu0.le
      (by
        have hcast :
            (((C.hi / C.lo : ℚ) : ℝ)) ≤ (((471 / 400 : ℚ) : ℝ)) := by
          exact_mod_cast hratio
        simpa using hcast)
      hband
  have hproduct := hproductCell.trans
    (outerPlanProductEnvelope_upper hx hxBounds.1 hxBounds.2 rfl hband
      hgeometry hsafe.2)
  have hmul := mul_le_intervalUpper_outer
    (by positivity : 0 ≤ ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ /
      (2 * (C.hi : ℝ)))
    (tyurinProductEnvelope_nonneg L u)
    hkernel hproduct
  unfold outerPlanIntegrand
  convert hmul using 1
  all_goals ring

private theorem foldl_range_add_eq_finsetSum_outer
    {α : Type*} [AddCommMonoid α] (f : ℕ → α) (n : ℕ) :
    (List.range n).foldl (fun acc i => acc + f i) 0 =
      ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ih]
      simp

/-- An arbitrary consecutive plan segment bounds the matching portion of the
outer integral. Cell safety itself certifies inclusion in the outer band. -/
theorem outerPlanSegmentIntegral_le
    {C : Cell} {L : ℝ} (endpoint : ℕ → ℚ) (cells : ℕ)
    (hgeometry : geometryCheck C = true)
    (hL : (C.lo : ℝ) ≤ L) (hLb : L ≤ (C.hi : ℝ))
    (hsafe : outerPlanSegmentSafe C endpoint cells = true) :
    (∫ u : ℝ in
        (endpoint 0 : ℝ) / (2 * (C.hi : ℝ))..
        (endpoint cells : ℝ) / (2 * (C.hi : ℝ)),
      ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
        tyurinProductEnvelope L u) ≤
      (outerPlanSegmentUpper C endpoint cells : ℝ) := by
  rcases geometryCheck_sound hgeometry with
    ⟨hlo, hlohi, _hratio, hcutoff, hcut, _⟩
  have hb : (0 : ℝ) < C.hi := by exact_mod_cast hlo.trans_le hlohi
  have hLpos : 0 < L := (by exact_mod_cast hlo : (0 : ℝ) < C.lo).trans_le hL
  have hcutoffReal : (0 : ℝ) < C.cutoff := by exact_mod_cast hcutoff
  have hbandReal : (0 : ℝ) < C.bandwidth := by
    exact_mod_cast hcutoff.trans_le hcut
  have hcutReal : (C.cutoff : ℝ) ≤ C.bandwidth := by exact_mod_cast hcut
  let f : ℝ → ℝ := fun u =>
    ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
      tyurinProductEnvelope L u
  let grid : ℕ → ℝ := fun i => (endpoint i : ℝ) / (2 * (C.hi : ℝ))
  have hglobal : IntervalIntegrable f volume
      (C.cutoff : ℝ) (C.bandwidth : ℝ) :=
    intervalIntegrable_tyurinOuterIntegrand hLpos hcutoffReal
      hbandReal hcutReal
  unfold outerPlanSegmentSafe at hsafe
  rw [List.all_eq_true] at hsafe
  have hpiece (i : ℕ) (hi : i < cells) :
      (∫ u : ℝ in grid i..grid (i + 1), f u) ≤
        ((endpoint (i + 1) - endpoint i : ℚ) : ℝ) *
          ((outerPlanIntegrand C (endpoint i) (endpoint (i + 1))).upperRat : ℝ) := by
    have hs := hsafe i (by simpa using hi)
    unfold outerPlanCellSafe at hs
    rw [Bool.and_eq_true, Bool.and_eq_true] at hs
    rcases of_decide_eq_true hs.1.1 with ⟨houterLo, hlohiCell, houterHi⟩
    have hcellOrder : grid i ≤ grid (i + 1) := by
      dsimp only [grid]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hlohiCell) (by positivity)
    have hfi : IntervalIntegrable f volume (grid i) (grid (i + 1)) := by
      apply IntervalIntegrable.mono_set hglobal
      rw [uIcc_of_le hcellOrder, uIcc_of_le hcutReal]
      intro u hu
      constructor
      · have hq :
            (C.cutoff : ℝ) ≤ (endpoint i : ℝ) / (2 * (C.hi : ℝ)) := by
          rw [le_div_iff₀ (by positivity : 0 < 2 * (C.hi : ℝ))]
          have hcast := (Rat.cast_le (K := ℝ)).mpr houterLo
          push_cast at hcast
          nlinarith
        exact hq.trans hu.1
      · have hq :
            (endpoint (i + 1) : ℝ) / (2 * (C.hi : ℝ)) ≤
              (C.bandwidth : ℝ) := by
          rw [div_le_iff₀ (by positivity : 0 < 2 * (C.hi : ℝ))]
          have hcast := (Rat.cast_le (K := ℝ)).mpr houterHi
          push_cast at hcast
          nlinarith
        exact hu.2.trans hq
    have hconst : IntervalIntegrable
        (fun _ : ℝ => (2 * (C.hi : ℝ)) *
          ((outerPlanIntegrand C (endpoint i) (endpoint (i + 1))).upperRat : ℝ))
        volume (grid i) (grid (i + 1)) :=
      continuous_const.intervalIntegrable _ _
    calc
      (∫ u : ℝ in grid i..grid (i + 1), f u) ≤
          ∫ _u : ℝ in grid i..grid (i + 1),
            (2 * (C.hi : ℝ)) *
              ((outerPlanIntegrand C (endpoint i) (endpoint (i + 1))).upperRat : ℝ) := by
        apply intervalIntegral.integral_mono_on hcellOrder hfi hconst
        intro u hu
        have hscaled := outerPlanIntegrand_upper hgeometry hL hLb
          (by simpa [grid] using hu) (hsafe i (by simpa using hi))
        have hden : 0 < 2 * (C.hi : ℝ) := by positivity
        have hrecovered := (div_le_iff₀ hden).mp hscaled
        simpa [f, mul_assoc, mul_left_comm, mul_comm] using hrecovered
      _ = ((endpoint (i + 1) - endpoint i : ℚ) : ℝ) *
          ((outerPlanIntegrand C (endpoint i) (endpoint (i + 1))).upperRat : ℝ) := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        dsimp only [grid]
        push_cast
        field_simp [hb.ne']
  have hsum :
      (∑ i ∈ Finset.range cells, ∫ u : ℝ in grid i..grid (i + 1), f u) ≤
        ∑ i ∈ Finset.range cells,
          ((endpoint (i + 1) - endpoint i : ℚ) : ℝ) *
            ((outerPlanIntegrand C (endpoint i) (endpoint (i + 1))).upperRat : ℝ) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hpiece i (Finset.mem_range.mp hi)
  have hsplit :
      (∑ i ∈ Finset.range cells, ∫ u : ℝ in grid i..grid (i + 1), f u) =
        ∫ u : ℝ in grid 0..grid cells, f u := by
    rw [intervalIntegral.sum_integral_adjacent_intervals]
    intro i hi
    have hs := hsafe i (by simpa using hi)
    unfold outerPlanCellSafe at hs
    rw [Bool.and_eq_true, Bool.and_eq_true] at hs
    rcases of_decide_eq_true hs.1.1 with ⟨houterLo, hlohiCell, houterHi⟩
    have hcellOrder : grid i ≤ grid (i + 1) := by
      dsimp only [grid]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hlohiCell) (by positivity)
    apply IntervalIntegrable.mono_set hglobal
    rw [uIcc_of_le hcellOrder, uIcc_of_le hcutReal]
    intro u hu
    constructor
    · have hq : (C.cutoff : ℝ) ≤ grid i := by
        dsimp only [grid]
        rw [le_div_iff₀ (by positivity : 0 < 2 * (C.hi : ℝ))]
        have hcast := (Rat.cast_le (K := ℝ)).mpr houterLo
        push_cast at hcast
        nlinarith
      exact hq.trans hu.1
    · have hq : grid (i + 1) ≤ (C.bandwidth : ℝ) := by
        dsimp only [grid]
        rw [div_le_iff₀ (by positivity : 0 < 2 * (C.hi : ℝ))]
        have hcast := (Rat.cast_le (K := ℝ)).mpr houterHi
        push_cast at hcast
        nlinarith
      exact hu.2.trans hq
  rw [hsplit] at hsum
  unfold outerPlanSegmentUpper
  rw [foldl_range_add_eq_finsetSum_outer]
  push_cast
  simpa [f, grid] using hsum

private theorem outerPlanSquareEndpoint_zero
    (lo hi : ℚ) (cells : ℕ) :
    outerPlanSquareEndpoint lo hi cells 0 = lo := by
  simp [outerPlanSquareEndpoint]

private theorem outerPlanSquareEndpoint_last
    (lo hi : ℚ) {cells : ℕ} (hcells : 0 < cells) :
    outerPlanSquareEndpoint lo hi cells cells = hi := by
  simp [outerPlanSquareEndpoint, Nat.ne_of_gt hcells]

private theorem outerPlanReverseSquareEndpoint_zero
    (lo hi : ℚ) (cells : ℕ) :
    outerPlanReverseSquareEndpoint lo hi cells 0 = lo := by
  simp [outerPlanReverseSquareEndpoint]

private theorem outerPlanReverseSquareEndpoint_last
    (lo hi : ℚ) {cells : ℕ} (hcells : 0 < cells) :
    outerPlanReverseSquareEndpoint lo hi cells cells = hi := by
  simp [outerPlanReverseSquareEndpoint, Nat.ne_of_gt hcells]
  ring

/-- The complete switch-aligned sum bounds exactly the old outer integral. -/
theorem outerIntegral_le_outerPlan
    {C : Cell} {L : ℝ} {cells : ℕ}
    (hgeometry : geometryCheck C = true)
    (hL : (C.lo : ℝ) ≤ L) (hLb : L ≤ (C.hi : ℝ))
    (hcheck : outerPlanCheck C cells = true) :
    (∫ u : ℝ in (C.cutoff : ℝ)..(C.bandwidth : ℝ),
      ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
        tyurinProductEnvelope L u) ≤
      (outerPlanUpper C cells : ℝ) := by
  unfold outerPlanCheck at hcheck
  dsimp only at hcheck
  simp only [Bool.and_eq_true] at hcheck
  rcases hcheck with
    ⟨⟨⟨⟨⟨⟨⟨hcells, hleft⟩, hright⟩, hs1⟩, hs2⟩, hs3⟩, hs4⟩, hs5⟩
  have hcells' : 0 < cells := of_decide_eq_true hcells
  let left : ℚ := 2 * C.hi * C.cutoff
  let right : ℚ := 2 * C.hi * C.bandwidth
  let e1 : ℕ → ℚ := outerPlanSquareEndpoint left outerPlanCubicEnd cells
  let e2 : ℕ → ℚ := fun | 0 => outerPlanCubicEnd | _ => 4
  let e3 : ℕ → ℚ := fun | 0 => 4 | _ => outerPlanCosineLeftEnd
  let e4 : ℕ → ℚ := fun
    | 0 => outerPlanCosineLeftEnd
    | _ => outerPlanCosineRightStart
  let e5 : ℕ → ℚ := outerPlanReverseSquareEndpoint
    outerPlanCosineRightStart right cells
  have he10 : e1 0 = left := outerPlanSquareEndpoint_zero _ _ _
  have he1n : e1 cells = outerPlanCubicEnd :=
    outerPlanSquareEndpoint_last _ _ hcells'
  have he20 : e2 0 = outerPlanCubicEnd := by simp [e2]
  have he21 : e2 1 = 4 := by simp [e2]
  have he30 : e3 0 = 4 := by simp [e3]
  have he31 : e3 1 = outerPlanCosineLeftEnd := by simp [e3]
  have he40 : e4 0 = outerPlanCosineLeftEnd := by simp [e4]
  have he41 : e4 1 = outerPlanCosineRightStart := by simp [e4]
  have he50 : e5 0 = outerPlanCosineRightStart :=
    outerPlanReverseSquareEndpoint_zero _ _ _
  have he5n : e5 cells = right :=
    outerPlanReverseSquareEndpoint_last _ _ hcells'
  have hs1' : outerPlanSegmentSafe C e1 cells = true := by
    simpa [e1, left] using hs1
  have hs2' : outerPlanSegmentSafe C e2 1 = true := by
    simpa [outerPlanSegmentSafe, e2] using hs2
  have hs3' : outerPlanSegmentSafe C e3 1 = true := by
    simpa [outerPlanSegmentSafe, e3] using hs3
  have hs4' : outerPlanSegmentSafe C e4 1 = true := by
    simpa [outerPlanSegmentSafe, e4] using hs4
  have hs5' : outerPlanSegmentSafe C e5 cells = true := by
    simpa [e5, right] using hs5
  have h1raw := outerPlanSegmentIntegral_le e1 cells
    hgeometry hL hLb hs1'
  rw [he10, he1n] at h1raw
  have h2raw := outerPlanSegmentIntegral_le e2 1
    hgeometry hL hLb hs2'
  rw [he20, he21] at h2raw
  have h3raw := outerPlanSegmentIntegral_le e3 1
    hgeometry hL hLb hs3'
  rw [he30, he31] at h3raw
  have h4raw := outerPlanSegmentIntegral_le e4 1
    hgeometry hL hLb hs4'
  rw [he40, he41] at h4raw
  have h5raw := outerPlanSegmentIntegral_le e5 cells
    hgeometry hL hLb hs5'
  rw [he50, he5n] at h5raw
  rcases geometryCheck_sound hgeometry with
    ⟨hlo, hlohi, _hratio, hcutoff, hcut, _⟩
  have hb : (0 : ℝ) < C.hi := by exact_mod_cast hlo.trans_le hlohi
  have hleftCast :
      (left : ℝ) / (2 * (C.hi : ℝ)) = (C.cutoff : ℝ) := by
    dsimp only [left]
    push_cast
    field_simp [hb.ne']
  have hrightCast :
      (right : ℝ) / (2 * (C.hi : ℝ)) = (C.bandwidth : ℝ) := by
    dsimp only [right]
    push_cast
    field_simp [hb.ne']
  rw [hleftCast] at h1raw
  rw [hrightCast] at h5raw
  let b1 : ℝ := (outerPlanCubicEnd : ℝ) / (2 * (C.hi : ℝ))
  let b2 : ℝ := 4 / (2 * (C.hi : ℝ))
  let b3 : ℝ := (outerPlanCosineLeftEnd : ℝ) / (2 * (C.hi : ℝ))
  let b4 : ℝ := (outerPlanCosineRightStart : ℝ) / (2 * (C.hi : ℝ))
  have h1 :
      (∫ u : ℝ in (C.cutoff : ℝ)..b1,
        ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
          tyurinProductEnvelope L u) ≤
        (outerPlanSegmentUpper C e1 cells : ℝ) := by
    simpa [b1] using h1raw
  have h2 :
      (∫ u : ℝ in b1..b2,
        ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
          tyurinProductEnvelope L u) ≤
        (outerPlanSegmentUpper C e2 1 : ℝ) := by
    simpa [b1, b2] using h2raw
  have h3 :
      (∫ u : ℝ in b2..b3,
        ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
          tyurinProductEnvelope L u) ≤
        (outerPlanSegmentUpper C e3 1 : ℝ) := by
    simpa [b2, b3] using h3raw
  have h4 :
      (∫ u : ℝ in b3..b4,
        ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
          tyurinProductEnvelope L u) ≤
        (outerPlanSegmentUpper C e4 1 : ℝ) := by
    simpa [b3, b4] using h4raw
  have h5 :
      (∫ u : ℝ in b4..(C.bandwidth : ℝ),
        ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
          tyurinProductEnvelope L u) ≤
        (outerPlanSegmentUpper C e5 cells : ℝ) := by
    simpa [b4] using h5raw
  have h01 : (C.cutoff : ℝ) ≤ b1 := by
    have hq : left ≤ outerPlanCubicEnd := of_decide_eq_true hleft
    have hcast := (Rat.cast_le (K := ℝ)).mpr hq
    have hdiv := div_le_div_of_nonneg_right hcast
      (by positivity : 0 ≤ 2 * (C.hi : ℝ))
    rw [hleftCast] at hdiv
    simpa [b1] using hdiv
  have h12 : b1 ≤ b2 := by
    dsimp only [b1, b2]
    apply div_le_div_of_nonneg_right
    · norm_num [outerPlanCubicEnd]
    · positivity
  have h23 : b2 ≤ b3 := by
    dsimp only [b2, b3]
    apply div_le_div_of_nonneg_right
    · norm_num [outerPlanCosineLeftEnd]
    · positivity
  have h34 : b3 ≤ b4 := by
    dsimp only [b3, b4]
    apply div_le_div_of_nonneg_right
    · norm_num [outerPlanCosineLeftEnd, outerPlanCosineRightStart]
    · positivity
  have h45 : b4 ≤ (C.bandwidth : ℝ) := by
    have hq : outerPlanCosineRightStart ≤ right :=
      of_decide_eq_true hright
    have hcast := (Rat.cast_le (K := ℝ)).mpr hq
    have hdiv := div_le_div_of_nonneg_right hcast
      (by positivity : 0 ≤ 2 * (C.hi : ℝ))
    rw [hrightCast] at hdiv
    simpa [b4] using hdiv
  let f : ℝ → ℝ := fun u =>
    ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
      tyurinProductEnvelope L u
  have hLpos : 0 < L := (by exact_mod_cast hlo : (0 : ℝ) < C.lo).trans_le hL
  have hcutoffReal : (0 : ℝ) < C.cutoff := by exact_mod_cast hcutoff
  have hbandReal : (0 : ℝ) < C.bandwidth := by
    exact_mod_cast hcutoff.trans_le hcut
  have hcutReal : (C.cutoff : ℝ) ≤ C.bandwidth := by exact_mod_cast hcut
  have hglobal : IntervalIntegrable f volume
      (C.cutoff : ℝ) (C.bandwidth : ℝ) :=
    intervalIntegrable_tyurinOuterIntegrand hLpos hcutoffReal
      hbandReal hcutReal
  have hsub (a b : ℝ) (ha : (C.cutoff : ℝ) ≤ a)
      (hb' : b ≤ (C.bandwidth : ℝ)) (hab : a ≤ b) :
      IntervalIntegrable f volume a b := by
    apply IntervalIntegrable.mono_set hglobal
    rw [uIcc_of_le hab, uIcc_of_le hcutReal]
    intro u hu
    exact ⟨ha.trans hu.1, hu.2.trans hb'⟩
  have hi1 := hsub (C.cutoff : ℝ) b1 le_rfl
    (h12.trans (h23.trans (h34.trans h45))) h01
  have hi2 := hsub b1 b2 h01
    (h23.trans (h34.trans h45)) h12
  have hi3 := hsub b2 b3 (h01.trans h12)
    (h34.trans h45) h23
  have hi4 := hsub b3 b4 (h01.trans (h12.trans h23)) h45 h34
  have hi5 := hsub b4 (C.bandwidth : ℝ)
    (h01.trans (h12.trans (h23.trans h34))) le_rfl h45
  have hsplit :
      (∫ u : ℝ in (C.cutoff : ℝ)..(C.bandwidth : ℝ), f u) =
        (∫ u : ℝ in (C.cutoff : ℝ)..b1, f u) +
        (∫ u : ℝ in b1..b2, f u) +
        (∫ u : ℝ in b2..b3, f u) +
        (∫ u : ℝ in b3..b4, f u) +
        (∫ u : ℝ in b4..(C.bandwidth : ℝ), f u) := by
    have h12i := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have h123i := intervalIntegral.integral_add_adjacent_intervals
      (hi1.trans hi2) hi3
    have h1234i := intervalIntegral.integral_add_adjacent_intervals
      ((hi1.trans hi2).trans hi3) hi4
    have hall := intervalIntegral.integral_add_adjacent_intervals
      (((hi1.trans hi2).trans hi3).trans hi4) hi5
    calc
      (∫ u : ℝ in (C.cutoff : ℝ)..(C.bandwidth : ℝ), f u) =
          (∫ u : ℝ in (C.cutoff : ℝ)..b4, f u) +
            ∫ u : ℝ in b4..(C.bandwidth : ℝ), f u := hall.symm
      _ = ((∫ u : ℝ in (C.cutoff : ℝ)..b3, f u) +
            ∫ u : ℝ in b3..b4, f u) +
            ∫ u : ℝ in b4..(C.bandwidth : ℝ), f u := by rw [h1234i]
      _ = (((∫ u : ℝ in (C.cutoff : ℝ)..b2, f u) +
            ∫ u : ℝ in b2..b3, f u) +
            ∫ u : ℝ in b3..b4, f u) +
            ∫ u : ℝ in b4..(C.bandwidth : ℝ), f u := by rw [h123i]
      _ = ((((∫ u : ℝ in (C.cutoff : ℝ)..b1, f u) +
            ∫ u : ℝ in b1..b2, f u) +
            ∫ u : ℝ in b2..b3, f u) +
            ∫ u : ℝ in b3..b4, f u) +
            ∫ u : ℝ in b4..(C.bandwidth : ℝ), f u := by rw [h12i]
  rw [hsplit]
  have htotal := add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5
  unfold outerPlanUpper
  dsimp only
  push_cast
  change _ ≤
    (outerPlanSegmentUpper C e1 cells : ℝ) +
      (outerPlanSegmentUpper C e2 1 : ℝ) +
      (outerPlanSegmentUpper C e3 1 : ℝ) +
      (outerPlanSegmentUpper C e4 1 : ℝ) +
      (outerPlanSegmentUpper C e5 cells : ℝ)
  exact htotal

/-- A cell certificate from any analytic core bound and the new outer plan. -/
theorem cellCertified_of_coreIntegralBound_outerPlan
    {C : Cell} {coreBound : ℚ} {cells : ℕ}
    (hg : geometryCheck C = true)
    (hcoreBound : ∀ {L : ℝ}, (C.lo : ℝ) ≤ L → L ≤ (C.hi : ℝ) →
      (∫ u : ℝ in 0..(C.cutoff : ℝ),
        ‖scaledPrawitzKernel (C.bandwidth : ℝ) u‖ *
          min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)) ≤
        (coreBound : ℝ))
    (hplan : outerPlanCheck C cells = true)
    (hfinal : 2 * coreBound + 2 * outerPlanUpper C cells +
      gaussianBudgetUpper C < cellTarget C) :
    CellCertified C := by
  rcases geometryCheck_sound hg with ⟨hlo, _, _, hcut, hcutU, _⟩
  refine ⟨by exact_mod_cast hcut, by exact_mod_cast hcutU, ?_⟩
  intro L hL hLb
  have hLp : 0 < L :=
    (by exact_mod_cast hlo : (0 : ℝ) < C.lo).trans_le hL
  have hcore := hcoreBound hL hLb
  have houter := outerIntegral_le_outerPlan hg hL hLb hplan
  have hgauss := gaussianSharpClosedBudget_le hg
  have hfin :
      2 * (coreBound : ℝ) + 2 * (outerPlanUpper C cells : ℝ) +
          (gaussianBudgetUpper C : ℝ) < (cellTarget C : ℝ) := by
    exact_mod_cast hfinal
  have htarg : (cellTarget C : ℝ) ≤ (3 / 5 : ℝ) * L := by
    unfold cellTarget
    push_cast
    gcongr
  unfold tyurinRationalDStar
  rw [div_lt_iff₀ hLp]
  nlinarith

/-- Production bridge for the first twenty cells' closed-core bound. -/
theorem cellCertified_of_closedCore_outerPlan
    {C : Cell} {cells : ℕ}
    (hg : geometryCheck C = true)
    (hs : C.cutoff * C.rootHi ≤ 5 / 3)
    (hc0 : 0 ≤ (varianceCapInterval C).upperRat)
    (hc1 : (varianceCapInterval C).upperRat < 1)
    (hplan : outerPlanCheck C cells = true)
    (hfinal : 2 * closedCoreIntegral C + 2 * outerPlanUpper C cells +
      gaussianBudgetUpper C < cellTarget C) :
    CellCertified C := by
  apply cellCertified_of_coreIntegralBound_outerPlan hg _ hplan hfinal
  intro L hL hLb
  exact coreIntegral_le_closedCoreIntegral hg hL hLb hs hc0 hc1

/-- Production bridge for the last four cells' crossing-core bound. -/
theorem cellCertified_of_crossingCore_outerPlan
    {C : Cell} {cells : ℕ}
    (hg : geometryCheck C = true)
    (hc0 : 0 ≤ crossingCoreCap C)
    (hc1 : crossingCoreCap C < 1)
    (hplan : outerPlanCheck C cells = true)
    (hfinal : 2 * crossingCoreIntegral C + 2 * outerPlanUpper C cells +
      gaussianBudgetUpper C < cellTarget C) :
    CellCertified C := by
  apply cellCertified_of_coreIntegralBound_outerPlan hg _ hplan hfinal
  intro L hL hLb
  exact coreIntegral_le_crossingCoreIntegral hg hL hLb hc0 hc1

end CertifiedJL.TyurinModerate
