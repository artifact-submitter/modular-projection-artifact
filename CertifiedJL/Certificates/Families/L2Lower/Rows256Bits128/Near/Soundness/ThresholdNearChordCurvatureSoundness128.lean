/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Soundness.ThresholdNearChordCurvature128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Data.ThresholdNearChordCurvatureNumeric128

/-! # Soundness of the Holder-weight curvature evaluator -/

namespace CertifiedJL
namespace ThresholdNearChordCurvature128

open ThresholdNearChord128

private theorem lowerRat_le_of_contains {p : ℕ} {I : Interval p} {z : ℝ}
    (h : I.Contains z) : (I.lowerRat : ℝ) ≤ z := by
  simpa only [Interval.lowerRat, Dyadic.cast_toRat] using h.1

theorem chordCentralSecond_contains_semantic
    (cell : Cell) {x a y : ℝ}
    (hcell : (cell.xLower : ℝ) ≤ x ∧ x ≤ cell.xUpper ∧
      (cell.aLower : ℝ) ≤ a ∧ a ≤ cell.aUpper ∧
      (cell.yLower : ℝ) ≤ y ∧ y ≤ cell.yUpper)
    (hsafe : ThresholdNearChord128.Safe cell)
    (hcurvSafe : ∀ I ∈ curvatureExponentIntervals cell,
      (-I).upperRat ≤ 1) :
    (chordCentralSecond cell).Contains
      (ThresholdNearChord128.semanticChordCentralSecond x a y) := by
  have hx : (xInterval cell).Contains x :=
    Interval.contains_enclose ⟨hcell.1, hcell.2.1⟩
  have ha : (aInterval cell).Contains a :=
    Interval.contains_enclose ⟨hcell.2.2.1, hcell.2.2.2.1⟩
  have hy : (yInterval cell).Contains y :=
    Interval.contains_enclose ⟨hcell.2.2.2.2.1, hcell.2.2.2.2.2⟩
  have hAFSq : (aFreqSq cell).Contains ((23 / 20 : ℝ) * a) := by
    simpa [aFreqSq] using Interval.contains_mul (contains_rat (23 / 20)) ha
  have hXsubA : (xInterval cell - aInterval cell).Contains (x - a) :=
    Interval.contains_sub hx ha
  have hBFSq : (bFreqSq cell).Contains ((23 / 20 : ℝ) * (x - a) * y) := by
    simpa [bFreqSq] using Interval.contains_mul
      (Interval.contains_mul (contains_rat (23 / 20)) hXsubA) hy
  have hAF : (aFreq cell).Contains (semanticAFreq a) := by
    simpa [aFreq, semanticAFreq] using
      Interval.contains_sqrt hsafe.aFreqSqNonneg hAFSq
  have hBF : (bFreq cell).Contains (semanticBFreq x a y) := by
    simpa [bFreq, semanticBFreq] using
      Interval.contains_sqrt hsafe.bSqNonneg hBFSq
  have hinvY : (inverseY cell).Contains (1 / y) :=
    contains_div hsafe.yPos (by simpa using contains_rat (1 : ℚ)) hy
  have hypos : 0 < y := by
    have hlo : 0 < Dyadic.toReal ThresholdNearCoarse128.precision
        (yInterval cell).lo := by
      unfold Dyadic.toReal
      apply div_pos
      · exact_mod_cast hsafe.yPos
      · exact_mod_cast Dyadic.scale_pos ThresholdNearCoarse128.precision
    exact hlo.trans_le hy.1
  have hmode (m : ℚ) (offsetI : DInterval) (offset : ℝ)
      (hoffset : offsetI.Contains offset)
      (hupper : (-(rat (1 / 2) *
        powNat (rat m * bFreq cell + offsetI) 2)).upperRat ≤ 1) :
      (mode cell m offsetI).Contains
          (semanticMode x a y m offset) ∧
        (modePrime cell m offsetI).Contains
          (semanticModePrime x a y m offset) ∧
        (modeSecond cell m offsetI).Contains
          (semanticModeSecond x a y m offset) := by
    have hmB : (rat m * bFreq cell).Contains
        ((m : ℝ) * semanticBFreq x a y) :=
      Interval.contains_mul (contains_rat m) hBF
    have hlinear := Interval.contains_add hmB hoffset
    have harg : (rat (1 / 2) *
        powNat (rat m * bFreq cell + offsetI) 2).Contains
        ((1 / 2 : ℝ) *
          ((m : ℝ) * semanticBFreq x a y + offset) ^ 2) :=
      Interval.contains_mul (by simpa using contains_rat (1 / 2))
        (contains_powNat hlinear 2)
    have hM : (mode cell m offsetI).Contains
        (semanticMode x a y m offset) := by
      have he := contains_expUpper (Interval.contains_neg harg) hupper
      have he' : (mode cell m offsetI).Contains
          (Real.exp (-((1 / 2 : ℝ) *
            ((m : ℝ) * semanticBFreq x a y + offset) ^ 2))) := by
        simpa only [mode, expNeg] using he
      convert he' using 1
      dsimp [semanticMode]
      congr 2
      ring
    have hnum := Interval.contains_mul hmB hlinear
    have hquot := contains_div hsafe.yPos hnum hy
    have hP : (modePrime cell m offsetI).Contains
        (semanticModePrime x a y m offset) := by
      have hp := Interval.contains_mul
        (Interval.contains_mul (by simpa using contains_rat (-(1 / 2))) hM) hquot
      convert hp using 1 <;>
        norm_num [modePrime, semanticModePrime] <;>
        field_simp [hypos.ne']
    have hsum := Interval.contains_add (contains_powNat hnum 2)
      (Interval.contains_mul hmB hoffset)
    have hquot2 := contains_div hsafe.yPos
      (contains_div hsafe.yPos hsum hy) hy
    have hS : (modeSecond cell m offsetI).Contains
        (semanticModeSecond x a y m offset) := by
      have hs := Interval.contains_mul
        (Interval.contains_mul (by simpa using contains_rat (1 / 4)) hM) hquot2
      convert hs using 1 <;>
        norm_num [modeSecond, semanticModeSecond] <;>
        field_simp [hypos.ne']
    exact ⟨hM, hP, hS⟩
  have hzero : (rat 0).Contains (0 : ℝ) := by simpa using contains_rat 0
  have htwoA : (rat 2 * aFreq cell).Contains (2 * semanticAFreq a) :=
    Interval.contains_mul (contains_rat 2) hAF
  have hnegTwoA : (-(rat 2 * aFreq cell)).Contains (-2 * semanticAFreq a) := by
    simpa using Interval.contains_neg htwoA
  have hm20 := hmode 2 (rat 0) 0 hzero
    (hcurvSafe _ (by simp [curvatureExponentIntervals]))
  have hm2p := hmode 2 (rat 2 * aFreq cell) (2 * semanticAFreq a) htwoA
    (hcurvSafe _ (by simp [curvatureExponentIntervals]))
  have hm2m := hmode 2 (-(rat 2 * aFreq cell)) (-2 * semanticAFreq a) hnegTwoA
    (hcurvSafe _ (by simp [curvatureExponentIntervals]))
  have hm40 := hmode 4 (rat 0) 0 hzero
    (hcurvSafe _ (by simp [curvatureExponentIntervals]))
  have hm4p := hmode 4 (rat 2 * aFreq cell) (2 * semanticAFreq a) htwoA
    (hcurvSafe _ (by simp [curvatureExponentIntervals]))
  have hm4m := hmode 4 (-(rat 2 * aFreq cell)) (-2 * semanticAFreq a) hnegTwoA
    (hcurvSafe _ (by simp [curvatureExponentIntervals]))
  have hM2 : (momentTwoValue cell).Contains
      (semanticMomentTwo x a y) := by
    rw [semanticMomentTwo_eq_modes]
    have hExpA : (expNeg (rat 2 * powNat (aFreq cell) 2)).Contains
        (Real.exp (-2 * semanticAFreq a ^ 2)) := by
      change (expUpper (-(rat 2 * powNat (aFreq cell) 2))).Contains _
      convert (contains_expUpper
          (Interval.contains_neg
            (Interval.contains_mul (contains_rat 2) (contains_powNat hAF 2)))
          (hsafe.negExp _ (by simp))) using 1 <;> norm_num
    simpa [momentTwoValue] using Interval.contains_mul
      (contains_rat (1 / 4))
      (Interval.contains_add
        (Interval.contains_add
          (Interval.contains_add (contains_rat 1) hExpA) hm20.1)
        (Interval.contains_mul (contains_rat (1 / 2))
          (Interval.contains_add hm2p.1 hm2m.1)))
  have hM2p : (momentTwoPrime cell).Contains
      (semanticMomentTwoPrime x a y) := by
    simpa [momentTwoPrime, semanticMomentTwoPrime] using Interval.contains_mul
      (contains_rat (1 / 4))
      (Interval.contains_add hm20.2.1
        (Interval.contains_mul (contains_rat (1 / 2))
          (Interval.contains_add hm2p.2.1 hm2m.2.1)))
  have hM2s : (momentTwoSecond cell).Contains
      (semanticMomentTwoSecond x a y) := by
    simpa [momentTwoSecond, semanticMomentTwoSecond] using Interval.contains_mul
      (contains_rat (1 / 4))
      (Interval.contains_add hm20.2.2
        (Interval.contains_mul (contains_rat (1 / 2))
          (Interval.contains_add hm2p.2.2 hm2m.2.2)))
  have hmix (m : ℚ)
      (h0 : (mode cell m (rat 0)).Contains (semanticMode x a y m 0) ∧
        (modePrime cell m (rat 0)).Contains (semanticModePrime x a y m 0) ∧
        (modeSecond cell m (rat 0)).Contains (semanticModeSecond x a y m 0))
      (hp : (mode cell m (rat 2 * aFreq cell)).Contains
          (semanticMode x a y m (2 * semanticAFreq a)) ∧
        (modePrime cell m (rat 2 * aFreq cell)).Contains
          (semanticModePrime x a y m (2 * semanticAFreq a)) ∧
        (modeSecond cell m (rat 2 * aFreq cell)).Contains
          (semanticModeSecond x a y m (2 * semanticAFreq a)))
      (hm : (mode cell m (-(rat 2 * aFreq cell))).Contains
          (semanticMode x a y m (-2 * semanticAFreq a)) ∧
        (modePrime cell m (-(rat 2 * aFreq cell))).Contains
          (semanticModePrime x a y m (-2 * semanticAFreq a)) ∧
        (modeSecond cell m (-(rat 2 * aFreq cell))).Contains
          (semanticModeSecond x a y m (-2 * semanticAFreq a))) :
      (mixedMomentValue cell m).Contains (semanticMixedMoment x a y m) ∧
      (mixedMomentPrime cell m).Contains (semanticMixedMomentPrime x a y m) ∧
      (mixedMomentSecond cell m).Contains (semanticMixedMomentSecond x a y m) := by
    rw [semanticMixedMoment_eq_modes]
    exact ⟨(by
        simpa [mixedMomentValue] using Interval.contains_add
          (Interval.contains_mul (contains_rat (1 / 2)) h0.1)
          (Interval.contains_mul (contains_rat (1 / 4))
            (Interval.contains_add hp.1 hm.1))),
      (by
        simpa [mixedMomentPrime, semanticMixedMomentPrime] using Interval.contains_add
          (Interval.contains_mul (contains_rat (1 / 2)) h0.2.1)
          (Interval.contains_mul (contains_rat (1 / 4))
            (Interval.contains_add hp.2.1 hm.2.1))),
      (by
        simpa [mixedMomentSecond, semanticMixedMomentSecond] using Interval.contains_add
          (Interval.contains_mul (contains_rat (1 / 2)) h0.2.2)
          (Interval.contains_mul (contains_rat (1 / 4))
            (Interval.contains_add hp.2.2 hm.2.2)))⟩
  have hmix2 := hmix 2 hm20 hm2p hm2m
  have hmix4 := hmix 4 hm40 hm4p hm4m
  have hM4 : (momentFourValue cell).Contains
      (semanticMomentFour x a y) := by
    have hExpA : (expNeg (rat 2 * powNat (aFreq cell) 2)).Contains
        (Real.exp (-2 * semanticAFreq a ^ 2)) := by
      change (expUpper (-(rat 2 * powNat (aFreq cell) 2))).Contains _
      convert (contains_expUpper
          (Interval.contains_neg
            (Interval.contains_mul (contains_rat 2) (contains_powNat hAF 2)))
          (hsafe.negExp _ (by simp))) using 1 <;> norm_num
    simpa [momentFourValue, semanticMomentFour] using
      Interval.contains_add
        (Interval.contains_add
            (Interval.contains_mul (contains_rat (3 / 8))
            (Interval.contains_mul (contains_rat (1 / 2))
              (Interval.contains_add (contains_rat 1) hExpA)))
          (Interval.contains_mul (contains_rat (1 / 2)) hmix2.1))
        (Interval.contains_mul (contains_rat (1 / 8)) hmix4.1)
  have hM4p : (momentFourPrime cell).Contains
      (semanticMomentFourPrime x a y) := by
    simpa [momentFourPrime, semanticMomentFourPrime] using Interval.contains_add
      (Interval.contains_mul (contains_rat (1 / 2)) hmix2.2.1)
      (Interval.contains_mul (contains_rat (1 / 8)) hmix4.2.1)
  have hM4s : (momentFourSecond cell).Contains
      (semanticMomentFourSecond x a y) := by
    simpa [momentFourSecond, semanticMomentFourSecond] using Interval.contains_add
      (Interval.contains_mul (contains_rat (1 / 2)) hmix2.2.2)
      (Interval.contains_mul (contains_rat (1 / 8)) hmix4.2.2)
  have htwoInv2 := Interval.contains_mul
    (Interval.contains_mul (contains_rat 2) hinvY) hinvY
  have htwoInv3 := Interval.contains_mul htwoInv2 hinvY
  have hfinal := Interval.contains_sub
      (Interval.contains_add
        (Interval.contains_add
          (Interval.contains_mul
            (Interval.contains_sub (contains_rat 2) hinvY) hM2s)
          (Interval.contains_mul
            (Interval.contains_sub hinvY (contains_rat 1)) hM4s))
        (Interval.contains_mul
          htwoInv2
          (Interval.contains_sub hM2p hM4p)))
      (Interval.contains_mul
        htwoInv3
        (Interval.contains_sub hM2 hM4))
  change (chordCentralSecond cell).Contains _ at hfinal
  convert hfinal using 1
  dsimp [semanticChordCentralSecond]
  field_simp [hypos.ne'] <;> ring

theorem semanticChordCentralSecond_gt_neg_81_div_20_of_curvatureCheck
    (cell : Cell) {x a y : ℝ}
    (hcell : (cell.xLower : ℝ) ≤ x ∧ x ≤ cell.xUpper ∧
      (cell.aLower : ℝ) ≤ a ∧ a ≤ cell.aUpper ∧
      (cell.yLower : ℝ) ≤ y ∧ y ≤ cell.yUpper)
    (hcheck : curvatureCheck cell = true) :
    -(81 / 20 : ℝ) < semanticChordCentralSecond x a y := by
  have hc : (chordSafeCheck cell = true ∧
      curvatureExponentSafeCheck cell = true) ∧
      decide ((-(81 / 20) : ℚ) < (chordCentralSecond cell).lowerRat) = true := by
    simpa only [curvatureCheck, Bool.and_eq_true] using hcheck
  have hs := chordSafeCheck_sound hc.1.1
  have hcurvSafe : ∀ I ∈ curvatureExponentIntervals cell,
      (-I).upperRat ≤ 1 :=
    of_decide_eq_true (by simpa only [curvatureExponentSafeCheck] using hc.1.2)
  have hcontains := chordCentralSecond_contains_semantic cell hcell hs hcurvSafe
  have hlower := lowerRat_le_of_contains hcontains
  have hrat : (-(81 / 20) : ℚ) < (chordCentralSecond cell).lowerRat :=
    of_decide_eq_true hc.2
  have hratReal : (-(81 / 20) : ℝ) <
      ((chordCentralSecond cell).lowerRat : ℝ) := by
    have hcast : (((-(81 / 20) : ℚ) : ℝ)) <
        ((chordCentralSecond cell).lowerRat : ℝ) := Rat.cast_lt.mpr hrat
    norm_num at hcast ⊢
    exact hcast
  exact hratReal.trans_le hlower

end ThresholdNearChordCurvature128
end CertifiedJL
