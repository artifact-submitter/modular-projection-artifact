/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Data.ThresholdNearChordNumeric128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Soundness.ThresholdNearCoarseSoundness128

/-! # Soundness of the power-chord near-band interval evaluator -/

namespace CertifiedJL
namespace ThresholdNearChord128

open ThresholdNearCoarse128

noncomputable def semanticAFreq (a : ℝ) : ℝ := Real.sqrt ((23 / 20) * a)

noncomputable def semanticBFreq (x a y : ℝ) : ℝ :=
  Real.sqrt ((23 / 20) * (x - a) * y)

noncomputable def semanticMomentTwo (x a y : ℝ) : ℝ :=
  let A := semanticAFreq a
  let B := semanticBFreq x a y
  (1 / 4) *
    (1 + Real.exp (-2 * A ^ 2) + Real.exp (-2 * B ^ 2) +
      (1 / 2) *
        (Real.exp (-2 * (A + B) ^ 2) + Real.exp (-2 * (A - B) ^ 2)))

noncomputable def semanticMixedMoment (x a y multiplier : ℝ) : ℝ :=
  let A := semanticAFreq a
  let B := semanticBFreq x a y
  let C := multiplier * B
  (1 / 2) * Real.exp (-(1 / 2) * C ^ 2) +
    (1 / 4) *
      (Real.exp (-(1 / 2) * (C + 2 * A) ^ 2) +
        Real.exp (-(1 / 2) * (C - 2 * A) ^ 2))

noncomputable def semanticMomentFour (x a y : ℝ) : ℝ :=
  (3 / 8) * ((1 / 2) * (1 + Real.exp (-2 * semanticAFreq a ^ 2))) +
    (1 / 2) * semanticMixedMoment x a y 2 +
    (1 / 8) * semanticMixedMoment x a y 4

noncomputable def semanticChordCentral (x a y : ℝ) : ℝ :=
  (2 - 1 / y) * semanticMomentTwo x a y +
    (1 / y - 1) * semanticMomentFour x a y

noncomputable def semanticEnvelope (x a y : ℝ) : ℝ :=
  semanticChordCentral x a y +
    (ThresholdNearCoarse128.semanticInactiveTail x a +
      ThresholdNearCoarse128.semanticActiveTail x a) / 2

structure Safe (cell : Cell) : Prop where
  aNonneg : 0 ≤ (aInterval cell).lo
  aFreqSqNonneg : 0 ≤ (aFreqSq cell).lo
  bSqNonneg : 0 ≤ (bFreqSq cell).lo
  yPos : 0 < (yInterval cell).lo
  negExp : ∀ I ∈ [
      rat 2 * powNat (aFreq cell) 2,
      rat 2 * powNat (bFreq cell) 2,
      rat 2 * powNat (aFreq cell + bFreq cell) 2,
      rat 2 * powNat (aFreq cell - bFreq cell) 2,
      rat (1 / 2) * powNat (rat 2 * bFreq cell) 2,
      rat (1 / 2) * powNat (rat 2 * bFreq cell + rat 2 * aFreq cell) 2,
      rat (1 / 2) * powNat (rat 2 * bFreq cell - rat 2 * aFreq cell) 2,
      rat (1 / 2) * powNat (rat 4 * bFreq cell) 2,
      rat (1 / 2) * powNat (rat 4 * bFreq cell + rat 2 * aFreq cell) 2,
      rat (1 / 2) * powNat (rat 4 * bFreq cell - rat 2 * aFreq cell) 2],
      (-I).upperRat ≤ 1

theorem chordSafeCheck_sound {cell : Cell}
    (h : chordSafeCheck cell = true) : Safe cell := by
  have h' := of_decide_eq_true (by simpa only [chordSafeCheck] using h)
  exact ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩

theorem contains_rat (x : ℚ) : (rat x).Contains (x : ℝ) :=
  ThresholdNearCoarse128.contains_rat x

theorem contains_div {I J : DInterval} {x y : ℝ}
    (hJ : 0 < J.lo) (hx : I.Contains x) (hy : J.Contains y) :
    (div I J).Contains (x / y) :=
  ThresholdNearCoarse128.contains_div hJ hx hy

theorem contains_powNat {I : DInterval} {x : ℝ}
    (hx : I.Contains x) (n : ℕ) :
    (powNat I n).Contains (x ^ n) :=
  ThresholdNearCoarse128.contains_powNat hx n

theorem contains_expUpper {I : DInterval} {x : ℝ}
    (hx : I.Contains x) (hupper : I.upperRat ≤ 1) :
    (expUpper I).Contains (Real.exp x) :=
  ThresholdNearCoarse128.contains_expUpper hx hupper

/-- One checked chord cell separately encloses the retained central moment. -/
theorem chordCentral_contains_semantic (cell : Cell) {x a y : ℝ}
    (hcell : (cell.xLower : ℝ) ≤ x ∧ x ≤ cell.xUpper ∧
      (cell.aLower : ℝ) ≤ a ∧ a ≤ cell.aUpper ∧
      (cell.yLower : ℝ) ≤ y ∧ y ≤ cell.yUpper)
    (hsafe : Safe cell) :
    (chordCentral cell).Contains (semanticChordCentral x a y) := by
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
  have hExpNeg {I : DInterval} {z : ℝ}
      (hI : I.Contains z)
      (hmem : I ∈ [
        rat 2 * powNat (aFreq cell) 2,
        rat 2 * powNat (bFreq cell) 2,
        rat 2 * powNat (aFreq cell + bFreq cell) 2,
        rat 2 * powNat (aFreq cell - bFreq cell) 2,
        rat (1 / 2) * powNat (rat 2 * bFreq cell) 2,
        rat (1 / 2) * powNat (rat 2 * bFreq cell + rat 2 * aFreq cell) 2,
        rat (1 / 2) * powNat (rat 2 * bFreq cell - rat 2 * aFreq cell) 2,
        rat (1 / 2) * powNat (rat 4 * bFreq cell) 2,
        rat (1 / 2) * powNat (rat 4 * bFreq cell + rat 2 * aFreq cell) 2,
        rat (1 / 2) * powNat (rat 4 * bFreq cell - rat 2 * aFreq cell) 2]) :
      (expNeg I).Contains (Real.exp (-z)) := by
    exact contains_expUpper (Interval.contains_neg hI) (hsafe.negExp I hmem)
  have heA : (expNeg (rat 2 * powNat (aFreq cell) 2)).Contains
      (Real.exp (-2 * semanticAFreq a ^ 2)) := by
    have hI : (rat 2 * powNat (aFreq cell) 2).Contains
        (2 * semanticAFreq a ^ 2) := by
      exact Interval.contains_mul (contains_rat 2) (contains_powNat hAF 2)
    convert hExpNeg (I := rat 2 * powNat (aFreq cell) 2)
      (z := 2 * semanticAFreq a ^ 2) hI (by simp) using 1 <;> ring
  have heB : (expNeg (rat 2 * powNat (bFreq cell) 2)).Contains
      (Real.exp (-2 * semanticBFreq x a y ^ 2)) := by
    have hI : (rat 2 * powNat (bFreq cell) 2).Contains
        (2 * semanticBFreq x a y ^ 2) := by
      exact Interval.contains_mul (contains_rat 2) (contains_powNat hBF 2)
    convert hExpNeg (I := rat 2 * powNat (bFreq cell) 2)
      (z := 2 * semanticBFreq x a y ^ 2) hI (by simp) using 1 <;> ring
  have hplus := Interval.contains_add hAF hBF
  have hminus := Interval.contains_sub hAF hBF
  have hePlus :
      (expNeg (rat 2 * powNat (aFreq cell + bFreq cell) 2)).Contains
        (Real.exp (-2 * (semanticAFreq a + semanticBFreq x a y) ^ 2)) := by
    convert hExpNeg
      (I := rat 2 * powNat (aFreq cell + bFreq cell) 2)
      (z := 2 * (semanticAFreq a + semanticBFreq x a y) ^ 2)
      (Interval.contains_mul (contains_rat 2) (contains_powNat hplus 2))
      (by simp) using 1 <;> ring
  have heMinus :
      (expNeg (rat 2 * powNat (aFreq cell - bFreq cell) 2)).Contains
        (Real.exp (-2 * (semanticAFreq a - semanticBFreq x a y) ^ 2)) := by
    convert hExpNeg
      (I := rat 2 * powNat (aFreq cell - bFreq cell) 2)
      (z := 2 * (semanticAFreq a - semanticBFreq x a y) ^ 2)
      (Interval.contains_mul (contains_rat 2) (contains_powNat hminus 2))
      (by simp) using 1 <;> ring
  have hM2 : (momentTwo cell).Contains (semanticMomentTwo x a y) := by
    simpa [momentTwo, semanticMomentTwo] using Interval.contains_mul
      (contains_rat (1 / 4))
      (Interval.contains_add
        (Interval.contains_add
          (Interval.contains_add (contains_rat 1) heA) heB)
        (Interval.contains_mul (contains_rat (1 / 2))
          (Interval.contains_add hePlus heMinus)))
  have hmix (m : ℚ)
      (hmul : (rat m * bFreq cell).Contains
        ((m : ℝ) * semanticBFreq x a y))
      (hmem0 : rat (1 / 2) * powNat (rat m * bFreq cell) 2 ∈ [
        rat 2 * powNat (aFreq cell) 2, rat 2 * powNat (bFreq cell) 2,
        rat 2 * powNat (aFreq cell + bFreq cell) 2,
        rat 2 * powNat (aFreq cell - bFreq cell) 2,
        rat (1 / 2) * powNat (rat 2 * bFreq cell) 2,
        rat (1 / 2) * powNat (rat 2 * bFreq cell + rat 2 * aFreq cell) 2,
        rat (1 / 2) * powNat (rat 2 * bFreq cell - rat 2 * aFreq cell) 2,
        rat (1 / 2) * powNat (rat 4 * bFreq cell) 2,
        rat (1 / 2) * powNat (rat 4 * bFreq cell + rat 2 * aFreq cell) 2,
        rat (1 / 2) * powNat (rat 4 * bFreq cell - rat 2 * aFreq cell) 2])
      (hmemPlus : rat (1 / 2) *
          powNat (rat m * bFreq cell + rat 2 * aFreq cell) 2 ∈ [
        rat 2 * powNat (aFreq cell) 2, rat 2 * powNat (bFreq cell) 2,
        rat 2 * powNat (aFreq cell + bFreq cell) 2,
        rat 2 * powNat (aFreq cell - bFreq cell) 2,
        rat (1 / 2) * powNat (rat 2 * bFreq cell) 2,
        rat (1 / 2) * powNat (rat 2 * bFreq cell + rat 2 * aFreq cell) 2,
        rat (1 / 2) * powNat (rat 2 * bFreq cell - rat 2 * aFreq cell) 2,
        rat (1 / 2) * powNat (rat 4 * bFreq cell) 2,
        rat (1 / 2) * powNat (rat 4 * bFreq cell + rat 2 * aFreq cell) 2,
        rat (1 / 2) * powNat (rat 4 * bFreq cell - rat 2 * aFreq cell) 2])
      (hmemMinus : rat (1 / 2) *
          powNat (rat m * bFreq cell - rat 2 * aFreq cell) 2 ∈ [
        rat 2 * powNat (aFreq cell) 2, rat 2 * powNat (bFreq cell) 2,
        rat 2 * powNat (aFreq cell + bFreq cell) 2,
        rat 2 * powNat (aFreq cell - bFreq cell) 2,
        rat (1 / 2) * powNat (rat 2 * bFreq cell) 2,
        rat (1 / 2) * powNat (rat 2 * bFreq cell + rat 2 * aFreq cell) 2,
        rat (1 / 2) * powNat (rat 2 * bFreq cell - rat 2 * aFreq cell) 2,
        rat (1 / 2) * powNat (rat 4 * bFreq cell) 2,
        rat (1 / 2) * powNat (rat 4 * bFreq cell + rat 2 * aFreq cell) 2,
        rat (1 / 2) * powNat (rat 4 * bFreq cell - rat 2 * aFreq cell) 2]) :
      (mixedMoment cell m).Contains (semanticMixedMoment x a y m) := by
    let C : ℝ := (m : ℝ) * semanticBFreq x a y
    have htwoA := Interval.contains_mul (contains_rat 2) hAF
    have hCplus := Interval.contains_add hmul htwoA
    have hCminus := Interval.contains_sub hmul htwoA
    have he0 := hExpNeg
      (Interval.contains_mul (contains_rat (1 / 2)) (contains_powNat hmul 2)) hmem0
    have hep := hExpNeg
      (Interval.contains_mul (contains_rat (1 / 2)) (contains_powNat hCplus 2))
      hmemPlus
    have hem := hExpNeg
      (Interval.contains_mul (contains_rat (1 / 2)) (contains_powNat hCminus 2))
      hmemMinus
    simpa [mixedMoment, semanticMixedMoment, C] using Interval.contains_add
      (Interval.contains_mul (contains_rat (1 / 2)) he0)
      (Interval.contains_mul (contains_rat (1 / 4))
        (Interval.contains_add hep hem))
  have hmix2 : (mixedMoment cell 2).Contains
      (semanticMixedMoment x a y 2) := by
    apply hmix 2 (Interval.contains_mul (contains_rat 2) hBF) <;> simp
  have hmix4 : (mixedMoment cell 4).Contains
      (semanticMixedMoment x a y 4) := by
    apply hmix 4 (Interval.contains_mul (contains_rat 4) hBF) <;> simp
  have hM4 : (momentFour cell).Contains (semanticMomentFour x a y) := by
    simpa [momentFour, semanticMomentFour] using Interval.contains_add
      (Interval.contains_add
        (Interval.contains_mul (contains_rat (3 / 8))
          (Interval.contains_mul (contains_rat (1 / 2))
            (Interval.contains_add (contains_rat 1) heA)))
        (Interval.contains_mul (contains_rat (1 / 2)) hmix2))
      (Interval.contains_mul (contains_rat (1 / 8)) hmix4)
  have hinvY : (inverseY cell).Contains (1 / y) :=
    contains_div hsafe.yPos (by simpa using contains_rat (1 : ℚ)) hy
  have hcentral : (chordCentral cell).Contains
      (semanticChordCentral x a y) := by
    simpa [chordCentral, semanticChordCentral] using Interval.contains_add
      (Interval.contains_mul
        (Interval.contains_sub (contains_rat 2) hinvY) hM2)
      (Interval.contains_mul
        (Interval.contains_sub hinvY (contains_rat 1)) hM4)
  exact hcentral

/-- One checked cell encloses the complete real power-chord envelope. -/
theorem envelope_contains_semantic (cell : Cell) {x a y : ℝ}
    (hcell : (cell.xLower : ℝ) ≤ x ∧ x ≤ cell.xUpper ∧
      (cell.aLower : ℝ) ≤ a ∧ a ≤ cell.aUpper ∧
      (cell.yLower : ℝ) ≤ y ∧ y ≤ cell.yUpper)
    (hsafe : Safe cell)
    (hcoarseSafe : ThresholdNearCoarse128.Safe (coarseCell cell)) :
    (envelope cell).Contains (semanticEnvelope x a y) := by
  have hcentral := chordCentral_contains_semantic cell hcell hsafe
  have htail := ThresholdNearCoarse128.conditionedTail_contains_semantic
    (coarseCell cell)
    (x := x) (a := a)
    (by simpa [coarseCell] using
      (And.intro hcell.1 (And.intro hcell.2.1
        (And.intro hcell.2.2.1 hcell.2.2.2.1))))
    hcoarseSafe
  have htail' :
      (rat (1 / 2) * (inactiveTail cell + activeTail cell)).Contains
        ((ThresholdNearCoarse128.semanticInactiveTail x a +
          ThresholdNearCoarse128.semanticActiveTail x a) / 2) := by
    simpa [inactiveTail, activeTail, coarseCell, rat,
      ThresholdNearCoarse128.conditionedTail] using htail
  simpa [envelope, semanticEnvelope] using Interval.contains_add hcentral htail'

end ThresholdNearChord128
end CertifiedJL
