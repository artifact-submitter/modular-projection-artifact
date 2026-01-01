/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Data.ThresholdNearCoarseNumeric128
import CertifiedJL.Arithmetic.Transcendental.Exponential.DyadicExp
import CertifiedJL.Arithmetic.Transcendental.Trigonometric.Pi
import CertifiedJL.Arithmetic.Interval.Reflection
import CertifiedJL.Arithmetic.Transcendental.SquareRoot.Sqrt

/-! # Soundness of the coarse near-band interval evaluator -/

namespace CertifiedJL
namespace ThresholdNearCoarse128

/-- Normalized total-plus-residual denominator. -/
noncomputable def semanticD (x a : ℝ) : ℝ := 1 + (23 / 10) * (x - a)

noncomputable def semanticT (x a : ℝ) : ℝ := (23 / 10) * a / semanticD x a

noncomputable def semanticTheta (x a : ℝ) : ℝ :=
  Real.exp (-(Real.pi ^ 2 / ((4 / 5) * semanticD x a)))

noncomputable def semanticCoarseCentral (x a : ℝ) : ℝ :=
  (1 + Real.exp (-(semanticT x a))) /
      (2 * Real.sqrt (semanticD x a)) *
    (1 + 2 * semanticTheta x a / (1 - semanticTheta x a ^ 3))

noncomputable def semanticRho (x a : ℝ) : ℝ :=
  Real.exp (-(207 / 10) / semanticD x a)

noncomputable def semanticInactiveTail (x a : ℝ) : ℝ :=
  2 * semanticRho x a / (1 - semanticRho x a ^ 3)

noncomputable def semanticM (a : ℝ) : ℝ := 3 / Real.sqrt a

noncomputable def semanticActiveTail (x a : ℝ) : ℝ :=
  let t := semanticT x a
  let M := semanticM a
  Real.exp (-t * (M - 1) ^ 2) /
      (1 - Real.exp (-t * (3 * M ^ 2 - 2 * M))) +
    Real.exp (-t * (M + 1) ^ 2) /
      (1 - Real.exp (-t * (3 * M ^ 2 + 2 * M)))

/-- Complete normalized envelope certified by this module. -/
noncomputable def semanticEnvelope (x a : ℝ) : ℝ :=
  semanticCoarseCentral x a +
    (semanticInactiveTail x a + semanticActiveTail x a) / 2

/-- Reflected sign premises used by the interval proof. -/
structure Safe (cell : Cell) : Prop where
  aNonneg : 0 ≤ (aInterval cell).lo
  aSqrtPos : 0 < (aInterval cell).sqrt.lo
  dPos : 0 < (dInterval cell).lo
  dSqrtPos : 0 < (dInterval cell).sqrt.lo
  negTExp : (-(tInterval cell)).upperRat ≤ 1
  thetaExp : (-(div (rat (5 / 4) * powNat piInterval 2)
    (dInterval cell))).upperRat ≤ 1
  thetaDen : 0 < (rat 1 - powNat (thetaInterval cell) 3).lo
  rhoExp : (-(div (rat (207 / 10)) (dInterval cell))).upperRat ≤ 1
  rhoDen : 0 < (rat 1 - powNat (rhoInterval cell) 3).lo
  activeMinusExp : (activeMinusExponent cell).upperRat ≤ 1
  activeMinusRatioExp : (activeMinusRatioExponent cell).upperRat ≤ 1
  activePlusExp : (activePlusExponent cell).upperRat ≤ 1
  activePlusRatioExp : (activePlusRatioExponent cell).upperRat ≤ 1
  activeMinusDen :
    0 < (rat 1 - expUpper (activeMinusRatioExponent cell)).lo
  activePlusDen :
    0 < (rat 1 - expUpper (activePlusRatioExponent cell)).lo

theorem safeCheck_sound {cell : Cell} (h : safeCheck cell = true) : Safe cell := by
  have h' := of_decide_eq_true (by simpa only [safeCheck] using h)
  exact ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2.1,
    h'.2.2.2.2.2.1, h'.2.2.2.2.2.2.1, h'.2.2.2.2.2.2.2.1,
    h'.2.2.2.2.2.2.2.2.1, h'.2.2.2.2.2.2.2.2.2.1,
    h'.2.2.2.2.2.2.2.2.2.2.1, h'.2.2.2.2.2.2.2.2.2.2.2.1,
    h'.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h'.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem contains_rat (x : ℚ) : (rat x).Contains (x : ℝ) :=
  Interval.contains_ofRat precision x

theorem contains_div {I J : DInterval} {x y : ℝ}
    (hJ : 0 < J.lo) (hx : I.Contains x) (hy : J.Contains y) :
    (div I J).Contains (x / y) := by
  simpa [div_eq_mul_inv, div] using
    Interval.contains_mul hx (Interval.contains_reciprocal_of_pos hJ hy)

private theorem contains_npowBinRec_go (k : ℕ)
    {A B : DInterval} {a b : ℝ}
    (hA : A.Contains a) (hB : B.Contains b) :
    (npowBinRec.go k A B).Contains (a * b ^ k) := by
  induction k using Nat.binaryRec generalizing A B a b with
  | zero => simpa [npowBinRec.go] using hA
  | bit bit n ih =>
      rw [npowBinRec.go, Nat.binaryRec_eq _ _ (Or.inl rfl)]
      cases bit
      · change (npowBinRec.go n A (B * B)).Contains
          (a * b ^ Nat.bit false n)
        simpa [Nat.bit_false, pow_mul, pow_two] using
          ih hA (Interval.contains_mul hB hB)
      · change (npowBinRec.go n (A * B) (B * B)).Contains
          (a * b ^ Nat.bit true n)
        convert ih (Interval.contains_mul hA hB)
          (Interval.contains_mul hB hB) using 1
        rw [Nat.bit_true, pow_succ, pow_mul, pow_two]
        ring

theorem contains_powNat {I : DInterval} {x : ℝ}
    (hx : I.Contains x) (n : ℕ) :
    (powNat I n).Contains (x ^ n) := by
  change (npowBinRec.go n (rat 1) I).Contains (x ^ n)
  simpa using contains_npowBinRec_go n (contains_rat 1) hx

theorem contains_expUpper {I : DInterval} {x : ℝ}
    (hx : I.Contains x) (hupper : I.upperRat ≤ 1) :
    (expUpper I).Contains (Real.exp x) := by
  apply DyadicExp.ofIntervalUpper_contains_of_upperRat_le_one
  · norm_num [precision, Dyadic.scale]
  · norm_num [expSquarings]
  · exact hx
  · exact hupper

theorem contains_piInterval : piInterval.Contains Real.pi := by
  apply Interval.contains_enclose
  constructor
  · have h := pi_gt_3141592_div_1000000
    norm_num at h ⊢
    exact h.le
  · have h := pi_lt_3141593_div_1000000
    norm_num at h ⊢
    exact h.le

/-- One checked cell separately encloses the real coupled central term. -/
theorem coarseCentral_contains_semantic (cell : Cell) {x a : ℝ}
    (hcell : (cell.xLower : ℝ) ≤ x ∧ x ≤ cell.xUpper ∧
      (cell.aLower : ℝ) ≤ a ∧ a ≤ cell.aUpper)
    (hsafe : Safe cell) :
    (coarseCentral cell).Contains (semanticCoarseCentral x a) := by
  have hx : (xInterval cell).Contains x :=
    Interval.contains_enclose ⟨hcell.1, hcell.2.1⟩
  have ha : (aInterval cell).Contains a :=
    Interval.contains_enclose ⟨hcell.2.2.1, hcell.2.2.2⟩
  have hD : (dInterval cell).Contains (semanticD x a) := by
    simpa [dInterval, semanticD] using Interval.contains_add (contains_rat 1)
      (Interval.contains_mul (contains_rat (23 / 10))
        (Interval.contains_sub hx ha))
  have ht : (tInterval cell).Contains (semanticT x a) := by
    simpa [tInterval, semanticT] using contains_div hsafe.dPos
      (Interval.contains_mul (contains_rat (23 / 10)) ha) hD
  have hpiSq : (powNat piInterval 2).Contains (Real.pi ^ 2) :=
    contains_powNat contains_piInterval 2
  have hfivePiSq : (rat (5 / 4) * powNat piInterval 2).Contains
      ((5 / 4 : ℝ) * Real.pi ^ 2) := by
    exact Interval.contains_mul (by simpa using contains_rat (5 / 4)) hpiSq
  have hthetaExponent :
      (-(div (rat (5 / 4) * powNat piInterval 2)
        (dInterval cell))).Contains
        (-(Real.pi ^ 2 / ((4 / 5 : ℝ) * semanticD x a))) := by
    have hquot := contains_div hsafe.dPos hfivePiSq hD
    convert Interval.contains_neg hquot using 1
    ring
  have htheta : (thetaInterval cell).Contains (semanticTheta x a) := by
    simpa [thetaInterval, semanticTheta] using
      contains_expUpper hthetaExponent hsafe.thetaExp
  have hDsqrt : (dInterval cell).sqrt.Contains
      (Real.sqrt (semanticD x a)) :=
    Interval.contains_sqrt (le_of_lt hsafe.dPos) hD
  have hnegT : (-(tInterval cell)).Contains (-(semanticT x a)) :=
    Interval.contains_neg ht
  have hexpNegT := contains_expUpper hnegT hsafe.negTExp
  have htheta3 : (powNat (thetaInterval cell) 3).Contains
      (semanticTheta x a ^ 3) := contains_powNat htheta 3
  have hthetaDen : (rat 1 - powNat (thetaInterval cell) 3).Contains
      (1 - semanticTheta x a ^ 3) :=
    Interval.contains_sub (by simpa using contains_rat (1 : ℚ)) htheta3
  have hcentral : (coarseCentral cell).Contains
      (semanticCoarseCentral x a) := by
    have hinvSqrt := contains_div hsafe.dSqrtPos (contains_rat 1) hDsqrt
    have hfirst := Interval.contains_mul
      (Interval.contains_mul (by simpa using contains_rat (1 / 2))
        (Interval.contains_add (contains_rat 1) hexpNegT)) hinvSqrt
    have hsecond := Interval.contains_add (contains_rat 1)
      (contains_div hsafe.thetaDen
        (Interval.contains_mul (contains_rat 2) htheta) hthetaDen)
    have hproduct := Interval.contains_mul hfirst hsecond
    convert hproduct using 1
    · rfl
    · simp only [semanticCoarseCentral, div_eq_mul_inv]
      ring
  exact hcentral


/-- One checked cell encloses the complete real coarse envelope. -/
theorem envelope_contains_semantic (cell : Cell) {x a : ℝ}
    (hcell : (cell.xLower : ℝ) ≤ x ∧ x ≤ cell.xUpper ∧
      (cell.aLower : ℝ) ≤ a ∧ a ≤ cell.aUpper)
    (hsafe : Safe cell) :
    (envelope cell).Contains (semanticEnvelope x a) := by
  have hx : (xInterval cell).Contains x :=
    Interval.contains_enclose ⟨hcell.1, hcell.2.1⟩
  have ha : (aInterval cell).Contains a :=
    Interval.contains_enclose ⟨hcell.2.2.1, hcell.2.2.2⟩
  have hD : (dInterval cell).Contains (semanticD x a) := by
    simpa [dInterval, semanticD] using Interval.contains_add (contains_rat 1)
      (Interval.contains_mul (contains_rat (23 / 10))
        (Interval.contains_sub hx ha))
  have ht : (tInterval cell).Contains (semanticT x a) := by
    simpa [tInterval, semanticT] using contains_div hsafe.dPos
      (Interval.contains_mul (contains_rat (23 / 10)) ha) hD
  have hpiSq : (powNat piInterval 2).Contains (Real.pi ^ 2) :=
    contains_powNat contains_piInterval 2
  have hfivePiSq : (rat (5 / 4) * powNat piInterval 2).Contains
      ((5 / 4 : ℝ) * Real.pi ^ 2) := by
    exact Interval.contains_mul (by simpa using contains_rat (5 / 4)) hpiSq
  have hthetaExponent :
      (-(div (rat (5 / 4) * powNat piInterval 2)
        (dInterval cell))).Contains
        (-(Real.pi ^ 2 / ((4 / 5 : ℝ) * semanticD x a))) := by
    have hquot := contains_div hsafe.dPos hfivePiSq hD
    convert Interval.contains_neg hquot using 1
    ring
  have htheta : (thetaInterval cell).Contains (semanticTheta x a) := by
    simpa [thetaInterval, semanticTheta] using
      contains_expUpper hthetaExponent hsafe.thetaExp
  have hDsqrt : (dInterval cell).sqrt.Contains
      (Real.sqrt (semanticD x a)) :=
    Interval.contains_sqrt (le_of_lt hsafe.dPos) hD
  have hnegT : (-(tInterval cell)).Contains (-(semanticT x a)) :=
    Interval.contains_neg ht
  have hexpNegT := contains_expUpper hnegT hsafe.negTExp
  have htheta3 : (powNat (thetaInterval cell) 3).Contains
      (semanticTheta x a ^ 3) := contains_powNat htheta 3
  have hthetaDen : (rat 1 - powNat (thetaInterval cell) 3).Contains
      (1 - semanticTheta x a ^ 3) :=
    Interval.contains_sub (by simpa using contains_rat (1 : ℚ)) htheta3
  have hcentral : (coarseCentral cell).Contains
      (semanticCoarseCentral x a) := by
    have hinvSqrt := contains_div hsafe.dSqrtPos (contains_rat 1) hDsqrt
    have hfirst := Interval.contains_mul
      (Interval.contains_mul (by simpa using contains_rat (1 / 2))
        (Interval.contains_add (contains_rat 1) hexpNegT)) hinvSqrt
    have hsecond := Interval.contains_add (contains_rat 1)
      (contains_div hsafe.thetaDen
        (Interval.contains_mul (contains_rat 2) htheta) hthetaDen)
    have hproduct := Interval.contains_mul hfirst hsecond
    convert hproduct using 1
    · rfl
    · simp only [semanticCoarseCentral, div_eq_mul_inv]
      ring
  have hrhoExponent : (-(div (rat (207 / 10)) (dInterval cell))).Contains
      (-(207 / 10 : ℝ) / semanticD x a) :=
    by
      have hquot := contains_div hsafe.dPos (contains_rat (207 / 10)) hD
      convert Interval.contains_neg hquot using 1
      ring
  have hrho : (rhoInterval cell).Contains (semanticRho x a) := by
    simpa [rhoInterval, semanticRho] using
      contains_expUpper hrhoExponent hsafe.rhoExp
  have hrho3 : (powNat (rhoInterval cell) 3).Contains
      (semanticRho x a ^ 3) := contains_powNat hrho 3
  have hrhoDen : (rat 1 - powNat (rhoInterval cell) 3).Contains
      (1 - semanticRho x a ^ 3) :=
    Interval.contains_sub (by simpa using contains_rat (1 : ℚ)) hrho3
  have hinactive : (inactiveTail cell).Contains
      (semanticInactiveTail x a) := by
    simpa [inactiveTail, semanticInactiveTail] using
      contains_div hsafe.rhoDen
        (Interval.contains_mul (contains_rat 2) hrho) hrhoDen
  have hasqrt : (aInterval cell).sqrt.Contains (Real.sqrt a) :=
    Interval.contains_sqrt hsafe.aNonneg ha
  have hM : (mInterval cell).Contains (semanticM a) := by
    simpa [mInterval, semanticM] using
      contains_div hsafe.aSqrtPos (contains_rat 3) hasqrt
  have hminus : (mInterval cell - rat 1).Contains (semanticM a - 1) :=
    Interval.contains_sub hM (by simpa using contains_rat (1 : ℚ))
  have hplus : (mInterval cell + rat 1).Contains (semanticM a + 1) :=
    Interval.contains_add hM (by simpa using contains_rat (1 : ℚ))
  have hMSq := contains_powNat hM 2
  have hminusExp : (activeMinusExponent cell).Contains
      (-(semanticT x a) * (semanticM a - 1) ^ 2) := by
    simpa [activeMinusExponent] using Interval.contains_neg
      (Interval.contains_mul ht (contains_powNat hminus 2))
  have hminusRatioExp : (activeMinusRatioExponent cell).Contains
      (-(semanticT x a) * (3 * semanticM a ^ 2 - 2 * semanticM a)) := by
    simpa [activeMinusRatioExponent] using Interval.contains_neg
      (Interval.contains_mul ht (Interval.contains_sub
        (Interval.contains_mul (contains_rat 3) hMSq)
        (Interval.contains_mul (contains_rat 2) hM)))
  have hplusExp : (activePlusExponent cell).Contains
      (-(semanticT x a) * (semanticM a + 1) ^ 2) := by
    simpa [activePlusExponent] using Interval.contains_neg
      (Interval.contains_mul ht (contains_powNat hplus 2))
  have hplusRatioExp : (activePlusRatioExponent cell).Contains
      (-(semanticT x a) * (3 * semanticM a ^ 2 + 2 * semanticM a)) := by
    simpa [activePlusRatioExponent] using Interval.contains_neg
      (Interval.contains_mul ht (Interval.contains_add
        (Interval.contains_mul (contains_rat 3) hMSq)
        (Interval.contains_mul (contains_rat 2) hM)))
  have heMinus := contains_expUpper hminusExp hsafe.activeMinusExp
  have heMinusRatio := contains_expUpper hminusRatioExp hsafe.activeMinusRatioExp
  have hePlus := contains_expUpper hplusExp hsafe.activePlusExp
  have hePlusRatio := contains_expUpper hplusRatioExp hsafe.activePlusRatioExp
  have hactive : (activeTail cell).Contains (semanticActiveTail x a) := by
    have hmd := Interval.contains_sub (contains_rat 1) heMinusRatio
    have hpd := Interval.contains_sub (contains_rat 1) hePlusRatio
    simpa [activeTail, semanticActiveTail] using Interval.contains_add
      (contains_div hsafe.activeMinusDen heMinus hmd)
      (contains_div hsafe.activePlusDen hePlus hpd)
  have htail : (conditionedTail cell).Contains
      ((semanticInactiveTail x a + semanticActiveTail x a) / 2) := by
    have := Interval.contains_mul (contains_rat (2⁻¹ : ℚ))
      (Interval.contains_add hinactive hactive)
    convert this using 1
    · rfl
    · ring
  simpa [envelope, semanticEnvelope] using Interval.contains_add hcentral htail

/-- The conditioned modular-image allowance is shared by the coarse-lobe and
power-chord central estimates.  Exposing it separately prevents the chord
certificate from duplicating the tail reflection proof. -/
theorem conditionedTail_contains_semantic (cell : Cell) {x a : ℝ}
    (hcell : (cell.xLower : ℝ) ≤ x ∧ x ≤ cell.xUpper ∧
      (cell.aLower : ℝ) ≤ a ∧ a ≤ cell.aUpper)
    (hsafe : Safe cell) :
    (conditionedTail cell).Contains
      ((semanticInactiveTail x a + semanticActiveTail x a) / 2) := by
  have hx : (xInterval cell).Contains x :=
    Interval.contains_enclose ⟨hcell.1, hcell.2.1⟩
  have ha : (aInterval cell).Contains a :=
    Interval.contains_enclose ⟨hcell.2.2.1, hcell.2.2.2⟩
  have hD : (dInterval cell).Contains (semanticD x a) := by
    simpa [dInterval, semanticD] using Interval.contains_add (contains_rat 1)
      (Interval.contains_mul (contains_rat (23 / 10))
        (Interval.contains_sub hx ha))
  have ht : (tInterval cell).Contains (semanticT x a) := by
    simpa [tInterval, semanticT] using contains_div hsafe.dPos
      (Interval.contains_mul (contains_rat (23 / 10)) ha) hD
  have hrhoExponent : (-(div (rat (207 / 10)) (dInterval cell))).Contains
      (-(207 / 10 : ℝ) / semanticD x a) := by
    have hquot := contains_div hsafe.dPos (contains_rat (207 / 10)) hD
    convert Interval.contains_neg hquot using 1
    ring
  have hrho : (rhoInterval cell).Contains (semanticRho x a) := by
    simpa [rhoInterval, semanticRho] using
      contains_expUpper hrhoExponent hsafe.rhoExp
  have hrho3 : (powNat (rhoInterval cell) 3).Contains
      (semanticRho x a ^ 3) := contains_powNat hrho 3
  have hrhoDen : (rat 1 - powNat (rhoInterval cell) 3).Contains
      (1 - semanticRho x a ^ 3) :=
    Interval.contains_sub (by simpa using contains_rat (1 : ℚ)) hrho3
  have hinactive : (inactiveTail cell).Contains
      (semanticInactiveTail x a) := by
    simpa [inactiveTail, semanticInactiveTail] using
      contains_div hsafe.rhoDen
        (Interval.contains_mul (contains_rat 2) hrho) hrhoDen
  have hasqrt : (aInterval cell).sqrt.Contains (Real.sqrt a) :=
    Interval.contains_sqrt hsafe.aNonneg ha
  have hM : (mInterval cell).Contains (semanticM a) := by
    simpa [mInterval, semanticM] using
      contains_div hsafe.aSqrtPos (contains_rat 3) hasqrt
  have hminus : (mInterval cell - rat 1).Contains (semanticM a - 1) :=
    Interval.contains_sub hM (by simpa using contains_rat (1 : ℚ))
  have hplus : (mInterval cell + rat 1).Contains (semanticM a + 1) :=
    Interval.contains_add hM (by simpa using contains_rat (1 : ℚ))
  have hMSq := contains_powNat hM 2
  have hminusExp : (activeMinusExponent cell).Contains
      (-(semanticT x a) * (semanticM a - 1) ^ 2) := by
    simpa [activeMinusExponent] using Interval.contains_neg
      (Interval.contains_mul ht (contains_powNat hminus 2))
  have hminusRatioExp : (activeMinusRatioExponent cell).Contains
      (-(semanticT x a) * (3 * semanticM a ^ 2 - 2 * semanticM a)) := by
    simpa [activeMinusRatioExponent] using Interval.contains_neg
      (Interval.contains_mul ht (Interval.contains_sub
        (Interval.contains_mul (contains_rat 3) hMSq)
        (Interval.contains_mul (contains_rat 2) hM)))
  have hplusExp : (activePlusExponent cell).Contains
      (-(semanticT x a) * (semanticM a + 1) ^ 2) := by
    simpa [activePlusExponent] using Interval.contains_neg
      (Interval.contains_mul ht (contains_powNat hplus 2))
  have hplusRatioExp : (activePlusRatioExponent cell).Contains
      (-(semanticT x a) * (3 * semanticM a ^ 2 + 2 * semanticM a)) := by
    simpa [activePlusRatioExponent] using Interval.contains_neg
      (Interval.contains_mul ht (Interval.contains_add
        (Interval.contains_mul (contains_rat 3) hMSq)
        (Interval.contains_mul (contains_rat 2) hM)))
  have heMinus := contains_expUpper hminusExp hsafe.activeMinusExp
  have heMinusRatio := contains_expUpper hminusRatioExp hsafe.activeMinusRatioExp
  have hePlus := contains_expUpper hplusExp hsafe.activePlusExp
  have hePlusRatio := contains_expUpper hplusRatioExp hsafe.activePlusRatioExp
  have hactive : (activeTail cell).Contains (semanticActiveTail x a) := by
    have hmd := Interval.contains_sub (contains_rat 1) heMinusRatio
    have hpd := Interval.contains_sub (contains_rat 1) hePlusRatio
    simpa [activeTail, semanticActiveTail] using Interval.contains_add
      (contains_div hsafe.activeMinusDen heMinus hmd)
      (contains_div hsafe.activePlusDen hePlus hpd)
  have := Interval.contains_mul (contains_rat (2⁻¹ : ℚ))
    (Interval.contains_add hinactive hactive)
  convert this using 1
  · rfl
  · ring

theorem semanticEnvelope_lt_of_certifiedCheck (cell : Cell) {x a : ℝ}
    (hcell : (cell.xLower : ℝ) ≤ x ∧ x ≤ cell.xUpper ∧
      (cell.aLower : ℝ) ≤ a ∧ a ≤ cell.aUpper)
    (hcheck : certifiedCheck cell = true) :
    semanticEnvelope x a < 543 / 1000 := by
  have hc : safeCheck cell = true ∧
      Interval.upperLTCheck (envelope cell) (543 / 1000) = true := by
    simpa only [certifiedCheck, Bool.and_eq_true] using hcheck
  have hs : safeCheck cell = true := hc.1
  have hb : Interval.upperLTCheck (envelope cell) (543 / 1000) = true :=
    hc.2
  simpa using Interval.lt_of_contains_of_upperLTCheck
    (envelope_contains_semantic cell hcell (safeCheck_sound hs)) hb

end ThresholdNearCoarse128
end CertifiedJL
