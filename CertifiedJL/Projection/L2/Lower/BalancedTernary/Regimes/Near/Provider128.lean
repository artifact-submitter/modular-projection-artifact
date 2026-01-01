/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Soundness.ThresholdBits128
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Near.Analytic128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Soundness.ThresholdNearChordInterpolated128
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Near.RetainedAssembly
import CertifiedJL.Projection.L2.Lower.BalancedTernary.WrappedFourier

/-!
# Complete near-dominant provider at 128 bits

The compact threshold subprofile retains the near coordinate.  Its central
zero-image moment is bounded by the low-Holder lobe certificate or the
high-Holder power-chord certificate, while the conditioned wrapped-image tail
is added exactly once.  Positive wrapped-Fourier deletion transports the
compact result back to the arbitrary original profile.
-/

open scoped BigOperators ENNReal

open MeasureTheory

namespace CertifiedJL

private noncomputable def nearConditionedTail (x a : ℝ) : ℝ :=
  (ThresholdNearCoarse128.semanticInactiveTail x a +
    ThresholdNearCoarse128.semanticActiveTail x a) / 2

private theorem nearConditionedTail_nonneg
    {x a : ℝ} (ha : 0 < a) (hax : a < x)
    (haUpper : a ≤ 2401 / 2500) :
    0 ≤ nearConditionedTail x a := by
  have hD : 0 < ThresholdNearCoarse128.semanticD x a := by
    dsimp [ThresholdNearCoarse128.semanticD]
    positivity
  have ht : 0 < ThresholdNearCoarse128.semanticT x a := by
    dsimp [ThresholdNearCoarse128.semanticT]
    positivity
  have hsqrtPos : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsqrtSq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hsqrtLt : Real.sqrt a < 1 := by
    have haLt : a < 1 := haUpper.trans_lt (by norm_num)
    nlinarith [Real.sqrt_nonneg a]
  have hM : 1 < ThresholdNearCoarse128.semanticM a := by
    dsimp [ThresholdNearCoarse128.semanticM]
    exact (lt_div_iff₀ hsqrtPos).2 (by nlinarith)
  have hrhoLt : ThresholdNearCoarse128.semanticRho x a < 1 := by
    dsimp [ThresholdNearCoarse128.semanticRho]
    apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (by norm_num) hD
  have hrhoPow : ThresholdNearCoarse128.semanticRho x a ^ 3 < 1 := by
    simpa using pow_lt_pow_left₀ hrhoLt
      (Real.exp_nonneg _)
      (by norm_num : (3 : ℕ) ≠ 0)
  have hminusRate : 0 <
      3 * ThresholdNearCoarse128.semanticM a ^ 2 -
        2 * ThresholdNearCoarse128.semanticM a := by
    nlinarith [sq_nonneg (ThresholdNearCoarse128.semanticM a - 1)]
  have hplusRate : 0 <
      3 * ThresholdNearCoarse128.semanticM a ^ 2 +
        2 * ThresholdNearCoarse128.semanticM a := by
    nlinarith [sq_nonneg (ThresholdNearCoarse128.semanticM a)]
  have hminusExp : Real.exp
      (-ThresholdNearCoarse128.semanticT x a *
        (3 * ThresholdNearCoarse128.semanticM a ^ 2 -
          2 * ThresholdNearCoarse128.semanticM a)) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr ht) hminusRate
  have hplusExp : Real.exp
      (-ThresholdNearCoarse128.semanticT x a *
        (3 * ThresholdNearCoarse128.semanticM a ^ 2 +
          2 * ThresholdNearCoarse128.semanticM a)) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr ht) hplusRate
  have hinactive :
      0 ≤ ThresholdNearCoarse128.semanticInactiveTail x a := by
    rw [ThresholdNearCoarse128.semanticInactiveTail]
    exact div_nonneg (mul_nonneg (by norm_num) (Real.exp_nonneg _))
      (sub_nonneg.mpr hrhoPow.le)
  have hactive : 0 ≤ ThresholdNearCoarse128.semanticActiveTail x a := by
    rw [ThresholdNearCoarse128.semanticActiveTail]
    exact add_nonneg
      (div_nonneg (Real.exp_nonneg _) (sub_nonneg.mpr hminusExp.le))
      (div_nonneg (Real.exp_nonneg _) (sub_nonneg.mpr hplusExp.le))
  exact div_nonneg (add_nonneg hinactive hactive) (by norm_num)

private theorem semanticCoarseCentral_nonneg
    {x a : ℝ} (ha : 0 < a) (hax : a < x) :
    0 ≤ ThresholdNearCoarse128.semanticCoarseCentral x a := by
  let D := ThresholdNearCoarse128.semanticD x a
  let t := ThresholdNearCoarse128.semanticT x a
  let theta := ThresholdNearCoarse128.semanticTheta x a
  have hD : 0 < D := by
    dsimp [D, ThresholdNearCoarse128.semanticD]
    positivity
  have ht : 0 < t := by
    dsimp [t, ThresholdNearCoarse128.semanticT]
    positivity
  have hthetaPos : 0 < theta := by
    dsimp [theta, ThresholdNearCoarse128.semanticTheta]
    positivity
  have hthetaLt : theta < 1 := by
    dsimp [theta, ThresholdNearCoarse128.semanticTheta]
    apply Real.exp_lt_one_iff.mpr
    exact neg_lt_zero.mpr (by positivity)
  have hthetaPow : theta ^ 3 < 1 := by
    simpa using pow_lt_pow_left₀ hthetaLt hthetaPos.le
      (by norm_num : (3 : ℕ) ≠ 0)
  have hden : 0 < 1 - theta ^ 3 := sub_pos.mpr hthetaPow
  dsimp [ThresholdNearCoarse128.semanticCoarseCentral,
    ThresholdNearCoarse128.semanticD, ThresholdNearCoarse128.semanticT,
    ThresholdNearCoarse128.semanticTheta]
  positivity

/-- Every coupled residual Holder factor lies below the exact central budget
left after reserving the conditioned modular-image tail. -/
theorem retainedNearGaussianCosineMoment_le_cap_sub_tail_of_replay
    (replay : CertificateContracts.SparseL2ThresholdNearReplay128)
    {x a y : ℝ}
    (hx : (1 : ℝ) ≤ x ∧ x ≤ 4901 / 2500)
    (ha : (9 / 16 : ℝ) ≤ a ∧ a ≤ 2401 / 2500)
    (hax : a < x) (hy : 0 < y) (hyUpper : y ≤ 1) :
    retainedGaussianCosineMoment ((23 / 10) * x) (a / x) y ≤
      ENNReal.ofReal (681 / 1250 - nearConditionedTail x a) := by
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
  have haPos : 0 < a := lt_of_lt_of_le (by norm_num) ha.1
  have hcoarseFull :=
    replay.coarseEnvelope hx.1 hx.2 ha.1 ha.2
  have hcentralNonneg :
      0 ≤ ThresholdNearCoarse128.semanticCoarseCentral x a :=
    semanticCoarseCentral_nonneg haPos hax
  have htailLt : nearConditionedTail x a < 543 / 1000 := by
    dsimp [ThresholdNearCoarse128.semanticEnvelope] at hcoarseFull
    dsimp [nearConditionedTail]
    linarith
  by_cases hyCoarse : y ≤ 4 / 5
  · have hmoment := retainedGaussianCosineMoment_le_semanticCoarseCentral
      hxPos haPos hax hy hyCoarse
    apply hmoment.trans
    apply ENNReal.ofReal_mono
    dsimp [ThresholdNearCoarse128.semanticEnvelope] at hcoarseFull
    dsimp [nearConditionedTail]
    linarith
  · have hyHigh : (4 / 5 : ℝ) ≤ y := (le_of_not_ge hyCoarse)
    have hmoment := retainedGaussianCosineMoment_le_semanticChordCentral
      hxPos haPos hax (by linarith) hyUpper
    have hchordFull :=
      ThresholdNearChord128.semanticEnvelope_lt_681_div_1250_interpolated_of_replay
        replay hx ha ⟨hyHigh, hyUpper⟩
    apply hmoment.trans
    apply ENNReal.ofReal_mono
    dsimp [ThresholdNearChord128.semanticEnvelope] at hchordFull
    dsimp [nearConditionedTail]
    linarith

private theorem near_expNegDivOneSubExpNeg_antitone
    {a₀ a c₀ c : ℝ} (haa : a₀ ≤ a)
    (hc₀ : 0 < c₀) (hcc : c₀ ≤ c) :
    Real.exp (-a) / (1 - Real.exp (-c)) ≤
      Real.exp (-a₀) / (1 - Real.exp (-c₀)) := by
  have hnum : Real.exp (-a) ≤ Real.exp (-a₀) :=
    Real.exp_le_exp.mpr (neg_le_neg haa)
  have hc : 0 < c := hc₀.trans_le hcc
  have hden₀ : 0 < 1 - Real.exp (-c₀) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hc₀))
  have hden : 0 < 1 - Real.exp (-c) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hc))
  have hdenOrder : 1 - Real.exp (-c₀) ≤ 1 - Real.exp (-c) := by
    have := Real.exp_le_exp.mpr (neg_le_neg hcc)
    linarith
  exact div_le_div₀ (Real.exp_nonneg _) hnum hden₀ hdenOrder

private theorem near_retainedActiveImageTail_antitone_modulus
    {alpha B₀ B : ℝ} (halpha : 0 < alpha)
    (hB₀ : 1 < B₀) (hB : B₀ ≤ B) :
    Real.exp (-alpha * (B - 1) ^ 2) /
          (1 - Real.exp (-alpha * (3 * B ^ 2 - 2 * B))) +
        Real.exp (-alpha * (B + 1) ^ 2) /
          (1 - Real.exp (-alpha * (3 * B ^ 2 + 2 * B))) ≤
      Real.exp (-alpha * (B₀ - 1) ^ 2) /
          (1 - Real.exp (-alpha * (3 * B₀ ^ 2 - 2 * B₀))) +
        Real.exp (-alpha * (B₀ + 1) ^ 2) /
          (1 - Real.exp (-alpha * (3 * B₀ ^ 2 + 2 * B₀))) := by
  have hB1 : 1 < B := hB₀.trans_le hB
  have hminusSq : (B₀ - 1) ^ 2 ≤ (B - 1) ^ 2 :=
    (sq_le_sq₀ (by linarith) (by linarith)).2 (by linarith)
  have hplusSq : (B₀ + 1) ^ 2 ≤ (B + 1) ^ 2 :=
    (sq_le_sq₀ (by linarith) (by linarith)).2 (by linarith)
  have hminusRate :
      3 * B₀ ^ 2 - 2 * B₀ ≤ 3 * B ^ 2 - 2 * B := by
    have hsum : 0 ≤ 3 * (B₀ + B) - 2 := by nlinarith
    have hdiff : 0 ≤ B - B₀ := by linarith
    nlinarith [mul_nonneg hdiff hsum]
  have hplusRate :
      3 * B₀ ^ 2 + 2 * B₀ ≤ 3 * B ^ 2 + 2 * B := by
    have hsum : 0 ≤ 3 * (B₀ + B) + 2 := by nlinarith
    have hdiff : 0 ≤ B - B₀ := by linarith
    nlinarith [mul_nonneg hdiff hsum]
  have hminusRatePos : 0 < 3 * B₀ ^ 2 - 2 * B₀ := by
    have : 0 < B₀ * (3 * B₀ - 2) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have hplusRatePos : 0 < 3 * B₀ ^ 2 + 2 * B₀ := by
    have : 0 < B₀ * (3 * B₀ + 2) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have hminus := near_expNegDivOneSubExpNeg_antitone
    (mul_le_mul_of_nonneg_left hminusSq halpha.le)
    (mul_pos halpha hminusRatePos)
    (mul_le_mul_of_nonneg_left hminusRate halpha.le)
  have hplus := near_expNegDivOneSubExpNeg_antitone
    (mul_le_mul_of_nonneg_left hplusSq halpha.le)
    (mul_pos halpha hplusRatePos)
    (mul_le_mul_of_nonneg_left hplusRate halpha.le)
  simpa only [neg_mul] using add_le_add hminus hplus

/-- At public margin three, the exact conditioned image tails for the retained
near coordinate are bounded by the normalized semantic tail used in the
`(x,a)` certificates. -/
theorem retainedConditionedImageTail_le_nearSemantic_marginThree
    {q inputThreshold A : ℕ} {V x a : ℝ}
    (hthreshold : 0 < inputThreshold) (hA : 0 < A) (hV : 0 ≤ V)
    (hx : x = ((A : ℝ) ^ 2 + V) / (inputThreshold : ℝ) ^ 2)
    (ha : a = (A : ℝ) ^ 2 / (inputThreshold : ℝ) ^ 2)
    (haUpper : a ≤ 2401 / 2500)
    (hmargin : 3 * inputThreshold ≤ q) :
    (retainedInactiveImageTail q A V ((23 / 10) * a) +
        retainedActiveImageTail q A V ((23 / 10) * a)) / 2 ≤
      nearConditionedTail x a := by
  let u : ℝ := V / (A : ℝ) ^ 2
  let B : ℝ := (q : ℝ) / (A : ℝ)
  let M : ℝ := ThresholdNearCoarse128.semanticM a
  let alpha : ℝ := ((23 / 10) * a) / (1 + (23 / 10) * a * u)
  have hbReal : 0 < (inputThreshold : ℝ) := by exact_mod_cast hthreshold
  have hAReal : 0 < (A : ℝ) := by exact_mod_cast hA
  have haPos : 0 < a := by rw [ha]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have halpha : 0 < alpha := by dsimp [alpha]; positivity
  have hsqrtA : Real.sqrt a = (A : ℝ) / inputThreshold := by
    rw [ha]
    have hquot : 0 ≤ (A : ℝ) / inputThreshold := by positivity
    rw [show (A : ℝ) ^ 2 / (inputThreshold : ℝ) ^ 2 =
        ((A : ℝ) / inputThreshold) ^ 2 by ring,
      Real.sqrt_sq hquot]
  have hM : M = 3 * (inputThreshold : ℝ) / A := by
    dsimp [M, ThresholdNearCoarse128.semanticM]
    rw [hsqrtA]
    field_simp [hAReal.ne', hbReal.ne']
  have hMB : M ≤ B := by
    rw [hM]
    dsimp [B]
    apply (div_le_div_iff_of_pos_right hAReal).2
    exact_mod_cast hmargin
  have hM1 : 1 < M := by
    rw [hM]
    have haLt : a < 1 := haUpper.trans_lt (by norm_num)
    have hsqLt : (A : ℝ) ^ 2 < (inputThreshold : ℝ) ^ 2 := by
      rw [ha] at haLt
      exact (div_lt_one (sq_pos_of_pos hbReal)).mp haLt
    have hAlt : (A : ℝ) < 3 * inputThreshold := by nlinarith
    exact (lt_div_iff₀ hAReal).2 (by simpa using hAlt)
  have hD : ThresholdNearCoarse128.semanticD x a =
      1 + (23 / 10) * a * u := by
    dsimp [ThresholdNearCoarse128.semanticD, u]
    rw [hx, ha]
    field_simp [hAReal.ne', hbReal.ne']
    ring
  have hT : ThresholdNearCoarse128.semanticT x a = alpha := by
    rw [ThresholdNearCoarse128.semanticT, hD]
  have hRho : ThresholdNearCoarse128.semanticRho x a =
      Real.exp (-alpha * M ^ 2) := by
    rw [ThresholdNearCoarse128.semanticRho, hD]
    congr 1
    dsimp [alpha, u]
    rw [hM, ha]
    field_simp [hAReal.ne', hbReal.ne']
    ring
  have hcM : 0 < alpha * M ^ 2 := by positivity
  have hcB : alpha * M ^ 2 ≤ alpha * B ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ halpha.le
    exact pow_le_pow_left₀ (by linarith : 0 ≤ M) hMB 2
  have hinactive :
      2 * Real.exp (-(alpha * B ^ 2)) /
          (1 - Real.exp (-(alpha * B ^ 2)) ^ 3) ≤
        2 * Real.exp (-(alpha * M ^ 2)) /
          (1 - Real.exp (-(alpha * M ^ 2)) ^ 3) := by
    have hr : Real.exp (-(alpha * B ^ 2)) ≤
        Real.exp (-(alpha * M ^ 2)) := by
      exact Real.exp_le_exp.mpr (neg_le_neg hcB)
    have hr₀Lt : Real.exp (-(alpha * M ^ 2)) < 1 :=
      Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hcM)
    have hr₀Pow : Real.exp (-(alpha * M ^ 2)) ^ 3 < 1 := by
      simpa using pow_lt_pow_left₀ hr₀Lt
        (Real.exp_nonneg _)
        (by norm_num : (3 : ℕ) ≠ 0)
    have hden₀ : 0 < 1 - Real.exp (-(alpha * M ^ 2)) ^ 3 :=
      sub_pos.mpr hr₀Pow
    have hpow : Real.exp (-(alpha * B ^ 2)) ^ 3 ≤
        Real.exp (-(alpha * M ^ 2)) ^ 3 :=
      pow_le_pow_left₀ (Real.exp_nonneg _) hr 3
    exact div_le_div₀ (by positivity) (by nlinarith) hden₀ (by nlinarith)
  have hinactive' :
      2 * Real.exp (-alpha * B ^ 2) /
          (1 - Real.exp (-alpha * B ^ 2) ^ 3) ≤
        2 * Real.exp (-alpha * M ^ 2) /
          (1 - Real.exp (-alpha * M ^ 2) ^ 3) := by
    simpa only [neg_mul] using hinactive
  have hactive := near_retainedActiveImageTail_antitone_modulus
    halpha hM1 hMB
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    retainedInactiveImageTail q A V ((23 / 10) * a) +
        retainedActiveImageTail q A V ((23 / 10) * a) =
      2 * Real.exp (-alpha * B ^ 2) /
          (1 - Real.exp (-alpha * B ^ 2) ^ 3) +
        (Real.exp (-alpha * (B - 1) ^ 2) /
            (1 - Real.exp (-alpha * (3 * B ^ 2 - 2 * B))) +
          Real.exp (-alpha * (B + 1) ^ 2) /
            (1 - Real.exp (-alpha * (3 * B ^ 2 + 2 * B)))) := by
      simp only [retainedInactiveImageTail, retainedActiveImageTail]
      rfl
    _ ≤ 2 * Real.exp (-alpha * M ^ 2) /
          (1 - Real.exp (-alpha * M ^ 2) ^ 3) +
        (Real.exp (-alpha * (M - 1) ^ 2) /
            (1 - Real.exp (-alpha * (3 * M ^ 2 - 2 * M))) +
          Real.exp (-alpha * (M + 1) ^ 2) /
            (1 - Real.exp (-alpha * (3 * M ^ 2 + 2 * M)))) :=
      add_le_add hinactive' hactive
    _ = ThresholdNearCoarse128.semanticInactiveTail x a +
        ThresholdNearCoarse128.semanticActiveTail x a := by
      rw [ThresholdNearCoarse128.semanticInactiveTail, hRho]
      simp only [ThresholdNearCoarse128.semanticActiveTail, hT]
      rfl

/-- A compact near-threshold profile has wrapped one-row transform at most
`681/1250`.  This is the semantic core of the public-threshold provider. -/
theorem sparseRow_nearCompact_wrapped_le_681_div_1250_of_replay
    (replay : CertificateContracts.SparseL2ThresholdNearReplay128)
    {q d inputThreshold : ℕ} (w : Fin d → ℤ) (i : Fin d)
    (hq : Odd q) (hthreshold : 0 < inputThreshold)
    (hlower : inputThreshold ^ 2 ≤ sqNorm w)
    (hupper : 2500 * sqNorm w < 4901 * inputThreshold ^ 2)
    (hcoordinate : ∀ j, 50 * (w j).natAbs ≤ 49 * inputThreshold)
    (hnear : 3 * inputThreshold < 4 * (w i).natAbs)
    (hmargin : 3 * inputThreshold ≤ q) :
    ∫ row, wrappedGaussianKernel q
        ((23 / 10 : ℝ) / (inputThreshold : ℝ) ^ 2)
        (∑ j, row j * w j)
        ∂(sparseRademacherRow d).toMeasure ≤
      681 / 1250 := by
  let A : ℕ := dominantAmplitude w i
  let U : ℕ := dominantRemainderSqNorm w i
  let W : ℝ := sqNorm w
  let x : ℝ := W / (inputThreshold : ℝ) ^ 2
  let aMass : ℝ := (A : ℝ) ^ 2 / (inputThreshold : ℝ) ^ 2
  let normalized : Fin d → ℝ := fun j ↦ (w j : ℝ) / Real.sqrt W
  let r : ℝ := aMass / x
  let S : Finset (Fin d) :=
    Finset.univ.filter fun j ↦ j ≠ i ∧ normalized j ≠ 0
  let tail : ℝ := nearConditionedTail x aMass
  let C : ℝ := 681 / 1250 - tail
  have hbReal : 0 < (inputThreshold : ℝ) := by exact_mod_cast hthreshold
  have hi : w i ≠ 0 := by
    intro hi
    simp [hi] at hnear
  have hA : 0 < A := by
    dsimp [A]
    exact dominantAmplitude_pos hi
  have hAReal : 0 < (A : ℝ) := by exact_mod_cast hA
  have hWLower : (inputThreshold : ℝ) ^ 2 ≤ W := by
    dsimp [W]
    exact_mod_cast hlower
  have hW : 0 < W := (sq_pos_of_pos hbReal).trans_le hWLower
  have hsqrtW : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW.le
  have hsqrtWne : Real.sqrt W ≠ 0 := (Real.sqrt_pos.2 hW).ne'
  have hsplitNat : sqNorm w = A ^ 2 + U := by
    simpa [A, U, dominantAmplitude] using
      sqNorm_eq_dominant_add_remainder w i
  have hsplitReal : W = (A : ℝ) ^ 2 + (U : ℝ) := by
    dsimp [W]
    rw [hsplitNat]
    push_cast
    ring
  have hAUpperNat : 50 * A ≤ 49 * inputThreshold := by
    simpa [A, dominantAmplitude] using hcoordinate i
  have hASqUpperNat : 2500 * A ^ 2 ≤ 2401 * inputThreshold ^ 2 := by
    have hsquare := Nat.pow_le_pow_left hAUpperNat 2
    simpa [mul_pow, mul_assoc, mul_left_comm, mul_comm] using hsquare
  have hASqUpper : 2500 * (A : ℝ) ^ 2 ≤
      2401 * (inputThreshold : ℝ) ^ 2 := by
    exact_mod_cast hASqUpperNat
  have hASqLt : (A : ℝ) ^ 2 < (inputThreshold : ℝ) ^ 2 := by
    nlinarith
  have hU : 0 < U := by
    have hUSq : (0 : ℝ) < U := by
      rw [hsplitReal] at hWLower
      nlinarith
    exact_mod_cast hUSq
  have hUReal : 0 < (U : ℝ) := by exact_mod_cast hU
  have hxBand : (1 : ℝ) ≤ x ∧ x ≤ 4901 / 2500 := by
    constructor
    · dsimp [x]
      exact (le_div_iff₀ (sq_pos_of_pos hbReal)).2 (by simpa using hWLower)
    · dsimp [x, W]
      apply (div_le_iff₀ (sq_pos_of_pos hbReal)).2
      have hupperReal : (2500 : ℝ) * sqNorm w <
          4901 * (inputThreshold : ℝ) ^ 2 := by exact_mod_cast hupper
      nlinarith
  have haBand : (9 / 16 : ℝ) ≤ aMass ∧
      aMass ≤ 2401 / 2500 := by
    constructor
    · dsimp [aMass]
      have hnearReal : (3 : ℝ) * inputThreshold < 4 * A := by
        have hnearCast : (3 : ℝ) * inputThreshold <
            4 * ((w i).natAbs : ℝ) := by
          exact_mod_cast hnear
        simpa [A, dominantAmplitude] using hnearCast
      have hsq : (9 : ℝ) * (inputThreshold : ℝ) ^ 2 <
          16 * (A : ℝ) ^ 2 := by
        have hproduct : 0 <
            (4 * (A : ℝ) - 3 * inputThreshold) *
              (4 * (A : ℝ) + 3 * inputThreshold) := by positivity
        nlinarith
      apply (le_div_iff₀ (sq_pos_of_pos hbReal)).2
      nlinarith
    · dsimp [aMass]
      apply (div_le_iff₀ (sq_pos_of_pos hbReal)).2
      nlinarith
  have hax : aMass < x := by
    dsimp [aMass, x]
    apply (div_lt_div_iff_of_pos_right (sq_pos_of_pos hbReal)).2
    rw [hsplitReal]
    linarith
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num) hxBand.1
  have haPos : 0 < aMass := lt_of_lt_of_le (by norm_num) haBand.1
  have hnormalizedSq : ∑ j, normalized j ^ 2 = 1 := by
    dsimp [normalized]
    calc
      ∑ j, ((w j : ℝ) / Real.sqrt W) ^ 2 =
          (∑ j, (w j : ℝ) ^ 2) / W := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        rw [div_pow, hsqrtW]
      _ = 1 := by
        rw [← realCast_sqNorm, show (sqNorm w : ℝ) = W by rfl]
        exact div_self hW.ne'
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r]
    exact (div_lt_one hxPos).2 hax
  have hri : normalized i ^ 2 = r := by
    dsimp [normalized, r, aMass, x]
    rw [div_pow, hsqrtW]
    have hiSq : (w i : ℝ) ^ 2 = (A : ℝ) ^ 2 := by
      norm_num [A, dominantAmplitude]
    rw [hiSq]
    field_simp [hW.ne', (sq_pos_of_pos hbReal).ne']
  have hnormalizedI : normalized i ≠ 0 := by
    dsimp [normalized]
    exact div_ne_zero (by exact_mod_cast hi) hsqrtWne
  have hS : ∀ j, j ∈ S ↔ j ≠ i ∧ normalized j ≠ 0 := by
    intro j
    simp [S]

  have hC : 0 ≤ C := by
    have hcoarseFull :=
      replay.coarseEnvelope hxBand.1 hxBand.2 haBand.1 haBand.2
    have hcentralNonneg :
        0 ≤ ThresholdNearCoarse128.semanticCoarseCentral x aMass :=
      semanticCoarseCentral_nonneg haPos hax
    dsimp [ThresholdNearCoarse128.semanticEnvelope] at hcoarseFull
    dsimp [C, tail, nearConditionedTail]
    linarith
  have hmoment : ∀ j, j ∈ S →
      retainedGaussianCosineMoment ((23 / 10) * x) r
          (normalized j ^ 2 / (1 - r)) ≤ ENNReal.ofReal C := by
    intro j hj
    have hji : j ≠ i := (hS j).1 hj |>.1
    have hjNonzero : normalized j ≠ 0 := (hS j).1 hj |>.2
    have hwj : w j ≠ 0 := by
      intro hwj
      exact hjNonzero (by simp [normalized, hwj])
    have hcoordSq : (w j).natAbs ^ 2 ≤ U := by
      dsimp [U, dominantRemainderSqNorm]
      exact Finset.single_le_sum
        (f := fun k : DominantRemainderIndex i ↦ (w k.1).natAbs ^ 2)
        (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ ⟨j, hji⟩)
    let y : ℝ := (w j : ℝ) ^ 2 / (U : ℝ)
    have hy : 0 < y := by
      dsimp [y]
      have hwjReal : (w j : ℝ) ≠ 0 := by exact_mod_cast hwj
      positivity
    have hyUpper : y ≤ 1 := by
      dsimp [y]
      apply (div_le_one hUReal).2
      have hcast : ((w j).natAbs ^ 2 : ℝ) ≤ (U : ℝ) := by
        exact_mod_cast hcoordSq
      have hsq : (w j : ℝ) ^ 2 = ((w j).natAbs ^ 2 : ℝ) := by
        norm_num
      simpa only [hsq] using hcast
    have hyEq : normalized j ^ 2 / (1 - r) = y := by
      dsimp [normalized, r, aMass, x, y]
      rw [div_pow, hsqrtW]
      rw [hsplitReal]
      field_simp [hW.ne', (sq_pos_of_pos hbReal).ne', hUReal.ne']
      ring
    rw [hyEq]
    exact retainedNearGaussianCosineMoment_le_cap_sub_tail_of_replay replay
      hxBand haBand hax hy hyUpper
  have hcentralNormalized := sparseRow_retained_nonmodulated_le_of_moment_cap
    normalized i ((23 / 10) * x) r C S
      (by positivity) hr0 hr1 hnormalizedSq hri hnormalizedI hS hC hmoment
  have hcentral :
      ENNReal.ofReal
          (∫ row, Real.exp
            (-(((23 / 10 : ℝ) * aMass) / (A : ℝ) ^ 2) *
              (((∑ j, row j * w j : ℤ) : ℝ) ^ 2))
            ∂(sparseRademacherRow d).toMeasure) ≤
        ENNReal.ofReal C := by
    convert hcentralNormalized using 1
    apply congrArg ENNReal.ofReal
    apply integral_congr_ae
    filter_upwards [] with row
    congr 1
    have hdot : realRowDot row normalized =
        ((∑ j, row j * w j : ℤ) : ℝ) / Real.sqrt W := by
      dsimp [realRowDot, normalized]
      calc
        ∑ j, (row j : ℝ) * ((w j : ℝ) / Real.sqrt W) =
            ∑ j, ((row j : ℝ) * (w j : ℝ)) / Real.sqrt W := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = (∑ j, (row j : ℝ) * (w j : ℝ)) / Real.sqrt W := by
          rw [Finset.sum_div]
        _ = ((∑ j, row j * w j : ℤ) : ℝ) / Real.sqrt W := by
          push_cast
          rfl
    rw [hdot]
    change
      -(((23 / 10 : ℝ) * aMass) / (A : ℝ) ^ 2) *
          (((∑ j, row j * w j : ℤ) : ℝ) ^ 2) =
        -((23 / 10 : ℝ) * x) *
          ((((∑ j, row j * w j : ℤ) : ℝ) / Real.sqrt W) ^ 2)
    dsimp [aMass, x]
    field_simp [hW.ne', (sq_pos_of_pos hAReal).ne',
      (sq_pos_of_pos hbReal).ne', hsqrtWne]
    rw [hsqrtW]

  have hB : 1 < (q : ℝ) / (A : ℝ) := by
    have hmarginReal : (3 : ℝ) * inputThreshold ≤ q := by
      exact_mod_cast hmargin
    have hAThreshold : (A : ℝ) < inputThreshold := by nlinarith
    apply (lt_div_iff₀ hAReal).2
    nlinarith
  have hassembly := sparseRow_wrapped_le_retainedZero_add_conditionedTail
    w i (U : ℝ) ((23 / 10) * aMass) C hq hi hUReal rfl
      (by positivity) hB hC hcentral
  have htail := retainedConditionedImageTail_le_nearSemantic_marginThree
    hthreshold hA hUReal.le
      (x := x) (a := aMass)
      (by dsimp [x]; rw [hsplitReal]) rfl haBand.2 hmargin
  have hsemanticTailNonneg : 0 ≤ tail := by
    dsimp [tail]
    exact nearConditionedTail_nonneg haPos hax haBand.2
  have hsum := hassembly.trans
    (add_le_add (le_refl (ENNReal.ofReal C)) (ENNReal.ofReal_mono htail))
  have hwrappedENN :
      ENNReal.ofReal
          (∫ row, wrappedGaussianKernel q
            (((23 / 10 : ℝ) * aMass) / (A : ℝ) ^ 2)
            (∑ j, row j * w j)
            ∂(sparseRademacherRow d).toMeasure) ≤
        ENNReal.ofReal (681 / 1250) := by
    calc
      _ ≤ ENNReal.ofReal C + ENNReal.ofReal tail := hsum
      _ = ENNReal.ofReal (C + tail) :=
        (ENNReal.ofReal_add hC hsemanticTailNonneg).symm
      _ = ENNReal.ofReal (681 / 1250) := by
        congr 1
        dsimp [C, tail]
        ring
  have hcoefficient :
      ((23 / 10 : ℝ) * aMass) / (A : ℝ) ^ 2 =
        (23 / 10) / (inputThreshold : ℝ) ^ 2 := by
    dsimp [aMass]
    field_simp [(sq_pos_of_pos hAReal).ne', (sq_pos_of_pos hbReal).ne']
  rw [hcoefficient] at hwrappedENN
  exact (ENNReal.ofReal_le_ofReal_iff
    (by norm_num : (0 : ℝ) ≤ 681 / 1250)).mp hwrappedENN

/-- Retained near profile in the wrapped form shared by affine and centered tails. -/
theorem sparseThresholdNearDominantWrappedRow128Bound_marginThree_of_replay
    (replay : CertificateContracts.SparseL2ThresholdNearReplay128) :
    ∀ (q d : ℕ) (w : Fin d → ℤ) (inputThreshold : ℕ),
      Odd q → 0 < inputThreshold → InputThresholdAtMostNorm inputThreshold w →
      3 * inputThreshold ≤ q →
      (∀ i, 50 * (w i).natAbs ≤ 49 * inputThreshold) →
      (∃ i, 3 * inputThreshold < 4 * (w i).natAbs) →
      ∃ support : Finset (Fin d),
        ∫ row, wrappedGaussianKernel q ((23 / 10 : ℝ) / (inputThreshold : ℝ) ^ 2)
            (∑ i, row i * (if i ∈ support then w i else 0))
            ∂(sparseRademacherRow d).toMeasure ≤ 681 / 1250 := by
  intro q d w inputThreshold hq hthreshold hnorm hmargin hcoordinate hnear
  obtain ⟨i, hi⟩ := hnear
  obtain ⟨support, hiSupport, hlower, hupper⟩ :=
    exists_threshold_subprofile_preserving_near
      w inputThreshold i hthreshold hnorm hcoordinate
  let compact : Fin d → ℤ := fun j ↦ if j ∈ support then w j else 0
  have hcompactCoordinate : ∀ j,
      50 * (compact j).natAbs ≤ 49 * inputThreshold := by
    intro j
    by_cases hj : j ∈ support
    · simpa [compact, hj] using hcoordinate j
    · simp [compact, hj]
  have hcompactNear : 3 * inputThreshold < 4 * (compact i).natAbs := by
    simpa [compact, hiSupport] using hi
  have hcompact := sparseRow_nearCompact_wrapped_le_681_div_1250_of_replay
    replay compact i hq hthreshold hlower hupper hcompactCoordinate hcompactNear hmargin
  exact ⟨support, hcompact⟩

/-- Complete centered near provider obtained from the shared wrapped bound. -/
theorem sparseThresholdNearDominantRow128Bound_marginThree_of_replay
    (replay : CertificateContracts.SparseL2ThresholdNearReplay128) :
    SparseThresholdNearDominantRow128BoundAt (NonnegativeRatio.ofNat 3) := by
  intro q d w b hq _hcentered hb hnorm hmodulus hcoordinate hnear
  have hmargin : 3 * b ≤ q := by
    simpa [InputThresholdWithinModulus, NonnegativeRatio.ofNat] using hmodulus
  obtain ⟨support, hwrapped⟩ :=
    sparseThresholdNearDominantWrappedRow128Bound_marginThree_of_replay
      replay q d w b hq hb hnorm hmargin hcoordinate hnear
  exact (sparseRow_centeredGaussian_le_wrappedGaussianKernel_restrict w support hq
    (by positivity : 0 < (23 / 10 : ℝ) / (b : ℝ) ^ 2)).trans hwrapped

end CertifiedJL
