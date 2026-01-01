/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Interval.Reflection
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Unrestricted.Analytic
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Dominant.Soundness.ThresholdDominantRetainedNumeric128
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Near.RetainedAssembly

/-!
# Endpoint and final-ratio bounds for the retained dominant branch
-/

namespace CertifiedJL

private theorem expNegDivOneSubExpNeg_antitone
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

/-- The two oriented active-image tails decrease as the normalized modulus
increases. -/
theorem retainedActiveImageTail_antitone_modulus
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
  have hminus := expNegDivOneSubExpNeg_antitone
    (mul_le_mul_of_nonneg_left hminusSq halpha.le)
    (mul_pos halpha hminusRatePos)
    (mul_le_mul_of_nonneg_left hminusRate halpha.le)
  have hplus := expNegDivOneSubExpNeg_antitone
    (mul_le_mul_of_nonneg_left hplusSq halpha.le)
    (mul_pos halpha hplusRatePos)
    (mul_le_mul_of_nonneg_left hplusRate halpha.le)
  simpa only [neg_mul] using add_le_add hminus hplus

/-- At public modulus margin three, the exact conditioned image tails are no
larger than the semantic endpoint used by the retained interval certificate. -/
theorem retainedConditionedImageTail_le_semantic_marginThree
    {q A : ℕ} {V : ℝ} (hA : 0 < A) (hV : 0 ≤ V)
    (hmodulus : 3 ≤ (q : ℝ) / (A : ℝ)) :
    let x : ℝ := 1 + V / (A : ℝ) ^ 2
    (retainedInactiveImageTail q A V (23 / 10) +
        retainedActiveImageTail q A V (23 / 10)) / 2 ≤
      (ThresholdNearCoarse128.semanticInactiveTail x 1 +
        ThresholdNearCoarse128.semanticActiveTail x 1) / 2 := by
  dsimp only
  let u : ℝ := V / (A : ℝ) ^ 2
  let B : ℝ := (q : ℝ) / (A : ℝ)
  let alpha : ℝ := (23 / 10) / (1 + (23 / 10) * u)
  have hAReal : 0 < (A : ℝ) := by exact_mod_cast hA
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have halpha : 0 < alpha := by dsimp [alpha]; positivity
  have hB : 3 ≤ B := by simpa only [B] using hmodulus
  have hc₀ : 0 < alpha * (3 : ℝ) ^ 2 := by positivity
  have hc : alpha * (3 : ℝ) ^ 2 ≤ alpha * B ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ halpha.le
    exact (sq_le_sq₀ (by norm_num) (by linarith)).2 hB
  have hinactive := twoSidedGeometricTail_antitone hc₀ hc
  have hinactive' :
      2 * Real.exp (-alpha * B ^ 2) /
          (1 - Real.exp (-alpha * B ^ 2) ^ 3) ≤
        2 * Real.exp (-alpha * (3 : ℝ) ^ 2) /
          (1 - Real.exp (-alpha * (3 : ℝ) ^ 2) ^ 3) := by
    simpa only [neg_mul] using hinactive
  have hactive := retainedActiveImageTail_antitone_modulus
    halpha (by norm_num : (1 : ℝ) < 3) hB
  have hD : ThresholdNearCoarse128.semanticD
      (1 + V / (A : ℝ) ^ 2) 1 = 1 + (23 / 10) * u := by
    dsimp [ThresholdNearCoarse128.semanticD, u]
    ring
  have hT : ThresholdNearCoarse128.semanticT
      (1 + V / (A : ℝ) ^ 2) 1 = alpha := by
    rw [ThresholdNearCoarse128.semanticT, hD]
    dsimp [alpha]
    ring
  have hM : ThresholdNearCoarse128.semanticM 1 = 3 := by
    norm_num [ThresholdNearCoarse128.semanticM]
  have hRho : ThresholdNearCoarse128.semanticRho
      (1 + V / (A : ℝ) ^ 2) 1 =
        Real.exp (-alpha * (3 : ℝ) ^ 2) := by
    rw [ThresholdNearCoarse128.semanticRho, hD]
    congr 1
    dsimp [alpha]
    have hden : 1 + (23 / 10 : ℝ) * u ≠ 0 := by positivity
    field_simp [hden]
    ring
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    retainedInactiveImageTail q A V (23 / 10) +
        retainedActiveImageTail q A V (23 / 10) =
      2 * Real.exp (-alpha * B ^ 2) /
          (1 - Real.exp (-alpha * B ^ 2) ^ 3) +
        (Real.exp (-alpha * (B - 1) ^ 2) /
            (1 - Real.exp (-alpha * (3 * B ^ 2 - 2 * B))) +
          Real.exp (-alpha * (B + 1) ^ 2) /
            (1 - Real.exp (-alpha * (3 * B ^ 2 + 2 * B)))) := by
      simp only [retainedInactiveImageTail, retainedActiveImageTail]
      rfl
    _ ≤ 2 * Real.exp (-alpha * (3 : ℝ) ^ 2) /
          (1 - Real.exp (-alpha * (3 : ℝ) ^ 2) ^ 3) +
        (Real.exp (-alpha * ((3 : ℝ) - 1) ^ 2) /
            (1 - Real.exp (-alpha * (3 * (3 : ℝ) ^ 2 - 2 * 3))) +
          Real.exp (-alpha * ((3 : ℝ) + 1) ^ 2) /
            (1 - Real.exp (-alpha * (3 * (3 : ℝ) ^ 2 + 2 * 3)))) :=
      add_le_add hinactive' hactive
    _ = ThresholdNearCoarse128.semanticInactiveTail
          (1 + V / (A : ℝ) ^ 2) 1 +
        ThresholdNearCoarse128.semanticActiveTail
          (1 + V / (A : ℝ) ^ 2) 1 := by
      rw [ThresholdNearCoarse128.semanticInactiveTail, hRho]
      simp only [ThresholdNearCoarse128.semanticActiveTail, hT, hM]

namespace ThresholdDominantRetainedRatio128

def precision : ℕ := 256
def squarings : ℕ := 32

private def enclosure : Interval precision :=
  Exp.posUpper precision (166750 / 2401) squarings *
    Interval.ofRat precision
      ((53 / 100 : ℚ) ^ 256 * 2 ^ 128 * 200 / 187)

private def check : Bool := Interval.upperLTCheck enclosure 1

private theorem check_eq_true : check = true := by
  set_option maxRecDepth 1000000 in
    decide +kernel

/-- The retained row cap fits inside the dominant high-activity share of the
128-bit failure budget. -/
theorem finalRatio :
    Real.exp ((23 / 10 : ℝ) * 29 * (2500 / 2401)) *
        (53 / 100 : ℝ) ^ 256 <
      (187 / 200 : ℝ) * (2 : ℝ)⁻¹ ^ 128 := by
  have hexp :
      (Exp.posUpper precision (166750 / 2401) squarings).Contains
        (Real.exp (166750 / 2401 : ℝ)) := by
    simpa using Exp.posUpper_contains
      (p := precision) (k := squarings) (x := (166750 / 2401 : ℚ))
      (by norm_num) (by norm_num [squarings]) (by
        change 0 < Dyadic.roundDown precision
          (1 - (166750 / 2401) / 2 ^ squarings)
        rw [Dyadic.roundDown, Int.floor_pos]
        norm_num [precision, squarings, Dyadic.scale])
  have hrat := Interval.contains_ofRat precision
    ((53 / 100 : ℚ) ^ 256 * 2 ^ 128 * 200 / 187)
  have hproduct := Interval.contains_mul hexp hrat
  have hlt :
      Real.exp (166750 / 2401 : ℝ) *
          ((((53 / 100 : ℚ) ^ 256 * 2 ^ 128 * 200 / 187) : ℚ) : ℝ) <
        1 := by
    simpa [enclosure] using
      Interval.lt_of_contains_of_upperLTCheck hproduct check_eq_true
  have hscaledDiv :
      (Real.exp (166750 / 2401 : ℝ) * (53 / 100 : ℝ) ^ 256 *
          2 ^ 128 * 200) / 187 < 1 := by
    convert hlt using 1 <;> norm_num <;> ring
  have hscaled :
      Real.exp (166750 / 2401 : ℝ) * (53 / 100 : ℝ) ^ 256 *
          2 ^ 128 * 200 < 187 :=
    (div_lt_one (by norm_num : (0 : ℝ) < 187)).mp hscaledDiv
  rw [show (23 / 10 : ℝ) * 29 * (2500 / 2401) = 166750 / 2401 by
      norm_num,
    inv_pow, inv_eq_one_div]
  rw [show (187 / 200 : ℝ) * (1 / 2 ^ 128) =
      (187 / 200) / 2 ^ 128 by ring]
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 128)).2
  apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 200)).2
  nlinarith

end ThresholdDominantRetainedRatio128
end CertifiedJL
