/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.Affine.Data.EndpointNumeric
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Soundness.TargetNumeric
import CertifiedJL.Projection.L2.Lower.BalancedTernary.L2General

/-! # Executable exact checks for affine lower-tail endpoints -/

namespace CertifiedJL.AffineEndpointNumeric

open DominantNumeric

private def singletonR (t : ℚ) : DominantNumeric.DInterval := Exp.negUpper 160 (9 * t) 64
private def singletonU (t : ℚ) : DominantNumeric.DInterval :=
  Exp.negUpper 160 ((2401 / 2500) * t) 64
private def singletonV (t : ℚ) : DominantNumeric.DInterval :=
  Exp.negUpper 160 ((10201 / 2500) * t) 64

/-- Interval expression enclosing the singleton Gaussian envelope `S(t)`. -/
def singletonEnvelopeInterval (t : ℚ) : DominantNumeric.DInterval :=
  div (rat 1 + singletonR t + singletonU t + singletonV t)
    (rat 2 * (rat 1 - singletonR t))

/-- Executable validity check for the interval expression for `S(t)`, using
separate simple rational caps for its three exponential terms. -/
def singletonEnvelopeCheck (t cap rCap uCap vCap : ℚ) : Bool :=
  decide (
    0 ≤ t ∧
    0 < (rat 2 * (rat 1 - singletonR t)).lo ∧
    (singletonR t).upperRat ≤ rCap ∧
    (singletonU t).upperRat ≤ uCap ∧
    (singletonV t).upperRat ≤ vCap ∧
    0 ≤ cap ∧ rCap < 1 ∧
    1 + rCap + uCap + vCap ≤ cap * (2 * (1 - rCap)))

/-- Direct interval check for a singleton-envelope cap. This is convenient for
new exact endpoints that do not need separately published exponential caps. -/
def singletonEnvelopeDirectCheck (t cap : ℚ) : Bool :=
  decide (
    0 ≤ t ∧
    0 < (rat 2 * (rat 1 - singletonR t)).lo ∧
    0 ≤ cap ∧
    (singletonEnvelopeInterval t).upperRat ≤ cap)

private theorem singletonEnvelopeCheck_of (t cap rCap uCap vCap : ℚ)
    (ht : 0 ≤ t)
    (hden : 0 < (rat 2 * (rat 1 - singletonR t)).lo)
    (hr : (singletonR t).upperRat ≤ rCap)
    (hu : (singletonU t).upperRat ≤ uCap)
    (hv : (singletonV t).upperRat ≤ vCap)
    (hcap : 0 ≤ cap) (hrLt : rCap < 1)
    (hcross : 1 + rCap + uCap + vCap ≤ cap * (2 * (1 - rCap))) :
    singletonEnvelopeCheck t cap rCap uCap vCap = true := by
  simp only [singletonEnvelopeCheck, decide_eq_true_eq]
  exact ⟨ht, hden, hr, hu, hv, hcap, hrLt, hcross⟩

private theorem singletonEnvelopeInterval_contains (t cap : ℚ)
    (rCap uCap vCap : ℚ)
    (hcheck : singletonEnvelopeCheck t cap rCap uCap vCap = true) :
    (singletonEnvelopeInterval t).Contains (singletonGaussianEnvelope (t : ℝ)) := by
  have h := of_decide_eq_true (by simpa only [singletonEnvelopeCheck] using hcheck)
  rcases h with ⟨ht, hden, _⟩
  have hr := Exp.negUpper_contains (p := 160) (k := 64) (x := 9 * t) (by positivity)
  have hu := Exp.negUpper_contains (p := 160) (k := 64)
    (x := (2401 / 2500) * t) (by positivity)
  have hv := Exp.negUpper_contains (p := 160) (k := 64)
    (x := (10201 / 2500) * t) (by positivity)
  have hnum := Interval.contains_add
    (Interval.contains_add (Interval.contains_add (contains_rat 1) hr) hu) hv
  have hdenContains := Interval.contains_mul (contains_rat 2)
    (Interval.contains_sub (contains_rat 1) hr)
  have hdiv := contains_div hden hnum hdenContains
  unfold singletonEnvelopeInterval at hdiv ⊢
  simp only [singletonR, singletonU, singletonV] at hdiv ⊢
  unfold singletonGaussianEnvelope
  convert hdiv using 1 <;> push_cast <;> ring

/-- A checked rational cap is a sound upper bound for `S(t)`. -/
theorem singletonEnvelope_le_cap (t cap rCap uCap vCap : ℚ)
    (hcheck : singletonEnvelopeCheck t cap rCap uCap vCap = true) :
    singletonGaussianEnvelope (t : ℝ) ≤ (cap : ℝ) := by
  have h := of_decide_eq_true (by simpa only [singletonEnvelopeCheck] using hcheck)
  rcases h with ⟨ht, _hdenInterval,
    hrCap, huCap, hvCap, hcapNonneg, hrLt, hcross⟩
  have hr := Exp.negUpper_contains (p := 160) (k := 64) (x := 9 * t) (by positivity)
  have hu := Exp.negUpper_contains (p := 160) (k := 64)
    (x := (2401 / 2500) * t) (by positivity)
  have hv := Exp.negUpper_contains (p := 160) (k := 64)
    (x := (10201 / 2500) * t) (by positivity)
  have hrUpper : Real.exp (-9 * (t : ℝ)) ≤ (rCap : ℝ) := by
    calc
      Real.exp (-9 * (t : ℝ)) ≤ ((singletonR t).upperRat : ℝ) := by
        convert hr.2 using 1 <;>
          simp only [singletonR, Interval.upperRat, Dyadic.cast_toRat,
            DominantNumeric.precision, Rat.cast_neg, Rat.cast_mul, Rat.cast_ofNat] <;> ring
      _ ≤ (rCap : ℝ) := (Rat.cast_le (K := ℝ)).2 hrCap
  have huUpper : Real.exp (-(49 / 50 : ℝ) ^ 2 * t) ≤ (uCap : ℝ) := by
    calc
      Real.exp (-(49 / 50 : ℝ) ^ 2 * t) ≤ ((singletonU t).upperRat : ℝ) := by
        convert hu.2 using 1 <;>
          simp only [singletonU, Interval.upperRat, Dyadic.cast_toRat,
            DominantNumeric.precision, Rat.cast_neg, Rat.cast_mul, Rat.cast_div,
            Rat.cast_ofNat] <;> ring
      _ ≤ (uCap : ℝ) := (Rat.cast_le (K := ℝ)).2 huCap
  have hvUpper : Real.exp (-(3 - 49 / 50 : ℝ) ^ 2 * t) ≤ (vCap : ℝ) := by
    calc
      Real.exp (-(3 - 49 / 50 : ℝ) ^ 2 * t) ≤ ((singletonV t).upperRat : ℝ) := by
        convert hv.2 using 1 <;>
          simp only [singletonV, Interval.upperRat, Dyadic.cast_toRat,
            DominantNumeric.precision, Rat.cast_neg, Rat.cast_mul, Rat.cast_div,
            Rat.cast_ofNat] <;> ring
      _ ≤ (vCap : ℝ) := (Rat.cast_le (K := ℝ)).2 hvCap
  have hden : 0 < 2 * (1 - Real.exp (-9 * (t : ℝ))) := by
    have : Real.exp (-9 * (t : ℝ)) < 1 := hrUpper.trans_lt
      (by simpa only [Rat.cast_one] using (Rat.cast_lt (K := ℝ)).2 hrLt)
    positivity
  rw [singletonGaussianEnvelope, div_le_iff₀ hden]
  calc
    1 + Real.exp (-9 * (t : ℝ)) + Real.exp (-(49 / 50 : ℝ) ^ 2 * t) +
          Real.exp (-(3 - 49 / 50 : ℝ) ^ 2 * t) ≤
        1 + rCap + uCap + vCap := by linarith
    _ ≤ (cap : ℝ) * (2 * (1 - (rCap : ℝ))) := by
      have hcrossReal := (Rat.cast_le (K := ℝ)).2 hcross
      push_cast at hcrossReal
      exact hcrossReal
    _ ≤ (cap : ℝ) * (2 * (1 - Real.exp (-9 * (t : ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ ((Rat.cast_nonneg (K := ℝ)).2 hcapNonneg)
      nlinarith

/-- A direct successful interval check is a sound upper bound for the
singleton Gaussian envelope. -/
theorem singletonEnvelope_le_cap_of_directCheck (t cap : ℚ)
    (hcheck : singletonEnvelopeDirectCheck t cap = true) :
    singletonGaussianEnvelope (t : ℝ) ≤ (cap : ℝ) := by
  have h := of_decide_eq_true (by
    simpa only [singletonEnvelopeDirectCheck] using hcheck)
  rcases h with ⟨ht, hden, _hcapNonneg, hcap⟩
  have hr := Exp.negUpper_contains (p := 160) (k := 64) (x := 9 * t) (by positivity)
  have hu := Exp.negUpper_contains (p := 160) (k := 64)
    (x := (2401 / 2500) * t) (by positivity)
  have hv := Exp.negUpper_contains (p := 160) (k := 64)
    (x := (10201 / 2500) * t) (by positivity)
  have hnum := Interval.contains_add
    (Interval.contains_add (Interval.contains_add (contains_rat 1) hr) hu) hv
  have hdenContains := Interval.contains_mul (contains_rat 2)
    (Interval.contains_sub (contains_rat 1) hr)
  have hcontains := contains_div hden hnum hdenContains
  simp only [singletonR] at hcontains
  have henvelope : (singletonEnvelopeInterval t).Contains
      (singletonGaussianEnvelope (t : ℝ)) := by
    unfold singletonEnvelopeInterval
    simp only [singletonR, singletonU, singletonV]
    unfold singletonGaussianEnvelope
    convert hcontains using 1 <;> push_cast <;> ring
  have hupper : singletonGaussianEnvelope (t : ℝ) ≤
      ((singletonEnvelopeInterval t).upperRat : ℝ) := by
    simpa only [Interval.upperRat, Dyadic.cast_toRat] using henvelope.2
  exact hupper.trans ((Rat.cast_le (K := ℝ)).2 hcap)

/-- Executable numerical check for one L2 endpoint. -/
def l2EndpointCheck (e : L2EndpointData) : Bool :=
  singletonEnvelopeCheck e.singletonTilt e.singletonCap
    e.singletonRCap e.singletonUCap e.singletonVCap &&
  decide (1250 / 2401 ≤ e.singletonTilt) &&
  decide ((e.diffuseTilt = 33 / 10 ∧ e.diffuseCap = 97 / 200) ∨
    (e.diffuseTilt = 5 / 2 ∧ e.diffuseCap = 539 / 1000)) &&
  SparseThresholdDominant.TargetNumeric.certifiedCheckAt
    e.rows e.squaredNormFloor e.singletonTilt 1 e.singletonCap
    ((1 / 2) ^ e.bits) &&
  SparseThresholdDominant.TargetNumeric.certifiedCheckAt
    e.rows e.squaredNormFloor (23 / 10) 1 (681 / 1250)
    ((1 / 2) ^ e.bits) &&
  SparseThresholdDominant.TargetNumeric.certifiedCheckAt
    e.rows e.squaredNormFloor e.diffuseTilt 1 e.diffuseCap
    ((1 / 2) ^ e.bits)

private theorem l2EndpointCheck_of (e : L2EndpointData)
    (hsingleton : singletonEnvelopeCheck e.singletonTilt e.singletonCap
      e.singletonRCap e.singletonUCap e.singletonVCap = true)
    (ht : 1250 / 2401 ≤ e.singletonTilt)
    (hselected : (e.diffuseTilt = 33 / 10 ∧ e.diffuseCap = 97 / 200) ∨
      (e.diffuseTilt = 5 / 2 ∧ e.diffuseCap = 539 / 1000))
    (hsingletonGrowth : SparseThresholdDominant.TargetNumeric.certifiedCheckAt
      e.rows e.squaredNormFloor e.singletonTilt 1 e.singletonCap ((1 / 2) ^ e.bits) = true)
    (hnear : SparseThresholdDominant.TargetNumeric.certifiedCheckAt
      e.rows e.squaredNormFloor (23 / 10) 1 (681 / 1250) ((1 / 2) ^ e.bits) = true)
    (hdiffuse : SparseThresholdDominant.TargetNumeric.certifiedCheckAt
      e.rows e.squaredNormFloor e.diffuseTilt 1 e.diffuseCap ((1 / 2) ^ e.bits) = true) :
    l2EndpointCheck e = true := by
  unfold l2EndpointCheck
  rw [hsingleton,
    show decide (1250 / 2401 ≤ e.singletonTilt) = true by
      simpa only [decide_eq_true_eq] using ht,
    show decide ((e.diffuseTilt = 33 / 10 ∧ e.diffuseCap = 97 / 200) ∨
      (e.diffuseTilt = 5 / 2 ∧ e.diffuseCap = 539 / 1000)) = true by
      simpa only [decide_eq_true_eq] using hselected,
    hsingletonGrowth, hnear, hdiffuse]
  rfl

/-- A checked L2 record proves exactly the finite-tilt inequality consumed by
the general affine L2 schema. -/
theorem l2EndpointCheck_sound (e : L2EndpointData)
    (hcheck : l2EndpointCheck e = true) :
    (1250 / 2401 : ℝ) ≤ e.singletonTilt ∧
    max (affineL2SingletonTiltBound e.rows e.squaredNormFloor e.singletonTilt)
      (max (affineL2NearBound e.rows e.squaredNormFloor)
        (affineL2DiffuseBound e.rows e.squaredNormFloor)) <
      (2 : ℝ)⁻¹ ^ e.bits := by
  simp only [l2EndpointCheck, Bool.and_eq_true] at hcheck
  rcases hcheck with
    ⟨⟨⟨⟨⟨hsingletonCap, ht⟩, hselected⟩, hsingleton⟩, hnear⟩, hdiffuse⟩
  have htReal : (1250 / 2401 : ℝ) ≤ e.singletonTilt := by
    have htRat := of_decide_eq_true ht
    have htCast : (((1250 / 2401 : ℚ) : ℝ) ≤ (e.singletonTilt : ℝ)) :=
      (Rat.cast_le (K := ℝ)).2 htRat
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at htCast
    exact htCast
  have hselected' := of_decide_eq_true hselected
  have hSNonneg : 0 ≤ singletonGaussianEnvelope (e.singletonTilt : ℝ) := by
    have htpos : 0 < (e.singletonTilt : ℝ) := lt_of_lt_of_le (by norm_num) htReal
    have hexp : Real.exp (-9 * (e.singletonTilt : ℝ)) < 1 := by
      rw [Real.exp_lt_one_iff]
      nlinarith
    unfold singletonGaussianEnvelope
    positivity
  have hS := SparseThresholdDominant.TargetNumeric.certifiedCheckAt_sound
    e.rows e.squaredNormFloor e.singletonTilt 1
    e.singletonCap ((1 / 2) ^ e.bits) (singletonGaussianEnvelope e.singletonTilt)
    hSNonneg (singletonEnvelope_le_cap e.singletonTilt e.singletonCap
      e.singletonRCap e.singletonUCap e.singletonVCap hsingletonCap)
    hsingleton
  have hN := SparseThresholdDominant.TargetNumeric.certifiedCheckAt_sound
    e.rows e.squaredNormFloor (23 / 10) 1
    (681 / 1250) ((1 / 2) ^ e.bits) (681 / 1250) (by norm_num) (by norm_num) hnear
  have hDNonneg : (0 : ℝ) ≤ e.diffuseCap := by
    rcases hselected' with hselected' | hselected' <;>
      norm_num [hselected'.2]
  have hD := SparseThresholdDominant.TargetNumeric.certifiedCheckAt_sound
    e.rows e.squaredNormFloor e.diffuseTilt 1
    e.diffuseCap ((1 / 2) ^ e.bits) e.diffuseCap hDNonneg (by norm_num) hdiffuse
  refine ⟨htReal, max_lt ?_ (max_lt ?_ ?_)⟩
  · simpa [affineL2SingletonTiltBound, NonnegativeRatio.ofNat,
      one_pow, inv_pow] using hS
  · simpa [affineL2NearBound, NonnegativeRatio.ofNat, one_pow, inv_pow] using hN
  · unfold affineL2DiffuseBound
    rcases hselected' with hselected | hselected
    · exact (min_le_left _ _).trans_lt
        (by simpa [hselected.1, hselected.2, one_pow, inv_pow] using hD)
    · exact (min_le_right _ _).trans_lt
        (by simpa [hselected.1, hselected.2, one_pow, inv_pow] using hD)

/-- Executable numerical check for one L-infinity endpoint. -/
def lInfEndpointCheck (e : LInfEndpointData) : Bool :=
  decide (0 < e.capDenominator ∧
    8 * e.capNumerator ≤ 3 * e.capDenominator ∧
    ((e.diffuseTilt = 33 / 10 ∧ e.diffuseCap = 97 / 200) ∨
      (e.diffuseTilt = 5 / 2 ∧ e.diffuseCap = 539 / 1000)) ∧
    (1 / 2 : ℚ) ^ e.rows < (1 / 2) ^ e.bits) &&
  SparseThresholdDominant.TargetNumeric.certifiedCheckAt e.rows e.rows e.diffuseTilt
    ((e.capNumerator / e.capDenominator : ℚ) ^ 2) e.diffuseCap
    ((1 / 2) ^ e.bits)

/-- Soundness of one checked L-infinity endpoint. -/
theorem lInfEndpointCheck_sound (e : LInfEndpointData)
    (hcheck : lInfEndpointCheck e = true) :
    0 < e.capDenominator ∧
    8 * e.capNumerator ≤ 3 * e.capDenominator ∧
    (1 / 2 : ℝ) ^ e.rows < (2 : ℝ)⁻¹ ^ e.bits ∧
    (Real.exp ((e.diffuseTilt : ℝ) *
      ((e.capNumerator : ℝ) / e.capDenominator) ^ 2) * e.diffuseCap) ^ e.rows <
      (2 : ℝ)⁻¹ ^ e.bits := by
  simp only [lInfEndpointCheck, Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨hbasic, hratio⟩
  obtain ⟨hden, hcap, hselected, hhalf⟩ := of_decide_eq_true hbasic
  have hK : (0 : ℝ) ≤ e.diffuseCap := by
    rcases hselected with hselected | hselected <;> norm_num [hselected.2]
  have h := SparseThresholdDominant.TargetNumeric.certifiedCheckAt_sound
    e.rows e.rows e.diffuseTilt
    ((e.capNumerator / e.capDenominator : ℚ) ^ 2) e.diffuseCap
    ((1 / 2) ^ e.bits) e.diffuseCap hK (by norm_num) hratio
  refine ⟨hden, hcap, ?_, ?_⟩
  · have hhalfReal := (Rat.cast_lt (K := ℝ)).2 hhalf
    norm_num only [Rat.cast_pow, Rat.cast_div, Rat.cast_one,
      Rat.cast_ofNat] at hhalfReal
    simpa only [one_div] using hhalfReal
  · rw [mul_pow, ← Real.exp_nat_mul]
    convert h using 1 <;> push_cast <;> field_simp <;> ring

private theorem singleton23Over8_checked : singletonEnvelopeCheck
    (23 / 8) (265806766031 / 500000000000) (5790 / 1000000000000000)
      (63219024661671 / 1000000000000000) (8039449077 / 1000000000000000) = true := by
  apply singletonEnvelopeCheck_of
  all_goals first | unfold singletonR | unfold singletonU | unfold singletonV | skip
  all_goals decide +kernel
private theorem singleton109Over50_checked : singletonEnvelopeCheck
    (109 / 50) (140421353901 / 250000000000) (3013994 / 1000000000000000)
      (123233789507952 / 1000000000000000) (137035300150 / 1000000000000000) = true := by
  apply singletonEnvelopeCheck_of
  all_goals first | unfold singletonR | unfold singletonU | unfold singletonV | skip
  all_goals decide +kernel
private theorem singleton17Over5_checked : singletonEnvelopeCheck
    (17 / 5) (129773016307 / 250000000000) (52 / 1000000000000000)
      (38183186661915 / 1000000000000000) (943792033 / 1000000000000000) = true := by
  apply singletonEnvelopeCheck_of
  all_goals first | unfold singletonR | unfold singletonU | unfold singletonV | skip
  all_goals decide +kernel
private theorem singleton11Over5_checked : singletonEnvelopeCheck
    (11 / 5) (35031737657 / 62500000000) (2517499 / 1000000000000000)
      (120889303405810 / 1000000000000000) (126296277819 / 1000000000000000) = true := by
  apply singletonEnvelopeCheck_of
  all_goals first | unfold singletonR | unfold singletonU | unfold singletonV | skip
  all_goals decide +kernel
private theorem singleton9Over5_checked : singletonEnvelopeCheck
    (9 / 5) (147269709277 / 250000000000) (92136009 / 1000000000000000)
      (177511479308014 / 1000000000000000) (645994221028 / 1000000000000000) = true := by
  apply singletonEnvelopeCheck_of
  all_goals first | unfold singletonR | unfold singletonU | unfold singletonV | skip
  all_goals decide +kernel
private theorem singleton14Over5_checked : singletonEnvelopeCheck
    (14 / 5) (66746976167 / 125000000000) (11371 / 1000000000000000)
      (67940700889620 / 1000000000000000) (10917757128 / 1000000000000000) = true := by
  apply singletonEnvelopeCheck_of
  all_goals first | unfold singletonR | unfold singletonU | unfold singletonV | skip
  all_goals decide +kernel
private theorem singleton107Over50_checked : singletonEnvelopeCheck
    (107 / 50) (141027673453 / 250000000000) (4320046 / 1000000000000000)
      (128060048008613 / 1000000000000000) (161330419667 / 1000000000000000) = true := by
  apply singletonEnvelopeCheck_of
  all_goals first | unfold singletonR | unfold singletonU | unfold singletonV | skip
  all_goals decide +kernel
private theorem singleton43Over20_checked : singletonEnvelopeCheck
    (43 / 20) (28174773369 / 50000000000) (3948224 / 1000000000000000)
      (126836046371552 / 1000000000000000) (154879989846 / 1000000000000000) = true := by
  apply singletonEnvelopeCheck_of
  all_goals first | unfold singletonR | unfold singletonU | unfold singletonV | skip
  all_goals decide +kernel

theorem l2_192_11_128_checked : l2EndpointCheck l2_192_11_128 = true := by
  unfold l2_192_11_128
  apply l2EndpointCheck_of _ singleton23Over8_checked <;> norm_num <;> decide +kernel
theorem l2_256_27_128_checked : l2EndpointCheck l2_256_27_128 = true := by
  unfold l2_256_27_128
  apply l2EndpointCheck_of _ singleton109Over50_checked <;> norm_num <;> decide +kernel
theorem l2_256_9_194_checked : l2EndpointCheck l2_256_9_194 = true := by
  unfold l2_256_9_194
  apply l2EndpointCheck_of _ singleton17Over5_checked <;> norm_num <;> decide +kernel
theorem l2_384_40_192_checked : l2EndpointCheck l2_384_40_192 = true := by
  unfold l2_384_40_192
  apply l2EndpointCheck_of _ singleton11Over5_checked <;> norm_num <;> decide +kernel
theorem l2_512_73_193_checked : l2EndpointCheck l2_512_73_193 = true := by
  unfold l2_512_73_193
  apply l2EndpointCheck_of _ singleton9Over5_checked <;> norm_num <;> decide +kernel
theorem l2_512_54_256_checked : l2EndpointCheck l2_512_54_256 = true := by
  unfold l2_512_54_256
  apply l2EndpointCheck_of _ singleton109Over50_checked <;> norm_num <;> decide +kernel
theorem l2_195_12_128_checked : l2EndpointCheck l2_195_12_128 = true := by
  unfold l2_195_12_128
  apply l2EndpointCheck_of _ singleton14Over5_checked <;> norm_num <;> decide +kernel
theorem l2_264_29_128_checked : l2EndpointCheck l2_264_29_128 = true := by
  unfold l2_264_29_128
  apply l2EndpointCheck_of _ singleton107Over50_checked <;> norm_num <;> decide +kernel
theorem l2_394_43_192_checked : l2EndpointCheck l2_394_43_192 = true := by
  unfold l2_394_43_192
  apply l2EndpointCheck_of _ singleton107Over50_checked <;> norm_num <;> decide +kernel
theorem l2_524_57_256_checked : l2EndpointCheck l2_524_57_256 = true := by
  unfold l2_524_57_256
  apply l2EndpointCheck_of _ singleton43Over20_checked <;> norm_num <;> decide +kernel

theorem lInf_192_279_1000_129_checked :
    lInfEndpointCheck lInf_192_279_1000_129 = true := by
  unfold lInfEndpointCheck lInf_192_279_1000_129; decide +kernel
theorem lInf_256_6_25_197_checked : lInfEndpointCheck lInf_256_6_25_197 = true := by
  unfold lInfEndpointCheck lInf_256_6_25_197; decide +kernel
theorem lInf_256_331_1000_133_checked :
    lInfEndpointCheck lInf_256_331_1000_133 = true := by
  unfold lInfEndpointCheck lInf_256_331_1000_133; decide +kernel
theorem lInf_384_331_1000_200_checked :
    lInfEndpointCheck lInf_384_331_1000_200 = true := by
  unfold lInfEndpointCheck lInf_384_331_1000_200; decide +kernel
theorem lInf_512_331_1000_266_checked :
    lInfEndpointCheck lInf_512_331_1000_266 = true := by
  unfold lInfEndpointCheck lInf_512_331_1000_266; decide +kernel
theorem lInf_512_46_125_206_checked :
    lInfEndpointCheck lInf_512_46_125_206 = true := by
  unfold lInfEndpointCheck lInf_512_46_125_206; decide +kernel
theorem lInf_256_67_200_130_checked :
    lInfEndpointCheck lInf_256_67_200_130 = true := by
  unfold lInfEndpointCheck lInf_256_67_200_130; decide +kernel
theorem lInf_256_9_25_109_checked : lInfEndpointCheck lInf_256_9_25_109 = true := by
  unfold lInfEndpointCheck lInf_256_9_25_109; decide +kernel
theorem lInf_462_9_25_197_checked : lInfEndpointCheck lInf_462_9_25_197 = true := by
  unfold lInfEndpointCheck lInf_462_9_25_197; decide +kernel

/-- Every raw L2 record passes its exact executable check. -/
theorem l2Endpoints_all_checked : l2Endpoints.all l2EndpointCheck = true := by
  simp [l2Endpoints, l2_192_11_128_checked, l2_256_27_128_checked,
    l2_256_9_194_checked, l2_384_40_192_checked, l2_512_73_193_checked,
    l2_512_54_256_checked, l2_195_12_128_checked, l2_264_29_128_checked,
    l2_394_43_192_checked, l2_524_57_256_checked]

/-- Every raw L-infinity record passes its exact executable check. -/
theorem lInfEndpoints_all_checked : lInfEndpoints.all lInfEndpointCheck = true := by
  simp [lInfEndpoints, lInf_192_279_1000_129_checked, lInf_256_6_25_197_checked,
    lInf_256_331_1000_133_checked, lInf_384_331_1000_200_checked,
    lInf_512_331_1000_266_checked, lInf_512_46_125_206_checked,
    lInf_256_67_200_130_checked, lInf_256_9_25_109_checked,
    lInf_462_9_25_197_checked]

/-- The L2 raw list covers exactly the required `(rows, floor, bits)` keys. -/
theorem l2Endpoints_coverage :
    l2Endpoints.map (fun e => (e.rows, e.squaredNormFloor, e.bits)) =
      [(192, 11, 128), (256, 27, 128), (256, 9, 194), (384, 40, 192),
       (512, 73, 193), (512, 54, 256), (195, 12, 128), (264, 29, 128),
       (394, 43, 192), (524, 57, 256)] := by decide

/-- The L-infinity raw list covers exactly the required `(rows, cap, bits)` keys. -/
theorem lInfEndpoints_coverage :
    lInfEndpoints.map (fun e => (e.rows, e.capNumerator, e.capDenominator, e.bits)) =
      [(192, 279, 1000, 129), (256, 6, 25, 197), (256, 331, 1000, 133),
       (384, 331, 1000, 200), (512, 331, 1000, 266), (512, 46, 125, 206),
       (256, 67, 200, 130), (256, 9, 25, 109), (462, 9, 25, 197)] := by decide

end CertifiedJL.AffineEndpointNumeric
