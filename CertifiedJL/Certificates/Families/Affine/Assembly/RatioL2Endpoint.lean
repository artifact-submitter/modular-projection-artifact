/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.Affine.Assembly.AffineL2General
import CertifiedJL.Certificates.Families.Affine.Soundness.EndpointNumeric
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Soundness.TargetNumeric

/-! # Exact rational-floor affine L2 endpoint factory -/

namespace CertifiedJL.AffineRatioEndpointNumeric

/-- Raw exact data for one rational-floor affine L2 endpoint. -/
structure L2EndpointData where
  rows : ℕ
  floorNumerator : ℕ
  floorDenominator : ℕ
  bits : ℕ
  singletonTilt : ℚ
  singletonCap : ℚ
  diffuseTilt : ℚ
  diffuseCap : ℚ
  deriving DecidableEq, Repr

/-- The exact rational floor encoded by an endpoint record. -/
def floorRat (e : L2EndpointData) : ℚ :=
  e.floorNumerator / e.floorDenominator

/-- The public nonnegative-ratio floor encoded by an endpoint record. -/
def floorRatio (e : L2EndpointData) (hden : 0 < e.floorDenominator) :
    NonnegativeRatio where
  numerator := e.floorNumerator
  denominator := e.floorDenominator
  denominator_pos := hden

/-- Exact executable check for a rational-floor affine L2 endpoint. -/
def endpointCheck (e : L2EndpointData) : Bool :=
  AffineEndpointNumeric.singletonEnvelopeDirectCheck
      e.singletonTilt e.singletonCap &&
    decide (0 < e.floorDenominator) &&
    decide (1250 / 2401 ≤ e.singletonTilt) &&
    decide ((e.diffuseTilt = 33 / 10 ∧ e.diffuseCap = 97 / 200) ∨
      (e.diffuseTilt = 5 / 2 ∧ e.diffuseCap = 539 / 1000)) &&
    SparseThresholdDominant.TargetNumeric.certifiedCheckAtRatio
      e.rows (floorRat e) e.singletonTilt 1 e.singletonCap
      ((1 / 2) ^ e.bits) &&
    SparseThresholdDominant.TargetNumeric.certifiedCheckAtRatio
      e.rows (floorRat e) (23 / 10) 1 (681 / 1250)
      ((1 / 2) ^ e.bits) &&
    SparseThresholdDominant.TargetNumeric.certifiedCheckAtRatio
      e.rows (floorRat e) e.diffuseTilt 1 e.diffuseCap
      ((1 / 2) ^ e.bits)

/-- A successful rational endpoint check supplies the exact finite-tilt
inequality consumed by the affine L2 assembly. -/
theorem endpointCheck_sound (e : L2EndpointData)
    (hcheck : endpointCheck e = true) :
    0 < e.floorDenominator ∧
    (1250 / 2401 : ℝ) ≤ e.singletonTilt ∧
    max (affineL2SingletonTiltBound e.rows (floorRat e : ℝ) e.singletonTilt)
      (max (affineL2NearBound e.rows (floorRat e : ℝ))
        (affineL2DiffuseBound e.rows (floorRat e : ℝ))) <
      (2 : ℝ)⁻¹ ^ e.bits := by
  simp only [endpointCheck, Bool.and_eq_true] at hcheck
  rcases hcheck with
    ⟨⟨⟨⟨⟨⟨hsingletonCap, hden⟩, ht⟩, hselected⟩,
      hsingleton⟩, hnear⟩, hdiffuse⟩
  have hden' : 0 < e.floorDenominator := of_decide_eq_true hden
  have htRat : 1250 / 2401 ≤ e.singletonTilt := of_decide_eq_true ht
  have htReal : (1250 / 2401 : ℝ) ≤ e.singletonTilt := by
    have hcast := (Rat.cast_le (K := ℝ)).2 htRat
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at hcast
    exact hcast
  have hselected' := of_decide_eq_true hselected
  have hSNonneg : 0 ≤ singletonGaussianEnvelope (e.singletonTilt : ℝ) := by
    have htpos : 0 < (e.singletonTilt : ℝ) :=
      lt_of_lt_of_le (by norm_num) htReal
    have hexp : Real.exp (-9 * (e.singletonTilt : ℝ)) < 1 := by
      rw [Real.exp_lt_one_iff]
      nlinarith
    unfold singletonGaussianEnvelope
    positivity
  have hS := SparseThresholdDominant.TargetNumeric.certifiedCheckAtRatio_sound
    e.rows (floorRat e) e.singletonTilt 1 e.singletonCap
    ((1 / 2) ^ e.bits) (singletonGaussianEnvelope e.singletonTilt)
    hSNonneg
    (AffineEndpointNumeric.singletonEnvelope_le_cap_of_directCheck
      e.singletonTilt e.singletonCap hsingletonCap)
    hsingleton
  have hN := SparseThresholdDominant.TargetNumeric.certifiedCheckAtRatio_sound
    e.rows (floorRat e) (23 / 10) 1 (681 / 1250)
    ((1 / 2) ^ e.bits) (681 / 1250) (by norm_num) (by norm_num) hnear
  have hDNonneg : (0 : ℝ) ≤ e.diffuseCap := by
    rcases hselected' with hselected' | hselected' <;>
      norm_num [hselected'.2]
  have hD := SparseThresholdDominant.TargetNumeric.certifiedCheckAtRatio_sound
    e.rows (floorRat e) e.diffuseTilt 1 e.diffuseCap
    ((1 / 2) ^ e.bits) e.diffuseCap hDNonneg (by norm_num) hdiffuse
  refine ⟨hden', htReal, max_lt ?_ (max_lt ?_ ?_)⟩
  · simpa [affineL2SingletonTiltBound, one_pow, inv_pow] using hS
  · simpa [affineL2NearBound, one_pow, inv_pow] using hN
  · unfold affineL2DiffuseBound
    rcases hselected' with hselected | hselected
    · exact (min_le_left _ _).trans_lt
        (by simpa [hselected.1, hselected.2, one_pow, inv_pow] using hD)
    · exact (min_le_right _ _).trans_lt
        (by simpa [hselected.1, hselected.2, one_pow, inv_pow] using hD)

end CertifiedJL.AffineRatioEndpointNumeric

namespace CertifiedJL.CertificateAssembly

/-- Reusable exact factory from a checked rational endpoint record and the
shared wrapped-profile contracts to the affine public theorem. -/
theorem affineL2RatioEndpoint
    (e : AffineRatioEndpointNumeric.L2EndpointData)
    (hden : 0 < e.floorDenominator)
    (profiles : AffineL2WrappedProfiles)
    (hcheck : AffineRatioEndpointNumeric.endpointCheck e = true) :
    AffineL2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := e.rows
        squaredNormFloor := AffineRatioEndpointNumeric.floorRatio e hden
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget e.bits) := by
  have h := AffineRatioEndpointNumeric.endpointCheck_sound e hcheck
  apply ternaryAffineL2ThresholdLowerTailAt_of_finiteTilt_lt_failureTarget
    e.rows e.bits (AffineRatioEndpointNumeric.floorRatio e hden)
      e.singletonTilt h.2.1 profiles.near profiles.diffuse33 profiles.diffuse25
  simpa [AffineRatioEndpointNumeric.floorRatio,
    AffineRatioEndpointNumeric.floorRat, NonnegativeRatio.toReal] using h.2.2

end CertifiedJL.CertificateAssembly
