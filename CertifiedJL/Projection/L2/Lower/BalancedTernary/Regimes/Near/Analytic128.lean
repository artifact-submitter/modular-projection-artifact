/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Near.CoupledLobes
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Soundness.ThresholdNearCoarseSoundness128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Soundness.ThresholdNearChordSoundness128

/-!
# Analytic consumers of the 128-bit near-band scalar envelopes

These lemmas identify the coupled retained-coordinate moments with the
normalized variables certified by the interval evaluators.  The low Holder
weights use the lobe periodization; the high weights use the exact power
chord.
-/

open scoped BigOperators ENNReal NNReal

open MeasureTheory ProbabilityTheory

namespace CertifiedJL

private theorem two_mul_geometric_div_mono
    {r R : ℝ} (hr0 : 0 ≤ r) (hrR : r ≤ R) (hR1 : R < 1) :
    2 * r / (1 - r ^ 3) ≤ 2 * R / (1 - R ^ 3) := by
  have hr1 : r < 1 := hrR.trans_lt hR1
  have hdenR : 0 < 1 - R ^ 3 := by
    have := pow_lt_pow_left₀ hR1 (hr0.trans hrR) (by norm_num : (3 : ℕ) ≠ 0)
    simpa using sub_pos.mpr this
  have hden : 0 < 1 - r ^ 3 := by
    have := pow_lt_pow_left₀ hr1 hr0 (by norm_num : (3 : ℕ) ≠ 0)
    simpa using sub_pos.mpr this
  have hpow : r ^ 3 ≤ R ^ 3 := pow_le_pow_left₀ hr0 hrR 3
  exact div_le_div₀ (mul_nonneg (by norm_num) (hr0.trans hrR))
    (by nlinarith) hdenR (by nlinarith)

/-- The lobe-periodized coupled moment is bounded by the coarse semantic
central envelope whenever the residual Holder weight is at most `4/5`. -/
theorem retainedGaussianCosineMoment_le_semanticCoarseCentral
    {x a y : ℝ} (hx : 0 < x) (ha : 0 < a) (hax : a < x)
    (hy : 0 < y) (hyUpper : y ≤ 4 / 5) :
    retainedGaussianCosineMoment ((23 / 10) * x) (a / x) y ≤
      ENNReal.ofReal (ThresholdNearCoarse128.semanticCoarseCentral x a) := by
  let s : ℝ := (23 / 10) * x
  let r : ℝ := a / x
  let u : ℝ := s * (1 - r)
  let A : ℝ := Real.sqrt (s / 2) * Real.sqrt r
  have hs : 0 < s := by dsimp [s]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := (div_lt_one hx).2 hax
  have hu : 0 < u := by dsimp [u]; positivity
  have hmoment := retainedGaussianCosineMoment_eq_ofReal_integral
    (s := s) (r := r) hy
  have hbase := retainedGaussianRpowMoment_le_coupled_geometricTail
    (A := A) (u := u) hu hy
  have hlhs :
      (∫ G : ℝ,
          Real.cos (Real.sqrt (s / 2) * G * Real.sqrt r) ^ 2 *
            |Real.cos (Real.sqrt ((s * (1 - r)) / (2 / y)) * G)| ^
              (2 / y)
          ∂(gaussianReal 0 1)) =
        ∫ G : ℝ, Real.cos (A * G) ^ 2 *
            |Real.cos (Real.sqrt (u / (2 / y)) * G)| ^ (2 / y)
          ∂(gaussianReal 0 1) := by
    apply integral_congr_ae
    filter_upwards [] with G
    dsimp [A, u]
    congr 3 <;> ring
  let D : ℝ := 1 + u
  let c : ℝ := Real.pi ^ 2 / (y * D)
  let C : ℝ := Real.pi ^ 2 / ((4 / 5) * D)
  let rho : ℝ := Real.exp (-c)
  let R : ℝ := Real.exp (-C)
  have hD : 0 < D := by dsimp [D]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hcC : C ≤ c := by
    dsimp [c, C]
    apply (div_le_div_iff₀ (by positivity : 0 < (4 / 5 : ℝ) * D)
      (by positivity : 0 < y * D)).2
    have hpi : 0 ≤ Real.pi ^ 2 := sq_nonneg _
    have hdenle : y * D ≤ (4 / 5 : ℝ) * D :=
      mul_le_mul_of_nonneg_right hyUpper hD.le
    exact mul_le_mul_of_nonneg_left hdenle hpi
  have hrhoR : rho ≤ R := by
    dsimp [rho, R]
    exact Real.exp_le_exp.mpr (neg_le_neg hcC)
  have hR1 : R < 1 := by
    dsimp [R]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hC)
  have htail := two_mul_geometric_div_mono
    (Real.exp_nonneg (-c)) hrhoR hR1
  have huId : u = (23 / 10) * (x - a) := by
    dsimp [u, s, r]
    field_simp [hx.ne']
  have hAId : 2 * A ^ 2 = (23 / 10) * a := by
    have hsqrtS : Real.sqrt (s / 2) ^ 2 = s / 2 :=
      Real.sq_sqrt (by positivity)
    have hsqrtR : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
    dsimp [A]
    rw [mul_pow, hsqrtS, hsqrtR]
    dsimp [s, r]
    field_simp [hx.ne']
  have hcentralEq :
      (1 + Real.exp (-2 * A ^ 2 / (1 + u))) /
          (2 * Real.sqrt (1 + u)) *
        (1 + 2 * R / (1 - R ^ 3)) =
        ThresholdNearCoarse128.semanticCoarseCentral x a := by
    dsimp [ThresholdNearCoarse128.semanticCoarseCentral,
      ThresholdNearCoarse128.semanticD,
      ThresholdNearCoarse128.semanticT,
      ThresholdNearCoarse128.semanticTheta, D, R, C]
    rw [huId]
    rw [show -2 * A ^ 2 = -((23 / 10 : ℝ) * a) by
      nlinarith [hAId]]
    ring
  rw [hmoment, hlhs]
  apply ENNReal.ofReal_mono
  calc
    (∫ G : ℝ, Real.cos (A * G) ^ 2 *
        |Real.cos (Real.sqrt (u / (2 / y)) * G)| ^ (2 / y)
        ∂(gaussianReal 0 1)) ≤
      (1 + Real.exp (-2 * A ^ 2 / (1 + u))) /
          (2 * Real.sqrt (1 + u)) *
        (1 + 2 * Real.exp (-(Real.pi ^ 2 / (y * (1 + u)))) /
          (1 - Real.exp (-(Real.pi ^ 2 / (y * (1 + u)))) ^ 3)) := hbase
    _ ≤ (1 + Real.exp (-2 * A ^ 2 / (1 + u))) /
          (2 * Real.sqrt (1 + u)) *
        (1 + 2 * R / (1 - R ^ 3)) := by
      have hrhoEq : Real.exp (-(Real.pi ^ 2 / (y * (1 + u)))) = rho := by
        rfl
      rw [hrhoEq]
      gcongr
    _ = ThresholdNearCoarse128.semanticCoarseCentral x a := hcentralEq

/-- For Holder weights at least `1/2`, the exact quadratic power chord is
the semantic central expression checked by the three-dimensional interval
certificate. -/
theorem retainedGaussianCosineMoment_le_semanticChordCentral
    {x a y : ℝ} (hx : 0 < x) (ha : 0 < a) (hax : a < x)
    (hyLower : 1 / 2 ≤ y) (hyUpper : y ≤ 1) :
    retainedGaussianCosineMoment ((23 / 10) * x) (a / x) y ≤
      ENNReal.ofReal (ThresholdNearChord128.semanticChordCentral x a y) := by
  have hy : 0 < y := by linarith
  let s : ℝ := (23 / 10) * x
  let r : ℝ := a / x
  let u : ℝ := s * (1 - r)
  let A : ℝ := Real.sqrt (s / 2) * Real.sqrt r
  let B : ℝ := Real.sqrt (u / (2 / y))
  have hs : 0 < s := by dsimp [s]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := (div_lt_one hx).2 hax
  have hu : 0 < u := by dsimp [u]; positivity
  have hmoment := retainedGaussianCosineMoment_eq_ofReal_integral
    (s := s) (r := r) hy
  have hAId : A = ThresholdNearChord128.semanticAFreq a := by
    dsimp [A, ThresholdNearChord128.semanticAFreq]
    rw [← Real.sqrt_mul (by positivity : 0 ≤ s / 2)]
    congr 1
    dsimp [s, r]
    field_simp [hx.ne']
    ring
  have huId : u = (23 / 10) * (x - a) := by
    dsimp [u, s, r]
    field_simp [hx.ne']
  have hBId : B = ThresholdNearChord128.semanticBFreq x a y := by
    dsimp [B, ThresholdNearChord128.semanticBFreq]
    rw [huId]
    congr 1
    field_simp [hy.ne']
    ring
  have hlhs :
      (∫ G : ℝ,
          Real.cos (Real.sqrt (s / 2) * G * Real.sqrt r) ^ 2 *
            |Real.cos (Real.sqrt ((s * (1 - r)) / (2 / y)) * G)| ^
              (2 / y)
          ∂(gaussianReal 0 1)) =
        ∫ G : ℝ, Real.cos (A * G) ^ 2 *
            |Real.cos (B * G)| ^ (2 / y)
          ∂(gaussianReal 0 1) := by
    apply integral_congr_ae
    filter_upwards [] with G
    dsimp [A, B, u]
    congr 3 <;> ring
  have hchord := retainedGaussianRpowMoment_le_powerChord
    (A := A) hyLower hyUpper B
  rw [hmoment, hlhs]
  apply ENNReal.ofReal_mono
  calc
    (∫ G : ℝ, Real.cos (A * G) ^ 2 * |Real.cos (B * G)| ^ (2 / y)
        ∂(gaussianReal 0 1)) ≤
      (2 - 1 / y) *
          (∫ G : ℝ, Real.cos (A * G) ^ 2 * Real.cos (B * G) ^ 2
            ∂(gaussianReal 0 1)) +
        (1 / y - 1) *
          (∫ G : ℝ, Real.cos (A * G) ^ 2 * Real.cos (B * G) ^ 4
            ∂(gaussianReal 0 1)) := hchord
    _ = ThresholdNearChord128.semanticChordCentral x a y := by
      rw [gaussian_cos_sq_mul_cos_sq_integral,
        gaussian_cos_sq_mul_cos_pow_four_integral, hAId, hBId]
      dsimp [ThresholdNearChord128.semanticChordCentral,
        ThresholdNearChord128.semanticMomentTwo,
        ThresholdNearChord128.semanticMomentFour,
        ThresholdNearChord128.semanticMixedMoment]
      congr 1 <;> ring

end CertifiedJL
