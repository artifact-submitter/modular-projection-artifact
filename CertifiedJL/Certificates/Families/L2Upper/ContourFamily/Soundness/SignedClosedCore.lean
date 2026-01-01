/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.AnalyticSoundness
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Reusable signed closed-contour row envelope

This module packages the cancellation in the fourth-order balanced-ternary
row estimate into exact rational sufficient conditions.  In particular, the
negative real part of the leading correction is retained.  The conclusion has
an amplitude deficit as well as Gaussian decay, so a profile box whose left
endpoint is positive does not lose its near-zero cancellation.

The conditions contain no interval arithmetic and no generated certificate
data.  Concrete profile endpoints can discharge them with `norm_num` after
choosing rational caps.
-/

open Set

namespace CertifiedJL.SparseUpperContourFamily.SignedClosedCore

/-- Exact rational sufficient conditions for one profile endpoint.

`rhoCap`, `ratioCap`, and `zNormSqCap` bound respectively `|s|`,
`(|s| + (1-lam))/(1-lam)`, and `|s/(1-s)|^2`.  `zRealBase` and
`zRealSlope` give the signed estimate
`Re ((s/(1-s))^2) >= zRealBase - zRealSlope * u^2`.
-/
structure EndpointConditions
    (profile lam cutoff rhoCap ratioCap zNormSqCap
      zRealBase zRealSlope gaussianLower sqrtProfileCap
      gaussianRate deficit rowRate : ℚ) : Prop where
  profile_nonneg : 0 ≤ profile
  lam_nonneg : 0 ≤ lam
  lam_lt_one : lam < 1
  cutoff_nonneg : 0 ≤ cutoff
  rhoCap_nonneg : 0 ≤ rhoCap
  rhoCap_sq : lam ^ 2 + cutoff ^ 2 ≤ rhoCap ^ 2
  ratioCap_nonneg : 0 ≤ ratioCap
  ratioCap_bound : rhoCap + (1 - lam) ≤ ratioCap * (1 - lam)
  zNormSqCap_one : 1 ≤ zNormSqCap
  zNormSqCap_bound : lam ^ 2 ≤ zNormSqCap * (1 - lam) ^ 2
  zRealBase_nonneg : 0 ≤ zRealBase
  zRealSlope_nonneg : 0 ≤ zRealSlope
  zReal_constant : zRealBase * (1 - lam) ^ 4 ≤ lam ^ 2 * (1 - lam) ^ 2
  zReal_linear :
    2 * lam * (1 - lam) + 1 + 2 * zRealBase * (1 - lam) ^ 2 ≤
      zRealSlope * (1 - lam) ^ 4
  zReal_quadratic : 0 ≤ 1 - zRealBase + 2 * zRealSlope * (1 - lam) ^ 2
  gaussianLower_nonneg : 0 ≤ gaussianLower
  gaussianLower_bound :
    gaussianLower ^ 4 * ((1 - lam) ^ 2 + cutoff ^ 2) ≤ (1 - lam) ^ 2
  sqrtProfileCap_nonneg : 0 ≤ sqrtProfileCap
  sqrtProfileCap_sq : profile ≤ sqrtProfileCap ^ 2
  gaussianRate_nonneg : 0 ≤ gaussianRate
  gaussianRate_bound :
    gaussianRate * (4 * (1 - lam) ^ 2 + 2 * cutoff ^ 2) ≤ 1
  deficit_nonneg : 0 ≤ deficit
  rowRate_nonneg : 0 ≤ rowRate
  cancellation_nonneg :
    0 ≤ profile * zRealBase / 8 -
      profile ^ 2 * zNormSqCap ^ 2 / 128 - deficit
  remainder_absorbed :
    profile ^ 2 * (35 / 192) * (rhoCap * ratioCap) ^ 4 +
        11 * profile * sqrtProfileCap / 48 * (rhoCap * ratioCap) ^ 3 ≤
      gaussianLower *
        (profile * zRealBase / 8 -
          profile ^ 2 * zNormSqCap ^ 2 / 128 - deficit)
  rowRate_bound : rowRate + profile * zRealSlope / 8 ≤ gaussianRate

/-- The elementary signed complex-modulus estimate used by every endpoint. -/
theorem leading_modulus_le (q zReal zImaginary : ℝ) :
    Real.sqrt
        ((1 - q * (zReal ^ 2 - zImaginary ^ 2)) ^ 2 +
          (-(q * (2 * zReal * zImaginary))) ^ 2) ≤
      1 - q * (zReal ^ 2 - zImaginary ^ 2) +
        q ^ 2 * (zReal ^ 2 + zImaginary ^ 2) ^ 2 / 2 := by
  let radicand :=
    (1 - q * (zReal ^ 2 - zImaginary ^ 2)) ^ 2 +
      (-(q * (2 * zReal * zImaginary))) ^ 2
  have hradicand : 0 ≤ radicand := by
    dsimp only [radicand]
    positivity
  have hsqrtSq := Real.sq_sqrt hradicand
  have hsquare := sq_nonneg (Real.sqrt radicand - 1)
  dsimp only [radicand] at hsqrtSq hsquare ⊢
  nlinarith

private noncomputable def gaussianFactor (lam : ℚ) (frequency : ℝ) : ℝ :=
  Real.sqrt (1 - (lam : ℝ)) /
    Real.sqrt (Real.sqrt ((1 - (lam : ℝ)) ^ 2 + frequency ^ 2))

private theorem gaussianFactor_fourth
    {lam : ℚ} (hlam : lam < 1) (frequency : ℝ) :
    gaussianFactor lam frequency ^ 4 =
      (1 - (lam : ℝ)) ^ 2 /
        ((1 - (lam : ℝ)) ^ 2 + frequency ^ 2) := by
  let a : ℝ := 1 - (lam : ℝ)
  let denominator := a ^ 2 + frequency ^ 2
  have ha : 0 < a := by
    dsimp only [a]
    exact_mod_cast sub_pos.mpr hlam
  have hdenominator : 0 < denominator := by
    dsimp only [denominator]
    positivity
  have haSq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hdenSq : Real.sqrt denominator ^ 2 = denominator :=
    Real.sq_sqrt hdenominator.le
  have hsqrtDenominator : 0 < Real.sqrt denominator := Real.sqrt_pos.2 hdenominator
  have hdenSqrtSq : Real.sqrt (Real.sqrt denominator) ^ 2 =
      Real.sqrt denominator := Real.sq_sqrt hsqrtDenominator.le
  dsimp only [gaussianFactor, a, denominator]
  calc
    (Real.sqrt (1 - (lam : ℝ)) /
        Real.sqrt (Real.sqrt ((1 - (lam : ℝ)) ^ 2 + frequency ^ 2))) ^ 4 =
      Real.sqrt (1 - (lam : ℝ)) ^ 4 /
        Real.sqrt (Real.sqrt ((1 - (lam : ℝ)) ^ 2 + frequency ^ 2)) ^ 4 := by
          rw [div_pow]
    _ = (1 - (lam : ℝ)) ^ 2 /
        ((1 - (lam : ℝ)) ^ 2 + frequency ^ 2) := by
      rw [show Real.sqrt (1 - (lam : ℝ)) ^ 4 =
          (Real.sqrt (1 - (lam : ℝ)) ^ 2) ^ 2 by ring,
        haSq,
        show Real.sqrt (Real.sqrt ((1 - (lam : ℝ)) ^ 2 + frequency ^ 2)) ^ 4 =
          (Real.sqrt (Real.sqrt ((1 - (lam : ℝ)) ^ 2 + frequency ^ 2)) ^ 2) ^ 2 by
            ring,
        hdenSqrtSq, hdenSq]

private theorem gaussianFactor_bounds
    {lam cutoff gaussianLower : ℚ} {frequency : ℝ}
    (hlam : lam < 1) (hcutoff : 0 ≤ cutoff)
    (hfrequency0 : 0 ≤ frequency) (hfrequency : frequency ≤ cutoff)
    (hgaussianLower0 : 0 ≤ gaussianLower)
    (hgaussianLower :
      gaussianLower ^ 4 * ((1 - lam) ^ 2 + cutoff ^ 2) ≤ (1 - lam) ^ 2) :
    (gaussianLower : ℝ) ≤ gaussianFactor lam frequency ∧
      gaussianFactor lam frequency ≤ 1 := by
  let a : ℝ := 1 - (lam : ℝ)
  let denominator := a ^ 2 + frequency ^ 2
  have ha : 0 < a := by
    dsimp only [a]
    exact_mod_cast sub_pos.mpr hlam
  have hdenominator : 0 < denominator := by
    dsimp only [denominator]
    positivity
  have hfrequencySq : frequency ^ 2 ≤ (cutoff : ℝ) ^ 2 := by
    have hcutoffReal : (0 : ℝ) ≤ cutoff := by exact_mod_cast hcutoff
    have hfrequencyUpper : frequency ≤ (cutoff : ℝ) := by exact_mod_cast hfrequency
    nlinarith
  have hfactorFourth := gaussianFactor_fourth (lam := lam) hlam frequency
  have hfactor0 : 0 ≤ gaussianFactor lam frequency := by
    unfold gaussianFactor
    positivity
  constructor
  · apply (pow_le_pow_iff_left₀ (by exact_mod_cast hgaussianLower0)
      hfactor0 (by norm_num : (4 : ℕ) ≠ 0)).mp
    rw [hfactorFourth]
    rw [le_div_iff₀ hdenominator]
    have hgaussianLowerReal :
        (gaussianLower : ℝ) ^ 4 *
            ((1 - (lam : ℝ)) ^ 2 + (cutoff : ℝ) ^ 2) ≤
          (1 - (lam : ℝ)) ^ 2 := by exact_mod_cast hgaussianLower
    dsimp only [denominator, a]
    have hgaussianLowerReal0 : (0 : ℝ) ≤ gaussianLower := by
      exact_mod_cast hgaussianLower0
    nlinarith [mul_nonneg (pow_nonneg hgaussianLowerReal0 4)
      (sub_nonneg.mpr hfrequencySq)]
  · apply (pow_le_pow_iff_left₀ hfactor0 (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (4 : ℕ) ≠ 0)).mp
    rw [hfactorFourth]
    norm_num only [one_pow]
    rw [div_le_one hdenominator]
    nlinarith [sq_nonneg frequency]

private theorem gaussianFactor_le_exp
    {lam cutoff gaussianRate : ℚ} {frequency : ℝ}
    (hlam : lam < 1) (hcutoff : 0 ≤ cutoff)
    (hfrequency0 : 0 ≤ frequency) (hfrequency : frequency ≤ cutoff)
    (_hgaussianRate0 : 0 ≤ gaussianRate)
    (hgaussianRate :
      gaussianRate * (4 * (1 - lam) ^ 2 + 2 * cutoff ^ 2) ≤ 1) :
    gaussianFactor lam frequency ≤
      Real.exp (-(gaussianRate : ℝ) * frequency ^ 2) := by
  let a : ℝ := 1 - (lam : ℝ)
  let x : ℝ := frequency ^ 2
  let t : ℝ := x / a ^ 2
  let y : ℝ := t / (2 + t)
  have ha : 0 < a := by
    dsimp only [a]
    exact_mod_cast sub_pos.mpr hlam
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hcutoffReal : (0 : ℝ) ≤ cutoff := by exact_mod_cast hcutoff
  have hfrequencyUpper : frequency ≤ (cutoff : ℝ) := by exact_mod_cast hfrequency
  have hx : x ≤ (cutoff : ℝ) ^ 2 := by
    dsimp only [x]
    nlinarith
  have ht0 : 0 ≤ t := by dsimp only [t]; positivity
  have hy0 : 0 ≤ y := by dsimp only [y]; positivity
  have hy1 : y < 1 := by
    dsimp only [y]
    rw [div_lt_one (by positivity : (0 : ℝ) < 2 + t)]
    linarith
  have hlogSeries := Real.sum_range_le_log_div hy0 hy1 1
  have hlogIdentity : (1 + y) / (1 - y) = 1 + t := by
    dsimp only [y]
    field_simp [show (2 + t : ℝ) ≠ 0 by positivity]
    ring
  have hlogLower : 2 * y ≤ Real.log (1 + t) := by
    rw [hlogIdentity] at hlogSeries
    norm_num [Finset.sum_range_succ] at hlogSeries
    linarith
  have hrateReal :
      (gaussianRate : ℝ) *
          (4 * (1 - (lam : ℝ)) ^ 2 + 2 * (cutoff : ℝ) ^ 2) ≤ 1 := by
    exact_mod_cast hgaussianRate
  have hrate : 4 * (gaussianRate : ℝ) * x ≤ 2 * y := by
    dsimp only [y, t]
    rw [div_div]
    have hdenCutoff : 0 < 2 * a ^ 2 + (cutoff : ℝ) ^ 2 := by positivity
    have hdenX : 0 < 2 * a ^ 2 + x := by positivity
    have hbase :
        4 * (gaussianRate : ℝ) ≤
          2 / (2 * a ^ 2 + (cutoff : ℝ) ^ 2) := by
      rw [le_div_iff₀ hdenCutoff]
      dsimp only [a] at hrateReal ⊢
      nlinarith
    calc
      4 * (gaussianRate : ℝ) * x ≤
          (2 / (2 * a ^ 2 + (cutoff : ℝ) ^ 2)) * x := by
            exact mul_le_mul_of_nonneg_right hbase hx0
      _ ≤ (2 / (2 * a ^ 2 + x)) * x := by
        gcongr
      _ = 2 * (x / (a ^ 2 * (2 + x / a ^ 2))) := by
        field_simp [ha.ne']
  have hlogRate : 4 * (gaussianRate : ℝ) * x ≤ Real.log (1 + t) :=
    hrate.trans hlogLower
  have htPos : 0 < 1 + t := by positivity
  have hratioExp : 1 / (1 + t) = Real.exp (-Real.log (1 + t)) := by
    rw [Real.exp_neg, Real.exp_log htPos]
    simp only [one_div]
  have hfactorFourth := gaussianFactor_fourth (lam := lam) hlam frequency
  have hfactorFourth' : gaussianFactor lam frequency ^ 4 = a ^ 2 / (a ^ 2 + x) := by
    simpa only [a, x] using hfactorFourth
  have hfactorRatio : gaussianFactor lam frequency ^ 4 = 1 / (1 + t) := by
    rw [hfactorFourth']
    dsimp only [t]
    field_simp [ha.ne']
  have hpow : gaussianFactor lam frequency ^ 4 ≤
      (Real.exp (-(gaussianRate : ℝ) * frequency ^ 2)) ^ 4 := by
    have hpowExp : (Real.exp (-(gaussianRate : ℝ) * frequency ^ 2)) ^ 4 =
        Real.exp (-(4 * (gaussianRate : ℝ) * x)) := by
      rw [← Real.exp_nat_mul]
      dsimp only [x]
      congr 1
      norm_num
      ring
    rw [hfactorRatio, hratioExp, hpowExp]
    apply Real.exp_le_exp.mpr
    exact neg_le_neg hlogRate
  apply (pow_le_pow_iff_left₀
    (by unfold gaussianFactor; positivity)
    (Real.exp_nonneg _) (by norm_num : (4 : ℕ) ≠ 0)).mp hpow

private theorem normalized_d6_le
    {lam rhoCap ratioCap : ℚ} {frequency : ℝ}
    (hlam : lam < 1) (hrhoCap0 : 0 ≤ rhoCap)
    (hrho : Real.sqrt ((lam : ℝ) ^ 2 + frequency ^ 2) ≤ rhoCap)
    (_hratioCap0 : 0 ≤ ratioCap)
    (hratio : (rhoCap : ℝ) + (1 - (lam : ℝ)) ≤
      (ratioCap : ℝ) * (1 - (lam : ℝ))) :
    Real.sqrt (1 - (lam : ℝ)) *
        quadraticExpDerivativeMajorant 6
          (Real.sqrt ((lam : ℝ) ^ 2 + frequency ^ 2)) (lam : ℝ) ≤
      120 * ((rhoCap : ℝ) * (ratioCap : ℝ)) ^ 3 := by
  let rho := Real.sqrt ((lam : ℝ) ^ 2 + frequency ^ 2)
  let a : ℝ := 1 - (lam : ℝ)
  have ha : 0 < a := by dsimp only [a]; exact_mod_cast sub_pos.mpr hlam
  have hrho0 : 0 ≤ rho := Real.sqrt_nonneg _
  have hratio0 : 0 ≤ (rho + a) / a := by positivity
  have hratioBound : (rho + a) / a ≤ (ratioCap : ℝ) := by
    rw [div_le_iff₀ ha]
    dsimp only [rho, a]
    calc
      Real.sqrt ((lam : ℝ) ^ 2 + frequency ^ 2) + (1 - (lam : ℝ)) ≤
          (rhoCap : ℝ) + (1 - (lam : ℝ)) := by gcongr
      _ ≤ _ := hratio
  have hclosed := UpperContourKernel.normalizedDerivativeMajorantValue_six_eq
    rho (lambda := lam) (by exact_mod_cast hlam)
  have honeMinus : (((1 - lam : ℚ) : ℝ)) = a := by
    dsimp only [a]
    push_cast
    rfl
  have heq : Real.sqrt (1 - (lam : ℝ)) *
        quadraticExpDerivativeMajorant 6 rho (lam : ℝ) =
      120 * rho ^ 3 * ((rho + a) / a) ^ 3 := by
    calc
      _ = UpperContourKernel.normalizedDerivativeMajorantValue 6 rho (1 - lam) :=
        hclosed.symm
      _ = 120 * rho ^ 3 * ((rho + a) / a) ^ 3 := by
        rw [UpperContourKernel.normalizedDerivativeMajorantValue_six]
        rw [honeMinus]
        field_simp [ha.ne']
        ring
  rw [heq]
  have hrhoPow := pow_le_pow_left₀ hrho0 hrho 3
  have hratioPow := pow_le_pow_left₀ hratio0 hratioBound 3
  calc
    120 * rho ^ 3 * ((rho + a) / a) ^ 3 ≤
        120 * (rhoCap : ℝ) ^ 3 * (ratioCap : ℝ) ^ 3 := by gcongr
    _ = 120 * ((rhoCap : ℝ) * (ratioCap : ℝ)) ^ 3 := by ring

private theorem normalized_d8_le
    {lam rhoCap ratioCap : ℚ} {frequency : ℝ}
    (hlam : lam < 1) (_hrhoCap0 : 0 ≤ rhoCap)
    (hrho : Real.sqrt ((lam : ℝ) ^ 2 + frequency ^ 2) ≤ rhoCap)
    (_hratioCap0 : 0 ≤ ratioCap)
    (hratio : (rhoCap : ℝ) + (1 - (lam : ℝ)) ≤
      (ratioCap : ℝ) * (1 - (lam : ℝ))) :
    Real.sqrt (1 - (lam : ℝ)) *
        quadraticExpDerivativeMajorant 8
          (Real.sqrt ((lam : ℝ) ^ 2 + frequency ^ 2)) (lam : ℝ) ≤
      1680 * ((rhoCap : ℝ) * (ratioCap : ℝ)) ^ 4 := by
  let rho := Real.sqrt ((lam : ℝ) ^ 2 + frequency ^ 2)
  let a : ℝ := 1 - (lam : ℝ)
  have ha : 0 < a := by dsimp only [a]; exact_mod_cast sub_pos.mpr hlam
  have hrho0 : 0 ≤ rho := Real.sqrt_nonneg _
  have hratio0 : 0 ≤ (rho + a) / a := by positivity
  have hratioBound : (rho + a) / a ≤ (ratioCap : ℝ) := by
    rw [div_le_iff₀ ha]
    dsimp only [rho, a]
    calc
      Real.sqrt ((lam : ℝ) ^ 2 + frequency ^ 2) + (1 - (lam : ℝ)) ≤
          (rhoCap : ℝ) + (1 - (lam : ℝ)) := by gcongr
      _ ≤ _ := hratio
  have hclosed := UpperContourKernel.normalizedDerivativeMajorantValue_eight_eq
    rho (lambda := lam) (by exact_mod_cast hlam)
  have honeMinus : (((1 - lam : ℚ) : ℝ)) = a := by
    dsimp only [a]
    push_cast
    rfl
  have heq : Real.sqrt (1 - (lam : ℝ)) *
        quadraticExpDerivativeMajorant 8 rho (lam : ℝ) =
      1680 * rho ^ 4 * ((rho + a) / a) ^ 4 := by
    calc
      _ = UpperContourKernel.normalizedDerivativeMajorantValue 8 rho (1 - lam) :=
        hclosed.symm
      _ = 1680 * rho ^ 4 * ((rho + a) / a) ^ 4 := by
        rw [UpperContourKernel.normalizedDerivativeMajorantValue_eight]
        rw [honeMinus]
        field_simp [ha.ne']
        ring
  rw [heq]
  have hrhoPow := pow_le_pow_left₀ hrho0 hrho 4
  have hratioPow := pow_le_pow_left₀ hratio0 hratioBound 4
  calc
    1680 * rho ^ 4 * ((rho + a) / a) ^ 4 ≤
        1680 * (rhoCap : ℝ) ^ 4 * (ratioCap : ℝ) ^ 4 := by gcongr
    _ = 1680 * ((rhoCap : ℝ) * (ratioCap : ℝ)) ^ 4 := by ring

set_option maxHeartbeats 1000000 in
-- The final normalization conversion expands several rational powers and complex products.
/-- One fourth-order row endpoint is bounded by a signed Gaussian envelope.
All hypotheses are exact inequalities between rationals. -/
theorem normalizedFourthOrderRowBound_le_signedGaussian
    {profile lam cutoff rhoCap ratioCap zNormSqCap
      zRealBase zRealSlope gaussianLower sqrtProfileCap
      gaussianRate deficit rowRate : ℚ}
    (conditions : EndpointConditions profile lam cutoff rhoCap ratioCap zNormSqCap
      zRealBase zRealSlope gaussianLower sqrtProfileCap
      gaussianRate deficit rowRate)
    {frequency : ℝ} (hfrequency : frequency ∈ Icc 0 (cutoff : ℝ)) :
    UpperContourKernel.normalizedFourthOrderRowBound rowCoefficients
        profile lam frequency ≤
      Real.exp (-(deficit : ℝ) - (rowRate : ℝ) * frequency ^ 2) := by
  let p : ℝ := profile
  let l : ℝ := lam
  let a : ℝ := 1 - l
  let x : ℝ := frequency ^ 2
  let denominator : ℝ := a ^ 2 + x
  let zReal : ℝ := (l * a) / denominator - x / denominator
  let zImaginary : ℝ := frequency / denominator
  let rho : ℝ := Real.sqrt (l ^ 2 + x)
  let factor : ℝ := gaussianFactor lam frequency
  have hp0 : 0 ≤ p := by dsimp only [p]; exact_mod_cast conditions.profile_nonneg
  have hl0 : 0 ≤ l := by dsimp only [l]; exact_mod_cast conditions.lam_nonneg
  have hl1 : l < 1 := by dsimp only [l]; exact_mod_cast conditions.lam_lt_one
  have ha : 0 < a := by dsimp only [a]; linarith
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hcutoff0 : (0 : ℝ) ≤ cutoff := by exact_mod_cast conditions.cutoff_nonneg
  have hfrequencyUpper : frequency ≤ (cutoff : ℝ) := hfrequency.2
  have hx : x ≤ (cutoff : ℝ) ^ 2 := by
    dsimp only [x]
    exact pow_le_pow_left₀ hfrequency.1 hfrequency.2 2
  have hdenominator : 0 < denominator := by dsimp only [denominator]; positivity
  have hrho0 : 0 ≤ rho := Real.sqrt_nonneg _
  have hrhoSq : rho ^ 2 = l ^ 2 + x := by
    dsimp only [rho]
    exact Real.sq_sqrt (by positivity)
  have hrhoCap0 : (0 : ℝ) ≤ rhoCap := by exact_mod_cast conditions.rhoCap_nonneg
  have hrhoCapSq : l ^ 2 + (cutoff : ℝ) ^ 2 ≤ (rhoCap : ℝ) ^ 2 := by
    dsimp only [l]
    exact_mod_cast conditions.rhoCap_sq
  have hrho : rho ≤ (rhoCap : ℝ) := by
    nlinarith
  have hratioCap0 : (0 : ℝ) ≤ ratioCap := by
    exact_mod_cast conditions.ratioCap_nonneg
  have hratio : (rhoCap : ℝ) + a ≤ (ratioCap : ℝ) * a := by
    dsimp only [a, l]
    exact_mod_cast conditions.ratioCap_bound
  have hzNormIdentity : zReal ^ 2 + zImaginary ^ 2 =
      (l ^ 2 + x) / denominator := by
    dsimp only [zReal, zImaginary]
    field_simp [hdenominator.ne']
    dsimp only [denominator, x, a]
    ring
  have hzNormCap1 : (1 : ℝ) ≤ zNormSqCap := by
    exact_mod_cast conditions.zNormSqCap_one
  have hzNormNumerator : l ^ 2 + x ≤
      (zNormSqCap : ℝ) * denominator := by
    have hbase : l ^ 2 ≤ (zNormSqCap : ℝ) * a ^ 2 := by
      dsimp only [l, a]
      exact_mod_cast conditions.zNormSqCap_bound
    dsimp only [denominator]
    nlinarith
  have hzNorm0 : 0 ≤ zReal ^ 2 + zImaginary ^ 2 := by positivity
  have hzNorm : zReal ^ 2 + zImaginary ^ 2 ≤ (zNormSqCap : ℝ) := by
    rw [hzNormIdentity, div_le_iff₀ hdenominator]
    exact hzNormNumerator
  have hzNormFourth : (zReal ^ 2 + zImaginary ^ 2) ^ 2 ≤
      (zNormSqCap : ℝ) ^ 2 :=
    pow_le_pow_left₀ hzNorm0 hzNorm 2
  have hzRealIdentity : zReal ^ 2 - zImaginary ^ 2 =
      ((l * a - x) ^ 2 - x) / denominator ^ 2 := by
    dsimp only [zReal, zImaginary]
    field_simp [hdenominator.ne']
    dsimp only [x]
  have hzConstant :
      (zRealBase : ℝ) * a ^ 4 ≤ l ^ 2 * a ^ 2 := by
    dsimp only [a, l]
    exact_mod_cast conditions.zReal_constant
  have hzLinear :
      2 * l * a + 1 + 2 * (zRealBase : ℝ) * a ^ 2 ≤
        (zRealSlope : ℝ) * a ^ 4 := by
    dsimp only [a, l]
    exact_mod_cast conditions.zReal_linear
  have hzQuadratic :
      0 ≤ 1 - (zRealBase : ℝ) + 2 * (zRealSlope : ℝ) * a ^ 2 := by
    dsimp only [a, l]
    exact_mod_cast conditions.zReal_quadratic
  have hzSlope0 : (0 : ℝ) ≤ zRealSlope := by
    exact_mod_cast conditions.zRealSlope_nonneg
  have hzPolynomial :
      0 ≤
        (l ^ 2 * a ^ 2 - (zRealBase : ℝ) * a ^ 4) +
        ((zRealSlope : ℝ) * a ^ 4 -
          (2 * l * a + 1 + 2 * (zRealBase : ℝ) * a ^ 2)) * x +
        (1 - (zRealBase : ℝ) +
          2 * (zRealSlope : ℝ) * a ^ 2) * x ^ 2 +
        (zRealSlope : ℝ) * x ^ 3 := by positivity
  have hzReal : (zRealBase : ℝ) - (zRealSlope : ℝ) * x ≤
      zReal ^ 2 - zImaginary ^ 2 := by
    rw [hzRealIdentity, le_div_iff₀ (sq_pos_of_pos hdenominator)]
    dsimp only [denominator]
    nlinarith [hzPolynomial]
  have hsqrtProfileCap0 : (0 : ℝ) ≤ sqrtProfileCap := by
    exact_mod_cast conditions.sqrtProfileCap_nonneg
  have hsqrtProfile : Real.sqrt p ≤ (sqrtProfileCap : ℝ) := by
    have hcapSq : p ≤ (sqrtProfileCap : ℝ) ^ 2 := by
      dsimp only [p]
      exact_mod_cast conditions.sqrtProfileCap_sq
    exact Real.sqrt_le_iff.mpr ⟨hsqrtProfileCap0, hcapSq⟩
  have hfactorBounds : (gaussianLower : ℝ) ≤ factor ∧ factor ≤ 1 := by
    dsimp only [factor]
    exact gaussianFactor_bounds conditions.lam_lt_one conditions.cutoff_nonneg
      hfrequency.1 hfrequency.2 conditions.gaussianLower_nonneg
      conditions.gaussianLower_bound
  have hgaussianLower0 : (0 : ℝ) ≤ gaussianLower := by
    exact_mod_cast conditions.gaussianLower_nonneg
  have hfactor0 : 0 ≤ factor := hgaussianLower0.trans hfactorBounds.1
  have hfactorExp : factor ≤
      Real.exp (-(gaussianRate : ℝ) * x) := by
    dsimp only [factor, x]
    exact gaussianFactor_le_exp conditions.lam_lt_one conditions.cutoff_nonneg
      hfrequency.1 hfrequency.2 conditions.gaussianRate_nonneg
      conditions.gaussianRate_bound
  have hd6 := normalized_d6_le conditions.lam_lt_one conditions.rhoCap_nonneg
    (by simpa only [rho, l, x] using hrho) conditions.ratioCap_nonneg (by
      simpa only [a, l] using hratio)
  have hd8 := normalized_d8_le conditions.lam_lt_one conditions.rhoCap_nonneg
    (by simpa only [rho, l, x] using hrho) conditions.ratioCap_nonneg (by
      simpa only [a, l] using hratio)
  have hnorm :
      ‖1 - (((p / 8 : ℝ) : ℂ) *
          ((zReal : ℂ) + (zImaginary : ℂ) * Complex.I) ^ 2)‖ =
        Real.sqrt
          ((1 - (p / 8) * (zReal ^ 2 - zImaginary ^ 2)) ^ 2 +
            (-((p / 8) * (2 * zReal * zImaginary))) ^ 2) := by
    simpa using (UpperContourKernel.leadingCorrectionValue_eq_norm
      (p / 8) 1 zReal zImaginary).symm
  have hlead := leading_modulus_le (p / 8) zReal zImaginary
  have hleadClosed :
      ‖1 - (((p / 8 : ℝ) : ℂ) *
          ((zReal : ℂ) + (zImaginary : ℂ) * Complex.I) ^ 2)‖ ≤
        1 - p * (zRealBase : ℝ) / 8 +
          p * (zRealSlope : ℝ) / 8 * x +
          p ^ 2 * (zNormSqCap : ℝ) ^ 2 / 128 := by
    rw [hnorm]
    calc
      _ ≤ 1 - (p / 8) * (zReal ^ 2 - zImaginary ^ 2) +
          (p / 8) ^ 2 * (zReal ^ 2 + zImaginary ^ 2) ^ 2 / 2 := hlead
      _ ≤ 1 - (p / 8) *
            ((zRealBase : ℝ) - (zRealSlope : ℝ) * x) +
          (p / 8) ^ 2 * (zNormSqCap : ℝ) ^ 2 / 2 := by gcongr
      _ = _ := by ring
  let error8 : ℝ := p ^ 2 * (35 / 192) *
    ((rhoCap : ℝ) * (ratioCap : ℝ)) ^ 4
  let error6 : ℝ := 11 * p * (sqrtProfileCap : ℝ) / 48 *
    ((rhoCap : ℝ) * (ratioCap : ℝ)) ^ 3
  have herror8 :
      p ^ 2 / 9216 *
          (Real.sqrt a * quadraticExpDerivativeMajorant 8 rho l) ≤ error8 := by
    dsimp only [error8]
    have hpSq0 : 0 ≤ p ^ 2 / 9216 := by positivity
    have hd8' : Real.sqrt a * quadraticExpDerivativeMajorant 8 rho l ≤
        1680 * ((rhoCap : ℝ) * (ratioCap : ℝ)) ^ 4 := by
      simpa only [a, rho, l, Rat.cast_mul] using hd8
    calc
      _ ≤ p ^ 2 / 9216 *
          (1680 * ((rhoCap : ℝ) * (ratioCap : ℝ)) ^ 4) := by gcongr
      _ = _ := by ring
  have herror6 :
      (if profile = 0 then 0 else
        (11 / 5760 : ℝ) * p * Real.sqrt p *
          (Real.sqrt a * quadraticExpDerivativeMajorant 6 rho l)) ≤ error6 := by
    by_cases hprofile : profile = 0
    · rw [if_pos hprofile]
      dsimp only [error6, p]
      simp [hprofile]
    · rw [if_neg hprofile]
      have hD6nonneg : 0 ≤ Real.sqrt a *
          quadraticExpDerivativeMajorant 6 rho l := by
        exact mul_nonneg (Real.sqrt_nonneg _)
          (quadraticExpDerivativeMajorant_nonneg hrho0 hl1)
      have hpSqrt : p * Real.sqrt p ≤ p * (sqrtProfileCap : ℝ) := by gcongr
      have hd6' : Real.sqrt a * quadraticExpDerivativeMajorant 6 rho l ≤
          120 * ((rhoCap : ℝ) * (ratioCap : ℝ)) ^ 3 := by
        simpa only [a, rho, l, Rat.cast_mul] using hd6
      have hcoefficient0 : 0 ≤ (11 / 5760 : ℝ) *
          (p * (sqrtProfileCap : ℝ)) := by positivity
      dsimp only [error6]
      calc
        _ = ((11 / 5760 : ℝ) * (p * Real.sqrt p)) *
            (Real.sqrt a * quadraticExpDerivativeMajorant 6 rho l) := by ring
        _ ≤ ((11 / 5760 : ℝ) *
            (p * (sqrtProfileCap : ℝ))) *
              (Real.sqrt a * quadraticExpDerivativeMajorant 6 rho l) := by
          apply mul_le_mul_of_nonneg_right _ hD6nonneg
          exact mul_le_mul_of_nonneg_left hpSqrt (by norm_num)
        _ ≤ (11 / 5760 : ℝ) *
            (p * (sqrtProfileCap : ℝ)) *
              (120 * ((rhoCap : ℝ) * (ratioCap : ℝ)) ^ 3) := by
          exact mul_le_mul_of_nonneg_left hd6' hcoefficient0
        _ = _ := by ring
  let gap : ℝ := p * (zRealBase : ℝ) / 8 -
    p ^ 2 * (zNormSqCap : ℝ) ^ 2 / 128 - (deficit : ℝ)
  have hgap0 : 0 ≤ gap := by
    dsimp only [gap, p]
    exact_mod_cast conditions.cancellation_nonneg
  have hremainder : error8 + error6 ≤ (gaussianLower : ℝ) * gap := by
    have hremReal :
        (((profile ^ 2 * (35 / 192) * (rhoCap * ratioCap) ^ 4 +
            11 * profile * sqrtProfileCap / 48 * (rhoCap * ratioCap) ^ 3 : ℚ) : ℝ)) ≤
          ((gaussianLower *
            (profile * zRealBase / 8 -
              profile ^ 2 * zNormSqCap ^ 2 / 128 - deficit) : ℚ) : ℝ) := by
      exact_mod_cast conditions.remainder_absorbed
    dsimp only [error8, error6, gap, p]
    push_cast at hremReal
    norm_num at hremReal ⊢
    exact hremReal
  have hremainderFactor : error8 + error6 ≤ factor * gap :=
    hremainder.trans (mul_le_mul_of_nonneg_right hfactorBounds.1 hgap0)
  have hrowMain :
      UpperContourKernel.normalizedFourthOrderRowBound rowCoefficients
          profile lam frequency ≤
        factor * (1 - (deficit : ℝ) +
          p * (zRealSlope : ℝ) / 8 * x) := by
    rw [UpperContourKernel.normalizedFourthOrderRowBound]
    norm_num [rowCoefficients]
    let leadingClosed : ℝ :=
      1 - p * (zRealBase : ℝ) / 8 +
        p * (zRealSlope : ℝ) / 8 * x +
        p ^ 2 * (zNormSqCap : ℝ) ^ 2 / 128
    have hfirst :
        factor *
              ‖1 - (((p / 8 : ℝ) : ℂ) *
                ((zReal : ℂ) + (zImaginary : ℂ) * Complex.I) ^ 2)‖ +
            p ^ 2 / 9216 *
              (Real.sqrt a * quadraticExpDerivativeMajorant 8 rho l) +
            (if profile = 0 then 0 else
              (11 / 5760 : ℝ) * p * Real.sqrt p *
                (Real.sqrt a * quadraticExpDerivativeMajorant 6 rho l)) ≤
          factor * leadingClosed + error8 + error6 := by
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hleadClosed hfactor0) herror8) herror6
    have hlocal :
        factor *
              ‖1 - (((p / 8 : ℝ) : ℂ) *
                ((zReal : ℂ) + (zImaginary : ℂ) * Complex.I) ^ 2)‖ +
            p ^ 2 / 9216 *
              (Real.sqrt a * quadraticExpDerivativeMajorant 8 rho l) +
            (if profile = 0 then 0 else
              (11 / 5760 : ℝ) * p * Real.sqrt p *
                (Real.sqrt a * quadraticExpDerivativeMajorant 6 rho l)) ≤
          factor * (1 - (deficit : ℝ) +
            p * (zRealSlope : ℝ) / 8 * x) := by
      calc
      _ ≤ factor * leadingClosed + error8 + error6 := hfirst
      _ = factor * leadingClosed + (error8 + error6) := by ring
      _ ≤ factor * leadingClosed + factor * gap :=
        (by simpa only [add_comm] using
          add_le_add_left hremainderFactor (factor * leadingClosed))
      _ = factor * (1 - (deficit : ℝ) +
          p * (zRealSlope : ℝ) / 8 * x) := by
        dsimp only [leadingClosed, gap]
        ring
    norm_num [factor, gaussianFactor, p, l, a, x, denominator, zReal,
      zImaginary, rho] at hlocal ⊢
    convert hlocal using 1 <;> ring
  have honeExp :
      1 - (deficit : ℝ) + p * (zRealSlope : ℝ) / 8 * x ≤
        Real.exp (-(deficit : ℝ) +
          p * (zRealSlope : ℝ) / 8 * x) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      Real.add_one_le_exp
        (-(deficit : ℝ) + p * (zRealSlope : ℝ) / 8 * x)
  have hrate : (rowRate : ℝ) + p * (zRealSlope : ℝ) / 8 ≤
      (gaussianRate : ℝ) := by
    dsimp only [p]
    exact_mod_cast conditions.rowRate_bound
  calc
    _ ≤ factor * (1 - (deficit : ℝ) +
        p * (zRealSlope : ℝ) / 8 * x) := hrowMain
    _ ≤ factor * Real.exp (-(deficit : ℝ) +
        p * (zRealSlope : ℝ) / 8 * x) := by gcongr
    _ ≤ Real.exp (-(gaussianRate : ℝ) * x) *
        Real.exp (-(deficit : ℝ) +
          p * (zRealSlope : ℝ) / 8 * x) := by gcongr
    _ = Real.exp (-(deficit : ℝ) -
        ((gaussianRate : ℝ) - p * (zRealSlope : ℝ) / 8) * x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(deficit : ℝ) - (rowRate : ℝ) * x) := by
      apply Real.exp_le_exp.mpr
      nlinarith

/-- Family-facing spelling of the endpoint envelope. -/
theorem fourthOrderMajorant_le_signedGaussian
    {profile lam cutoff rhoCap ratioCap zNormSqCap
      zRealBase zRealSlope gaussianLower sqrtProfileCap
      gaussianRate deficit rowRate : ℚ}
    (conditions : EndpointConditions profile lam cutoff rhoCap ratioCap zNormSqCap
      zRealBase zRealSlope gaussianLower sqrtProfileCap
      gaussianRate deficit rowRate)
    {frequency : ℝ} (hfrequency : frequency ∈ Icc 0 (cutoff : ℝ)) :
    sparseUpperFourthOrderNormalizedMajorant
        (profile : ℝ) (lam : ℝ) frequency ≤
      Real.exp (-(deficit : ℝ) - (rowRate : ℝ) * frequency ^ 2) := by
  rw [← normalizedFourthOrderRowBound_eq_sparseUpperMajorant
    profile lam frequency (by exact_mod_cast conditions.lam_lt_one)]
  exact normalizedFourthOrderRowBound_le_signedGaussian conditions hfrequency

/-- A signed Gaussian row envelope throughout a rational profile box.

The two endpoint witnesses have the same output amplitude and rate.  Convexity
is used only after the signed endpoint estimates have been established.
-/
theorem rowMajorant_le_signedGaussian
    {profileLeft profileRight lam cutoff deficit rowRate : ℚ}
    {leftRhoCap leftRatioCap leftZNormSqCap leftZRealBase leftZRealSlope
      leftGaussianLower leftSqrtProfileCap leftGaussianRate : ℚ}
    {rightRhoCap rightRatioCap rightZNormSqCap rightZRealBase rightZRealSlope
      rightGaussianLower rightSqrtProfileCap rightGaussianRate : ℚ}
    (hprofileOrder : profileLeft ≤ profileRight)
    (hleft : EndpointConditions profileLeft lam cutoff
      leftRhoCap leftRatioCap leftZNormSqCap leftZRealBase leftZRealSlope
      leftGaussianLower leftSqrtProfileCap leftGaussianRate deficit rowRate)
    (hright : EndpointConditions profileRight lam cutoff
      rightRhoCap rightRatioCap rightZNormSqCap rightZRealBase rightZRealSlope
      rightGaussianLower rightSqrtProfileCap rightGaussianRate deficit rowRate)
    {profile frequency : ℝ}
    (hprofile : profile ∈ Icc (profileLeft : ℝ) (profileRight : ℝ))
    (hfrequency : frequency ∈ Icc 0 (cutoff : ℝ)) :
    sparseUpperContourRowMajorant profile (lam : ℝ) frequency ≤
      Real.exp (-(deficit : ℝ) - (rowRate : ℝ) * frequency ^ 2) := by
  have hleftEnvelope := fourthOrderMajorant_le_signedGaussian hleft hfrequency
  have hrightEnvelope := fourthOrderMajorant_le_signedGaussian hright hfrequency
  have hconvex :=
    (convexOn_sparseUpperFourthOrderNormalizedMajorant
      (lambda := (lam : ℝ)) (frequency := frequency)
      (by exact_mod_cast hleft.lam_lt_one)).le_max_of_mem_Icc
      (show (profileLeft : ℝ) ∈ Ici 0 by
        simpa only [mem_Ici] using (show (0 : ℝ) ≤ profileLeft by
          exact_mod_cast hleft.profile_nonneg))
      (show (profileRight : ℝ) ∈ Ici 0 by
        simpa only [mem_Ici] using (show (0 : ℝ) ≤ profileRight by
          exact_mod_cast hleft.profile_nonneg.trans hprofileOrder))
      hprofile
  calc
    sparseUpperContourRowMajorant profile (lam : ℝ) frequency ≤
        sparseUpperFourthOrderNormalizedMajorant profile (lam : ℝ) frequency :=
      min_le_left _ _
    _ ≤ max
        (sparseUpperFourthOrderNormalizedMajorant
          (profileLeft : ℝ) (lam : ℝ) frequency)
        (sparseUpperFourthOrderNormalizedMajorant
          (profileRight : ℝ) (lam : ℝ) frequency) := hconvex
    _ ≤ Real.exp (-(deficit : ℝ) -
        (rowRate : ℝ) * frequency ^ 2) := max_le hleftEnvelope hrightEnvelope

end CertifiedJL.SparseUpperContourFamily.SignedClosedCore
