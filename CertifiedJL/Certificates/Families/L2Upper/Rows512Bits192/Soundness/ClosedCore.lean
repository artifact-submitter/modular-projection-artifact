/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Soundness.AnalyticCore

/-!
# Closed first-box upper-contour core

This file replaces the fine near-zero contour mesh for the first sparse
512-row box by a single Gaussian envelope.  The signed fourth-order correction
is retained: at the right profile endpoint it pays for the sixth- and
eighth-derivative remainders before the remaining small loss is absorbed into
the Gaussian exponent.
-/

open MeasureTheory Set

namespace CertifiedJL
namespace SparseUpperContour
namespace ClosedCore

private noncomputable def gaussianFactor (frequency : ℝ) : ℝ :=
  Real.sqrt (421 / 1000 : ℝ) /
    Real.sqrt (Real.sqrt ((421 / 1000 : ℝ) ^ 2 + frequency ^ 2))

/-- A signed leading-term estimate, independent of the contour parameters.
Keeping the negative quadratic term permits reuse for other row counts,
profiles, and contour shifts; replacing it by an absolute value loses that gain. -/
theorem leading_modulus_le
    (q zReal zImaginary : ℝ) :
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

private theorem rho_le
    {frequency : ℝ} (hfrequency0 : 0 ≤ frequency)
    (hfrequency : frequency ≤ 1 / 4) :
    Real.sqrt ((579 / 1000 : ℝ) ^ 2 + frequency ^ 2) ≤ 829 / 1000 := by
  have hsqrt := Real.sq_sqrt
    (show 0 ≤ (579 / 1000 : ℝ) ^ 2 + frequency ^ 2 by positivity)
  have hsqrt0 := Real.sqrt_nonneg
    ((579 / 1000 : ℝ) ^ 2 + frequency ^ 2)
  have hsum : Real.sqrt ((579 / 1000 : ℝ) ^ 2 + frequency ^ 2) ≤
      579 / 1000 + frequency := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 579 / 1000 by norm_num) hfrequency0]
  linarith

private theorem normalized_d6_le
    {frequency : ℝ} (hfrequency0 : 0 ≤ frequency)
    (hfrequency : frequency ≤ 1 / 4) :
    Real.sqrt (1 - (579 / 1000 : ℝ)) *
        quadraticExpDerivativeMajorant 6
          (Real.sqrt ((579 / 1000 : ℝ) ^ 2 + frequency ^ 2))
          (579 / 1000 : ℝ) ≤ 2000 := by
  let rho := Real.sqrt ((579 / 1000 : ℝ) ^ 2 + frequency ^ 2)
  have hrho0 : 0 ≤ rho := Real.sqrt_nonneg _
  have hrho : rho ≤ 829 / 1000 := rho_le hfrequency0 hfrequency
  have hratio0 : 0 ≤ (rho + 421 / 1000) / (421 / 1000 : ℝ) := by positivity
  have hratio : (rho + 421 / 1000) / (421 / 1000 : ℝ) ≤ 3 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 421 / 1000)]
    linarith
  have hfactor :
      Real.sqrt (1 - (579 / 1000 : ℝ)) *
          quadraticExpDerivativeMajorant 6 rho (579 / 1000 : ℝ) =
        120 * rho ^ 3 * ((rho + 421 / 1000) / (421 / 1000 : ℝ)) ^ 3 := by
    have hclosed := UpperContourKernel.normalizedDerivativeMajorantValue_six_eq
      rho (lambda := (579 / 1000 : ℚ)) (by norm_num)
    norm_num at hclosed ⊢
    calc
      _ = UpperContourKernel.normalizedDerivativeMajorantValue 6 rho
            (421 / 1000 : ℚ) := hclosed.symm
      _ = 120 * rho ^ 3 * ((rho + 421 / 1000) / (421 / 1000 : ℝ)) ^ 3 := by
        rw [UpperContourKernel.normalizedDerivativeMajorantValue_six]
        norm_num
        ring
  rw [hfactor]
  have hrhoPow := pow_le_pow_left₀ hrho0 hrho 3
  have hratioPow := pow_le_pow_left₀ hratio0 hratio 3
  calc
    120 * rho ^ 3 * ((rho + 421 / 1000) / (421 / 1000 : ℝ)) ^ 3 ≤
        120 * (829 / 1000 : ℝ) ^ 3 * 3 ^ 3 := by gcongr
    _ ≤ 2000 := by norm_num

private theorem normalized_d8_le
    {frequency : ℝ} (hfrequency0 : 0 ≤ frequency)
    (hfrequency : frequency ≤ 1 / 4) :
    Real.sqrt (1 - (579 / 1000 : ℝ)) *
        quadraticExpDerivativeMajorant 8
          (Real.sqrt ((579 / 1000 : ℝ) ^ 2 + frequency ^ 2))
          (579 / 1000 : ℝ) ≤ 70000 := by
  let rho := Real.sqrt ((579 / 1000 : ℝ) ^ 2 + frequency ^ 2)
  have hrho0 : 0 ≤ rho := Real.sqrt_nonneg _
  have hrho : rho ≤ 829 / 1000 := rho_le hfrequency0 hfrequency
  have hratio0 : 0 ≤ (rho + 421 / 1000) / (421 / 1000 : ℝ) := by positivity
  have hratio : (rho + 421 / 1000) / (421 / 1000 : ℝ) ≤ 3 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 421 / 1000)]
    linarith
  have hfactor :
      Real.sqrt (1 - (579 / 1000 : ℝ)) *
          quadraticExpDerivativeMajorant 8 rho (579 / 1000 : ℝ) =
        1680 * rho ^ 4 * ((rho + 421 / 1000) / (421 / 1000 : ℝ)) ^ 4 := by
    have hclosed := UpperContourKernel.normalizedDerivativeMajorantValue_eight_eq
      rho (lambda := (579 / 1000 : ℚ)) (by norm_num)
    norm_num at hclosed ⊢
    calc
      _ = UpperContourKernel.normalizedDerivativeMajorantValue 8 rho
            (421 / 1000 : ℚ) := hclosed.symm
      _ = 1680 * rho ^ 4 * ((rho + 421 / 1000) / (421 / 1000 : ℝ)) ^ 4 := by
        rw [UpperContourKernel.normalizedDerivativeMajorantValue_eight]
        norm_num
        ring
  rw [hfactor]
  have hrhoPow := pow_le_pow_left₀ hrho0 hrho 4
  have hratioPow := pow_le_pow_left₀ hratio0 hratio 4
  calc
    1680 * rho ^ 4 * ((rho + 421 / 1000) / (421 / 1000 : ℝ)) ^ 4 ≤
        1680 * (829 / 1000 : ℝ) ^ 4 * 3 ^ 4 := by gcongr
    _ ≤ 70000 := by norm_num

private theorem gaussianFactor_bounds
    {frequency : ℝ} (hfrequency0 : 0 ≤ frequency)
    (hfrequency : frequency ≤ 1 / 4) :
    9 / 10 ≤ gaussianFactor frequency ∧ gaussianFactor frequency ≤ 1 := by
  let denominator := (421 / 1000 : ℝ) ^ 2 + frequency ^ 2
  have hdenominator : 0 < denominator := by dsimp only [denominator]; positivity
  have hsqrtDenominator : 0 < Real.sqrt denominator := Real.sqrt_pos.2 hdenominator
  have hsqrtSqrtDenominator : 0 < Real.sqrt (Real.sqrt denominator) :=
    Real.sqrt_pos.2 hsqrtDenominator
  have hfrequencySq : frequency ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by nlinarith
  have hfactorFourth : gaussianFactor frequency ^ 4 =
      (421 / 1000 : ℝ) ^ 2 / denominator := by
    have haSq : Real.sqrt (421 / 1000 : ℝ) ^ 2 = 421 / 1000 :=
      Real.sq_sqrt (by norm_num)
    have hdenSq : Real.sqrt denominator ^ 2 = denominator :=
      Real.sq_sqrt hdenominator.le
    have hdenSqrtSq : Real.sqrt (Real.sqrt denominator) ^ 2 =
        Real.sqrt denominator := Real.sq_sqrt hsqrtDenominator.le
    dsimp only [gaussianFactor]
    calc
      (Real.sqrt (421 / 1000 : ℝ) /
          Real.sqrt (Real.sqrt denominator)) ^ 4 =
        Real.sqrt (421 / 1000 : ℝ) ^ 4 /
          Real.sqrt (Real.sqrt denominator) ^ 4 := by rw [div_pow]
      _ = (421 / 1000 : ℝ) ^ 2 / denominator := by
        rw [show Real.sqrt (421 / 1000 : ℝ) ^ 4 =
            (Real.sqrt (421 / 1000 : ℝ) ^ 2) ^ 2 by ring,
          haSq,
          show Real.sqrt (Real.sqrt denominator) ^ 4 =
            (Real.sqrt (Real.sqrt denominator) ^ 2) ^ 2 by ring,
          hdenSqrtSq, hdenSq]
  have hfactor0 : 0 ≤ gaussianFactor frequency := by
    unfold gaussianFactor
    positivity
  constructor
  · apply (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 9 / 10)
      hfactor0 (by norm_num : (4 : ℕ) ≠ 0)).mp
    rw [hfactorFourth]
    rw [le_div_iff₀ hdenominator]
    dsimp only [denominator]
    nlinarith
  · apply (pow_le_pow_iff_left₀ hfactor0 (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (4 : ℕ) ≠ 0)).mp
    rw [hfactorFourth]
    norm_num
    exact (div_le_one hdenominator).2 (by
      dsimp only [denominator]
      nlinarith [sq_nonneg frequency])

private theorem gaussianFactor_le_exp
    {frequency : ℝ} (hfrequency0 : 0 ≤ frequency)
    (hfrequency : frequency ≤ 1 / 4) :
    gaussianFactor frequency ≤
      Real.exp (-(250000 / 239741 : ℝ) * frequency ^ 2) := by
  let denominator := (421 / 1000 : ℝ) ^ 2 + frequency ^ 2
  let cap := (421 / 1000 : ℝ) ^ 2 + (1 / 4 : ℝ) ^ 2
  let y := frequency ^ 2 / cap
  have hdenominator : 0 < denominator := by dsimp only [denominator]; positivity
  have hcap : 0 < cap := by dsimp only [cap]; positivity
  have hfrequencySq : frequency ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by nlinarith
  have hy0 : 0 ≤ y := by dsimp only [y]; positivity
  have hfactorFourth : gaussianFactor frequency ^ 4 =
      (421 / 1000 : ℝ) ^ 2 / denominator := by
    have haSq : Real.sqrt (421 / 1000 : ℝ) ^ 2 = 421 / 1000 :=
      Real.sq_sqrt (by norm_num)
    have hdenSq : Real.sqrt denominator ^ 2 = denominator :=
      Real.sq_sqrt hdenominator.le
    have hsqrtDenominator : 0 < Real.sqrt denominator := Real.sqrt_pos.2 hdenominator
    have hdenSqrtSq : Real.sqrt (Real.sqrt denominator) ^ 2 =
        Real.sqrt denominator := Real.sq_sqrt hsqrtDenominator.le
    dsimp only [gaussianFactor]
    calc
      (Real.sqrt (421 / 1000 : ℝ) /
          Real.sqrt (Real.sqrt denominator)) ^ 4 =
        Real.sqrt (421 / 1000 : ℝ) ^ 4 /
          Real.sqrt (Real.sqrt denominator) ^ 4 := by rw [div_pow]
      _ = (421 / 1000 : ℝ) ^ 2 / denominator := by
        rw [show Real.sqrt (421 / 1000 : ℝ) ^ 4 =
            (Real.sqrt (421 / 1000 : ℝ) ^ 2) ^ 2 by ring,
          haSq,
          show Real.sqrt (Real.sqrt denominator) ^ 4 =
            (Real.sqrt (Real.sqrt denominator) ^ 2) ^ 2 by ring,
          hdenSqrtSq, hdenSq]
  have hratio : (421 / 1000 : ℝ) ^ 2 / denominator ≤ 1 - y := by
    rw [div_le_iff₀ hdenominator]
    have hnonneg : 0 ≤ frequency ^ 2 * ((1 / 4 : ℝ) ^ 2 - frequency ^ 2) :=
      mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hfrequencySq)
    dsimp only [denominator, cap, y]
    field_simp
    nlinarith
  have honeExp : 1 - y ≤ Real.exp (-y) := by
    nlinarith [Real.add_one_le_exp (-y)]
  have hpow : gaussianFactor frequency ^ 4 ≤
      (Real.exp (-(250000 / 239741 : ℝ) * frequency ^ 2)) ^ 4 := by
    rw [hfactorFourth]
    calc
      _ ≤ 1 - y := hratio
      _ ≤ Real.exp (-y) := honeExp
      _ = (Real.exp (-(250000 / 239741 : ℝ) * frequency ^ 2)) ^ 4 := by
        rw [← Real.exp_nat_mul]
        dsimp only [y, cap]
        norm_num
        ring
  apply (pow_le_pow_iff_left₀
    (by unfold gaussianFactor; positivity)
    (Real.exp_nonneg _) (by norm_num : (4 : ℕ) ≠ 0)).mp hpow

private theorem z_norm_sq_le_six
    {frequency : ℝ} (hfrequency0 : 0 ≤ frequency)
    (hfrequency : frequency ≤ 1 / 4) :
    let denominator := (421 / 1000 : ℝ) ^ 2 + frequency ^ 2
    let zReal := ((579 / 1000 : ℝ) * (421 / 1000)) / denominator -
      frequency ^ 2 / denominator
    let zImaginary := frequency / denominator
    (zReal ^ 2 + zImaginary ^ 2) ^ 2 ≤ 6 := by
  dsimp only
  let denominator := (421 / 1000 : ℝ) ^ 2 + frequency ^ 2
  have hdenominator : 0 < denominator := by dsimp only [denominator]; positivity
  have hfrequencySq : frequency ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by nlinarith
  have hidentity :
      ((((579 / 1000 : ℝ) * (421 / 1000)) / denominator -
            frequency ^ 2 / denominator) ^ 2 +
          (frequency / denominator) ^ 2) =
        ((579 / 1000 : ℝ) ^ 2 + frequency ^ 2) / denominator := by
    field_simp [hdenominator.ne']
    dsimp only [denominator]
    ring
  rw [hidentity]
  have hratio0 : 0 ≤
      ((579 / 1000 : ℝ) ^ 2 + frequency ^ 2) / denominator := by positivity
  have hratio :
      ((579 / 1000 : ℝ) ^ 2 + frequency ^ 2) / denominator ≤ 9 / 4 := by
    rw [div_le_iff₀ hdenominator]
    dsimp only [denominator]
    nlinarith
  exact (pow_le_pow_left₀ hratio0 hratio 2).trans (by norm_num)

private theorem z_square_real_lower
    {frequency : ℝ} (hfrequency0 : 0 ≤ frequency)
    (hfrequency : frequency ≤ 1 / 4) :
    let denominator := (421 / 1000 : ℝ) ^ 2 + frequency ^ 2
    let zReal := ((579 / 1000 : ℝ) * (421 / 1000)) / denominator -
      frequency ^ 2 / denominator
    let zImaginary := frequency / denominator
    3 / 2 - 40 * frequency ^ 2 ≤ zReal ^ 2 - zImaginary ^ 2 := by
  dsimp only
  let x := frequency ^ 2
  let denominator := (421 / 1000 : ℝ) ^ 2 + x
  have hx0 : 0 ≤ x := sq_nonneg frequency
  have hx : x ≤ 1 / 16 := by dsimp only [x]; nlinarith
  have hdenominator : 0 < denominator := by dsimp only [denominator]; positivity
  have hidentity :
      ((((579 / 1000 : ℝ) * (421 / 1000)) / denominator -
            frequency ^ 2 / denominator) ^ 2 -
          (frequency / denominator) ^ 2) =
        (((579 / 1000 : ℝ) * (421 / 1000) - x) ^ 2 - x) /
          denominator ^ 2 := by
    dsimp only [x]
    field_simp [hdenominator.ne']
  rw [hidentity]
  rw [le_div_iff₀ (sq_pos_of_pos hdenominator)]
  have hcube : 0 ≤ x ^ 3 := by positivity
  have hsquare : 0 ≤ (x - 7 / 250 : ℝ) ^ 2 := sq_nonneg _
  dsimp only [denominator]
  norm_num at hx ⊢
  ring_nf at ⊢
  nlinarith

private theorem endpoint_zero_le_exp
    {frequency : ℝ} (hfrequency0 : 0 ≤ frequency)
    (hfrequency : frequency ≤ 1 / 4) :
    sparseUpperFourthOrderNormalizedMajorant 0 (579 / 1000) frequency ≤
      Real.exp (-(103 / 100 : ℝ) * frequency ^ 2) := by
  have heq := normalizedFourthOrderRowBound_eq_sparseUpperMajorant
    (0 : ℚ) (579 / 1000 : ℚ) frequency (by norm_num)
  norm_num at heq
  rw [← heq]
  have hgaussian := gaussianFactor_le_exp hfrequency0 hfrequency
  have hexponent :
      Real.exp (-(250000 / 239741 : ℝ) * frequency ^ 2) ≤
        Real.exp (-(103 / 100 : ℝ) * frequency ^ 2) := by
    apply Real.exp_le_exp.mpr
    have : (103 / 100 : ℝ) ≤ 250000 / 239741 := by norm_num
    nlinarith [sq_nonneg frequency]
  have hzero :
      UpperContourKernel.normalizedFourthOrderRowBound rowCoefficients
          (0 : ℚ) (579 / 1000 : ℚ) frequency = gaussianFactor frequency := by
    norm_num [UpperContourKernel.normalizedFourthOrderRowBound, gaussianFactor,
      rowCoefficients]
  rw [hzero]
  exact hgaussian.trans hexponent

private theorem endpoint_right_le_gaussian_loss
    {frequency : ℝ} (hfrequency0 : 0 ≤ frequency)
    (hfrequency : frequency ≤ 1 / 4) :
    sparseUpperFourthOrderNormalizedMajorant (1 / 1024) (579 / 1000) frequency ≤
      gaussianFactor frequency * (1 + frequency ^ 2 / 100) := by
  have heq := normalizedFourthOrderRowBound_eq_sparseUpperMajorant
    (1 / 1024 : ℚ) (579 / 1000 : ℚ) frequency (by norm_num)
  norm_num at heq
  rw [← heq, UpperContourKernel.normalizedFourthOrderRowBound]
  norm_num [rowCoefficients]
  let denominator := (177241 / 1000000 : ℝ) + frequency ^ 2
  let rootA := Real.sqrt (421 : ℝ) / Real.sqrt 1000
  let factor := rootA / Real.sqrt (Real.sqrt denominator)
  let zReal := (243759 / 1000000 : ℝ) / denominator -
    frequency ^ 2 / denominator
  let zImaginary := frequency / denominator
  let rho := Real.sqrt ((335241 / 1000000 : ℝ) + frequency ^ 2)
  have hrootEq : rootA = Real.sqrt (421 / 1000 : ℝ) := by
    dsimp only [rootA]
    norm_num
  have hfactorEq : factor = gaussianFactor frequency := by
    dsimp only [factor, gaussianFactor, denominator]
    rw [hrootEq]
    norm_num
  rw [← hfactorEq]
  have hfactor := gaussianFactor_bounds hfrequency0 hfrequency
  rw [← hfactorEq] at hfactor
  have hfactor0 : 0 ≤ factor :=
    (by norm_num : (0 : ℝ) ≤ 9 / 10).trans hfactor.1
  have hreal := z_square_real_lower hfrequency0 hfrequency
  have hnormSq := z_norm_sq_le_six hfrequency0 hfrequency
  dsimp only [denominator, zReal, zImaginary] at hreal hnormSq
  have hnorm :
      ‖1 - (1 / 8192 : ℂ) *
          ((zReal : ℂ) + (zImaginary : ℂ) * Complex.I) ^ 2‖ =
        Real.sqrt
          ((1 - (1 / 8192 : ℝ) * (zReal ^ 2 - zImaginary ^ 2)) ^ 2 +
            (-((1 / 8192 : ℝ) * (2 * zReal * zImaginary))) ^ 2) := by
    simpa using
      (UpperContourKernel.leadingCorrectionValue_eq_norm
        (1 / 8192 : ℝ) 1 zReal zImaginary).symm
  have hlead := leading_modulus_le (1 / 8192 : ℝ) zReal zImaginary
  have hleadClosed :
      Real.sqrt
          ((1 - (1 / 8192 : ℝ) * (zReal ^ 2 - zImaginary ^ 2)) ^ 2 +
            (-((1 / 8192 : ℝ) * (2 * zReal * zImaginary))) ^ 2) ≤
        1 - 3 / 16384 + 5 / 1024 * frequency ^ 2 + 1 / 1024000 := by
    calc
      _ ≤ 1 - (1 / 8192 : ℝ) * (zReal ^ 2 - zImaginary ^ 2) +
          (1 / 8192 : ℝ) ^ 2 * (zReal ^ 2 + zImaginary ^ 2) ^ 2 / 2 := hlead
      _ ≤ _ := by nlinarith
  have hd8 := normalized_d8_le hfrequency0 hfrequency
  have hd6 := normalized_d6_le hfrequency0 hfrequency
  norm_num [rho, rootA] at hd8 hd6
  have hd8Closed :
      1 / 9663676416 *
          (rootA *
            quadraticExpDerivativeMajorant 8 rho (579 / 1000)) ≤
        factor * (1 / 102400 : ℝ) := by
    have hfactorLower : (9 / 10 : ℝ) ≤ factor := hfactor.1
    dsimp only [rho, rootA]
    nlinarith
  have hd6Closed :
      11 / 188743680 *
          (rootA *
            quadraticExpDerivativeMajorant 6 rho (579 / 1000)) ≤
        factor * (3 / 20480 : ℝ) := by
    have hfactorLower : (9 / 10 : ℝ) ≤ factor := hfactor.1
    dsimp only [rho, rootA]
    nlinarith
  have hmain :
      factor *
          ‖1 - (1 / 8192 : ℂ) *
            ((zReal : ℂ) + (zImaginary : ℂ) * Complex.I) ^ 2‖ +
        1 / 9663676416 *
          (rootA * quadraticExpDerivativeMajorant 8 rho (579 / 1000)) +
        11 / 188743680 *
          (rootA * quadraticExpDerivativeMajorant 6 rho (579 / 1000)) ≤
        factor * (1 + frequency ^ 2 / 100) := by
    rw [hnorm]
    calc
      factor *
          Real.sqrt
            ((1 - (1 / 8192 : ℝ) * (zReal ^ 2 - zImaginary ^ 2)) ^ 2 +
              (-((1 / 8192 : ℝ) * (2 * zReal * zImaginary))) ^ 2) +
        1 / 9663676416 *
          (rootA *
            quadraticExpDerivativeMajorant 8 rho (579 / 1000)) +
        11 / 188743680 *
          (rootA *
            quadraticExpDerivativeMajorant 6 rho (579 / 1000)) ≤
      factor *
          (1 - 3 / 16384 + 5 / 1024 * frequency ^ 2 + 1 / 1024000) +
        factor * (1 / 102400) +
          factor * (3 / 20480) := by gcongr
      _ ≤ factor * (1 + 5 / 1024 * frequency ^ 2) := by
        nlinarith
      _ ≤ factor * (1 + frequency ^ 2 / 100) := by
        gcongr
        nlinarith [sq_nonneg frequency]
  norm_num [factor, rootA, denominator, zReal, zImaginary, rho] at hmain ⊢
  exact hmain

private theorem endpoint_right_le_exp
    {frequency : ℝ} (hfrequency0 : 0 ≤ frequency)
    (hfrequency : frequency ≤ 1 / 4) :
    sparseUpperFourthOrderNormalizedMajorant (1 / 1024) (579 / 1000) frequency ≤
      Real.exp (-(103 / 100 : ℝ) * frequency ^ 2) := by
  have hrow := endpoint_right_le_gaussian_loss hfrequency0 hfrequency
  have hgaussian := gaussianFactor_le_exp hfrequency0 hfrequency
  have hloss : 1 + frequency ^ 2 / 100 ≤
      Real.exp (frequency ^ 2 / 100) := by
    simpa [add_comm] using Real.add_one_le_exp (frequency ^ 2 / 100)
  have hnonneg : 0 ≤ 1 + frequency ^ 2 / 100 := by positivity
  calc
    _ ≤ gaussianFactor frequency * (1 + frequency ^ 2 / 100) := hrow
    _ ≤ Real.exp (-(250000 / 239741 : ℝ) * frequency ^ 2) *
        Real.exp (frequency ^ 2 / 100) :=
      mul_le_mul hgaussian hloss hnonneg (Real.exp_nonneg _)
    _ = Real.exp (-((250000 / 239741 : ℝ) - 1 / 100) * frequency ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(103 / 100 : ℝ) * frequency ^ 2) := by
      apply Real.exp_le_exp.mpr
      have : (103 / 100 : ℝ) ≤ 250000 / 239741 - 1 / 100 := by norm_num
      nlinarith [sq_nonneg frequency]

/-- On the first profile box and the whole quarter-frequency core, the actual
normalized U4/U8 row majorant is bounded by one closed Gaussian.  The proof
uses profile convexity only after both endpoint estimates have been proved. -/
theorem rowMajorant_le_closedGaussian
    {profile frequency : ℝ}
    (hprofile : profile ∈ Set.Icc (0 : ℝ) (1 / 1024))
    (hfrequency : frequency ∈ Set.Icc (0 : ℝ) (1 / 4)) :
    sparseUpperContourRowMajorant profile (579 / 1000) frequency ≤
      Real.exp (-(103 / 100 : ℝ) * frequency ^ 2) := by
  have hleft := endpoint_zero_le_exp hfrequency.1 hfrequency.2
  have hright := endpoint_right_le_exp hfrequency.1 hfrequency.2
  have hconvex :=
    (convexOn_sparseUpperFourthOrderNormalizedMajorant
      (lambda := (579 / 1000 : ℝ)) (frequency := frequency) (by norm_num)).le_max_of_mem_Icc
      (show (0 : ℝ) ∈ Set.Ici 0 by simp)
      (show (1 / 1024 : ℝ) ∈ Set.Ici 0 by norm_num)
      hprofile
  calc
    sparseUpperContourRowMajorant profile (579 / 1000) frequency ≤
        sparseUpperFourthOrderNormalizedMajorant profile (579 / 1000) frequency :=
      min_le_left _ _
    _ ≤ max
        (sparseUpperFourthOrderNormalizedMajorant 0 (579 / 1000) frequency)
        (sparseUpperFourthOrderNormalizedMajorant (1 / 1024)
          (579 / 1000) frequency) := hconvex
    _ ≤ Real.exp (-(103 / 100 : ℝ) * frequency ^ 2) :=
      max_le hleft hright

end ClosedCore
end SparseUpperContour
end CertifiedJL
