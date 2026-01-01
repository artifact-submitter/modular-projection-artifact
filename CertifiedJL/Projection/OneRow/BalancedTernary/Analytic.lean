/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Transcendental.Trigonometric.Pi
import CertifiedJL.Certificates.Families.OneRow975.Finite.LocalSoundness
import CertifiedJL.Projection.OneRow.BalancedTernary.Core

/-!
# Scalar analytic bound for the sparse one-row theorem

This file proves the scalar majorization used inside the bounded profile-split
assembly. The complete theorem is assembled in `SparseOneRowProfileSplit`.
-/

open scoped BigOperators ENNReal

open MeasureTheory ProbabilityTheory

namespace CertifiedJL

open Probability

private theorem sparseOneRowThreshold_pos :
    0 < sparseOneRowRademacherThreshold := by
  unfold sparseOneRowRademacherThreshold
  positivity

private theorem sparseOneRowThreshold_sq_div_two :
    sparseOneRowRademacherThreshold ^ 2 / 2 = (1521 : ℝ) / 16 := by
  unfold sparseOneRowRademacherThreshold
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private theorem sparseOneRow_gaussianCoefficient_eq :
    (Real.sqrt (2 * Real.pi) *
        sparseOneRowRademacherThreshold)⁻¹ =
      2 / (39 * Real.sqrt Real.pi) := by
  unfold sparseOneRowRademacherThreshold
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrtTwoSq : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrtPi : Real.sqrt Real.pi ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
  field_simp
  nlinarith

/--
At the exact sparse one-row threshold and Berry--Esseen constant `3/5`, the
analytic profile is bounded by the executable scalar envelope.
-/
theorem sparseOneRow_profile_le_scalarEnvelope
    {B : ℝ} (hB0 : 0 ≤ B) :
    Real.exp
          (-sparseOneRowRademacherThreshold ^ 2 * (1 + B ^ 2) / 2) *
        Real.cosh (sparseOneRowRademacherThreshold * B) *
        (Real.cosh (sparseOneRowRademacherThreshold * B ^ 2) /
              (Real.sqrt (2 * Real.pi) *
                sparseOneRowRademacherThreshold) +
          2 * ((3 : ℝ) / 5) * B ^ 2 *
            Real.cosh (sparseOneRowRademacherThreshold * B ^ 2) ^ 3) ≤
      SparseOneRowCertificate.scalarEnvelope B := by
  let x := sparseOneRowRademacherThreshold
  let xu : ℝ := SparseOneRowCertificate.xUpper
  let g : ℝ := SparseOneRowCertificate.gaussianCoefficientUpper
  have hx0 : 0 ≤ x := sparseOneRowThreshold_pos.le
  have hxu0 : 0 ≤ xu := by
    norm_num [xu, SparseOneRowCertificate.xUpper]
  have hx_le : x ≤ xu := by
    simpa [x, xu, sparseOneRowRademacherThreshold,
      SparseOneRowCertificate.xUpper] using
      (sparseOneRowThreshold_lt_13789_div_1000).le
  have hBsq0 : 0 ≤ B ^ 2 := sq_nonneg B
  have hlinear :
      Real.cosh (x * B) ≤ Real.cosh (xu * B) := by
    rw [Real.cosh_le_cosh]
    rw [abs_of_nonneg (mul_nonneg hx0 hB0),
      abs_of_nonneg (mul_nonneg hxu0 hB0)]
    exact mul_le_mul_of_nonneg_right hx_le hB0
  have hquadratic :
      Real.cosh (x * B ^ 2) ≤ Real.cosh (xu * B ^ 2) := by
    rw [Real.cosh_le_cosh]
    rw [abs_of_nonneg (mul_nonneg hx0 hBsq0),
      abs_of_nonneg (mul_nonneg hxu0 hBsq0)]
    exact mul_le_mul_of_nonneg_right hx_le hBsq0
  have hcube :
      Real.cosh (x * B ^ 2) ^ 3 ≤
        Real.cosh (xu * B ^ 2) ^ 3 :=
    pow_le_pow_left₀ (Real.cosh_pos _).le hquadratic 3
  have hcoefficient :
      (Real.sqrt (2 * Real.pi) * x)⁻¹ ≤ g := by
    rw [show (Real.sqrt (2 * Real.pi) * x)⁻¹ =
      2 / (39 * Real.sqrt Real.pi) by
        exact sparseOneRow_gaussianCoefficient_eq]
    simpa [g, SparseOneRowCertificate.gaussianCoefficientUpper] using
      (two_div_39_mul_sqrt_pi_lt_200_div_6903).le
  have hgaussian :
      (Real.sqrt (2 * Real.pi) * x)⁻¹ *
          Real.cosh (x * B ^ 2) ≤
        g * Real.cosh (xu * B ^ 2) := by
    exact mul_le_mul hcoefficient hquadratic
      (Real.cosh_pos _).le
      (by norm_num [g,
        SparseOneRowCertificate.gaussianCoefficientUpper])
  have hberry :
      (6 / 5 : ℝ) * B ^ 2 *
          Real.cosh (x * B ^ 2) ^ 3 ≤
        (6 / 5 : ℝ) * B ^ 2 *
          Real.cosh (xu * B ^ 2) ^ 3 := by
    exact mul_le_mul_of_nonneg_left hcube
      (mul_nonneg (by norm_num) hBsq0)
  have hbracket :
      Real.cosh (x * B ^ 2) /
              (Real.sqrt (2 * Real.pi) * x) +
          2 * ((3 : ℝ) / 5) * B ^ 2 *
            Real.cosh (x * B ^ 2) ^ 3 ≤
        g * Real.cosh (xu * B ^ 2) +
          (6 / 5 : ℝ) * B ^ 2 *
            Real.cosh (xu * B ^ 2) ^ 3 := by
    rw [div_eq_mul_inv, mul_comm
      (Real.cosh (x * B ^ 2))]
    norm_num only
    exact add_le_add hgaussian hberry
  have hbracket0 :
      0 ≤ Real.cosh (x * B ^ 2) /
              (Real.sqrt (2 * Real.pi) * x) +
          2 * ((3 : ℝ) / 5) * B ^ 2 *
            Real.cosh (x * B ^ 2) ^ 3 := by positivity
  have hexponent :
      -x ^ 2 * (1 + B ^ 2) / 2 =
        -(SparseOneRowCertificate.exponentRate : ℝ) *
          (1 + B ^ 2) := by
    rw [show -x ^ 2 * (1 + B ^ 2) / 2 =
      -(x ^ 2 / 2) * (1 + B ^ 2) by ring]
    rw [show x ^ 2 / 2 = (1521 : ℝ) / 16 by
      simpa [x] using sparseOneRowThreshold_sq_div_two]
    norm_num [SparseOneRowCertificate.exponentRate]
  have hmiddle :
      Real.exp (-x ^ 2 * (1 + B ^ 2) / 2) *
          Real.cosh (x * B) ≤
        Real.exp
            (-(SparseOneRowCertificate.exponentRate : ℝ) *
              (1 + B ^ 2)) *
          Real.cosh (xu * B) := by
    rw [hexponent]
    exact mul_le_mul_of_nonneg_left hlinear (Real.exp_nonneg _)
  have htotal :
      Real.exp (-x ^ 2 * (1 + B ^ 2) / 2) *
          Real.cosh (x * B) *
          (Real.cosh (x * B ^ 2) /
                (Real.sqrt (2 * Real.pi) * x) +
            2 * ((3 : ℝ) / 5) * B ^ 2 *
              Real.cosh (x * B ^ 2) ^ 3) ≤
        Real.exp
            (-(SparseOneRowCertificate.exponentRate : ℝ) *
              (1 + B ^ 2)) *
          Real.cosh (xu * B) *
          (g * Real.cosh (xu * B ^ 2) +
            (6 / 5 : ℝ) * B ^ 2 *
              Real.cosh (xu * B ^ 2) ^ 3) :=
    mul_le_mul hmiddle hbracket hbracket0
      (mul_nonneg (Real.exp_nonneg _) (Real.cosh_pos _).le)
  simpa [SparseOneRowCertificate.scalarEnvelope, x, xu, g,
    SparseOneRowCertificate.berryEsseenFactor] using htotal

end CertifiedJL
