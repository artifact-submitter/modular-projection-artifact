/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.Assembly
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ConcreteSoundness
import CertifiedJL.Arithmetic.Transcendental.Trigonometric.Pi

/-! # Soundness of the centered-hybrid scalar prefactor -/

namespace CertifiedJL
namespace SparseUpperHybrid

open UpperContourKernel

/-- The exact real value represented by the rational and exponential factors
in `prefactor`, before outward rounding. -/
noncomputable def rationalPrefactorValue (box : ProfileBox) : ℝ :=
  let exponent : ℝ := (threshold : ℝ) * (box.lam : ℝ) -
    (gaussianSigma : ℝ) ^ 2 * (box.lam : ℝ) ^ 2 / 2
  (2 ^ securityBits : ℝ) * (((1 / (314159 / 100000) : ℚ) : ℝ)) *
    Real.exp (-exponent) *
    (1 / (1 - (box.lam : ℝ))) ^ (rows / 2) * 2

/-- The rational lower bound on pi gives the required one-sided comparison
between the analytic and executable prefactors. -/
theorem actualPrefactorValue_le_rationalPrefactorValue (box : ProfileBox) :
    actualPrefactorValue box ≤ rationalPrefactorValue box := by
  have hpiLower : (314159 / 100000 : ℝ) < Real.pi := by
    nlinarith [pi_gt_3141592_div_1000000]
  have hpiInv : 1 / Real.pi ≤ (((1 / (314159 / 100000) : ℚ) : ℝ)) := by
    norm_num only [one_div, Rat.cast_inv, Rat.cast_ofScientific,
      Rat.cast_natCast]
    rw [show (100000 : ℝ) / 314159 =
      ((314159 : ℝ) / 100000)⁻¹ by norm_num]
    exact (inv_le_inv₀ Real.pi_pos (by norm_num)).2 hpiLower.le
  unfold actualPrefactorValue rationalPrefactorValue
  have hscale : (0 : ℝ) ≤ 2 ^ securityBits := by positivity
  have hexp : 0 ≤ Real.exp (-(((threshold * box.lam -
      gaussianSigma ^ 2 * box.lam ^ 2 / 2 : ℚ)) : ℝ)) := Real.exp_nonneg _
  let common : ℝ := (2 ^ securityBits : ℝ) *
    Real.exp (-((threshold : ℝ) * (box.lam : ℝ) -
      (gaussianSigma : ℝ) ^ 2 * (box.lam : ℝ) ^ 2 / 2)) *
    (1 / (1 - (box.lam : ℝ))) ^ (rows / 2) * 2
  have hcommon : 0 ≤ common := by
    dsimp only [common]
    change 0 ≤ (2 ^ securityBits : ℝ) * Real.exp _ * _ ^ 128 * 2
    rw [show 128 = 2 * 64 by norm_num, pow_mul]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hscale (Real.exp_nonneg _))
        (pow_nonneg (sq_nonneg _) 64))
      (by norm_num)
  change (2 ^ securityBits : ℝ) * (2 / Real.pi) * _ * _ ≤ _
  change _ ≤ (2 ^ securityBits : ℝ) *
        (((1 / (314159 / 100000) : ℚ) : ℝ)) *
        Real.exp (-((threshold : ℝ) * (box.lam : ℝ) -
          (gaussianSigma : ℝ) ^ 2 * (box.lam : ℝ) ^ 2 / 2)) *
        (1 / (1 - (box.lam : ℝ))) ^ (rows / 2) * 2
  calc
    _ = (1 / Real.pi) * common := by simp only [common]; ring
    _ ≤ (((1 / (314159 / 100000) : ℚ) : ℝ)) * common :=
      mul_le_mul_of_nonneg_right hpiInv hcommon
    _ = _ := by simp only [common]; ring

/-- The interval prefactor contains its exact rational surrogate for every
manifest box. -/
theorem prefactor_contains_rationalPrefactorValue
    {certificate : CertificateBox} (hcertificate : certificate ∈ certificateBoxes) :
    (prefactor certificate.box).Contains
      (rationalPrefactorValue certificate.box) := by
  have hnumeric := certificateBox_numeric_facts hcertificate
  have hexponent : 0 ≤ threshold * certificate.box.lam -
      gaussianSigma ^ 2 * certificate.box.lam ^ 2 / 2 := by
    have hl : (0 : ℚ) < certificate.box.lam := hnumeric.2.2.1
    have hu : certificate.box.lam < 1 := hnumeric.2.2.2.1
    norm_num [threshold, gaussianSigma] at *
    nlinarith [sq_nonneg certificate.box.lam]
  have hscale := Interval.contains_ofRat precision (2 ^ securityBits : ℚ)
  have hpi := Interval.contains_ofRat precision (1 / (314159 / 100000) : ℚ)
  have hexp := Exp.negUpper_contains (p := precision) (k := 32) hexponent
  have hpower := Interval.contains_ofRat precision
    (1 / (1 - certificate.box.lam) ^ (rows / 2) : ℚ)
  have htwo := Interval.contains_ofRat precision (2 : ℚ)
  have hproduct := Interval.contains_mul
    (Interval.contains_mul
      (Interval.contains_mul (Interval.contains_mul hscale hpi) hexp) hpower)
      htwo
  simpa [prefactor, rationalPrefactorValue, frac, Rat.cast_sub,
    Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_natCast] using hproduct

/-- The executable upper endpoint dominates the exact analytic prefactor. -/
theorem actualPrefactorValue_le_prefactor_upperRat
    {certificate : CertificateBox} (hcertificate : certificate ∈ certificateBoxes) :
    actualPrefactorValue certificate.box ≤
      ((prefactor certificate.box).upperRat : ℝ) := by
  calc
    actualPrefactorValue certificate.box ≤
        rationalPrefactorValue certificate.box :=
      actualPrefactorValue_le_rationalPrefactorValue certificate.box
    _ ≤ ((prefactor certificate.box).upperRat : ℝ) := by
      simpa only [Interval.upperRat, Dyadic.cast_toRat] using
        (prefactor_contains_rationalPrefactorValue hcertificate).2

end SparseUpperHybrid
end CertifiedJL
