/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Fourier.Prawitz.Kernel

/-!
# Frequency multipliers for the Beurling--Prawitz kernels

This file fixes the Fourier normalization used in the sharp smoothing
argument.  In Vaaler's convention `e(t x) = exp (2 π i t x)`, the Fourier
transform of the squared-sinc kernel is the triangle multiplier

`K̂(t) = 1 - |t|` on `|t| < 1`,

and the Fourier transform of the derivative of the Beurling approximation
is

`Ĵ(t) = π t (1 - |t|) cot(π t) + |t|`.

At zero the latter has removable value one.  We define it using
`regularizedFrequencyCot`, so its value at zero is correct by construction.
The main theorem identifies these two multipliers exactly with the real and
imaginary parts of the regularized Prawitz kernel.  This is the algebraic
normalization boundary needed before proving the analytic Fourier inversion
formula for `beurlingH`.
-/

open Set
open scoped ComplexConjugate

namespace CertifiedJL
namespace Probability

/-- The compactly supported triangle multiplier. -/
noncomputable def beurlingKHat (t : ℝ) : ℝ :=
  if |t| < 1 then 1 - |t| else 0

/--
The compactly supported Vaaler multiplier, with its removable value at zero.
-/
noncomputable def beurlingJHat (t : ℝ) : ℝ :=
  if |t| < 1 then
    Real.pi * (1 - |t|) * regularizedFrequencyCot t + |t|
  else 0

@[simp]
theorem beurlingKHat_zero :
    beurlingKHat 0 = 1 := by
  simp [beurlingKHat]

@[simp]
theorem beurlingJHat_zero :
    beurlingJHat 0 = 1 := by
  simp [beurlingJHat]

@[simp]
theorem beurlingKHat_one :
    beurlingKHat 1 = 0 := by
  simp [beurlingKHat]

@[simp]
theorem beurlingJHat_one :
    beurlingJHat 1 = 0 := by
  simp [beurlingJHat]

theorem beurlingKHat_eq_zero_of_one_le_abs
    {t : ℝ} (ht : 1 ≤ |t|) :
    beurlingKHat t = 0 := by
  simp [beurlingKHat, not_lt.mpr ht]

theorem beurlingJHat_eq_zero_of_one_le_abs
    {t : ℝ} (ht : 1 ≤ |t|) :
    beurlingJHat t = 0 := by
  simp [beurlingJHat, not_lt.mpr ht]

theorem regularizedFrequencyCot_neg (t : ℝ) :
    regularizedFrequencyCot (-t) =
      regularizedFrequencyCot t := by
  simp [regularizedFrequencyCot, Real.sinc_neg]

theorem beurlingKHat_neg (t : ℝ) :
    beurlingKHat (-t) = beurlingKHat t := by
  simp [beurlingKHat]

theorem beurlingJHat_neg (t : ℝ) :
    beurlingJHat (-t) = beurlingJHat t := by
  simp [beurlingJHat, regularizedFrequencyCot_neg]

theorem beurlingJHat_of_abs_lt_one
    {t : ℝ} (ht : |t| < 1) :
    beurlingJHat t =
      Real.pi * (1 - |t|) * regularizedFrequencyCot t + |t| := by
  simp [beurlingJHat, ht]

theorem beurlingJHat_of_ne_zero_of_abs_lt_one
    {t : ℝ} (ht0 : t ≠ 0) (ht : |t| < 1) :
    beurlingJHat t =
      Real.pi * t * (1 - |t|) * Real.cot (Real.pi * t) + |t| := by
  rw [beurlingJHat_of_abs_lt_one ht,
    regularizedFrequencyCot_eq_mul_cot ht ht0]
  ring

private theorem mul_realSign_eq_abs (t : ℝ) :
    t * Real.sign t = |t| := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [Real.sign_of_neg ht, abs_of_neg ht]
    ring
  · simp
  · rw [Real.sign_of_pos ht, abs_of_pos ht]
    ring

theorem prawitzKernelReal_eq_half_beurlingKHat (t : ℝ) :
    prawitzKernelReal t = beurlingKHat t / 2 := by
  unfold prawitzKernelReal beurlingKHat
  split_ifs <;> ring

theorem regularizedPrawitzFrequencyKernel_eq_multipliers
    (t : ℝ) :
    regularizedPrawitzFrequencyKernel t =
      ((t * beurlingKHat t / 2 : ℝ) : ℂ) +
        (((beurlingJHat t / (2 * Real.pi) : ℝ) : ℂ) *
          Complex.I) := by
  unfold regularizedPrawitzFrequencyKernel beurlingKHat beurlingJHat
  split_ifs with ht
  · push_cast
    field_simp [Real.pi_ne_zero]
  · simp

theorem prawitzKernelImag_eq_beurlingJHat_div
    {t : ℝ} (ht0 : t ≠ 0) :
    prawitzKernelImag t =
      beurlingJHat t / (2 * Real.pi * t) := by
  by_cases ht : |t| < 1
  · rw [prawitzKernelImag_of_abs_lt_one ht,
      beurlingJHat_of_ne_zero_of_abs_lt_one ht0 ht]
    field_simp [Real.pi_ne_zero, ht0]
    rw [mul_add, mul_realSign_eq_abs]
    ring
  · have habs : 1 ≤ |t| := not_lt.mp ht
    rw [prawitzKernelImag, if_neg ht,
      beurlingJHat_eq_zero_of_one_le_abs habs]
    simp

theorem prawitzKernel_eq_multipliers
    {t : ℝ} (ht0 : t ≠ 0) :
    prawitzKernel t =
      ((beurlingKHat t / 2 : ℝ) : ℂ) +
        (((beurlingJHat t / (2 * Real.pi * t) : ℝ) : ℂ) *
          Complex.I) := by
  rw [prawitzKernel, prawitzKernelReal_eq_half_beurlingKHat,
    prawitzKernelImag_eq_beurlingJHat_div ht0]

end Probability
end CertifiedJL
