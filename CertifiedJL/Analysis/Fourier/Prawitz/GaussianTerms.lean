/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Fourier.Prawitz.Smoothing
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Explicit Gaussian terms in the Prawitz decomposition

This file evaluates the reference characteristic function and the principal
CDF kernel appearing in the four-term Prawitz decomposition.  It also gives
a rational pointwise envelope for the Gaussian reference tail.  These are
analytic inputs, not moment-reduction assumptions.
-/

open MeasureTheory ProbabilityTheory

namespace CertifiedJL
namespace Probability

/-- Characteristic function of the standard Gaussian. -/
theorem charFun_standardGaussian (t : ℝ) :
    charFun (gaussianReal 0 1) t =
      ((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ) := by
  rw [charFun_gaussianReal]
  change
    Complex.exp
      ((t : ℂ) * (0 : ℂ) * Complex.I -
        (1 : ℂ) * (t : ℂ) ^ 2 / 2) =
      ((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ)
  have harg :
      (t : ℂ) * (0 : ℂ) * Complex.I -
          (1 : ℂ) * (t : ℂ) ^ 2 / 2 =
        ((-(t ^ 2) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, Complex.ofReal_exp]

/-- Norm of the standard Gaussian characteristic function. -/
theorem norm_charFun_standardGaussian (t : ℝ) :
    ‖charFun (gaussianReal 0 1) t‖ = Real.exp (-(t ^ 2) / 2) := by
  rw [charFun_standardGaussian, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

/-- Exact norm of the principal CDF kernel, including its totalized value at zero. -/
theorem norm_principalCDFKernel (t : ℝ) :
    ‖principalCDFKernel t‖ = 1 / (2 * Real.pi * |t|) := by
  unfold principalCDFKernel
  rw [norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_pos Real.pi_pos]

/-- Exact standard-Gaussian specialization of the reference tail integrand. -/
theorem prawitzReferenceTailTerm_standardGaussian
    (U₀ u : ℝ) :
    prawitzReferenceTailTerm (gaussianReal 0 1) U₀ u =
      if U₀ < |u| then
        Real.exp (-(u ^ 2) / 2) / (2 * Real.pi * |u|)
      else 0 := by
  unfold prawitzReferenceTailTerm
  split_ifs with h
  · rw [norm_principalCDFKernel, norm_charFun_standardGaussian]
    ring
  · rfl

/--
On the reference-tail region, replace the singular factor `1/|u|` by
`|u|/U₀²`.  This is the pointwise step behind the elementary closed-form
Gaussian tail estimate.
-/
theorem prawitzReferenceTailTerm_standardGaussian_le
    {U₀ u : ℝ} (hU₀ : 0 < U₀) :
    prawitzReferenceTailTerm (gaussianReal 0 1) U₀ u ≤
      if U₀ < |u| then
        Real.exp (-(u ^ 2) / 2) * |u| /
          (2 * Real.pi * U₀ ^ 2)
      else 0 := by
  rw [prawitzReferenceTailTerm_standardGaussian]
  split_ifs with hu
  · have hu0 : 0 < |u| := hU₀.trans hu
    have hsq : U₀ ^ 2 ≤ |u| ^ 2 := by
      nlinarith [sq_nonneg (|u| - U₀)]
    have hreciprocal :
        1 / |u| ≤ |u| / U₀ ^ 2 := by
      rw [div_le_div_iff₀ hu0 (sq_pos_of_pos hU₀)]
      nlinarith
    have hexp : 0 ≤ Real.exp (-(u ^ 2) / 2) := (Real.exp_pos _).le
    have hden : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
    calc
      Real.exp (-(u ^ 2) / 2) / (2 * Real.pi * |u|)
          = (Real.exp (-(u ^ 2) / 2) / (2 * Real.pi)) *
              (1 / |u|) := by field_simp
      _ ≤ (Real.exp (-(u ^ 2) / 2) / (2 * Real.pi)) *
              (|u| / U₀ ^ 2) :=
        mul_le_mul_of_nonneg_left hreciprocal
          (div_nonneg hexp hden.le)
      _ = Real.exp (-(u ^ 2) / 2) * |u| /
          (2 * Real.pi * U₀ ^ 2) := by field_simp
  · exact le_rfl

end Probability
end CertifiedJL
