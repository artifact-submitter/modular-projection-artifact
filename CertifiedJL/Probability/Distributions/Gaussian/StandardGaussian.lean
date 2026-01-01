/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Gaussian.HalfGaussian
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The standard Gaussian tail

This module fixes a real-valued normalization for the standard Gaussian
density and upper tail.  The sparse one-row proof consumes the real integral
directly, so the elementary analytic bounds live here rather than behind an
`ENNReal` probability coercion.
-/

open MeasureTheory

namespace CertifiedJL
namespace Probability

/-- The density of the standard real Gaussian. -/
noncomputable def standardGaussianDensity (z : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-z ^ 2 / 2)

/-- The standard Gaussian upper tail `P[G > z]`. -/
noncomputable def standardGaussianTail (z : ℝ) : ℝ :=
  ∫ y : ℝ in Set.Ioi z, standardGaussianDensity y

theorem standardGaussianDensity_eq_gaussianPDFReal :
    standardGaussianDensity =
      ProbabilityTheory.gaussianPDFReal 0 1 := by
  funext z
  simp only [standardGaussianDensity,
    ProbabilityTheory.gaussianPDFReal, NNReal.coe_one, sub_zero]
  congr 2 <;> ring_nf

theorem integrable_standardGaussianDensity :
    Integrable standardGaussianDensity := by
  rw [standardGaussianDensity_eq_gaussianPDFReal]
  exact ProbabilityTheory.integrable_gaussianPDFReal 0 1

theorem standardGaussianDensity_nonneg (z : ℝ) :
    0 ≤ standardGaussianDensity z := by
  rw [standardGaussianDensity_eq_gaussianPDFReal]
  exact ProbabilityTheory.gaussianPDFReal_nonneg 0 1 z

theorem standardGaussianDensity_pos (z : ℝ) :
    0 < standardGaussianDensity z := by
  rw [standardGaussianDensity_eq_gaussianPDFReal]
  exact ProbabilityTheory.gaussianPDFReal_pos 0 1 z (by norm_num)

theorem standardGaussianTail_nonneg (z : ℝ) :
    0 ≤ standardGaussianTail z := by
  unfold standardGaussianTail
  exact setIntegral_nonneg measurableSet_Ioi
    (fun y _ => standardGaussianDensity_nonneg y)

theorem standardGaussianTail_le_one (z : ℝ) :
    standardGaussianTail z ≤ 1 := by
  unfold standardGaussianTail
  calc
    (∫ y : ℝ in Set.Ioi z, standardGaussianDensity y) ≤
        ∫ y : ℝ, standardGaussianDensity y := by
      exact setIntegral_le_integral integrable_standardGaussianDensity
        (ae_of_all _ standardGaussianDensity_nonneg)
    _ = 1 := by
      rw [standardGaussianDensity_eq_gaussianPDFReal]
      exact ProbabilityTheory.integral_gaussianPDFReal_eq_one 0
        (by norm_num)

/--
The standard Gaussian Mills inequality in the exact normalization used by
the tilted one-row argument.
-/
theorem standardGaussianTail_le_mills {z : ℝ} (hz : 0 < z) :
    standardGaussianTail z ≤
      Real.exp (-z ^ 2 / 2) /
        (Real.sqrt (2 * Real.pi) * z) := by
  unfold standardGaussianTail standardGaussianDensity
  rw [MeasureTheory.integral_const_mul]
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ *
        ∫ y : ℝ in Set.Ioi z, Real.exp (-y ^ 2 / 2) ≤
      (Real.sqrt (2 * Real.pi))⁻¹ *
        (Real.exp (-(1 / 2 : ℝ) * z ^ 2) /
          (2 * (1 / 2 : ℝ) * z)) := by
      gcongr
      have h := integral_Ioi_exp_neg_mul_sq_le
        (c := (1 / 2 : ℝ)) (b := z) (by norm_num) hz
      calc
        (∫ y : ℝ in Set.Ioi z, Real.exp (-y ^ 2 / 2)) =
            ∫ y : ℝ in Set.Ioi z,
              Real.exp (-(1 / 2 : ℝ) * y ^ 2) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro y _
          exact congrArg Real.exp (by ring)
        _ ≤ Real.exp (-(1 / 2 : ℝ) * z ^ 2) /
            (2 * (1 / 2 : ℝ) * z) := h
    _ = Real.exp (-z ^ 2 / 2) /
        (Real.sqrt (2 * Real.pi) * z) := by
      ring_nf

end Probability
end CertifiedJL
