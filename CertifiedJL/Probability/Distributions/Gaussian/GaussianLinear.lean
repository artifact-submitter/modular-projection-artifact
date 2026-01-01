/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib.Probability.Distributions.Gaussian.Real

/-! Positive quadratic-exponential linearization by a standard Gaussian. -/

open MeasureTheory ProbabilityTheory
namespace CertifiedJL

/-- Positive Gaussian linearization of one quadratic exponential. -/
theorem gaussian_exp_linear_kernel {lambda z : ℝ} (hlambda : 0 ≤ lambda) :
    (∫ G : ℝ, Real.exp (Real.sqrt (2 * lambda) * G * z)
        ∂gaussianReal 0 1) =
      Real.exp (lambda * z ^ 2) := by
  have hmgf := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1))
    (Real.sqrt (2 * lambda) * z)
  change (∫ G : ℝ, Real.exp ((Real.sqrt (2 * lambda) * z) * G)
      ∂gaussianReal 0 1) =
    Real.exp (0 * (Real.sqrt (2 * lambda) * z) +
      (1 : ℝ) * (Real.sqrt (2 * lambda) * z) ^ 2 / 2) at hmgf
  calc
    (∫ G : ℝ, Real.exp (Real.sqrt (2 * lambda) * G * z)
        ∂gaussianReal 0 1) =
      ∫ G : ℝ, Real.exp ((Real.sqrt (2 * lambda) * z) * G)
        ∂gaussianReal 0 1 := by
          apply integral_congr_ae
          filter_upwards [] with G
          congr 1
          ring
    _ = Real.exp ((Real.sqrt (2 * lambda) * z) ^ 2 / 2) := by
      simpa using hmgf
    _ = Real.exp (lambda * z ^ 2) := by
      congr 1
      rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) hlambda)]
      ring

end CertifiedJL
