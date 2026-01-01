/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Gaussian.GaussianCharacteristic
import CertifiedJL.Probability.Distributions.Gaussian.GaussianLinear

/-! Paired Gaussian identities; analytic consumers import the side they use. -/

open MeasureTheory ProbabilityTheory
namespace CertifiedJL

/-- The paired standard-Gaussian identities used by the paper: imaginary
linearization for a negative square and real linearization for a positive
square.  Both identities include their zero-parameter boundary. -/
theorem combined_gaussian_kernel_identities (s lambda x : ℝ)
    (hs : 0 ≤ s) (hlambda : 0 ≤ lambda) :
    ((Real.exp (-s * x ^ 2) : ℂ) =
      ∫ G : ℝ, Complex.exp
        (Complex.I * (Real.sqrt (2 * s) * G * x : ℝ))
        ∂(gaussianReal 0 1)) ∧
    (Real.exp (lambda * x ^ 2) =
      ∫ G : ℝ, Real.exp (Real.sqrt (2 * lambda) * G * x)
        ∂gaussianReal 0 1) := by
  exact ⟨gaussian_complex_exponential_kernel s x hs,
    (gaussian_exp_linear_kernel hlambda).symm⟩

end CertifiedJL
