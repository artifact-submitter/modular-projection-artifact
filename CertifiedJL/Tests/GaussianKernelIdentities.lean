import CertifiedJL.Analysis.Gaussian.GaussianCosine
import CertifiedJL.Analysis.Gaussian.GaussianMillsStrict

open MeasureTheory ProbabilityTheory

namespace CertifiedJL.Tests.GaussianKernelIdentities

#check gaussian_complex_exponential_kernel
#check gaussian_exp_linear_kernel
#check combined_gaussian_kernel_identities

/-- The paper-facing theorem includes the zero-parameter boundary exactly. -/
example (x : ℝ) :
    ((Real.exp (-(0 : ℝ) * x ^ 2) : ℂ) =
      ∫ G : ℝ, Complex.exp
        (Complex.I * (Real.sqrt (2 * (0 : ℝ)) * G * x : ℝ))
        ∂(gaussianReal 0 1)) ∧
    (Real.exp ((0 : ℝ) * x ^ 2) =
      ∫ G : ℝ, Real.exp (Real.sqrt (2 * (0 : ℝ)) * G * x)
        ∂gaussianReal 0 1) := by
  exact combined_gaussian_kernel_identities 0 0 x (by positivity) (by positivity)

#print axioms CertifiedJL.Probability.standardGaussianTail_lt_mills
#print axioms gaussian_complex_exponential_kernel
#print axioms gaussian_exp_linear_kernel
#print axioms combined_gaussian_kernel_identities

end CertifiedJL.Tests.GaussianKernelIdentities
