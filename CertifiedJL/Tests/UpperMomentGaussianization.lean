/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Peano.PeanoQuadraticExpSecond
import Lean.Util.CollectAxioms

/-!
# Mutation canaries for mass-parametric upper-tail Gaussianization
-/

open Lean MeasureTheory ProbabilityTheory

namespace CertifiedJL.Tests.UpperMomentGaussianization

/- The product map reads `W` from the first coordinate and `t` from the
second, including at a negative scale. -/
example : (fun p : ℝ × ℝ => p.1 + (-1) * p.2) (2, 3) = -1 := by norm_num

example (ρ τ : Measure ℝ) :
    independentAffineSumMeasure ρ τ (-1) =
      Measure.map (fun p : ℝ × ℝ => p.1 + (-1) * p.2) (ρ.prod τ) := rfl

/- Independent addition preserves the stop-loss mass parameter `gamma`; it
does not silently normalize the positive measure to mass one. -/
example {ρ μ ν : Measure ℝ} {varianceW : NNReal} {gamma : ℝ}
    (hW : GaussianEvenMomentDomination ρ 1 varianceW)
    (hΔ : PositiveStopLossMomentDomination μ ν gamma) (c : ℝ) :
    GaussianEvenMomentDomination
      (independentAffineSumMeasure ρ
        (positiveDensityMeasure (firstStopLossDifference μ ν)) c)
      gamma (varianceW + scaledVariance c 1) :=
  hΔ.independentAffineSum hW c

/- The variance arithmetic is additive and includes exactly `c²`. -/
example : (4 : NNReal)⁻¹ + scaledVariance (1 / 2 : ℝ) 1 = (2 : NNReal)⁻¹ := by
  ext
  norm_num [scaledVariance]

/- Symmetry supplies direct odd cancellation. -/
example {μ : Measure ℝ} {mass : ℝ} {variance : NNReal}
    (h : GaussianEvenMomentDomination μ mass variance) :
    (∫ x : ℝ, x ^ 7 ∂μ) = 0 := by
  simpa using h.integral_odd_eq_zero 3

/- Variance weakening runs from the smaller reference variance to the larger
one, never in the reverse direction. -/
example {μ : Measure ℝ} {mass : ℝ}
    (h : GaussianEvenMomentDomination μ mass (4 : NNReal)⁻¹) :
    GaussianEvenMomentDomination μ mass (2 : NNReal)⁻¹ := by
  apply h.variance_mono
  exact inv_anti₀ (by norm_num : (0 : NNReal) < 2) (by norm_num : (2 : NNReal) ≤ 4)

/- The mass-parametric D6 theorem includes the zero-real-tilt boundary. -/
example {μ : Measure ℝ} {mass : ℝ} {variance : NNReal}
    (h : GaussianEvenMomentDomination μ mass variance)
    (hvariance : variance ≤ (2 : NNReal)⁻¹) :
    (∫ x : ℝ, ‖iteratedDeriv 6 (complexQuadraticExp Complex.I) x‖ ∂μ) ≤
      mass * quadraticExpDerivativeMajorant 6 ‖Complex.I‖ 0 := by
  simpa using
    integral_norm_six_le_of_gaussianEvenMomentDomination
      h hvariance Complex.I (by norm_num) (by norm_num)

/- The public stop-loss theorem exposes the nested integral and the complete
variance premise that lane A's concrete K law will instantiate. -/
example {ρ μ ν : Measure ℝ} {varianceW : NNReal} {gamma : ℝ}
    (hW : GaussianEvenMomentDomination ρ 1 varianceW)
    (hΔ : PositiveStopLossMomentDomination μ ν gamma) (c : ℝ)
    (hvariance : varianceW + scaledVariance c 1 ≤ (2 : NNReal)⁻¹) :
    ‖∫ w, ∫ t, firstStopLossDifference μ ν t •
        iteratedDeriv 6 (complexQuadraticExp Complex.I) (w + c * t) ∂volume ∂ρ‖ ≤
      gamma * quadraticExpDerivativeMajorant 6 ‖Complex.I‖ 0 := by
  simpa using
    norm_integral_integral_firstStopLossDifference_iteratedDeriv_six_le
      hW hΔ c hvariance Complex.I (by norm_num) (by norm_num)

#print axioms GaussianEvenMomentDomination.integral_odd_eq_zero
#print axioms GaussianEvenMomentDomination.map_const_mul
#print axioms GaussianEvenMomentDomination.independentAffineSum
#print axioms GaussianEvenMomentDomination.variance_mono
#print axioms tiltedEvenMoment_le_of_gaussianEvenMomentDomination
#print axioms integral_norm_six_le_of_gaussianEvenMomentDomination
#print axioms PositiveStopLossMomentDomination.independentAffineSum
#print axioms norm_integral_integral_firstStopLossDifference_iteratedDeriv_six_le
#print axioms norm_partialSum_secondPeanoDifference_le_of_gaussianization
#print axioms norm_partialSum_secondPeanoDifference_le_of_positiveStopLossMomentDomination

run_cmd
  let allowed : Array Name :=
    #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Name :=
    #[``CertifiedJL.GaussianEvenMomentDomination.integral_odd_eq_zero,
      ``CertifiedJL.GaussianEvenMomentDomination.map_const_mul,
      ``CertifiedJL.GaussianEvenMomentDomination.independentAffineSum,
      ``CertifiedJL.GaussianEvenMomentDomination.variance_mono,
      ``CertifiedJL.tiltedEvenMoment_le_of_gaussianEvenMomentDomination,
      ``CertifiedJL.integral_norm_six_le_of_gaussianEvenMomentDomination,
      ``CertifiedJL.PositiveStopLossMomentDomination.independentAffineSum,
      ``CertifiedJL.norm_integral_integral_firstStopLossDifference_iteratedDeriv_six_le,
      ``CertifiedJL.norm_partialSum_secondPeanoDifference_le_of_gaussianization,
      ``CertifiedJL.norm_partialSum_secondPeanoDifference_le_of_positiveStopLossMomentDomination]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    unless axioms.size == allowed.size &&
        axioms.all allowed.contains && allowed.all axioms.contains do
      throwError "unexpected axioms for {target}: {axioms}"

end CertifiedJL.Tests.UpperMomentGaussianization
