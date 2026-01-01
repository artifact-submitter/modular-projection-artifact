/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Gaussian.ShiftedGaussianInversion
import Lean.Util.CollectAxioms

/-! Mutation canaries for the exact U10 smoothing boundary. -/

namespace CertifiedJL.Tests.ShiftedGaussianInversion

open MeasureTheory ProbabilityTheory

/-- Exact sign and scale canary for the contour envelope. -/
example (lambda sigma y u : ℝ) :
    ‖shiftedGaussianContourKernel lambda sigma y u‖ =
      Real.exp
          (lambda * y + sigma ^ 2 * (lambda ^ 2 - u ^ 2) / 2) /
        Real.sqrt (lambda ^ 2 + u ^ 2) :=
  norm_shiftedGaussianContourKernel lambda sigma y u

/-- Absolute-convergence canary used before any limiting operation. -/
example {lambda sigma y : ℝ}
    (hlambda : 0 < lambda) (hsigma : 0 < sigma) :
    Integrable (shiftedGaussianContourKernel lambda sigma y) :=
  integrable_shiftedGaussianContourKernel hlambda hsigma

/-- Limiting canary for decay along the positive end of the contour. -/
example {lambda sigma y : ℝ}
    (hlambda : 0 < lambda) (hsigma : 0 < sigma) :
    Filter.Tendsto
      (fun u : ℝ => ‖shiftedGaussianContourKernel lambda sigma y u‖)
      Filter.atTop (nhds 0) :=
  tendsto_norm_shiftedGaussianContourKernel_atTop hlambda hsigma

/-- Direct asymmetric sign canary: the shifted argument is negative. -/
example :
    (1 / (2 * Real.pi) : ℂ) *
        ∫ u : ℝ, shiftedGaussianContourKernel 2 3 (-5) u =
      (standardGaussianCDF ((-5 : ℝ) / 3) : ℂ) := by
  simpa using integral_shiftedGaussianContourKernel_eq_cdf
    (lambda := (2 : ℝ)) (sigma := (3 : ℝ)) (y := (-5 : ℝ))
    (by norm_num) (by norm_num)

/-- Scale canary: choosing `y = sigma * z` leaves the standardized argument
exactly `z`. -/
example {lambda sigma z : ℝ}
    (hlambda : 0 < lambda) (hsigma : 0 < sigma) :
    (1 / (2 * Real.pi) : ℂ) *
        ∫ u : ℝ,
          shiftedGaussianContourKernel lambda sigma (sigma * z) u =
      (standardGaussianCDF z : ℂ) := by
  simpa [hsigma.ne'] using integral_shiftedGaussianContourKernel_eq_cdf
    (lambda := lambda) (sigma := sigma) (y := sigma * z) hlambda hsigma

/-- Direct consumer of the final normalized U10 contour surface. -/
example {lambda sigma theta t x : ℝ}
    (hlambda : 0 < lambda) (hsigma : 0 < sigma) :
    (shiftedGaussianSmoothing sigma theta t x : ℂ) =
      (1 / (2 * Real.pi * standardGaussianCDF theta) : ℂ) *
        ∫ u : ℝ,
          shiftedGaussianContourKernel lambda sigma
            (x - t + theta * sigma) u :=
  shiftedGaussianSmoothing_eq_contourIntegral hlambda hsigma

example (t : ℝ) : strictUpperIndicator t t = 0 := by
  simp [strictUpperIndicator]

example {sigma theta t : ℝ} (hsigma : sigma ≠ 0)
    (hCDFPos : 0 < standardGaussianCDF theta) :
    shiftedGaussianSmoothing sigma theta t t = 1 :=
  shiftedGaussianSmoothing_at_threshold hsigma hCDFPos

/-- A direct asymmetric consumer of the expectation-level U10 boundary. -/
example {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (X : Omega → ℝ) (hX : Measurable X)
    {sigma theta t : ℝ} (hsigma : 0 < sigma)
    (hsmooth : Integrable
      (fun omega => shiftedGaussianSmoothing sigma theta t (X omega)) mu) :
    mu.real (X ⁻¹' Set.Ioi t) ≤
      ∫ omega, shiftedGaussianSmoothing sigma theta t (X omega) ∂mu :=
  measureReal_strictUpper_preimage_le_integral_shiftedGaussianSmoothing
    mu hX hsigma hsmooth

example {Omega : Type*} [MeasurableSpace Omega]
    (Z : Omega → ℝ) (mu : Measure Omega) (lambda u : ℝ) :
    ‖quadraticComplexMGF Z mu (lambda + u * Complex.I)‖ ≤
      mgf (fun omega => (Z omega) ^ 2) mu lambda := by
  simpa using norm_quadraticComplexMGF_le_real Z mu (lambda + u * Complex.I)

run_cmd
  let allowed : Array Lean.Name :=
    #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Lean.Name :=
    #[``CertifiedJL.norm_shiftedGaussianContourKernel,
      ``CertifiedJL.integrable_shiftedGaussianContourKernel,
      ``CertifiedJL.tendsto_norm_shiftedGaussianContourKernel_atTop,
      ``CertifiedJL.integral_shiftedGaussianContourKernel_eq_cdf,
      ``CertifiedJL.shiftedGaussianSmoothing_eq_contourIntegral,
      ``CertifiedJL.strictMono_standardGaussianCDF,
      ``CertifiedJL.strictUpperIndicator_lt_shiftedGaussianSmoothing,
      ``CertifiedJL.measureReal_strictUpper_preimage_le_integral_shiftedGaussianSmoothing,
      ``CertifiedJL.norm_quadraticComplexMGF_pow_le]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    unless axioms.size == allowed.size &&
        axioms.all allowed.contains && allowed.all axioms.contains do
      throwError "unexpected axioms for {target}: {axioms}"

end CertifiedJL.Tests.ShiftedGaussianInversion
