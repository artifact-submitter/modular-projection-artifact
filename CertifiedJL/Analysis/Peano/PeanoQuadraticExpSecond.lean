/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Peano.PeanoCutoffProduct
import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpDerivative
import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpMomentComparison
import CertifiedJL.Analysis.Peano.PositiveStopLossGaussianization

/-!
# Second Peano replacement for the fourth quadratic-exponential derivative

This module specializes the audited second-order cutoff boundary to the U3b
function `f_s⁽⁴⁾`.  The conclusion exposes the sixth derivative exactly as in
the paper and includes the fixed-shift `c²` scaling.  Integration over the
independent partial sum and the mixed-even-moment/`D₆` domination remain
downstream obligations.
-/

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace CertifiedJL

/-- The fourth real derivative of the quadratic exponential is `C²`, as
required by the second-order Peano replacement. -/
theorem contDiff_two_iteratedDeriv_four_complexQuadraticExp (s : ℂ) :
    ContDiff ℝ 2 (iteratedDeriv 4 (complexQuadraticExp s)) := by
  have hfun : iteratedDeriv 4 (complexQuadraticExp s) =
      fun y : ℝ => complexQuadraticExpFourthPolynomialComplex s (y : ℂ) *
        complexQuadraticExp s y := by
    funext y
    exact iteratedDeriv_four_complexQuadraticExp s y
  rw [hfun]
  have hpoly : ContDiff ℝ 2
      (fun y : ℝ => complexQuadraticExpFourthPolynomialComplex s (y : ℂ)) := by
    simp only [complexQuadraticExpFourthPolynomialComplex]
    have hy : ContDiff ℝ 2 (fun y : ℝ => (y : ℂ)) :=
      Complex.ofRealCLM.contDiff.of_le (show (2 : ℕ∞ω) ≤ ω by simp)
    exact (contDiff_const.add (contDiff_const.mul (hy.pow 2))).add
      (contDiff_const.mul (hy.pow 4))
  exact hpoly.mul ((contDiff_complexQuadraticExp s).of_le (by norm_num))

/-- Scaling and translating the fourth derivative produces the exact `c²`
factor and sixth derivative used in U3b. -/
theorem iteratedDeriv_two_scaled_iteratedDeriv_four_complexQuadraticExp
    (s : ℂ) (w c z : ℝ) :
    iteratedDeriv 2
        (fun y : ℝ => iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)) z =
      c ^ 2 • iteratedDeriv 6 (complexQuadraticExp s) (w + c * z) := by
  let F : ℝ → ℂ := iteratedDeriv 4 (complexQuadraticExp s)
  have hF : ContDiff ℝ 2 F :=
    contDiff_two_iteratedDeriv_four_complexQuadraticExp s
  have hshift : ContDiff ℝ 2 (fun u : ℝ => F (w + u)) :=
    hF.comp (by fun_prop)
  have hscale := congrFun (iteratedDeriv_comp_const_smul hshift c) z
  have htranslate := congrFun (iteratedDeriv_comp_const_add 2 F w) (c * z)
  have h26 : iteratedDeriv 2 (iteratedDeriv 4 (complexQuadraticExp s)) =
      iteratedDeriv 6 (complexQuadraticExp s) := by
    rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
      iteratedDeriv_eq_iterate]
    rw [← Function.iterate_add_apply]
  simpa only [F, htranslate, h26] using hscale

/-- The noncompact second Peano identity for `f_s⁽⁴⁾`, obtained from the
translated cutoff products and one explicit index-independent majorant. -/
theorem peanoIdentity2_iteratedDeriv_four_complexQuadraticExp
    {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]
    (s : ℂ) (x : ℝ)
    (hμf : Integrable
      (fun y => iteratedDeriv 4 (complexQuadraticExp s) (x + y)) μ)
    (hνf : Integrable
      (fun y => iteratedDeriv 4 (complexQuadraticExp s) (x + y)) ν)
    (hμKernel : ∀ n, Integrable
      (Function.uncurry (fun t y => max (y - t) 0 •
        iteratedDeriv 2
          (upperCutoffProduct n (iteratedDeriv 4 (complexQuadraticExp s)) x)
          (x + t))) (volume.prod μ))
    (hνKernel : ∀ n, Integrable
      (Function.uncurry (fun t y => max (y - t) 0 •
        iteratedDeriv 2
          (upperCutoffProduct n (iteratedDeriv 4 (complexQuadraticExp s)) x)
          (x + t))) (volume.prod ν))
    (hμRhs : ∀ n, Integrable (fun t =>
      (∫ y, max (y - t) 0 ∂μ) •
        iteratedDeriv 2
          (upperCutoffProduct n (iteratedDeriv 4 (complexQuadraticExp s)) x)
          (x + t)))
    (hνRhs : ∀ n, Integrable (fun t =>
      (∫ y, max (y - t) 0 ∂ν) •
        iteratedDeriv 2
          (upperCutoffProduct n (iteratedDeriv 4 (complexQuadraticExp s)) x)
          (x + t)))
    (hΔ : StronglyMeasurable (firstStopLossDifference μ ν))
    (bound : ℝ → ℝ) (hboundInt : Integrable bound)
    (hbound : ∀ n t,
      ‖firstStopLossDifference μ ν t •
        iteratedDeriv 2
          (upperCutoffProduct n (iteratedDeriv 4 (complexQuadraticExp s)) x)
          (x + t)‖ ≤ bound t) :
    (∫ y, iteratedDeriv 4 (complexQuadraticExp s) (x + y) ∂μ) -
        ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (x + y) ∂ν =
      ∫ t, firstStopLossDifference μ ν t •
        iteratedDeriv 6 (complexQuadraticExp s) (x + t) := by
  have hf4 := contDiff_two_iteratedDeriv_four_complexQuadraticExp s
  have hidentity := peanoIdentity2_of_upperCutoffProduct
    hf4 x hμf hνf hμKernel hνKernel hμRhs hνRhs hΔ bound hboundInt hbound
  have h26 : iteratedDeriv 2 (iteratedDeriv 4 (complexQuadraticExp s)) =
      iteratedDeriv 6 (complexQuadraticExp s) := by
    rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
      iteratedDeriv_eq_iterate]
    rw [← Function.iterate_add_apply]
  simpa only [h26] using hidentity

/-- The scaled fixed-shift form of the second Peano replacement.  It is the
exact identity at the start of the U3b proof, before integrating over the
independent partial sum and applying the mixed-even-moment majorant. -/
theorem peanoIdentity2_scaled_iteratedDeriv_four_complexQuadraticExp
    {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]
    (s : ℂ) (w c : ℝ)
    (hμf : Integrable
      (fun y => iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)) μ)
    (hνf : Integrable
      (fun y => iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)) ν)
    (hμKernel : ∀ n, Integrable
      (Function.uncurry (fun t y => max (y - t) 0 • iteratedDeriv 2
        (upperCutoffProduct n
          (fun z => iteratedDeriv 4 (complexQuadraticExp s) (w + c * z)) 0) t))
        (volume.prod μ))
    (hνKernel : ∀ n, Integrable
      (Function.uncurry (fun t y => max (y - t) 0 • iteratedDeriv 2
        (upperCutoffProduct n
          (fun z => iteratedDeriv 4 (complexQuadraticExp s) (w + c * z)) 0) t))
        (volume.prod ν))
    (hμRhs : ∀ n, Integrable (fun t =>
      (∫ y, max (y - t) 0 ∂μ) • iteratedDeriv 2
        (upperCutoffProduct n
          (fun z => iteratedDeriv 4 (complexQuadraticExp s) (w + c * z)) 0) t))
    (hνRhs : ∀ n, Integrable (fun t =>
      (∫ y, max (y - t) 0 ∂ν) • iteratedDeriv 2
        (upperCutoffProduct n
          (fun z => iteratedDeriv 4 (complexQuadraticExp s) (w + c * z)) 0) t))
    (hΔ : StronglyMeasurable (firstStopLossDifference μ ν))
    (bound : ℝ → ℝ) (hboundInt : Integrable bound)
    (hbound : ∀ n t,
      ‖firstStopLossDifference μ ν t • iteratedDeriv 2
        (upperCutoffProduct n
          (fun z => iteratedDeriv 4 (complexQuadraticExp s) (w + c * z)) 0) t‖ ≤
        bound t) :
    (∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y) ∂μ) -
        ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y) ∂ν =
      ∫ t, firstStopLossDifference μ ν t •
        (c ^ 2 • iteratedDeriv 6 (complexQuadraticExp s) (w + c * t)) := by
  have hf : ContDiff ℝ 2
      (fun z : ℝ => iteratedDeriv 4 (complexQuadraticExp s) (w + c * z)) :=
    (contDiff_two_iteratedDeriv_four_complexQuadraticExp s).comp (by fun_prop)
  have hidentity := peanoIdentity2_of_upperCutoffProduct
    hf 0
    (by simpa only [zero_add] using hμf)
    (by simpa only [zero_add] using hνf)
    (fun n => by simpa only [zero_add] using hμKernel n)
    (fun n => by simpa only [zero_add] using hνKernel n)
    (fun n => by simpa only [zero_add] using hμRhs n)
    (fun n => by simpa only [zero_add] using hνRhs n)
    hΔ bound hboundInt
    (fun n t => by simpa only [zero_add] using hbound n t)
  simpa only [zero_add,
    iteratedDeriv_two_scaled_iteratedDeriv_four_complexQuadraticExp] using hidentity

/-- Integrating the fixed-shift second Peano identity over an independent
partial-sum law gives the exact nested-expectation identity used in U3b.

The pointwise premise is supplied by
`peanoIdentity2_scaled_iteratedDeriv_four_complexQuadraticExp`; keeping it as
a premise prevents this lifting theorem from duplicating that producer's
cutoff and integrability interface. -/
theorem peanoIdentity2_partialSum_scaled_iteratedDeriv_four_complexQuadraticExp
    {ρ μ ν : Measure ℝ}
    (s : ℂ) (c : ℝ)
    (hμ : Integrable (fun w =>
      ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y) ∂μ) ρ)
    (hν : Integrable (fun w =>
      ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y) ∂ν) ρ)
    (hfixed : ∀ w,
      (∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y) ∂μ) -
          ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y) ∂ν =
        ∫ t, firstStopLossDifference μ ν t •
          (c ^ 2 • iteratedDeriv 6 (complexQuadraticExp s) (w + c * t))) :
    (∫ w, ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y) ∂μ ∂ρ) -
        ∫ w, ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y) ∂ν ∂ρ =
      c ^ 2 • ∫ w, ∫ t, firstStopLossDifference μ ν t •
        iteratedDeriv 6 (complexQuadraticExp s) (w + c * t) ∂volume ∂ρ := by
  rw [← integral_sub hμ hν]
  calc
    _ = ∫ w, ∫ t, firstStopLossDifference μ ν t •
          (c ^ 2 • iteratedDeriv 6 (complexQuadraticExp s) (w + c * t))
          ∂volume ∂ρ := by
      apply integral_congr_ae
      exact ae_of_all ρ hfixed
    _ = _ := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with w
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [smul_smul]
      congr 1
      ring

/-- The exact U3b conclusion from the paper-faithful `gamma * D6`
Gaussianization boundary. -/
theorem norm_partialSum_secondPeanoDifference_le_of_gaussianization
    {ρ μ ν : Measure ℝ}
    (s : ℂ) (c gamma : ℝ)
    (hlifted :
      (∫ w, ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y) ∂μ ∂ρ) -
          ∫ w, ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y) ∂ν ∂ρ =
        c ^ 2 • ∫ w, ∫ t, firstStopLossDifference μ ν t •
          iteratedDeriv 6 (complexQuadraticExp s) (w + c * t) ∂volume ∂ρ)
    (hgaussianize :
      ‖∫ w, ∫ t, firstStopLossDifference μ ν t •
          iteratedDeriv 6 (complexQuadraticExp s) (w + c * t) ∂volume ∂ρ‖ ≤
        gamma * quadraticExpDerivativeMajorant 6 ‖s‖ s.re) :
    ‖(∫ w, ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y) ∂μ ∂ρ) -
        ∫ w, ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y) ∂ν ∂ρ‖ ≤
      gamma * c ^ 2 * quadraticExpDerivativeMajorant 6 ‖s‖ s.re := by
  rw [hlifted, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg c)]
  calc
    c ^ 2 * ‖∫ w, ∫ t, firstStopLossDifference μ ν t •
          iteratedDeriv 6 (complexQuadraticExp s) (w + c * t) ∂volume ∂ρ‖ ≤
        c ^ 2 * (gamma * quadraticExpDerivativeMajorant 6 ‖s‖ s.re) :=
      mul_le_mul_of_nonneg_left hgaussianize (sq_nonneg c)
    _ = _ := by ring

/-- The exact U3b `γ c² D₆` conclusion after the independent-partial-sum
identity, conditional on the remaining Gaussianization inequality.

The `hgaussianize` premise is the honest boundary for the paper's stop-loss
positivity/U3a and mixed-even-moment argument.  Once it is supplied, raw
even-moment domination by the variance-one-half Gaussian gives the exact
`D₆` bound through the existing nonnegative-series comparison. -/
theorem norm_partialSum_secondPeanoDifference_le_of_evenMomentDomination
    {ρ μ ν κ : Measure ℝ}
    (s : ℂ) (c gamma : ℝ)
    (hlifted :
      (∫ w, ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y) ∂μ ∂ρ) -
          ∫ w, ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y) ∂ν ∂ρ =
        c ^ 2 • ∫ w, ∫ t, firstStopLossDifference μ ν t •
          iteratedDeriv 6 (complexQuadraticExp s) (w + c * t) ∂volume ∂ρ)
    (hκ : GaussianHalfEvenMomentDomination κ)
    (hs_nonneg : 0 ≤ s.re) (hs_lt_one : s.re < 1)
    (hgamma : 0 ≤ gamma)
    (hgaussianize :
      ‖∫ w, ∫ t, firstStopLossDifference μ ν t •
          iteratedDeriv 6 (complexQuadraticExp s) (w + c * t) ∂volume ∂ρ‖ ≤
        gamma * ∫ x, ‖iteratedDeriv 6 (complexQuadraticExp s) x‖ ∂κ) :
    ‖(∫ w, ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y) ∂μ ∂ρ) -
        ∫ w, ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y) ∂ν ∂ρ‖ ≤
      gamma * c ^ 2 * quadraticExpDerivativeMajorant 6 ‖s‖ s.re := by
  rw [hlifted, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg c)]
  have hD6 :=
    integral_norm_iteratedDeriv_six_complexQuadraticExp_le_of_evenMomentDomination
      hκ s hs_nonneg hs_lt_one
  calc
    c ^ 2 * ‖∫ w, ∫ t, firstStopLossDifference μ ν t •
          iteratedDeriv 6 (complexQuadraticExp s) (w + c * t) ∂volume ∂ρ‖ ≤
        c ^ 2 * (gamma * ∫ x,
          ‖iteratedDeriv 6 (complexQuadraticExp s) x‖ ∂κ) :=
      mul_le_mul_of_nonneg_left hgaussianize (sq_nonneg c)
    _ ≤ c ^ 2 * (gamma * quadraticExpDerivativeMajorant 6 ‖s‖ s.re) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hD6 hgamma) (sq_nonneg c)
    _ = _ := by ring

/-- The complete general U3b bridge for a positive stop-loss law.  The
moment assumptions discharge the Gaussianization premise of
`norm_partialSum_secondPeanoDifference_le_of_gaussianization`. -/
theorem norm_partialSum_secondPeanoDifference_le_of_positiveStopLossMomentDomination
    {ρ μ ν : Measure ℝ} {varianceW : NNReal}
    (s : ℂ) (c gamma : ℝ)
    (hlifted :
      (∫ w, ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y) ∂μ ∂ρ) -
          ∫ w, ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y) ∂ν ∂ρ =
        c ^ 2 • ∫ w, ∫ t, firstStopLossDifference μ ν t •
          iteratedDeriv 6 (complexQuadraticExp s) (w + c * t) ∂volume ∂ρ)
    (hW : GaussianEvenMomentDomination ρ 1 varianceW)
    (hΔ : PositiveStopLossMomentDomination μ ν gamma)
    (hvariance : varianceW + scaledVariance c 1 ≤ (2 : NNReal)⁻¹)
    (hs_nonneg : 0 ≤ s.re) (hs_lt_one : s.re < 1) :
    ‖(∫ w, ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y) ∂μ ∂ρ) -
        ∫ w, ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y) ∂ν ∂ρ‖ ≤
      gamma * c ^ 2 * quadraticExpDerivativeMajorant 6 ‖s‖ s.re := by
  apply norm_partialSum_secondPeanoDifference_le_of_gaussianization
    s c gamma hlifted
  exact norm_integral_integral_firstStopLossDifference_iteratedDeriv_six_le
    hW hΔ c hvariance s hs_nonneg hs_lt_one

end CertifiedJL
