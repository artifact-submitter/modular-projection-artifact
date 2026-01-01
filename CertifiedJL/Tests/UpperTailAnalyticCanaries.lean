/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperFourthOrder
import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperPeano
import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpGaussianHalfIntegral
import CertifiedJL.Tests.ShiftedGaussianInversion
import CertifiedJL.Tests.UpperMomentGaussianization
import Lean.Util.CollectAxioms

/-!
# Upper-tail analytic canaries

This module holds analytic upper-tail tests separately from the public
normalization canaries. Importing `CertifiedJL.Tests.UpperTailCanaries`
still runs these tests transitively.
-/

open Filter Lean MeasureTheory ProbabilityTheory
open scoped ContDiff NNReal Topology

namespace CertifiedJL.Tests.UpperTailAnalyticCanaries

example (s : ℂ) : ContDiff ℝ ω (complexQuadraticExp s) :=
  contDiff_omega_complexQuadraticExp s

/- A nonreal parameter directly pins the exact principal-power Gaussian
reference on the full half-plane `Re(s) < 1`. -/
example :
    (∫ x : ℝ, complexQuadraticExp ((1 / 2 : ℝ) + Complex.I) x
        ∂(gaussianReal 0 (2 : NNReal)⁻¹)) =
      (1 - ((1 / 2 : ℝ) + Complex.I)) ^ (-1 / 2 : ℂ) := by
  apply integral_gaussianHalf_complexQuadraticExp
  norm_num

/- The two parameter derivatives are tested away from the real axis, so the
   principal complex powers and both tilted-moment coefficients are pinned. -/
example :
    (∫ x : ℝ, (x : ℂ) ^ 2 *
        complexQuadraticExp ((1 / 2 : ℝ) + Complex.I) x
        ∂(gaussianReal 0 (2 : NNReal)⁻¹)) =
      (1 / 2 : ℂ) *
        (1 - ((1 / 2 : ℝ) + Complex.I)) ^ (-3 / 2 : ℂ) := by
  apply integral_gaussianHalf_sq_mul_complexQuadraticExp
  norm_num

example :
    (∫ x : ℝ, (x : ℂ) ^ 4 *
        complexQuadraticExp ((1 / 2 : ℝ) + Complex.I) x
        ∂(gaussianReal 0 (2 : NNReal)⁻¹)) =
      (3 / 4 : ℂ) *
        (1 - ((1 / 2 : ℝ) + Complex.I)) ^ (-5 / 2 : ℂ) := by
  apply integral_gaussianHalf_fourthPow_mul_complexQuadraticExp
  norm_num

/- This is the exact full-Gaussian U4 reference, including the coefficient
   12, the spatial derivative order four, and the principal `-5/2` power. -/
example :
    (∫ x : ℝ,
        iteratedDeriv 4 (complexQuadraticExp ((1 / 2 : ℝ) + Complex.I)) x
        ∂(gaussianReal 0 (2 : NNReal)⁻¹)) =
      12 * (((1 / 2 : ℝ) + Complex.I) : ℂ) ^ 2 *
        (1 - ((1 / 2 : ℝ) + Complex.I)) ^ (-5 / 2 : ℂ) := by
  apply integral_gaussianHalf_iteratedDeriv_four_complexQuadraticExp
  norm_num

/- The exact U7-to-U4 substitution is consumed with a symbolic asymmetric
   profile; this pins both final denominators and the `r * sqrt r` direction. -/
example {d : ℕ} (a : Fin d → ℝ) (M : ℂ) {s : ℂ} (hs : s.re < 1)
    (hhybrid :
      ‖(1 - s) ^ (-1 / 2 : ℂ) - M -
          ((∑ p : Fin d × Fin 2,
              sparseUpperDuplicatedCoefficient a p ^ 4) / 12 : ℂ) *
            (∫ x : ℝ, iteratedDeriv 4 (complexQuadraticExp s) x
              ∂(gaussianReal 0 (2 : NNReal)⁻¹))‖ ≤
        (∑ p : Fin d × Fin 2,
            sparseUpperDuplicatedCoefficient a p ^ 4) ^ 2 / 144 *
              quadraticExpDerivativeMajorant 8 ‖s‖ s.re +
        11 * (∑ p : Fin d × Fin 2,
            sparseUpperDuplicatedCoefficient a p ^ 6) / 180 *
              quadraticExpDerivativeMajorant 6 ‖s‖ s.re) :
    ‖M - (1 - s) ^ (-1 / 2 : ℂ) +
        ((sparseProfileFourthMoment a / 8 : ℝ) : ℂ) * s ^ 2 *
          (1 - s) ^ (-5 / 2 : ℂ)‖ ≤
      sparseProfileFourthMoment a ^ 2 / 9216 *
          quadraticExpDerivativeMajorant 8 ‖s‖ s.re +
      11 * (sparseProfileFourthMoment a *
          Real.sqrt (sparseProfileFourthMoment a)) / 5760 *
            quadraticExpDerivativeMajorant 6 ‖s‖ s.re :=
  sparseUpper_fourthOrder_of_hybrid a M hs hhybrid

/- The reference law is the centered Gaussian of variance one half, not the
   standard variance-one Gaussian. -/
example {lambda : ℝ} (hlambda : lambda < 1) (ell : ℕ) :
    (∫ x : ℝ, |x| ^ (2 * ell) * Real.exp (lambda * x ^ 2)
        ∂(gaussianReal 0 (2 : NNReal)⁻¹)) =
      gaussianHalfTiltedEvenMomentMajorant ell lambda :=
  integral_gaussianHalf_abs_evenPow_mul_exp_sq ell hlambda

/- At zero tilt the exact Gaussian-half moments pin the normalization through
   every power consumed by D₈. -/
example :
    (∫ _ : ℝ, (1 : ℝ) ∂(gaussianReal 0 (2 : NNReal)⁻¹)) = 1 ∧
    (∫ x : ℝ, |x| ^ 2 ∂(gaussianReal 0 (2 : NNReal)⁻¹)) = 1 / 2 ∧
    (∫ x : ℝ, |x| ^ 4 ∂(gaussianReal 0 (2 : NNReal)⁻¹)) = 3 / 4 ∧
    (∫ x : ℝ, |x| ^ 6 ∂(gaussianReal 0 (2 : NNReal)⁻¹)) = 15 / 8 ∧
    (∫ x : ℝ, |x| ^ 8 ∂(gaussianReal 0 (2 : NNReal)⁻¹)) = 105 / 16 := by
  constructor
  · have h := integral_gaussianHalf_abs_evenPow_mul_exp_sq 0 (lambda := 0) (by norm_num)
    norm_num [gaussianHalfTiltedEvenMomentMajorant] at h ⊢
  constructor
  · have h := integral_gaussianHalf_abs_evenPow_mul_exp_sq 1 (lambda := 0) (by norm_num)
    norm_num [gaussianHalfTiltedEvenMomentMajorant] at h ⊢
    exact h
  constructor
  · have h := integral_gaussianHalf_abs_evenPow_mul_exp_sq 2 (lambda := 0) (by norm_num)
    norm_num [gaussianHalfTiltedEvenMomentMajorant] at h ⊢
    exact h
  constructor
  · have h := integral_gaussianHalf_abs_evenPow_mul_exp_sq 3 (lambda := 0) (by norm_num)
    norm_num [gaussianHalfTiltedEvenMomentMajorant] at h ⊢
    exact h
  · have h := integral_gaussianHalf_abs_evenPow_mul_exp_sq 4 (lambda := 0) (by norm_num)
    norm_num [gaussianHalfTiltedEvenMomentMajorant] at h ⊢
    exact h

example : QuadraticExpEvenMomentBound
    (gaussianReal 0 (2 : NNReal)⁻¹) (1 / 2 : ℝ) :=
  gaussianHalf_quadraticExpEvenMomentBound (by norm_num) (by norm_num)

/- The raw comparison interface is nonvacuous and uses the same variance-half
   reference law. -/
example : GaussianHalfEvenMomentDomination
    (gaussianReal 0 (2 : NNReal)⁻¹) :=
  gaussianHalf_evenMomentDomination

/- Three terms pin the Taylor indexing, factorial normalization, and the
   shift from `ell` to `ell+n`. -/
example (ell : ℕ) (lambda x : ℝ) (hx : 0 ≤ x) :
    quadraticExpTiltedMomentPartialSum ell lambda 3 x =
      |x| ^ (2 * ell) +
      lambda * |x| ^ (2 * (ell + 1)) +
      lambda ^ 2 / 2 * |x| ^ (2 * (ell + 2)) := by
  norm_num [quadraticExpTiltedMomentPartialSum, quadraticExpTiltedMomentTerm,
    Finset.sum_range_succ, abs_of_nonneg hx]

example (ell : ℕ) (lambda x : ℝ) :
    HasSum (fun n : ℕ => quadraticExpTiltedMomentTerm ell lambda n x)
      (|x| ^ (2 * ell) * Real.exp (lambda * x ^ 2)) :=
  hasSum_quadraticExpTiltedMoment_terms ell lambda x

example {μ : Measure ℝ} (h : GaussianHalfEvenMomentDomination μ) :
    QuadraticExpEvenMomentBound μ (1 / 2 : ℝ) :=
  quadraticExpEvenMomentBound_of_evenMomentDomination h (by norm_num) (by norm_num)

/- The lower endpoint is part of the public transfer domain.  This direct
   application prevents silently tightening `0 ≤ lambda` to `0 < lambda`. -/
example {μ : Measure ℝ} (h : GaussianHalfEvenMomentDomination μ) :
    QuadraticExpEvenMomentBound μ 0 :=
  quadraticExpEvenMomentBound_of_evenMomentDomination h le_rfl (by norm_num)

/- A nonreal parameter pins that the two U3c consumers use `s.re` for the
   tilt and `‖s‖` for the derivative coefficients. -/
example {μ : Measure ℝ} (h : GaussianHalfEvenMomentDomination μ) :
    (∫ x : ℝ,
        ‖iteratedDeriv 6 (complexQuadraticExp ((1 / 2 : ℝ) + Complex.I)) x‖ ∂μ) ≤
      quadraticExpDerivativeMajorant 6 ‖(1 / 2 : ℂ) + Complex.I‖ (1 / 2) := by
  simpa using
    integral_norm_iteratedDeriv_six_complexQuadraticExp_le_of_evenMomentDomination
      h ((1 / 2 : ℝ) + Complex.I) (by norm_num) (by norm_num)

example {μ : Measure ℝ} (h : GaussianHalfEvenMomentDomination μ) :
    (∫ x : ℝ,
        ‖iteratedDeriv 8 (complexQuadraticExp ((1 / 2 : ℝ) + Complex.I)) x‖ ∂μ) ≤
      quadraticExpDerivativeMajorant 8 ‖(1 / 2 : ℂ) + Complex.I‖ (1 / 2) := by
  simpa using
    integral_norm_iteratedDeriv_eight_complexQuadraticExp_le_of_evenMomentDomination
      h ((1 / 2 : ℝ) + Complex.I) (by norm_num) (by norm_num)

/- The pure-imaginary cases pin the included `s.re = 0` boundary for both
   derivative consumers. -/
example {μ : Measure ℝ} (h : GaussianHalfEvenMomentDomination μ) :
    (∫ x : ℝ, ‖iteratedDeriv 6 (complexQuadraticExp Complex.I) x‖ ∂μ) ≤
      quadraticExpDerivativeMajorant 6 ‖Complex.I‖ 0 := by
  simpa using
    integral_norm_iteratedDeriv_six_complexQuadraticExp_le_of_evenMomentDomination
      h Complex.I (by norm_num) (by norm_num)

example {μ : Measure ℝ} (h : GaussianHalfEvenMomentDomination μ) :
    (∫ x : ℝ, ‖iteratedDeriv 8 (complexQuadraticExp Complex.I) x‖ ∂μ) ≤
      quadraticExpDerivativeMajorant 8 ‖Complex.I‖ 0 := by
  simpa using
    integral_norm_iteratedDeriv_eight_complexQuadraticExp_le_of_evenMomentDomination
      h Complex.I (by norm_num) (by norm_num)

example (μ ν : Measure ℝ) (t : ℝ) :
    firstStopLossDifference μ ν t =
      (∫ y, max (y - t) 0 ∂μ) - ∫ y, max (y - t) 0 ∂ν := rfl

/- The second-order cutoff boundary keeps all four Fubini/RHS obligations and
   all three limits explicit. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]
    {f : ℝ → E} (x : ℝ) (g : ℕ → ℝ → E)
    (hg2 : ∀ n, ContDiff ℝ 2 (g n))
    (hgc : ∀ n, HasCompactSupport (g n))
    (hμKernel : ∀ n, Integrable
      (Function.uncurry (fun t y =>
        max (y - t) 0 • deriv (deriv (g n)) (x + t))) (volume.prod μ))
    (hνKernel : ∀ n, Integrable
      (Function.uncurry (fun t y =>
        max (y - t) 0 • deriv (deriv (g n)) (x + t))) (volume.prod ν))
    (hμRhs : ∀ n, Integrable (fun t =>
      (∫ y, max (y - t) 0 ∂μ) • deriv (deriv (g n)) (x + t)))
    (hνRhs : ∀ n, Integrable (fun t =>
      (∫ y, max (y - t) 0 ∂ν) • deriv (deriv (g n)) (x + t)))
    (hμLimit : Tendsto (fun n => ∫ y, g n (x + y) ∂μ) atTop
      (𝓝 (∫ y, f (x + y) ∂μ)))
    (hνLimit : Tendsto (fun n => ∫ y, g n (x + y) ∂ν) atTop
      (𝓝 (∫ y, f (x + y) ∂ν)))
    (hRhsLimit : Tendsto
      (fun n => ∫ t, firstStopLossDifference μ ν t •
        deriv (deriv (g n)) (x + t)) atTop
      (𝓝 (∫ t, firstStopLossDifference μ ν t •
        deriv (deriv f) (x + t)))) :
    (∫ y, f (x + y) ∂μ) - ∫ y, f (x + y) ∂ν =
      ∫ t, firstStopLossDifference μ ν t • deriv (deriv f) (x + t) :=
  peanoIdentity2_of_compact_approximants x g hg2 hgc
    hμKernel hνKernel hμRhs hνRhs hμLimit hνLimit hRhsLimit

/- The exact three terms pin both cutoff cross terms and their binomial
   coefficient before the U3b majorant is introduced. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ 2 f) (n : ℕ) (x t : ℝ) :
    iteratedDeriv 2 (upperCutoffProduct n f x) (x + t) =
      upperCutoff n t • iteratedDeriv 2 f (x + t) +
        (2 : ℕ) • iteratedDeriv 1 (upperCutoff n) t •
          iteratedDeriv 1 f (x + t) +
        iteratedDeriv 2 (upperCutoff n) t • f (x + t) := by
  rw [upperCutoffProduct_iteratedDeriv_two hf n x (x + t)]
  have hshift (i : ℕ) :
      iteratedDeriv i (fun w : ℝ => upperCutoff n (w - x)) (x + t) =
        iteratedDeriv i (upperCutoff n) t := by
    have h := congrFun (iteratedDeriv_comp_sub_const i (upperCutoff n) x) (x + t)
    simpa only [add_sub_cancel_left] using h
  simp [Finset.sum_range_succ, iteratedDeriv_zero, hshift, add_assoc]

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ 2 f) (x t : ℝ) :
    Tendsto
      (fun n => iteratedDeriv 2 (upperCutoffProduct n f x) (x + t))
      atTop (𝓝 (iteratedDeriv 2 f (x + t))) :=
  upperCutoffProduct_iteratedDeriv_two_tendsto hf x t

/- This direct application keeps the two law limits, four compact Fubini/RHS
   obligations, measurability, and one index-independent majorant visible. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]
    {f : ℝ → E} (hf : ContDiff ℝ 2 f) (x : ℝ)
    (hμf : Integrable (fun y => f (x + y)) μ)
    (hνf : Integrable (fun y => f (x + y)) ν)
    (hμKernel : ∀ n, Integrable
      (Function.uncurry (fun t y => max (y - t) 0 •
        iteratedDeriv 2 (upperCutoffProduct n f x) (x + t))) (volume.prod μ))
    (hνKernel : ∀ n, Integrable
      (Function.uncurry (fun t y => max (y - t) 0 •
        iteratedDeriv 2 (upperCutoffProduct n f x) (x + t))) (volume.prod ν))
    (hμRhs : ∀ n, Integrable (fun t =>
      (∫ y, max (y - t) 0 ∂μ) •
        iteratedDeriv 2 (upperCutoffProduct n f x) (x + t)))
    (hνRhs : ∀ n, Integrable (fun t =>
      (∫ y, max (y - t) 0 ∂ν) •
        iteratedDeriv 2 (upperCutoffProduct n f x) (x + t)))
    (hΔ : StronglyMeasurable (firstStopLossDifference μ ν))
    (bound : ℝ → ℝ) (hboundInt : Integrable bound)
    (hbound : ∀ n t,
      ‖firstStopLossDifference μ ν t •
          iteratedDeriv 2 (upperCutoffProduct n f x) (x + t)‖ ≤ bound t) :
    (∫ y, f (x + y) ∂μ) - ∫ y, f (x + y) ∂ν =
      ∫ t, firstStopLossDifference μ ν t • iteratedDeriv 2 f (x + t) :=
  peanoIdentity2_of_upperCutoffProduct hf x hμf hνf hμKernel hνKernel
    hμRhs hνRhs hΔ bound hboundInt hbound

/- The U3b specialization exposes fourth derivatives on the laws and the
   sixth derivative on the stop-loss RHS. -/
example {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]
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
      (∫ y, max (y - t) 0 ∂μ) • iteratedDeriv 2
        (upperCutoffProduct n (iteratedDeriv 4 (complexQuadraticExp s)) x)
        (x + t)))
    (hνRhs : ∀ n, Integrable (fun t =>
      (∫ y, max (y - t) 0 ∂ν) • iteratedDeriv 2
        (upperCutoffProduct n (iteratedDeriv 4 (complexQuadraticExp s)) x)
        (x + t)))
    (hΔ : StronglyMeasurable (firstStopLossDifference μ ν))
    (bound : ℝ → ℝ) (hboundInt : Integrable bound)
    (hbound : ∀ n t,
      ‖firstStopLossDifference μ ν t • iteratedDeriv 2
        (upperCutoffProduct n (iteratedDeriv 4 (complexQuadraticExp s)) x)
        (x + t)‖ ≤ bound t) :
    (∫ y, iteratedDeriv 4 (complexQuadraticExp s) (x + y) ∂μ) -
        ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (x + y) ∂ν =
      ∫ t, firstStopLossDifference μ ν t •
        iteratedDeriv 6 (complexQuadraticExp s) (x + t) :=
  peanoIdentity2_iteratedDeriv_four_complexQuadraticExp s x hμf hνf
    hμKernel hνKernel hμRhs hνRhs hΔ bound hboundInt hbound

example (s : ℂ) :
    iteratedDeriv 2
        (fun y : ℝ => iteratedDeriv 4 (complexQuadraticExp s) (2 + (-3) * y)) 5 =
      (-3 : ℝ) ^ 2 • iteratedDeriv 6 (complexQuadraticExp s) (2 + (-3) * 5) :=
  iteratedDeriv_two_scaled_iteratedDeriv_four_complexQuadraticExp s 2 (-3) 5

/- The fixed-shift scaled theorem pins the paper's `c²`, `w+c y`, and
   `w+c t` placements before the independent-W integration step. -/
example {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]
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
        (c ^ 2 • iteratedDeriv 6 (complexQuadraticExp s) (w + c * t)) :=
  peanoIdentity2_scaled_iteratedDeriv_four_complexQuadraticExp s w c hμf hνf
    hμKernel hνKernel hμRhs hνRhs hΔ bound hboundInt hbound

/- The independent-partial-sum lift keeps the Gaussian-minus-comparator
   orientation, a negative scale inside `W-3t`, and the even scale outside. -/
example {ρ μ ν : Measure ℝ} (s : ℂ)
    (hμ : Integrable (fun w =>
      ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + (-3) * y) ∂μ) ρ)
    (hν : Integrable (fun w =>
      ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + (-3) * y) ∂ν) ρ)
    (hfixed : ∀ w,
      (∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + (-3) * y) ∂μ) -
          ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + (-3) * y) ∂ν =
        ∫ t, firstStopLossDifference μ ν t •
          ((-3 : ℝ) ^ 2 •
            iteratedDeriv 6 (complexQuadraticExp s) (w + (-3) * t))) :
    (∫ w, ∫ y, iteratedDeriv 4
          (complexQuadraticExp s) (w + (-3) * y) ∂μ ∂ρ) -
        ∫ w, ∫ y, iteratedDeriv 4
          (complexQuadraticExp s) (w + (-3) * y) ∂ν ∂ρ =
      (-3 : ℝ) ^ 2 • ∫ w, ∫ t, firstStopLossDifference μ ν t •
        iteratedDeriv 6 (complexQuadraticExp s) (w + (-3) * t) ∂volume ∂ρ :=
  peanoIdentity2_partialSum_scaled_iteratedDeriv_four_complexQuadraticExp
    s (-3) hμ hν hfixed

/- This is the exact paper-U3b consumer boundary.  The variance-one-half law,
   `gamma=11/15`, `Re(s)=1/2`, `|s|`, and the negative scale are all visible;
   only the U3a/mixed-moment Gaussianization inequality remains a premise. -/
example {ρ μ ν : Measure ℝ}
    (hlifted :
      (∫ w, ∫ y, iteratedDeriv 4
          (complexQuadraticExp ((1 / 2 : ℝ) + Complex.I)) (w + (-3) * y) ∂μ ∂ρ) -
          ∫ w, ∫ y, iteratedDeriv 4
            (complexQuadraticExp ((1 / 2 : ℝ) + Complex.I))
              (w + (-3) * y) ∂ν ∂ρ =
        (-3 : ℝ) ^ 2 • ∫ w, ∫ t, firstStopLossDifference μ ν t •
          iteratedDeriv 6 (complexQuadraticExp ((1 / 2 : ℝ) + Complex.I))
            (w + (-3) * t) ∂volume ∂ρ)
    (hgaussianize :
      ‖∫ w, ∫ t, firstStopLossDifference μ ν t •
          iteratedDeriv 6 (complexQuadraticExp ((1 / 2 : ℝ) + Complex.I))
            (w + (-3) * t) ∂volume ∂ρ‖ ≤
        (11 / 15 : ℝ) * ∫ x,
          ‖iteratedDeriv 6 (complexQuadraticExp ((1 / 2 : ℝ) + Complex.I)) x‖
            ∂(gaussianReal 0 (2 : NNReal)⁻¹)) :
    ‖(∫ w, ∫ y, iteratedDeriv 4
          (complexQuadraticExp ((1 / 2 : ℝ) + Complex.I)) (w + (-3) * y) ∂μ ∂ρ) -
        ∫ w, ∫ y, iteratedDeriv 4
          (complexQuadraticExp ((1 / 2 : ℝ) + Complex.I))
            (w + (-3) * y) ∂ν ∂ρ‖ ≤
      (11 / 15 : ℝ) * (-3 : ℝ) ^ 2 *
        quadraticExpDerivativeMajorant 6
          ‖((1 / 2 : ℝ) : ℂ) + Complex.I‖ (1 / 2) := by
  simpa only [Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero] using
    norm_partialSum_secondPeanoDifference_le_of_evenMomentDomination
      ((1 / 2 : ℝ) + Complex.I) (-3) (11 / 15)
      hlifted gaussianHalf_evenMomentDomination (by norm_num) (by norm_num)
      (by norm_num) hgaussianize

#print axioms integral_gaussianHalf_abs_evenPow_mul_exp_sq
#print axioms integral_gaussianHalf_complexQuadraticExp
#print axioms integral_gaussianHalf_sq_mul_complexQuadraticExp
#print axioms integral_gaussianHalf_fourthPow_mul_complexQuadraticExp
#print axioms integral_gaussianHalf_iteratedDeriv_four_complexQuadraticExp
#print axioms sparseUpper_fourthOrder_of_hybrid
#print axioms gaussianHalf_quadraticExpEvenMomentBound
#print axioms gaussianHalf_evenMomentDomination
#print axioms hasSum_quadraticExpTiltedMoment_terms
#print axioms integrable_quadraticExpTiltedMomentPartialSum
#print axioms integral_quadraticExpTiltedMomentPartialSum_le
#print axioms quadraticExpEvenMomentBound_of_evenMomentDomination
#print axioms integral_norm_iteratedDeriv_six_complexQuadraticExp_le_of_evenMomentDomination
#print axioms integral_norm_iteratedDeriv_eight_complexQuadraticExp_le_of_evenMomentDomination
#print axioms firstStopLossDifference
#print axioms peanoIdentity2_of_compact_approximants
#print axioms upperCutoffProduct_integral_tendsto
#print axioms upperCutoffProduct_iteratedDeriv_two
#print axioms upperCutoffProduct_iteratedDeriv_two_tendsto
#print axioms peanoIdentity2_of_upperCutoffProduct
#print axioms contDiff_omega_complexQuadraticExp
#print axioms peanoIdentity2_iteratedDeriv_four_complexQuadraticExp
#print axioms contDiff_two_iteratedDeriv_four_complexQuadraticExp
#print axioms iteratedDeriv_two_scaled_iteratedDeriv_four_complexQuadraticExp
#print axioms peanoIdentity2_scaled_iteratedDeriv_four_complexQuadraticExp
#print axioms peanoIdentity2_partialSum_scaled_iteratedDeriv_four_complexQuadraticExp
#print axioms norm_partialSum_secondPeanoDifference_le_of_evenMomentDomination

run_cmd
  let allowed : Array Name :=
    #[``propext, ``Classical.choice, ``Quot.sound]
  let sixth : Name :=
    ``CertifiedJL.integral_norm_iteratedDeriv_six_complexQuadraticExp_le_of_evenMomentDomination
  let eighth : Name :=
    ``CertifiedJL.integral_norm_iteratedDeriv_eight_complexQuadraticExp_le_of_evenMomentDomination
  let targets : Array Name :=
    #[``CertifiedJL.integral_gaussianHalf_abs_evenPow_mul_exp_sq,
      ``CertifiedJL.integral_gaussianHalf_complexQuadraticExp,
      ``CertifiedJL.integral_gaussianHalf_sq_mul_complexQuadraticExp,
      ``CertifiedJL.integral_gaussianHalf_fourthPow_mul_complexQuadraticExp,
      ``CertifiedJL.integral_gaussianHalf_iteratedDeriv_four_complexQuadraticExp,
      ``CertifiedJL.sparseUpper_fourthOrder_of_hybrid,
      ``CertifiedJL.gaussianHalf_quadraticExpEvenMomentBound,
      ``CertifiedJL.gaussianHalf_evenMomentDomination,
      ``CertifiedJL.hasSum_quadraticExpTiltedMoment_terms,
      ``CertifiedJL.integrable_quadraticExpTiltedMomentPartialSum,
      ``CertifiedJL.integral_quadraticExpTiltedMomentPartialSum_le,
      ``CertifiedJL.quadraticExpEvenMomentBound_of_evenMomentDomination,
      sixth,
      eighth,
      ``CertifiedJL.firstStopLossDifference,
      ``CertifiedJL.peanoIdentity2_of_compact_approximants,
      ``CertifiedJL.upperCutoffProduct_integral_tendsto,
      ``CertifiedJL.upperCutoffProduct_iteratedDeriv_two,
      ``CertifiedJL.upperCutoffProduct_iteratedDeriv_two_tendsto,
      ``CertifiedJL.peanoIdentity2_of_upperCutoffProduct,
      ``CertifiedJL.contDiff_omega_complexQuadraticExp,
      ``CertifiedJL.peanoIdentity2_iteratedDeriv_four_complexQuadraticExp,
      ``CertifiedJL.contDiff_two_iteratedDeriv_four_complexQuadraticExp,
      ``CertifiedJL.iteratedDeriv_two_scaled_iteratedDeriv_four_complexQuadraticExp,
      ``CertifiedJL.peanoIdentity2_scaled_iteratedDeriv_four_complexQuadraticExp,
      ``CertifiedJL.peanoIdentity2_partialSum_scaled_iteratedDeriv_four_complexQuadraticExp,
      ``CertifiedJL.norm_partialSum_secondPeanoDifference_le_of_evenMomentDomination]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    unless axioms.size == allowed.size &&
        axioms.all allowed.contains &&
        allowed.all axioms.contains do
      throwError "unexpected axioms for {target}: {axioms}"

end CertifiedJL.Tests.UpperTailAnalyticCanaries
