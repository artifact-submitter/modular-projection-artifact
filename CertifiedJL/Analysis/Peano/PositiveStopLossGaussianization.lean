/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Peano.PeanoIdentity
import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpMomentComparison
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Positive stop-loss Gaussianization

The paper's U3a premise is represented as a finite positive measure with
density `firstStopLossDifference μ ν` relative to Lebesgue measure.  The
public product theorem keeps the independent law explicit as the pushforward
of `ρ.prod stopLossMeasure` under `(w, t) ↦ w + c * t`.
-/

namespace CertifiedJL

open MeasureTheory

/-- The positive measure with Lebesgue density `h`.  When `h` is
nonnegative, integration against this measure is integration against
`h(t) dt`. -/
noncomputable def positiveDensityMeasure (h : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity fun t => ENNReal.ofReal (h t)

/-- The exact lane-A premise for the stop-loss law.  Lane A supplies
nonnegativity and measurability of the concrete K-law stop-loss difference,
then proves the mass-`gamma`, variance-one moment domination of its density
measure. -/
structure PositiveStopLossMomentDomination
    (μ ν : Measure ℝ) (gamma : ℝ) : Prop where
  nonnegative (t : ℝ) : 0 ≤ firstStopLossDifference μ ν t
  measurable : Measurable (firstStopLossDifference μ ν)
  domination : GaussianEvenMomentDomination
    (positiveDensityMeasure (firstStopLossDifference μ ν)) gamma 1

/-- Integration against a nonnegative real density written as a positive
measure agrees with the scalar-weighted Lebesgue integral. -/
theorem integral_positiveDensityMeasure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ → ℝ) (hh : Measurable h) (hnonneg : ∀ t, 0 ≤ h t) (g : ℝ → E) :
    (∫ t, g t ∂positiveDensityMeasure h) = ∫ t, h t • g t ∂volume := by
  unfold positiveDensityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    hh.ennreal_ofReal (ae_of_all _ fun t => ENNReal.ofReal_lt_top) g]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by simp [hnonneg t]

/-- The positive stop-loss product law inherits mass `gamma` and variance
`varianceW + c²`.  Independence is visible through the product pushforward
in `independentAffineSumMeasure`. -/
theorem PositiveStopLossMomentDomination.independentAffineSum
    {ρ μ ν : Measure ℝ} {varianceW : NNReal} {gamma : ℝ}
    (hW : GaussianEvenMomentDomination ρ 1 varianceW)
    (hΔ : PositiveStopLossMomentDomination μ ν gamma) (c : ℝ) :
    GaussianEvenMomentDomination
      (independentAffineSumMeasure ρ
        (positiveDensityMeasure (firstStopLossDifference μ ν)) c)
      gamma (varianceW + scaledVariance c 1) := by
  simpa only [one_mul] using hW.independentAffineSum hΔ.domination c

private theorem continuous_iteratedDeriv_six_complexQuadraticExp (s : ℂ) :
    Continuous (iteratedDeriv 6 (complexQuadraticExp s)) := by
  have hfun : iteratedDeriv 6 (complexQuadraticExp s) =
      fun x : ℝ =>
        (120 * s ^ 3 + 720 * s ^ 4 * (x : ℂ) ^ 2 +
          480 * s ^ 5 * (x : ℂ) ^ 4 + 64 * s ^ 6 * (x : ℂ) ^ 6) *
            complexQuadraticExp s x := by
    funext x
    exact iteratedDeriv_six_complexQuadraticExp s x
  rw [hfun]
  simp only [complexQuadraticExp]
  fun_prop

/-- Strongest general U3b Gaussianization bound for a positive stop-loss
product law.  The first product coordinate is `W`; the second is the
stop-loss variable `t`; and the pushforward is `W + c * t`.

All Fubini and derivative integrability facts are derived from the moment
domination hypotheses. -/
theorem norm_integral_integral_firstStopLossDifference_iteratedDeriv_six_le
    {ρ μ ν : Measure ℝ} {varianceW : NNReal} {gamma : ℝ}
    (hW : GaussianEvenMomentDomination ρ 1 varianceW)
    (hΔ : PositiveStopLossMomentDomination μ ν gamma) (c : ℝ)
    (hvariance : varianceW + scaledVariance c 1 ≤ (2 : NNReal)⁻¹)
    (s : ℂ) (hs_nonneg : 0 ≤ s.re) (hs_lt_one : s.re < 1) :
    ‖∫ w, ∫ t, firstStopLossDifference μ ν t •
        iteratedDeriv 6 (complexQuadraticExp s) (w + c * t) ∂volume ∂ρ‖ ≤
      gamma * quadraticExpDerivativeMajorant 6 ‖s‖ s.re := by
  let τ : Measure ℝ :=
    positiveDensityMeasure (firstStopLossDifference μ ν)
  let F : ℝ → ℂ := iteratedDeriv 6 (complexQuadraticExp s)
  let : IsFiniteMeasure ρ := hW.isFiniteMeasure
  let : IsFiniteMeasure τ := by
    simpa only [τ] using hΔ.domination.isFiniteMeasure
  have hFcont : Continuous F := by
    simpa only [F] using continuous_iteratedDeriv_six_complexQuadraticExp s
  have hjoint : GaussianEvenMomentDomination
      (independentAffineSumMeasure ρ τ c) gamma
        (varianceW + scaledVariance c 1) := by
    simpa only [τ] using hΔ.independentAffineSum hW c
  have hpack :=
    integrable_and_integral_norm_six_le_of_gaussianEvenMomentDomination
      hjoint hvariance s hs_nonneg hs_lt_one
  have hnormProd : Integrable
      (fun p : ℝ × ℝ => ‖F (p.1 + c * p.2)‖) (ρ.prod τ) := by
    have hcomp := (integrable_map_measure
      (μ := ρ.prod τ) (f := fun p : ℝ × ℝ => p.1 + c * p.2)
      (g := fun z : ℝ => ‖F z‖) hpack.1.aestronglyMeasurable
      (by fun_prop)).mp hpack.1
    change Integrable (fun p : ℝ × ℝ => ‖F (p.1 + c * p.2)‖) (ρ.prod τ) at hcomp
    exact hcomp
  have hprod : Integrable
      (fun p : ℝ × ℝ => F (p.1 + c * p.2)) (ρ.prod τ) := by
    apply (integrable_norm_iff (μ := ρ.prod τ)
      (f := fun p : ℝ × ℝ => F (p.1 + c * p.2))
      (hFcont.comp (by fun_prop)).aestronglyMeasurable).mp
    exact hnormProd
  have hinner (w : ℝ) :
      (∫ t, F (w + c * t) ∂τ) =
        ∫ t, firstStopLossDifference μ ν t • F (w + c * t) ∂volume := by
    exact integral_positiveDensityMeasure _ hΔ.measurable hΔ.nonnegative _
  calc
    ‖∫ w, ∫ t, firstStopLossDifference μ ν t •
          iteratedDeriv 6 (complexQuadraticExp s) (w + c * t) ∂volume ∂ρ‖ =
        ‖∫ p : ℝ × ℝ, F (p.1 + c * p.2) ∂ρ.prod τ‖ := by
      congr 1
      rw [integral_prod _ hprod]
      apply integral_congr_ae
      exact ae_of_all _ fun w => (hinner w).symm
    _ ≤ ∫ p : ℝ × ℝ, ‖F (p.1 + c * p.2)‖ ∂ρ.prod τ :=
      norm_integral_le_integral_norm _
    _ = ∫ z : ℝ, ‖F z‖ ∂independentAffineSumMeasure ρ τ c := by
      unfold independentAffineSumMeasure
      rw [integral_map (by fun_prop) hFcont.norm.aestronglyMeasurable]
    _ ≤ gamma * quadraticExpDerivativeMajorant 6 ‖s‖ s.re := by
      simpa only [F] using hpack.2

end CertifiedJL
