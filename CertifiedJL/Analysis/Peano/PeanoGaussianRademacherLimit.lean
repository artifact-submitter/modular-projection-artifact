/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import CertifiedJL.Analysis.Peano.PeanoGaussianRademacherDCT

/-!
# Weighted Gaussian--Rademacher cutoff limit

This upper-owned module consumes the global integrable cutoff majorant and
the pointwise fourth-derivative limit.  It supplies the weighted right-hand
side convergence needed by the later concrete noncompact Peano identity.
-/

open MeasureTheory Set Filter
open ProbabilityTheory
open scoped Topology

namespace CertifiedJL

/-- The stop-loss-weighted fourth derivatives of the translated compact
cutoff remainders converge in Bochner integral to the uncut fourth derivative.
The integrable dominating function is independent of the cutoff index. -/
theorem upperCutoffRemainder_standardGaussianRademacher_weighted_fourthDeriv_integral_tendsto
    {s : ℂ} {x : ℝ} (hs : s.re < 0) :
    Tendsto
      (fun n => ∫ t : ℝ,
        ((1 / 6 : ℝ) * cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t) •
          iteratedDeriv 4
            (upperCutoffRemainder n (complexQuadraticExp s) x) (x + t))
      atTop
      (𝓝 (∫ t : ℝ,
        ((1 / 6 : ℝ) * cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t) •
          iteratedDeriv 4 (complexQuadraticExp s) (x + t))) := by
  obtain ⟨C, _hC, hmajor⟩ :=
    upperCutoffRemainder_standardGaussianRademacher_integrable_majorant
  have hdata := hmajor (s := s) (x := x) hs
  refine tendsto_integral_of_dominated_convergence
    (upperCutoffRemainder_standardGaussianRademacher_majorant C s x)
    ?_ hdata.1 ?_ ?_
  · intro n
    have hΔ := stronglyMeasurable_standardGaussianRademacher_cubicStopLossDifference
    have hcoef : StronglyMeasurable (fun t : ℝ =>
        (1 / 6 : ℝ) * cubicStopLossDifference
          (gaussianReal 0 1) standardRademacherMeasure t) := by
      simpa using hΔ.const_mul (1 / 6 : ℝ)
    have hfour : StronglyMeasurable (fun t : ℝ =>
        iteratedDeriv 4
          (upperCutoffRemainder n (complexQuadraticExp s) x) (x + t)) := by
      exact ((upperCutoffRemainder_contDiff (contDiff_complexQuadraticExp s) n x)
        |>.continuous_iteratedDeriv' 4 |>.comp
          (continuous_const.add continuous_id)).stronglyMeasurable
    exact hcoef.smul hfour |>.aestronglyMeasurable
  · intro n
    exact Filter.Eventually.of_forall (hdata.2 n)
  · filter_upwards [] with t
    exact tendsto_const_nhds.smul
      (upperCutoffRemainder_iteratedDeriv_four_tendsto
        (contDiff_complexQuadraticExp s) x t)

end CertifiedJL
