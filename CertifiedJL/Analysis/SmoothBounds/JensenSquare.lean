/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author.
-/

import Mathlib.Analysis.Convex.Integral

/-!
# Jensen's inequality for a squared input

This is a law-independent analysis lemma.  It belongs to the probability /
analysis layer rather than to the sparse-row namespace; the sparse upper
replacement proof imports it through `UpperPeano`.
-/

open MeasureTheory

namespace CertifiedJL

/-- Jensen's inequality for a convex function of a squared input. -/
theorem convexSquareExpectation_le
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (H : ℝ → ℝ) (a : ℝ)
    (hconv : ConvexOn ℝ (Set.Ici 0)
      (fun v : ℝ => H (a * Real.sqrt v)))
    (hcont : ContinuousOn
      (fun v : ℝ => H (a * Real.sqrt v)) (Set.Ici 0))
    (hsecond : ∫ y, y ^ 2 ∂μ = 1)
    (hfi : Integrable (fun y : ℝ => y ^ 2) μ)
      (hgi : Integrable (fun y : ℝ => H (a * Real.sqrt (y ^ 2))) μ) :
      H a ≤ ∫ y, H (a * Real.sqrt (y ^ 2)) ∂μ := by
  have hmem : ∀ᵐ y ∂μ, y ^ 2 ∈ Set.Ici (0 : ℝ) := by
    filter_upwards [] with y
    exact Set.mem_Ici.mpr (sq_nonneg y)
  have hgi' : Integrable ((fun v : ℝ => H (a * Real.sqrt v)) ∘
      (fun y : ℝ => y ^ 2)) μ := by
    simpa [Function.comp_def] using hgi
  have hjensen := hconv.map_integral_le hcont isClosed_Ici hmem hfi hgi'
  rw [hsecond] at hjensen
  simpa only [Real.sqrt_one, mul_one, Function.comp_apply] using hjensen

end CertifiedJL
