/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Peano.PeanoIdentity

/-!
# Explicit compact-approximant assembly for second-order Peano replacement

This is the cutoff boundary used by U3b.  It turns a sequence of compactly
supported `C²` approximants and three explicit convergence statements into
the noncompact degree-one stop-loss identity.  Existence of the approximants
and every integrability or convergence obligation remain visible to the
concrete consumer.
-/

open MeasureTheory Filter
open scoped Topology

namespace CertifiedJL

/-- Pass the compact second-order Peano identity through explicit law and
kernel limits. -/
theorem peanoIdentity2_of_compact_approximants
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]
    {f : ℝ → E} (x : ℝ)
    (g : ℕ → ℝ → E)
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
      ∫ t, firstStopLossDifference μ ν t • deriv (deriv f) (x + t) := by
  have hcompact : ∀ n,
      (∫ y, g n (x + y) ∂μ) - ∫ y, g n (x + y) ∂ν =
        ∫ t, firstStopLossDifference μ ν t •
          deriv (deriv (g n)) (x + t) := by
    intro n
    simpa only [firstStopLossDifference] using peanoIdentity2_compact
      (μ := μ) (ν := ν) (f := g n) (x := x)
      (hg2 n) (hgc n) (hμKernel n) (hνKernel n) (hμRhs n) (hνRhs n)
  have hleft := hμLimit.sub hνLimit
  have hright : Tendsto
      (fun n => (∫ y, g n (x + y) ∂μ) - ∫ y, g n (x + y) ∂ν) atTop
      (𝓝 (∫ t, firstStopLossDifference μ ν t •
        deriv (deriv f) (x + t))) := by
    apply hRhsLimit.congr'
    exact Filter.Eventually.of_forall fun n => (hcompact n).symm
  exact tendsto_nhds_unique hleft hright

end CertifiedJL
