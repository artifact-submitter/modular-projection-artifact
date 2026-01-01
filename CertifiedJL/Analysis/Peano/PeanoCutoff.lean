/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author.
-/

import CertifiedJL.Analysis.Peano.PeanoMoments

/-!
# Explicit compact-approximant assembly for fourth-order P0

This is the cutoff boundary between the compact Peano identity and the later
noncompact exponential-square consumer.  It takes an explicit sequence of
compactly supported `C⁴` approximants and three actual convergence statements:
the two law integrals and the fourth-derivative stop-loss integral.  Nothing
about the existence of such a sequence is hidden in the theorem.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace CertifiedJL

theorem peanoIdentity4_of_compact_approximants
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]
    {f : ℝ → E} (x : ℝ)
    (hm : EqualMomentsThrough μ ν 3)
    (hμf : Integrable (fun y => f (x + y)) μ)
    (hνf : Integrable (fun y => f (x + y)) ν)
    (g : ℕ → ℝ → E)
    (hg4 : ∀ n, ContDiff ℝ 4 (g n))
    (hgc : ∀ n, HasCompactSupport (g n))
    (hμKernel : ∀ n, Integrable
      (Function.uncurry (fun t y =>
        ((1 / 6 : ℝ) * (max (y - t) 0) ^ 3) •
          deriv (deriv (deriv (deriv (g n)))) (x + t))) (volume.prod μ))
    (hνKernel : ∀ n, Integrable
      (Function.uncurry (fun t y =>
        ((1 / 6 : ℝ) * (max (y - t) 0) ^ 3) •
          deriv (deriv (deriv (deriv (g n)))) (x + t))) (volume.prod ν))
    (hμRhs : ∀ n, Integrable (fun t =>
      (((1 / 6 : ℝ) * (∫ y, (max (y - t) 0) ^ 3 ∂μ)) •
        deriv (deriv (deriv (deriv (g n)))) (x + t))))
    (hνRhs : ∀ n, Integrable (fun t =>
      (((1 / 6 : ℝ) * (∫ y, (max (y - t) 0) ^ 3 ∂ν)) •
        deriv (deriv (deriv (deriv (g n)))) (x + t))))
    (hμLimit : Tendsto
      (fun n => ∫ y, g n (x + y) ∂μ) atTop
      (𝓝 (∫ y, (f (x + y) - taylorPolynomial3 f x y) ∂μ)))
    (hνLimit : Tendsto
      (fun n => ∫ y, g n (x + y) ∂ν) atTop
      (𝓝 (∫ y, (f (x + y) - taylorPolynomial3 f x y) ∂ν)))
    (hRhsLimit : Tendsto
      (fun n => ∫ t, ((1 / 6 : ℝ) * cubicStopLossDifference μ ν t) •
        deriv (deriv (deriv (deriv (g n)))) (x + t)) atTop
      (𝓝 (∫ t, ((1 / 6 : ℝ) * cubicStopLossDifference μ ν t) •
        deriv (deriv (deriv (deriv f))) (x + t)))) :
    (∫ y, f (x + y) ∂μ) - ∫ y, f (x + y) ∂ν =
      ∫ t, ((1 / 6 : ℝ) * cubicStopLossDifference μ ν t) •
        deriv (deriv (deriv (deriv f))) (x + t) := by
  have hμT : Integrable (fun y => taylorPolynomial3 f x y) μ :=
    integrable_taylorPolynomial3_left hm f x
  have hνT : Integrable (fun y => taylorPolynomial3 f x y) ν :=
    integrable_taylorPolynomial3_right hm f x
  have hμsub :
      (∫ y, f (x + y) - taylorPolynomial3 f x y ∂μ) =
        (∫ y, f (x + y) ∂μ) - ∫ y, taylorPolynomial3 f x y ∂μ := by
    simpa using integral_sub hμf hμT
  have hνsub :
      (∫ y, f (x + y) - taylorPolynomial3 f x y ∂ν) =
        (∫ y, f (x + y) ∂ν) - ∫ y, taylorPolynomial3 f x y ∂ν := by
    simpa using integral_sub hνf hνT
  have hpoly := equalMomentsThrough_taylorPolynomial3 hm f x
  have hcompact : ∀ n,
      (∫ y, g n (x + y) ∂μ) - ∫ y, g n (x + y) ∂ν =
        ∫ t, ((1 / 6 : ℝ) * cubicStopLossDifference μ ν t) •
          deriv (deriv (deriv (deriv (g n)))) (x + t) := by
    intro n
    exact peanoIdentity4_compact
      (μ := μ) (ν := ν) (f := g n) (x := x)
      (hg4 n) (hgc n) (hμKernel n) (hνKernel n) (hμRhs n) (hνRhs n)
  have hleftLimit : Tendsto
      (fun n => (∫ y, g n (x + y) ∂μ) - ∫ y, g n (x + y) ∂ν) atTop
      (𝓝 ((∫ y, (f (x + y) - taylorPolynomial3 f x y) ∂μ) -
        ∫ y, (f (x + y) - taylorPolynomial3 f x y) ∂ν)) :=
    hμLimit.sub hνLimit
  have hrightLimit : Tendsto
      (fun n => (∫ y, g n (x + y) ∂μ) - ∫ y, g n (x + y) ∂ν) atTop
      (𝓝 (∫ t, ((1 / 6 : ℝ) * cubicStopLossDifference μ ν t) •
        deriv (deriv (deriv (deriv f))) (x + t))) := by
    apply hRhsLimit.congr'
    exact Filter.Eventually.of_forall (fun n => (hcompact n).symm)
  have hlimit := tendsto_nhds_unique hleftLimit hrightLimit
  calc
    (∫ y, f (x + y) ∂μ) - ∫ y, f (x + y) ∂ν =
        ((∫ y, (f (x + y) - taylorPolynomial3 f x y) ∂μ) -
          ∫ y, (f (x + y) - taylorPolynomial3 f x y) ∂ν) := by
      rw [hμsub, hνsub]
      rw [hpoly]
      abel
    _ = ∫ t, ((1 / 6 : ℝ) * cubicStopLossDifference μ ν t) •
        deriv (deriv (deriv (deriv f))) (x + t) := hlimit

end CertifiedJL
