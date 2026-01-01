/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import CertifiedJL.Analysis.Peano.PeanoCutoff
import CertifiedJL.Analysis.Peano.PeanoGaussianRademacherLimit

/-!
# Noncompact Gaussian--Rademacher fourth-order Peano identity

This module assembles the concrete standard-Gaussian and two-point
Rademacher instance of the fourth-order Peano identity for the quadratic
exponential.  All compact-kernel, law-limit, and weighted right-hand-side
convergence premises are discharged internally.
-/

open MeasureTheory Set Filter
open ProbabilityTheory
open scoped Topology

namespace CertifiedJL

private theorem integrable_standardRademacher
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : Integrable f standardRademacherMeasure := by
  rw [standardRademacherMeasure]
  apply Integrable.add_measure
  · exact (integrable_dirac (f := f) (a := (-1 : ℝ)) (by simp)).smul_measure
      (by norm_num)
  · exact (integrable_dirac (f := f) (a := (1 : ℝ)) (by simp)).smul_measure
      (by norm_num)

/-- The concrete noncompact `k = 4` Peano identity for the standard Gaussian
and the two-point Rademacher law in the strict development domain
`Re(s) < 0`. -/
theorem peanoIdentity4_standardGaussianRademacher_complexQuadraticExp
    {s : ℂ} (hs : s.re < 0) (x : ℝ) :
    (∫ y : ℝ, complexQuadraticExp s (x + y) ∂(gaussianReal 0 1)) -
        ∫ y : ℝ, complexQuadraticExp s (x + y) ∂standardRademacherMeasure =
      ∫ t : ℝ, ((1 / 6 : ℝ) *
        cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t) •
        iteratedDeriv 4 (complexQuadraticExp s) (x + t) := by
  have hsGaussian : s.re < 1 / (2 * (1 : ℝ)) := by
    norm_num
    linarith
  have hμf : Integrable (fun y : ℝ => complexQuadraticExp s (x + y))
      (gaussianReal 0 1) :=
    integrable_gaussianReal_shifted_complexQuadraticExp
      (μ := 0) (v := 1) (x := x) (by norm_num) hsGaussian
  have hνf : Integrable (fun y : ℝ => complexQuadraticExp s (x + y))
      standardRademacherMeasure :=
    integrable_standardRademacher _
  have hμrem : Integrable
      (fun y : ℝ => complexQuadraticExp s (x + y) -
        taylorPolynomial3 (complexQuadraticExp s) x y)
      (gaussianReal 0 1) :=
    integrable_gaussianReal_shifted_complexQuadraticExp_remainder
      (μ := 0) (v := 1) (x := x) (by norm_num) hsGaussian
  have hμLimit := upperCutoffRemainder_integral_tendsto
    (μ := gaussianReal 0 1) (contDiff_complexQuadraticExp s) x hμrem
  have hνLimit := upperCutoffRemainder_standardRademacher_integral_tendsto
    (contDiff_complexQuadraticExp s) x
  have hdata (n : ℕ) :=
    upperCutoffRemainder_standardGaussianRademacher_kernel_data
      (contDiff_complexQuadraticExp s) x n
  have hRhsLimit : Tendsto
      (fun n => ∫ t, ((1 / 6 : ℝ) *
        cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t) •
        deriv (deriv (deriv (deriv
          (upperCutoffRemainder n (complexQuadraticExp s) x)))) (x + t))
      atTop
      (𝓝 (∫ t, ((1 / 6 : ℝ) *
        cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t) •
        deriv (deriv (deriv (deriv (complexQuadraticExp s)))) (x + t))) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      (upperCutoffRemainder_standardGaussianRademacher_weighted_fourthDeriv_integral_tendsto
        (s := s) (x := x) hs)
  have hidentity := peanoIdentity4_of_compact_approximants
    (E := ℂ) (μ := gaussianReal 0 1) (ν := standardRademacherMeasure)
    (f := complexQuadraticExp s) (x := x)
    standardGaussianRademacher_equalMoments hμf hνf
    (fun n => upperCutoffRemainder n (complexQuadraticExp s) x)
    (fun n => upperCutoffRemainder_contDiff (contDiff_complexQuadraticExp s) n x)
    (fun n => upperCutoffRemainder_hasCompactSupport n (complexQuadraticExp s) x)
    (fun n => (hdata n).1.1) (fun n => (hdata n).2.1)
    (fun n => (hdata n).1.2) (fun n => (hdata n).2.2)
    hμLimit hνLimit hRhsLimit
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hidentity

end CertifiedJL
