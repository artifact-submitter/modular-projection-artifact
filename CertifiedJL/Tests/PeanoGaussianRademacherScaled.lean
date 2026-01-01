/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Peano.PeanoGaussianRademacherScaled
import Lean.Util.CollectAxioms

/-! Mutation canaries for the scaled fourth-Peano replacement. -/

open MeasureTheory ProbabilityTheory Lean

namespace CertifiedJL.Tests.PeanoGaussianRademacherScaled

example : Integrable (fun t : ℝ => (t ^ 2 + 2) *
    ‖iteratedDeriv 8 (complexQuadraticExp ((2 / 5 : ℝ) + Complex.I))
      ((-3 / 7 : ℝ) + t)‖) (gaussianReal 0 1) := by
  apply integrable_gaussianReal_sq_add_mul_norm_iteratedDeriv_all
  norm_num

example :
    (∫ y : ℝ, iteratedDeriv 4
          (complexQuadraticExp ((4 / 5 : ℝ) + Complex.I))
          ((-2 / 3 : ℝ) + (1 / 2 : ℝ) * y) ∂(gaussianReal 0 1)) -
      ∫ y : ℝ, iteratedDeriv 4
          (complexQuadraticExp ((4 / 5 : ℝ) + Complex.I))
          ((-2 / 3 : ℝ) + (1 / 2 : ℝ) * y)
        ∂standardRademacherMeasure =
      (((1 / 2 : ℝ) ^ 4) / 12 : ℝ) •
        ∫ k : ℝ, iteratedDeriv 8
          (complexQuadraticExp ((4 / 5 : ℝ) + Complex.I))
          ((-2 / 3 : ℝ) + (1 / 2 : ℝ) * k) ∂peanoKMeasure := by
  apply peanoIdentity4_standardGaussianRademacher_scaled_iteratedDeriv_four_complexQuadraticExp
  norm_num

/-- A direct asymmetric canary in the enlarged unscaled domain. -/
example :
    (∫ y : ℝ, complexQuadraticExp ((2 / 5 : ℝ) + Complex.I)
          ((-3 / 7 : ℝ) + y) ∂(gaussianReal 0 1)) -
        ∫ y : ℝ, complexQuadraticExp ((2 / 5 : ℝ) + Complex.I)
          ((-3 / 7 : ℝ) + y) ∂standardRademacherMeasure =
      ∫ t : ℝ, ((1 / 6 : ℝ) *
        cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t) •
        iteratedDeriv 4 (complexQuadraticExp ((2 / 5 : ℝ) + Complex.I))
          ((-3 / 7 : ℝ) + t) := by
  apply peanoIdentity4_standardGaussianRademacher_complexQuadraticExp_of_re_lt_half
  norm_num

/-- A positive-strip, nonreal, negative-scale canary for the exact scaled
producer. -/
example :
    (∫ y : ℝ, complexQuadraticExp ((4 / 5 : ℝ) + 2 * Complex.I)
          ((2 / 3 : ℝ) + (-1 / 2 : ℝ) * y) ∂(gaussianReal 0 1)) -
        ∫ y : ℝ, complexQuadraticExp ((4 / 5 : ℝ) + 2 * Complex.I)
          ((2 / 3 : ℝ) + (-1 / 2 : ℝ) * y)
          ∂standardRademacherMeasure =
      (((-1 / 2 : ℝ) ^ 4) / 12 : ℝ) •
        ∫ k : ℝ, iteratedDeriv 4
          (complexQuadraticExp ((4 / 5 : ℝ) + 2 * Complex.I))
          ((2 / 3 : ℝ) + (-1 / 2 : ℝ) * k) ∂peanoKMeasure := by
  apply peanoIdentity4_standardGaussianRademacher_scaled_complexQuadraticExp_peanoK
  norm_num

/-- The zero-scale boundary is included without a division side condition. -/
example (s : ℂ) (w : ℝ) :
    (∫ y : ℝ, complexQuadraticExp s (w + 0 * y) ∂(gaussianReal 0 1)) -
        ∫ y : ℝ, complexQuadraticExp s (w + 0 * y)
          ∂standardRademacherMeasure =
      ((0 : ℝ) ^ 4 / 12 : ℝ) •
        ∫ k : ℝ, iteratedDeriv 4 (complexQuadraticExp s) (w + 0 * k)
          ∂peanoKMeasure := by
  apply peanoIdentity4_standardGaussianRademacher_scaled_complexQuadraticExp_peanoK
  norm_num

/-- A nontrivial Dirac partial-sum law pins the outer-integral lifting. -/
example :
    (∫ w, ∫ y : ℝ, complexQuadraticExp ((3 / 4 : ℝ) + Complex.I)
          (w + (1 / 2 : ℝ) * y) ∂(gaussianReal 0 1)
        ∂Measure.dirac (5 / 7 : ℝ)) -
      ∫ w, ∫ y : ℝ, complexQuadraticExp ((3 / 4 : ℝ) + Complex.I)
          (w + (1 / 2 : ℝ) * y) ∂standardRademacherMeasure
        ∂Measure.dirac (5 / 7 : ℝ) =
      (((1 / 2 : ℝ) ^ 4) / 12 : ℝ) •
        ∫ w, ∫ k : ℝ, iteratedDeriv 4
          (complexQuadraticExp ((3 / 4 : ℝ) + Complex.I))
          (w + (1 / 2 : ℝ) * k) ∂peanoKMeasure
        ∂Measure.dirac (5 / 7 : ℝ) := by
  apply peanoIdentity4_partialSum_standardGaussianRademacher_scaled
  · norm_num
  · exact integrable_dirac (by simp)
  · exact integrable_dirac (by simp)

/-- A nontrivial Dirac partial sum pins the lifted D4-to-D8 producer. -/
example :
    (∫ w, ∫ y : ℝ, iteratedDeriv 4
          (complexQuadraticExp ((3 / 4 : ℝ) + Complex.I))
          (w + (1 / 2 : ℝ) * y) ∂gaussianReal 0 1
        ∂Measure.dirac (-4 / 7 : ℝ)) -
      ∫ w, ∫ y : ℝ, iteratedDeriv 4
          (complexQuadraticExp ((3 / 4 : ℝ) + Complex.I))
          (w + (1 / 2 : ℝ) * y) ∂standardRademacherMeasure
        ∂Measure.dirac (-4 / 7 : ℝ) =
      (((1 / 2 : ℝ) ^ 4) / 12 : ℝ) •
        ∫ w, ∫ k : ℝ, iteratedDeriv 8
          (complexQuadraticExp ((3 / 4 : ℝ) + Complex.I))
          (w + (1 / 2 : ℝ) * k) ∂peanoKMeasure
        ∂Measure.dirac (-4 / 7 : ℝ) := by
  apply peanoIdentity4_partialSum_standardGaussianRademacher_scaled_iteratedDeriv_four
  · norm_num
  · exact integrable_dirac (by simp)
  · exact integrable_dirac (by simp)

set_option linter.style.longLine false in
run_cmd
  let allowed : Array Lean.Name :=
    #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Lean.Name :=
    #[``CertifiedJL.integrable_abs_evenPow_mul_exp_sq_peanoKMeasure,
      ``CertifiedJL.integrable_gaussianReal_sq_add_mul_norm_iteratedDeriv_all,
      ``CertifiedJL.integrable_cubicEnvelope_mul_norm_iteratedDeriv_all_of_re_lt_half,
      ``CertifiedJL.integrable_cubicEnvelope_mul_norm_iteratedDeriv_of_re_lt_half,
      ``CertifiedJL.iteratedDeriv_iteratedDeriv_add,
``CertifiedJL.peanoIdentity4_standardGaussianRademacher_iteratedDeriv_complexQuadraticExp_of_re_lt_half,
``CertifiedJL.peanoIdentity4_standardGaussianRademacher_scaled_iteratedDeriv_four_complexQuadraticExp,
      ``CertifiedJL.scaledFourthPeanoMajorant_exists,
      ``CertifiedJL.upperCutoffRemainder_weighted_fourthDeriv_integral_tendsto_of_re_lt_half,
      ``CertifiedJL.peanoIdentity4_standardGaussianRademacher_complexQuadraticExp_of_re_lt_half,
      ``CertifiedJL.iteratedDeriv_four_scaled_complexQuadraticExp,
      ``CertifiedJL.peanoIdentity4_standardGaussianRademacher_scaled_complexQuadraticExp,
      ``CertifiedJL.peanoIdentity4_standardGaussianRademacher_scaled_complexQuadraticExp_peanoK,
      ``CertifiedJL.peanoIdentity4_partialSum_standardGaussianRademacher_scaled,
      ``CertifiedJL.peanoIdentity4_partialSum_standardGaussianRademacher_scaled_iteratedDeriv_four]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    unless axioms.size == allowed.size &&
        axioms.all allowed.contains && allowed.all axioms.contains do
      throwError "unexpected axioms for {target}: {axioms}"

end CertifiedJL.Tests.PeanoGaussianRademacherScaled
