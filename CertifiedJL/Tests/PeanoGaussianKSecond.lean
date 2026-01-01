/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Peano.PeanoGaussianKSecond
import Lean.Util.CollectAxioms

/-! Mutation canaries for the Gaussian-to-K second-Peano replacement. -/

open MeasureTheory ProbabilityTheory Lean

namespace CertifiedJL.Tests.PeanoGaussianKSecond

/-- A shifted, nonreal, negative-scale canary in the positive strip. -/
example :
    (∫ y : ℝ, iteratedDeriv 4
          (complexQuadraticExp ((4 / 5 : ℝ) + 2 * Complex.I))
          ((2 / 3 : ℝ) + (-1 / 2 : ℝ) * y) ∂gaussianReal 0 1) -
      ∫ y : ℝ, iteratedDeriv 4
          (complexQuadraticExp ((4 / 5 : ℝ) + 2 * Complex.I))
          ((2 / 3 : ℝ) + (-1 / 2 : ℝ) * y) ∂peanoKMeasure =
      (-1 / 2 : ℝ) ^ 2 • ∫ t : ℝ,
        firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t •
          iteratedDeriv 6
            (complexQuadraticExp ((4 / 5 : ℝ) + 2 * Complex.I))
            ((2 / 3 : ℝ) + (-1 / 2 : ℝ) * t) := by
  apply peanoIdentity2_standardGaussian_peanoK_scaled_iteratedDeriv_four
  · norm_num
  · norm_num

/-- The zero-scale boundary is part of the public theorem. -/
example (s : ℂ) (w : ℝ) (hs0 : 0 ≤ s.re) :
    (∫ y : ℝ, iteratedDeriv 4 (complexQuadraticExp s) (w + 0 * y)
        ∂gaussianReal 0 1) -
      ∫ y : ℝ, iteratedDeriv 4 (complexQuadraticExp s) (w + 0 * y)
        ∂peanoKMeasure =
      (0 : ℝ) ^ 2 • ∫ t : ℝ,
        firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t •
          iteratedDeriv 6 (complexQuadraticExp s) (w + 0 * t) := by
  apply peanoIdentity2_standardGaussian_peanoK_scaled_iteratedDeriv_four w 0 hs0
  norm_num

set_option linter.style.longLine false in
run_cmd
  let allowed : Array Lean.Name :=
    #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Lean.Name :=
    #[``CertifiedJL.peanoIdentity2_standardGaussian_peanoK_iteratedDeriv_four,
      ``CertifiedJL.peanoIdentity2_standardGaussian_peanoK_scaled_iteratedDeriv_four,
      ``CertifiedJL.norm_partialSum_secondPeanoDifference_standardGaussian_peanoKMeasure_le_unconditional]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    unless axioms.size == allowed.size &&
        axioms.all allowed.contains && allowed.all axioms.contains do
      throwError "unexpected axioms for {target}: {axioms}"

end CertifiedJL.Tests.PeanoGaussianKSecond
