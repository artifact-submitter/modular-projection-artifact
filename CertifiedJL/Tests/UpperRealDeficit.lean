/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperRealDeficit

open scoped BigOperators
open MeasureTheory

namespace CertifiedJL.Tests

/-- The exact Gaussian/hyperbolic evaluator is pinned away from zero tilt. -/
example :
    (∫ x : ℝ, Real.exp ((1 - 2) * x ^ 2 / 2) *
        Real.cosh (3 * x) ^ 2 ∂ProbabilityTheory.gaussianReal 0 1) =
      (1 + Real.exp (2 * 3 ^ 2 / 2)) / (2 * Real.sqrt 2) := by
  exact integral_gaussianReal_exp_quadratic_mul_cosh_sq (by norm_num) 3

/-- A direct nonzero-profile consumer of the public U8 producer. -/
example :
    (∫ row, Real.exp ((1 / 2 : ℝ) *
        (realRowDot row (fun _ : Fin 1 => (1 : ℝ))) ^ 2)
        ∂(sparseRademacherRow 1).toMeasure) ≤
      (1 / Real.sqrt (1 - (1 / 2 : ℝ))) *
        realRowDeficitCap
          (Real.sqrt (sparseProfileFourthMoment
            (fun _ : Fin 1 => (1 : ℝ))) * (1 / 2) / (1 - 1 / 2)) := by
  apply realSparseRowDeficit
  · norm_num
  · norm_num
  · simp

/-- The abstract U8 interface pins asymmetric scale hypotheses and direction. -/
example (a : Fin 2 → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hnorm : ∑ i, a i ^ 2 = 1)
    (hbound : ∀ i, |a i| ≤ B) (hfourth : ∑ i, a i ^ 4 = B ^ 4) :
    (∫ row, Real.exp ((1 / 3 : ℝ) * (realRowDot row a) ^ 2)
        ∂(sparseRademacherRow 2).toMeasure) ≤
      (1 + Real.exp
        ((1 / 3 : ℝ) * B ^ 2 / (1 - 1 / 3 + (1 / 3) * B ^ 2))) /
        (2 * Real.sqrt (1 - 1 / 3 + (1 / 3) * B ^ 2)) := by
  exact sparseRow_positiveQuadratic_le_entropyEnvelope a
    (by norm_num) (by norm_num) hB hnorm hbound hfourth

/-- The cap direction used by left-endpoint profile boxes is pinned directly. -/
example : realRowDeficitCap (1 / 2) ≤ realRowDeficitCap (1 / 4) := by
  exact antitoneOn_realRowDeficitCap (by norm_num) (by norm_num) (by norm_num)

/-- The public profile bridge distinguishes `sqrt rho` from `rho`. -/
example :
    (∫ row, Real.exp ((1 / 3 : ℝ) *
        (realRowDot row ![(3 / 5 : ℝ), (4 / 5 : ℝ)]) ^ 2)
        ∂(sparseRademacherRow 2).toMeasure) ≤
      (1 / Real.sqrt (1 - (1 / 3 : ℝ))) *
        realRowDeficitCap
          (Real.sqrt (sparseProfileFourthMoment
            ![(3 / 5 : ℝ), (4 / 5 : ℝ)]) * (1 / 3) / (1 - 1 / 3)) := by
  exact
    (realSparseRowDeficit ![(3 / 5 : ℝ), (4 / 5 : ℝ)]
      (lambda := (1 / 3 : ℝ)) (by norm_num) (by norm_num) (by norm_num))

example : sparseProfileFourthMoment ![(3 / 5 : ℝ), (4 / 5 : ℝ)] = 337 / 625 := by
  norm_num [sparseProfileFourthMoment, Fin.sum_univ_two]

/-- The vertical-line modulus corollary is consumed at nonzero frequency. -/
example :
    ‖quadraticComplexMGF
        (fun row => realRowDot row ![(3 / 5 : ℝ), (4 / 5 : ℝ)])
        (sparseRademacherRow 2).toMeasure ((1 / 3 : ℝ) + 2 * Complex.I)‖ ≤
      (1 / Real.sqrt (1 - (1 / 3 : ℝ))) *
        realRowDeficitCap
          (Real.sqrt (sparseProfileFourthMoment
            ![(3 / 5 : ℝ), (4 / 5 : ℝ)]) * (1 / 3) / (1 - 1 / 3)) := by
  exact
    (norm_sparseRow_quadraticComplexMGF_le_realDeficit
      ![(3 / 5 : ℝ), (4 / 5 : ℝ)]
      (lambda := (1 / 3 : ℝ)) (u := 2)
      (by norm_num) (by norm_num) (by norm_num))

end CertifiedJL.Tests
