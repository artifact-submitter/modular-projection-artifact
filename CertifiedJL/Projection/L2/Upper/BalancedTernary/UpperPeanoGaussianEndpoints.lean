/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperPeanoHGG

/-! # All-Gaussian endpoints of the sparse upper Peano telescope -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace CertifiedJL

/-- The all-Gaussian derivative-four hybrid stage is exactly the
variance-`1/2` Gaussian endpoint. -/
theorem upperPeanoHybridDerivFourValue_zero_eq_gaussianHalf
    {n : ℕ} (b : Fin n → ℝ) (s : ℂ)
    (hsq : ∑ i, b i ^ 2 = (1 / 2 : ℝ)) :
    upperPeanoHybridDerivFourValue b s 0 =
      ∫ x : ℝ, iteratedDeriv 4 (complexQuadraticExp s) x
        ∂gaussianReal 0 (2 : NNReal)⁻¹ := by
  have hlaw : upperPeanoHybridCoordinateLaw (n := n) 0 =
      fun _ : Fin n => gaussianReal 0 1 := by
    funext i
    simp [upperPeanoHybridCoordinateLaw]
  have hdot : Continuous (fun x : Fin n → ℝ => ∑ i, b i * x i) := by
    apply continuous_finsetSum
    intro i hi
    exact continuous_const.mul (continuous_apply i)
  rw [upperPeanoHybridDerivFourValue, hlaw]
  rw [← integral_map hdot.measurable.aemeasurable
    ((contDiff_complexQuadraticExp s).continuous_iteratedDeriv' 4
      |>.aestronglyMeasurable)]
  rw [map_weightedSum_pi_gaussianReal_eq_gaussianHalf b hsq]

/-- The all-Gaussian quadratic-exponential hybrid stage is exactly the
variance-`1/2` Gaussian endpoint. -/
theorem upperPeanoHybridValue_zero_eq_gaussianHalf
    {n : ℕ} (b : Fin n → ℝ) (s : ℂ)
    (hsq : ∑ i, b i ^ 2 = (1 / 2 : ℝ)) :
    upperPeanoHybridValue b s 0 =
      ∫ x : ℝ, complexQuadraticExp s x
        ∂gaussianReal 0 (2 : NNReal)⁻¹ := by
  rw [upperPeanoHybridValue_zero]
  have hdot : Continuous (fun x : Fin n → ℝ => ∑ i, b i * x i) := by
    apply continuous_finsetSum
    intro i hi
    exact continuous_const.mul (continuous_apply i)
  rw [← integral_map hdot.measurable.aemeasurable
    (contDiff_complexQuadraticExp s).continuous.aestronglyMeasurable]
  rw [map_weightedSum_pi_gaussianReal_eq_gaussianHalf b hsq]

/-- In the positive convergence half-plane, the all-Gaussian hybrid stage is
the literal Gaussian-half quadratic MGF. -/
theorem upperPeanoHybridValue_zero_eq_gaussianHalf_quadraticMGF
    {n : ℕ} (b : Fin n → ℝ) {s : ℂ}
    (hsq : ∑ i, b i ^ 2 = (1 / 2 : ℝ)) (hs : s.re < 1) :
    upperPeanoHybridValue b s 0 = (1 - s) ^ (-1 / 2 : ℂ) := by
  rw [upperPeanoHybridValue_zero]
  exact integral_pi_gaussianReal_complexQuadraticExp_eq_gaussianHalf b hsq hs

end CertifiedJL
