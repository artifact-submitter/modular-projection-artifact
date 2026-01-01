/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperPeanoProductLaws
import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperHybrid
import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpGaussianHalfIntegral

/-! # Concrete endpoints for the sparse upper Peano telescope -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace CertifiedJL

/-- The actual sparse-row quadratic MGF is exactly the all-Rademacher product
endpoint of the Peano telescope. -/
theorem quadraticComplexMGF_sparseRow_eq_pi_standardRademacher
    {d : ℕ} (a : Fin d → ℝ) (s : ℂ) :
    quadraticComplexMGF (fun row : Fin d → ℤ => realRowDot row a)
        (sparseRademacherRow d).toMeasure s =
      ∫ x : Fin d × Fin 2 → ℝ, complexQuadraticExp s
          (∑ i, sparseUpperDuplicatedCoefficient a i * x i)
        ∂Measure.pi (fun _ : Fin d × Fin 2 => standardRademacherMeasure) := by
  rw [quadraticComplexMGF_sparseRow_eq_rademacherSum]
  let b : Fin d × Fin 2 → ℝ := sparseUpperDuplicatedCoefficient a
  let F : ℝ → ℂ := complexQuadraticExp s
  have hF : AEStronglyMeasurable F
      (Measure.map (rademacherSum b)
        (rademacherPMF (Fin d × Fin 2)).toMeasure) :=
    (contDiff_complexQuadraticExp s).continuous.aestronglyMeasurable
  have hdot : Continuous
      (fun x : Fin d × Fin 2 → ℝ => ∑ i, b i * x i) := by
    apply continuous_finset_sum
    intro i hi
    exact continuous_const.mul (continuous_apply i)
  calc
    (∫ bits, F (rademacherSum b bits)
        ∂(rademacherPMF (Fin d × Fin 2)).toMeasure) =
        ∫ z, F z ∂Measure.map (rademacherSum b)
          (rademacherPMF (Fin d × Fin 2)).toMeasure := by
      exact (integral_map (measurable_of_finite _).aemeasurable hF).symm
    _ = ∫ z, F z ∂Measure.map
          (fun x : Fin d × Fin 2 → ℝ => ∑ i, b i * x i)
          (Measure.pi (fun _ : Fin d × Fin 2 =>
            standardRademacherMeasure)) := by
      rw [rademacherSum_map_eq_map_pi_standardRademacher]
    _ = ∫ x : Fin d × Fin 2 → ℝ, F (∑ i, b i * x i)
          ∂Measure.pi (fun _ : Fin d × Fin 2 =>
            standardRademacherMeasure) := by
      rw [integral_map hdot.measurable.aemeasurable
        (contDiff_complexQuadraticExp s).continuous.aestronglyMeasurable]

/-- The normalized all-Gaussian product endpoint is the exact Gaussian-half
quadratic MGF. -/
theorem integral_pi_gaussianReal_complexQuadraticExp_eq_gaussianHalf
    {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (hsq : ∑ i, b i ^ 2 = (1 / 2 : ℝ)) {s : ℂ} (hs : s.re < 1) :
    (∫ x : ι → ℝ, complexQuadraticExp s (∑ i, b i * x i)
        ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      (1 - s) ^ (-1 / 2 : ℂ) := by
  have hdot : Continuous (fun x : ι → ℝ => ∑ i, b i * x i) := by
    apply continuous_finset_sum
    intro i hi
    exact continuous_const.mul (continuous_apply i)
  rw [← integral_map hdot.measurable.aemeasurable
    (contDiff_complexQuadraticExp s).continuous.aestronglyMeasurable]
  rw [map_weightedSum_pi_gaussianReal_eq_gaussianHalf b hsq]
  exact integral_gaussianHalf_complexQuadraticExp hs

end CertifiedJL
