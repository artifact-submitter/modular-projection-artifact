/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperNormalization
import CertifiedJL.Model.Distributions.BalancedTernary.Duplication
import CertifiedJL.Analysis.Gaussian.ShiftedGaussianInversion

/-!
# Concrete sparse-row entrance to the upper hybrid comparison

This module identifies the actual sparse-row linear form with the duplicated
Rademacher sum used by the fourth-order replacement.  The result is stated at
both the PMF and quadratic-complex-MGF levels, so the later analytic telescope
does not need to restate a symbolic row MGF premise.
-/

open MeasureTheory ProbabilityTheory

namespace CertifiedJL

/-- A sparse-row dot product is pointwise the duplicated Rademacher sum with
coefficient `a i / 2` on each of the two sign copies. -/
theorem realRowDot_sparseRow_eq_rademacherSum
    {d : ℕ} (a : Fin d → ℝ) (seed : SparseRowSeed d) :
    realRowDot (sparseRow seed) a =
      rademacherSum (sparseUpperDuplicatedCoefficient a)
        (sparseRowSeedSigns seed) := by
  rw [realRowDot, rademacherSum, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, sparseUpperDuplicatedCoefficient,
    sparseRowSeedSigns]
  apply Finset.sum_congr rfl
  intro i _
  have hs := sparseBit_eq_average (seed i)
  have hsReal := congrArg (fun z : ℤ => (z : ℝ)) hs
  norm_num only [Int.cast_mul, Int.cast_add, Int.cast_ofNat] at hsReal
  simp only [sparseRow, if_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
  linear_combination (a i / 2) * hsReal

/-- The pushforward law of the actual sparse-row dot product is exactly the
law of the duplicated Rademacher sum. -/
theorem sparseRademacherRow_map_realRowDot_eq_rademacherSum
    {d : ℕ} (a : Fin d → ℝ) :
    (sparseRademacherRow d).map (fun row => realRowDot row a) =
      (rademacherPMF (Fin d × Fin 2)).map
        (rademacherSum (sparseUpperDuplicatedCoefficient a)) := by
  rw [sparseRademacherRow_eq_map_uniformRowSeed, PMF.map_comp]
  calc
    (PMF.uniformOfFintype (SparseRowSeed d)).map
        ((fun row => realRowDot row a) ∘ sparseRow) =
      (PMF.uniformOfFintype (SparseRowSeed d)).map
        (rademacherSum (sparseUpperDuplicatedCoefficient a) ∘
          sparseRowSeedSigns) := by
      congr 1
      funext seed
      exact realRowDot_sparseRow_eq_rademacherSum a seed
    _ = ((PMF.uniformOfFintype (SparseRowSeed d)).map
          sparseRowSeedSigns).map
        (rademacherSum (sparseUpperDuplicatedCoefficient a)) := by
      rw [PMF.map_comp]
    _ = (PMF.uniformOfFintype (Fin d × Fin 2 → Bool)).map
        (rademacherSum (sparseUpperDuplicatedCoefficient a)) := by
      rw [map_uniformSparseSeed_signs]
    _ = (rademacherPMF (Fin d × Fin 2)).map
        (rademacherSum (sparseUpperDuplicatedCoefficient a)) := by
      unfold rademacherPMF
      rw [uniformPiPMF_eq_uniformOfFintype]

/-- The actual sparse-row quadratic complex MGF is the finite duplicated-sign
expectation used at the entrance to the U7 hybrid telescope. -/
theorem quadraticComplexMGF_sparseRow_eq_rademacherSum
    {d : ℕ} (a : Fin d → ℝ) (s : ℂ) :
    quadraticComplexMGF (fun row : Fin d → ℤ => realRowDot row a)
        (sparseRademacherRow d).toMeasure s =
      ∫ bits, complexQuadraticExp s
          (rademacherSum (sparseUpperDuplicatedCoefficient a) bits)
        ∂(rademacherPMF (Fin d × Fin 2)).toMeasure := by
  let X : (Fin d → ℤ) → ℝ := fun row => realRowDot row a
  let Y : (Fin d × Fin 2 → Bool) → ℝ :=
    rademacherSum (sparseUpperDuplicatedCoefficient a)
  have hmap : (sparseRademacherRow d).map X =
      (rademacherPMF (Fin d × Fin 2)).map Y := by
    simpa only [X, Y] using sparseRademacherRow_map_realRowDot_eq_rademacherSum a
  have hX : Measurable X := measurable_of_countable _
  have hY : Measurable Y := measurable_of_finite _
  have hf : Continuous (complexQuadraticExp s) :=
    contDiff_complexQuadraticExp s |>.continuous
  unfold quadraticComplexMGF complexMGF
  simp only [complexQuadraticExp, Complex.ofReal_pow]
  change (∫ row, complexQuadraticExp s (X row)
      ∂(sparseRademacherRow d).toMeasure) = _
  calc
    (∫ row, complexQuadraticExp s (X row)
        ∂(sparseRademacherRow d).toMeasure) =
        ∫ x, complexQuadraticExp s x
          ∂Measure.map X (sparseRademacherRow d).toMeasure := by
      exact (integral_map hX.aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ x, complexQuadraticExp s x
          ∂((sparseRademacherRow d).map X).toMeasure := by
      rw [PMF.toMeasure_map X (sparseRademacherRow d) hX]
    _ = ∫ x, complexQuadraticExp s x
          ∂((rademacherPMF (Fin d × Fin 2)).map Y).toMeasure := by
      rw [hmap]
    _ = ∫ x, complexQuadraticExp s x
          ∂Measure.map Y (rademacherPMF (Fin d × Fin 2)).toMeasure := by
      rw [PMF.toMeasure_map Y (rademacherPMF (Fin d × Fin 2)) hY]
    _ = ∫ bits, complexQuadraticExp s (Y bits)
          ∂(rademacherPMF (Fin d × Fin 2)).toMeasure := by
      exact integral_map hY.aemeasurable hf.aestronglyMeasurable

end CertifiedJL
