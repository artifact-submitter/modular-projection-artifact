/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Unrestricted.Analytic

/-! # Mutation canaries for dominant analytic row bounds -/

open scoped BigOperators ENNReal

open MeasureTheory

namespace CertifiedJL.Tests.DominantAnalytic

open Probability

/-- Both shifted image orientations are pinned at unequal concrete values. -/
example :
    (∑' n : ℤ, if n = 0 then (0 : ℝ≥0∞) else
      ENNReal.ofReal (Real.exp (-(2 : ℝ) * ((n : ℝ) * 3 - 1) ^ 2))) ≤
      ENNReal.ofReal
        (Real.exp (-(2 : ℝ) * (3 - 1) ^ 2) /
            (1 - Real.exp (-(2 : ℝ) * (3 * 3 ^ 2 - 2 * 3))) +
          Real.exp (-(2 : ℝ) * (3 + 1) ^ 2) /
            (1 - Real.exp (-(2 : ℝ) * (3 * 3 ^ 2 + 2 * 3)))) := by
  exact integerShiftedGaussian_exp_nonzero_geometricTail 2 3
    (by norm_num) (by norm_num)

private def shiftedWrapWeights : Fin 2 → ℤ := fun i =>
  if i = 0 then -1 else 2

private def crossingActiveWeights : Fin 2 → ℤ := ![3, 2]

private def negativeCrossingActiveWeights : Fin 2 → ℤ := ![-3, 2]

private theorem crossingActive_hD
    (w : Fin 2 → ℤ) (hw : sqNorm w = 13) :
    (3 : ℝ) ≤ (11 : ℝ) / Real.sqrt (sqNorm w : ℝ) := by
  norm_num [hw]
  have hsqrt : Real.sqrt (13 : ℝ) ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg := Real.sqrt_nonneg (13 : ℝ)
  have hsqrt_pos := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 13)
  rw [le_div_iff₀ hsqrt_pos]
  nlinarith

/-- The sparse producer keeps non-unit `z`, amplitude, and modulus visible. -/
example :
    let u : ℝ := 5 / (3 : ℝ) ^ 2
    let B : ℝ := (11 : ℝ) / 3
    let alpha : ℝ := (2 / 3) / (1 + (2 / 3) * u)
    ENNReal.ofReal
        (∫ row, Real.exp
          (-(2 / 3 : ℝ) * ((centeredMod 11
            ((3 : ℤ) + ∑ i, row i * shiftedWrapWeights i : ℤ) : ℝ) / 3) ^ 2)
          ∂(sparseRademacherRow 2).toMeasure) ≤
      ENNReal.ofReal
        (∫ row, Real.exp
          (-(2 / 3 : ℝ) * ((((3 : ℤ) +
            ∑ i, row i * shiftedWrapWeights i : ℤ) : ℝ) / 3) ^ 2)
          ∂(sparseRademacherRow 2).toMeasure) +
      ENNReal.ofReal
        (Real.exp (-alpha * (B - 1) ^ 2) /
            (1 - Real.exp (-alpha * (3 * B ^ 2 - 2 * B))) +
          Real.exp (-alpha * (B + 1) ^ 2) /
            (1 - Real.exp (-alpha * (3 * B ^ 2 + 2 * B)))) := by
  apply sparseRow_shiftedNormalizedPeriodization_nonzeroImageBound
      shiftedWrapWeights 11 3 5 (2 / 3)
  · decide
  · norm_num
  · norm_num
  · norm_num [Fin.sum_univ_two, shiftedWrapWeights]
  · norm_num
  · norm_num

/-- The complete active scalar row consumes a cell crossing `1 / z`, with
non-unit tilt, amplitude, modulus, and unequal endpoints. -/
example :
    (∫ row, Real.exp
          (-(((2 / 3 : ℚ) : ℝ)) * ((centeredMod 11
            ((dominantAmplitude crossingActiveWeights (0 : Fin 2) : ℤ) +
              ∑ j, row j * dominantRemainderFinWeights
                crossingActiveWeights (0 : Fin 2) j : ℤ) : ℝ) /
                (dominantAmplitude crossingActiveWeights (0 : Fin 2) : ℝ)) ^ 2)
          ∂(sparseRademacherRow
            (Fintype.card (DominantRemainderIndex (0 : Fin 2)))).toMeasure) ≤
      dominantCellActiveRow (1 / 4) 2 (2 / 3) := by
  have hu : dominantResidualRatio crossingActiveWeights (0 : Fin 2) = 4 / 9 := by
    have hU : dominantRemainderSqNorm crossingActiveWeights (0 : Fin 2) = 4 := by
      decide
    rw [dominantResidualRatio, hU]
    norm_num [dominantAmplitude, crossingActiveWeights]
  have hmod : 3 * Real.sqrt (1 + (((1 / 4 : ℚ) : ℝ))) ≤
      (11 : ℝ) / (dominantAmplitude crossingActiveWeights (0 : Fin 2) : ℝ) := by
    have hsqrt : Real.sqrt (5 / 4 : ℝ) ^ 2 = 5 / 4 := by
      rw [Real.sq_sqrt]
      norm_num
    have hsqrt_nonneg := Real.sqrt_nonneg (5 / 4 : ℝ)
    norm_num [dominantAmplitude, crossingActiveWeights] at hsqrt ⊢
    nlinarith
  have h := dominantRemainderFin_active_le_cellRow crossingActiveWeights (0 : Fin 2)
    11 (1 / 4) 2 (2 / 3) (by decide) (by decide) (by norm_num)
    (by rw [hu]; norm_num) (by rw [hu]; norm_num) (by norm_num) hmod
  simpa only using h

/-- After `1 / z`, the left endpoint is the active Hsq maximum. -/
example :
    (((1 : ℚ) : ℝ) * Real.sqrt (5 / 2) /
      (1 + ((1 : ℚ) : ℝ) * (5 / 2))) ^ 2 ≤
      dominantCellHsq 2 3 1 := by
  exact dominantCellHsq_ge 2 3 1 (5 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- A cell crossing `1 / z` exercises the explicit critical-point branch. -/
example :
    (((1 : ℚ) : ℝ) * Real.sqrt 1 / (1 + ((1 : ℚ) : ℝ) * 1)) ^ 2 ≤
      dominantCellHsq (1 / 2) 2 1 := by
  exact dominantCellHsq_ge (1 / 2) 2 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Before `1 / z`, the right endpoint is the active Hsq maximum. -/
example :
    (((1 : ℚ) : ℝ) * Real.sqrt (1 / 4) /
      (1 + ((1 : ℚ) : ℝ) * (1 / 4))) ^ 2 ≤
      dominantCellHsq (1 / 10) (1 / 2) 1 := by
  exact dominantCellHsq_ge (1 / 10) (1 / 2) 1 (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- A nontrivial asymmetric endpoint interval consumes the complete rho bound. -/
example :
    let s : ℝ := (((2 / 3 : ℚ) : ℝ)) * (1 / 5)
    let h : ℝ := (((2 / 3 : ℚ) : ℝ)) * Real.sqrt (1 / 5) / (1 + s)
    min 1 (1 - s / 2 * (Real.cosh h)⁻¹ ^ 2 +
        3 * s ^ 2 + 4 * s ^ 2 * h ^ 4) ≤
      dominantCellRho (1 / 100) (3 / 10) (2 / 3) := by
  exact shiftedDominantRho_le_cell (1 / 100) (3 / 10) (2 / 3) (1 / 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Both active wrap orientations survive asymmetric endpoint enlargement. -/
example :
    let alpha : ℝ := (((2 / 3 : ℚ) : ℝ)) /
      (1 + (((2 / 3 : ℚ) : ℝ)) * (1 / 4))
    Real.exp (-alpha * (4 - 1) ^ 2) /
        (1 - Real.exp (-alpha * (3 * 4 ^ 2 - 2 * 4))) +
      Real.exp (-alpha * (4 + 1) ^ 2) /
        (1 - Real.exp (-alpha * (3 * 4 ^ 2 + 2 * 4))) ≤
      dominantCellActiveWrap (1 / 10) (1 / 2) (2 / 3) := by
  apply shiftedActiveWrap_le_cell (1 / 10) (1 / 2) (2 / 3) (1 / 4) 4
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · have hsqrt : Real.sqrt (11 / 10 : ℝ) ^ 2 = 11 / 10 := by
      rw [Real.sq_sqrt]
      norm_num
    have hsqrt_nonneg := Real.sqrt_nonneg (11 / 10 : ℝ)
    norm_num at hsqrt ⊢
    nlinarith

/-- Exact likelihood transport pins distinct signed coefficients and a
nonconstant integrand. -/
example :
    ∫ bits, Real.exp ((2 : ℝ) *
          rademacherSum (fun i : Fin 2 => if i = 0 then -1 else 3) bits) *
        (if bits 0 then 7 else 11) ∂(rademacherPMF (Fin 2)).toMeasure =
      (∏ i : Fin 2,
          Real.cosh ((2 : ℝ) * (if i = 0 then -1 else 3))) *
        ∫ bits, (if bits 0 then 7 else 11)
          ∂(biasedSignProductPMF
            (fun i : Fin 2 => (2 : ℝ) * (if i = 0 then -1 else 3))).toMeasure := by
  exact rademacherIntegral_exp_mul_eq_biasedSignProduct
    2 (fun i : Fin 2 => if i = 0 then -1 else 3)
      (fun bits => if bits 0 then 7 else 11)

/-- The normalizer bound consumes both unequal signed coordinates. -/
example :
    (∏ i : Fin 2, Real.cosh ((3 / 2 : ℝ) *
        (if i = 0 then -2 else 5))) ≤
      Real.exp ((3 / 2 : ℝ) ^ 2 *
        (∑ i : Fin 2, (if i = 0 then (-2 : ℝ) else 5) ^ 2) / 2) := by
  exact prod_cosh_le_exp_sum_sq
    (3 / 2) (fun i : Fin 2 => if i = 0 then -2 else 5)

/-- Exact tilted variance pins distinct tilt and coefficient vectors. -/
example :
    ∫ bits,
        (∑ i : Fin 2, (if i = 0 then (-3 : ℝ) else 5) *
          (biasedSignValue (bits i) -
            Real.tanh (if i = 0 then (1 : ℝ) else -2))) ^ 2
      ∂(biasedSignProductPMF
        (fun i : Fin 2 => if i = 0 then (1 : ℝ) else -2)).toMeasure =
      ∑ i : Fin 2, (if i = 0 then (-3 : ℝ) else 5) ^ 2 *
        (1 - Real.tanh (if i = 0 then (1 : ℝ) else -2) ^ 2) := by
  exact biasedSignProduct_centeredWeightedSumVariance
    (fun i : Fin 2 => if i = 0 then 1 else -2)
    (fun i : Fin 2 => if i = 0 then -3 else 5)

/-- The fourth-moment producer observes a proper support subset, so replacing
`S` by `univ` changes the conclusion. -/
example :
    ∫ bits,
        (∑ i ∈ ({0} : Finset (Fin 2)),
          (if i = 0 then (-3 : ℝ) else 5) *
            (biasedSignValue (bits i) -
              Real.tanh (if i = 0 then (1 : ℝ) else -2))) ^ 4
      ∂(biasedSignProductPMF
        (fun i : Fin 2 => if i = 0 then (1 : ℝ) else -2)).toMeasure ≤
      3 * (∑ i ∈ ({0} : Finset (Fin 2)),
        (if i = 0 then (-3 : ℝ) else 5) ^ 2) ^ 2 := by
  exact biasedSignProduct_centeredWeightedFourthMoment_le
    (fun i : Fin 2 => if i = 0 then 1 else -2)
    (fun i : Fin 2 => if i = 0 then -3 else 5) {0}

/-- The exact active Esscher producer accepts asymmetric signed coefficients. -/
example :
    ∫ row, Real.exp (-(2 / 3 : ℝ) *
        (1 + realRowDot row (fun j : Fin 2 => if j = 0 then -3 / 10 else 4 / 10)) ^ 2)
        ∂(sparseRademacherRow 2).toMeasure ≤
      Real.exp (-(2 / 3 : ℝ) / (1 + (2 / 3 : ℝ) * (1 / 4))) *
        min 1
          (1 - ((2 / 3 : ℝ) * (1 / 4)) / 2 *
              (Real.cosh ((2 / 3 : ℝ) * Real.sqrt (1 / 4) /
                (1 + (2 / 3 : ℝ) * (1 / 4))))⁻¹ ^ 2 +
            3 * ((2 / 3 : ℝ) * (1 / 4)) ^ 2 +
            4 * ((2 / 3 : ℝ) * (1 / 4)) ^ 2 *
              ((2 / 3 : ℝ) * Real.sqrt (1 / 4) /
                (1 + (2 / 3 : ℝ) * (1 / 4))) ^ 4) := by
  apply sparseRow_shiftedDominantRow
  · norm_num
  · norm_num
  · norm_num [Fin.sum_univ_two]

/-- The geometric comparison is directional and distinguishes its endpoints. -/
example :
    2 * Real.exp (-2) / (1 - (Real.exp (-2)) ^ 3) ≤
      2 * Real.exp (-1) / (1 - (Real.exp (-1)) ^ 3) := by
  exact twoSidedGeometricTail_antitone (by norm_num) (by norm_num)

/-- The scalar lobe producer directly exercises distinct actual and upper tilts. -/
example :
    sparseScalarF (1 / 100) 3 ≤
      1 / Real.sqrt (1 + (1 / 100 : ℝ)) *
        (1 + 2 * Real.exp (-Real.pi ^ 2 / (1 + (1 / 50 : ℝ))) /
          (1 - (Real.exp
            (-Real.pi ^ 2 / (1 + (1 / 50 : ℝ)))) ^ 3)) := by
  exact sparseScalarF_lobe_le_dominantCentral
    (by norm_num) (by norm_num) (by norm_num)

/-- Two unequal nonzero coordinates pin the support-product and `rpow` collapse. -/
example :
    ∏ j ∈ (Finset.univ : Finset (Fin 2)),
        gaussianCosineMoment (1 / 100)
          (2 / ((![2 / Real.sqrt 5, 1 / Real.sqrt 5] j : ℝ) ^ 2)) ^
            ((![2 / Real.sqrt 5, 1 / Real.sqrt 5] j : ℝ) ^ 2) ≤
      ENNReal.ofReal
        ((1 / Real.sqrt (1 + (1 / 200 : ℝ))) *
          (1 + 2 * Real.exp (-Real.pi ^ 2 / (1 + (1 / 50 : ℝ))) /
            (1 - (Real.exp
              (-Real.pi ^ 2 / (1 + (1 / 50 : ℝ)))) ^ 3))) := by
  let a : Fin 2 → ℝ := ![2 / Real.sqrt 5, 1 / Real.sqrt 5]
  have hsqrt : Real.sqrt (5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hnorm : ∑ j, a j ^ 2 = 1 := by
    simp only [a, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp [(Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 5)).ne', hsqrt]
    nlinarith [hsqrt]
  apply gaussianCosineProduct_le_dominantCentral a Finset.univ
  · intro j
    simp only [Finset.mem_univ, true_iff]
    fin_cases j <;> simp [a]
  · exact hnorm
  · norm_num
  · norm_num
  · norm_num
  · norm_num

private def negativeDominantWeights : Fin 2 → ℤ := ![-10, 1]

private def positiveDominantWeights : Fin 2 → ℤ := ![10, -1]

/-- Negative dominant coefficients retain the natural absolute-value scale. -/
example : dominantAmplitude negativeDominantWeights (0 : Fin 2) = 10 := by
  decide

/-- The non-unit scale bridge uses total norm, amplitude, and a nonzero remainder. -/
example {q : ℕ}
    (hD : (3 : ℝ) ≤ (q : ℝ) /
      Real.sqrt (sqNorm negativeDominantWeights : ℝ)) :
    3 * Real.sqrt (1 + (1 / 100 : ℝ)) ≤
      (q : ℝ) /
        (dominantAmplitude negativeDominantWeights (0 : Fin 2) : ℝ) := by
  have hU : dominantRemainderSqNorm negativeDominantWeights (0 : Fin 2) = 1 := by
    decide
  have hu : dominantResidualRatio negativeDominantWeights (0 : Fin 2) = 1 / 100 := by
    rw [dominantResidualRatio, hU]
    norm_num [dominantAmplitude, negativeDominantWeights]
  apply dominantAmplitude_modulus_lower negativeDominantWeights (0 : Fin 2)
    (by decide) hD (by norm_num)
  rw [hu]

end CertifiedJL.Tests.DominantAnalytic

#print axioms CertifiedJL.gaussianCosineProduct_le_dominantCentral
#print axioms CertifiedJL.integerShiftedGaussian_exp_nonzero_geometricTail
#print axioms CertifiedJL.sparseRow_shiftedNormalizedPeriodization_nonzeroImageBound
#print axioms CertifiedJL.shiftedDominantRow
#print axioms CertifiedJL.sparseRow_shiftedDominantRow
#print axioms CertifiedJL.dominantCellHsq_ge
#print axioms CertifiedJL.shiftedDominantRho_le_cell
#print axioms CertifiedJL.shiftedActiveWrap_le_cell
#print axioms CertifiedJL.dominantRemainderFin_active_le_cellRow
