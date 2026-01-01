/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.Soundness
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.TailSoundness
import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperContour

/-!
# Sparse-matrix assembly for the centered-hybrid upper certificate

This module specializes the generic centered-hybrid inversion theorem to the
actual sparse signed Rademacher matrix and reduces the exact whole-line
contour to its positive-frequency half.
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace CertifiedJL
namespace SparseUpperHybrid

private theorem sparseMatrix_integrable {m d : ℕ}
    (f : (Fin m → Fin d → ℤ) → ℝ) :
    Integrable f (sparseRademacherMatrix m d).toMeasure := by
  rw [sparseRademacherMatrix_eq_map_uniformSeed]
  rw [← PMF.toMeasure_map
    (p := PMF.uniformOfFintype (SparseSeed m d))
    (f := sparseMatrix) (measurable_of_finite sparseMatrix)]
  apply (integrable_map_measure
    (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_finite sparseMatrix).aemeasurable).2
  exact Integrable.of_finite

private theorem sparseRow_integrable {d : ℕ}
    (f : (Fin d → ℤ) → ℝ) :
    Integrable f (sparseRademacherRow d).toMeasure := by
  rw [sparseRademacherRow_eq_map_uniformRowSeed]
  rw [← PMF.toMeasure_map
    (p := PMF.uniformOfFintype (SparseRowSeed d))
    (f := sparseRow) (measurable_of_finite sparseRow)]
  apply (integrable_map_measure
    (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_finite sparseRow).aemeasurable).2
  exact Integrable.of_finite

/-- Exact centered-hybrid contour norm after iid row factorization. -/
noncomputable def sparseHybridContourIntegrand {d : ℕ}
    (a : Fin d → ℝ) (box : ProfileBox) (frequency : ℝ) : ℝ :=
  ‖centeredUniformContourWeightN box.uniformCount
      (box.uniformHalfWidth : ℝ) (box.lam : ℝ)
      (shiftedGaussianContourWeight (gaussianSigma : ℝ) 0
        (threshold : ℝ) (box.lam : ℝ)) frequency‖ *
    ‖quadraticComplexMGF
      (fun row : Fin d → ℤ => realRowDot row a)
      (sparseRademacherRow d).toMeasure
      ((box.lam : ℝ) + frequency * Complex.I) ^ rows‖

/-- The exact sparse hybrid contour norm is absolutely integrable. -/
theorem integrable_sparseHybridContourIntegrand
    {d : ℕ} (a : Fin d → ℝ) (box : ProfileBox)
    (hh : 0 < (box.uniformHalfWidth : ℝ))
    (hlambda : 0 < (box.lam : ℝ)) :
    Integrable (sparseHybridContourIntegrand a box) := by
  let rowValue : (Fin d → ℤ) → ℝ := fun row => realRowDot row a
  let C : ℝ := mgf (fun row => rowValue row ^ 2)
    (sparseRademacherRow d).toMeasure (box.lam : ℝ) ^ rows
  have hweight : Integrable (fun frequency : ℝ =>
      centeredUniformContourWeightN box.uniformCount
        (box.uniformHalfWidth : ℝ) (box.lam : ℝ)
        (shiftedGaussianContourWeight (gaussianSigma : ℝ) 0
          (threshold : ℝ) (box.lam : ℝ)) frequency) :=
    integrable_centeredUniformContourWeightN hh hlambda
      (integrable_shiftedGaussianContourWeight hlambda
        (by norm_num [gaussianSigma])) box.uniformCount
  have hExp : integrableExpSet (fun row => rowValue row ^ 2)
      (sparseRademacherRow d).toMeasure = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    exact sparseRow_integrable _
  have hMGF : Continuous fun frequency : ℝ =>
      ‖quadraticComplexMGF rowValue (sparseRademacherRow d).toMeasure
        ((box.lam : ℝ) + frequency * Complex.I) ^ rows‖ := by
    have hcomplex : Continuous
        (complexMGF (fun row => rowValue row ^ 2)
          (sparseRademacherRow d).toMeasure) := by
      rw [continuous_iff_continuousAt]
      intro z
      exact (analyticAt_complexMGF (by rw [hExp]; simp)).continuousAt
    exact (((hcomplex.comp (by fun_prop)).pow rows).norm)
  refine (hweight.norm.const_mul C).mono'
    (hweight.norm.aestronglyMeasurable.mul hMGF.aestronglyMeasurable) ?_
  filter_upwards [] with frequency
  unfold sparseHybridContourIntegrand
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  calc
    _ ≤ ‖centeredUniformContourWeightN box.uniformCount
          (box.uniformHalfWidth : ℝ) (box.lam : ℝ)
          (shiftedGaussianContourWeight (gaussianSigma : ℝ) 0
            (threshold : ℝ) (box.lam : ℝ)) frequency‖ * C := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa [C, rowValue] using norm_quadraticComplexMGF_pow_le
        rowValue (sparseRademacherRow d).toMeasure
          ((box.lam : ℝ) + frequency * Complex.I) rows
    _ = _ := mul_comm _ _

/-- The centered-hybrid sparse contour has even modulus. -/
theorem even_sparseHybridContourIntegrand
    {d : ℕ} (a : Fin d → ℝ) (box : ProfileBox) :
    Function.Even (sparseHybridContourIntegrand a box) := by
  intro frequency
  unfold sparseHybridContourIntegrand
  rw [centeredUniformContourWeightN_apply,
    centeredUniformContourWeightN_apply]
  simp only [norm_mul, norm_pow]
  rw [norm_shiftedGaussianContourWeight_neg,
    norm_centeredUniformLaplace_neg]
  congr 2
  have harg : ((box.lam : ℝ) : ℂ) + ((-frequency : ℝ) : ℂ) * Complex.I =
      ((box.lam : ℝ) : ℂ) - (frequency : ℂ) * Complex.I := by
    rw [Complex.ofReal_neg]
    ring
  rw [harg]
  simpa using norm_quadraticComplexMGF_pow_neg_eq
    (fun row : Fin d → ℤ => realRowDot row a)
      (sparseRademacherRow d).toMeasure (box.lam : ℝ) frequency 1

/-- The exact whole-line sparse hybrid contour is twice its positive half. -/
theorem integral_sparseHybridContourIntegrand_eq_two_mul_Ioi
    {d : ℕ} (a : Fin d → ℝ) (box : ProfileBox)
    (hh : 0 < (box.uniformHalfWidth : ℝ))
    (hlambda : 0 < (box.lam : ℝ)) :
    (∫ frequency : ℝ, sparseHybridContourIntegrand a box frequency) =
      2 * ∫ frequency : ℝ in Set.Ioi 0,
        sparseHybridContourIntegrand a box frequency := by
  exact integral_eq_two_mul_integral_Ioi_of_even
    (integrable_sparseHybridContourIntegrand a box hh hlambda)
    (even_sparseHybridContourIntegrand a box)

/-- Fully semantic sparse-matrix specialization of centered-hybrid
inversion, already reduced to positive frequencies. -/
theorem sparseMatrix_toReal_le_positiveHybridContour
    {d : ℕ} (a : Fin d → ℝ) (box : ProfileBox)
    (hh : 0 < (box.uniformHalfWidth : ℝ))
    (hlambda : 0 < (box.lam : ℝ)) :
    (eventProbability (sparseRademacherMatrix rows d)
      (fun J => (threshold : ℝ) < realProjectionSqNorm a J)).toReal ≤
      2 * ∫ frequency : ℝ in Set.Ioi 0,
        sparseHybridContourIntegrand a box frequency := by
  let X : (Fin rows → Fin d → ℤ) → ℝ := realProjectionSqNorm a
  have hX : Measurable X := measurable_of_countable _
  have hsmooth : Integrable (fun J => centeredHybridSmoothing
      box.uniformCount (box.uniformHalfWidth : ℝ) (gaussianSigma : ℝ)
      (threshold : ℝ) (X J))
      (sparseRademacherMatrix rows d).toMeasure := sparseMatrix_integrable _
  have hreal : Integrable (fun J => Real.exp ((box.lam : ℝ) * X J))
      (sparseRademacherMatrix rows d).toMeasure := sparseMatrix_integrable _
  rw [eventProbability_eq_toMeasure]
  calc
    _ ≤ ∫ frequency : ℝ,
        ‖centeredUniformContourWeightN box.uniformCount
          (box.uniformHalfWidth : ℝ) (box.lam : ℝ)
          (shiftedGaussianContourWeight (gaussianSigma : ℝ) 0
            (threshold : ℝ) (box.lam : ℝ)) frequency‖ *
        ‖complexMGF X (sparseRademacherMatrix rows d).toMeasure
          ((box.lam : ℝ) + frequency * Complex.I)‖ := by
      exact measureReal_strictUpper_preimage_le_centeredHybridContour
        (sparseRademacherMatrix rows d).toMeasure hX hh
          (by norm_num [gaussianSigma]) hlambda box.uniformCount hsmooth hreal
    _ = ∫ frequency : ℝ, sparseHybridContourIntegrand a box frequency := by
      apply integral_congr_ae
      filter_upwards [] with frequency
      unfold sparseHybridContourIntegrand
      congr 1
      exact congrArg norm
        (complexMGF_realProjectionSqNorm_eq_pow a
          ((box.lam : ℝ) + frequency * Complex.I))
    _ = 2 * ∫ frequency : ℝ in Set.Ioi 0,
        sparseHybridContourIntegrand a box frequency :=
      integral_sparseHybridContourIntegrand_eq_two_mul_Ioi a box hh hlambda

/-- The exact real prefactor multiplying the positive-frequency deterministic
hybrid integrand after scaling by the `128`-bit target. -/
noncomputable def actualPrefactorValue (box : ProfileBox) : ℝ :=
  (2 ^ securityBits : ℝ) * (2 / Real.pi) *
    Real.exp (-((box.lam : ℝ) * (threshold : ℝ) -
      (gaussianSigma : ℝ) ^ 2 * (box.lam : ℝ) ^ 2 / 2)) *
    (1 / (1 - (box.lam : ℝ))) ^ (rows / 2)

/-- The exact factored contour integrand is bounded pointwise by the
certificate's deterministic row/uniform/Gaussian integrand. -/
theorem sparseHybridContourIntegrand_le_actual
    {d : ℕ} (a : Fin d → ℝ) (box : ProfileBox) (frequency : ℝ)
    (hnorm : ∑ i, a i ^ 2 = 1)
    (hfourth :
      Real.sqrt (1 - (box.lam : ℝ)) *
          ‖quadraticComplexMGF
            (fun row : Fin d → ℤ => realRowDot row a)
            (sparseRademacherRow d).toMeasure
            ((box.lam : ℝ) + frequency * Complex.I)‖ ≤
        sparseUpperFourthOrderNormalizedMajorant
          (sparseProfileFourthMoment a) (box.lam : ℝ) frequency)
    (hlam : 0 < (box.lam : ℝ)) (hlamOne : (box.lam : ℝ) < 1) :
    sparseHybridContourIntegrand a box frequency ≤
      ((1 / Real.pi) *
        Real.exp (-((box.lam : ℝ) * (threshold : ℝ) -
          (gaussianSigma : ℝ) ^ 2 * (box.lam : ℝ) ^ 2 / 2)) *
        (1 / Real.sqrt (1 - (box.lam : ℝ))) ^ rows) *
      actualHybridIntegrand box (sparseProfileFourthMoment a) frequency := by
  have hnormalized := normalized_rowMGF_le_contourRowMajorant
    a hlam.le hlamOne hnorm hfourth
  have hsqrt : 0 < Real.sqrt (1 - (box.lam : ℝ)) :=
    Real.sqrt_pos.2 (sub_pos.mpr hlamOne)
  have hnormLe :
      ‖quadraticComplexMGF
        (fun row : Fin d → ℤ => realRowDot row a)
        (sparseRademacherRow d).toMeasure
        ((box.lam : ℝ) + frequency * Complex.I)‖ ≤
      (1 / Real.sqrt (1 - (box.lam : ℝ))) *
        sparseUpperContourRowMajorant
          (sparseProfileFourthMoment a) (box.lam : ℝ) frequency := by
    rw [one_div, inv_mul_eq_div]
    exact (le_div_iff₀ hsqrt).2 (by simpa [mul_comm] using hnormalized)
  have hpow := pow_le_pow_left₀ (norm_nonneg _) hnormLe rows
  have hcommon : 0 ≤
      (1 / Real.pi) *
        Real.exp (-((box.lam : ℝ) * (threshold : ℝ) -
          (gaussianSigma : ℝ) ^ 2 * (box.lam : ℝ) ^ 2 / 2)) *
        Real.exp (-((gaussianSigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
        (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2)) *
        ‖centeredUniformLaplace (box.uniformHalfWidth : ℝ)
          (box.lam : ℝ) frequency‖ ^ box.uniformCount := by positivity
  unfold sparseHybridContourIntegrand actualHybridIntegrand
  rw [centeredUniformContourWeightN_apply, norm_mul, norm_pow,
    norm_pow, norm_shiftedGaussianContourWeight_eq_quadratureFactors]
  rw [standardGaussianCDF_zero]
  have hpiFactor : 1 / (2 * Real.pi * (1 / 2 : ℝ)) = 1 / Real.pi := by
    field_simp [Real.pi_ne_zero]
  rw [hpiFactor]
  simp only [zero_mul, sub_zero]
  calc
    _ ≤ (1 / Real.pi) *
        Real.exp (-((box.lam : ℝ) * (threshold : ℝ) -
          (gaussianSigma : ℝ) ^ 2 * (box.lam : ℝ) ^ 2 / 2)) *
        Real.exp (-((gaussianSigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
        (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2)) *
        ‖centeredUniformLaplace (box.uniformHalfWidth : ℝ)
          (box.lam : ℝ) frequency‖ ^ box.uniformCount *
        ((1 / Real.sqrt (1 - (box.lam : ℝ))) *
          sparseUpperContourRowMajorant
            (sparseProfileFourthMoment a) (box.lam : ℝ) frequency) ^ rows := by
      exact mul_le_mul_of_nonneg_left hpow hcommon
    _ = _ := by ring

/-- Complete semantic reduction from the sparse matrix event to the positive
deterministic hybrid integral and its exact scaled prefactor. -/
theorem scaled_sparseMatrix_toReal_le_actualHybridEndpoint
    {d : ℕ} (a : Fin d → ℝ) (box : ProfileBox)
    (hnorm : ∑ i, a i ^ 2 = 1)
    (hfourth : ∀ frequency : ℝ,
      Real.sqrt (1 - (box.lam : ℝ)) *
          ‖quadraticComplexMGF
            (fun row : Fin d → ℤ => realRowDot row a)
            (sparseRademacherRow d).toMeasure
            ((box.lam : ℝ) + frequency * Complex.I)‖ ≤
        sparseUpperFourthOrderNormalizedMajorant
          (sparseProfileFourthMoment a) (box.lam : ℝ) frequency)
    (hh : 0 < (box.uniformHalfWidth : ℝ))
    (hlam : 0 < (box.lam : ℝ)) (hlamOne : (box.lam : ℝ) < 1) :
    (2 ^ securityBits : ℝ) *
      (eventProbability (sparseRademacherMatrix rows d)
        (fun J => (threshold : ℝ) < realProjectionSqNorm a J)).toReal ≤
      actualPrefactorValue box *
        (∫ frequency : ℝ in Set.Ioi 0,
          actualHybridIntegrand box (sparseProfileFourthMoment a) frequency) := by
  have hevent := sparseMatrix_toReal_le_positiveHybridContour a box hh hlam
  have hcontourInt := integrable_sparseHybridContourIntegrand a box hh hlam
  have hprofileNonneg : 0 ≤ sparseProfileFourthMoment a := by
    unfold sparseProfileFourthMoment
    positivity
  have hactualNonneg : ∀ frequency : ℝ,
      0 ≤ actualHybridIntegrand box (sparseProfileFourthMoment a) frequency := by
    intro frequency
    unfold actualHybridIntegrand
    positivity [sparseUpperContourRowMajorant_nonneg
      (frequency := frequency) hprofileNonneg
      hlam.le hlamOne]
  have hactualInt := integrable_actualHybridIntegrand box
    (sparseProfileFourthMoment a) hprofileNonneg hh hlam hlamOne
  let coefficient : ℝ := (1 / Real.pi) *
    Real.exp (-((box.lam : ℝ) * (threshold : ℝ) -
      (gaussianSigma : ℝ) ^ 2 * (box.lam : ℝ) ^ 2 / 2)) *
    (1 / Real.sqrt (1 - (box.lam : ℝ))) ^ rows
  have hcoefficient : 0 ≤ coefficient := by
    dsimp only [coefficient]
    positivity
  have hintegral :
      (∫ frequency : ℝ in Set.Ioi 0,
        sparseHybridContourIntegrand a box frequency) ≤
      coefficient * (∫ frequency : ℝ in Set.Ioi 0,
        actualHybridIntegrand box (sparseProfileFourthMoment a) frequency) := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on hcontourInt.integrableOn
      (hactualInt.const_mul coefficient).integrableOn measurableSet_Ioi
    intro frequency _
    simpa only [coefficient] using
      sparseHybridContourIntegrand_le_actual a box frequency hnorm
        (hfourth frequency) hlam hlamOne
  have hevent' :
      (eventProbability (sparseRademacherMatrix rows d)
        (fun J => (threshold : ℝ) < realProjectionSqNorm a J)).toReal ≤
      2 * coefficient * (∫ frequency : ℝ in Set.Ioi 0,
        actualHybridIntegrand box (sparseProfileFourthMoment a) frequency) := by
    have htwice := mul_le_mul_of_nonneg_left hintegral (by norm_num : (0 : ℝ) ≤ 2)
    exact hevent.trans (by simpa only [mul_assoc] using htwice)
  calc
    _ ≤ (2 ^ securityBits : ℝ) *
        (2 * coefficient * (∫ frequency : ℝ in Set.Ioi 0,
          actualHybridIntegrand box
            (sparseProfileFourthMoment a) frequency)) :=
      mul_le_mul_of_nonneg_left hevent' (by positivity)
    _ = _ := by
      have hsqrtSq : Real.sqrt (1 - (box.lam : ℝ)) ^ 2 =
          1 - (box.lam : ℝ) := Real.sq_sqrt (sub_nonneg.mpr hlamOne.le)
      have hpow : (1 / Real.sqrt (1 - (box.lam : ℝ))) ^ rows =
          (1 / (1 - (box.lam : ℝ))) ^ (rows / 2) := by
        calc
          _ = ((1 / Real.sqrt (1 - (box.lam : ℝ))) ^ 2) ^ 128 := by
            simpa [rows] using pow_mul
              (1 / Real.sqrt (1 - (box.lam : ℝ))) 2 128
          _ = (1 / (1 - (box.lam : ℝ))) ^ 128 := by
            rw [div_pow, one_pow, hsqrtSq]
          _ = _ := by norm_num [rows]
      unfold actualPrefactorValue
      dsimp only [coefficient]
      rw [hpow]
      ring

end SparseUpperHybrid
end CertifiedJL
