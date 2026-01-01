/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.Counterexamples.L2Upper.ExperimentGeometry

-- See the corresponding note in `GaussianComparison`.
set_option Elab.async false

/-!
# The 130-bit obstruction at the balanced-ternary upper endpoint

This module reuses the finite half-Gaussian mesh comparison behind the
upper-336 endpoint obstruction.  At the proved upper endpoint `338`, the
shape-128 Gamma tail remains above `2⁻¹³⁰`; the finite balanced-ternary law
inherits that lower bound with a certified factor `3/2`.
-/

open scoped BigOperators ENNReal

open MeasureTheory

namespace CertifiedJL
open Probability
namespace Counterexamples.SparseUpper.Internal

/-! ## Gaussian mass above the shifted endpoint -/

/-- Half-Gaussian vectors above the shifted threshold `338`. -/
def gaussianRadialTail338 : Set (Fin 256 → ℝ) :=
  {x | radialThreshold 338 < squaredRadius x}

theorem measurableSet_gaussianRadialTail338 :
    MeasurableSet gaussianRadialTail338 := by
  unfold gaussianRadialTail338 squaredRadius
  exact measurableSet_lt measurable_const
    (Finset.measurable_sum _ fun j _ =>
      (measurable_pi_apply j).pow_const 2)

theorem gaussianRadialTail338_eq_union :
    gaussianRadialTail338 =
      gaussianCore 338 ∪
        halfGaussianTruncationSet
          (radialThreshold 338) coordinateBound := by
  ext x
  simp only [gaussianRadialTail338, gaussianCore,
    halfGaussianTruncationSet, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · intro hradial
    by_cases hcoord : ∀ j, |x j| < coordinateBound
    · exact Or.inl ⟨hradial, hcoord⟩
    · push Not at hcoord
      exact Or.inr ⟨hradial, hcoord⟩
  · rintro (h | h) <;> exact h.1

theorem gaussianCore338_disjoint_truncation :
    Disjoint (gaussianCore 338)
      (halfGaussianTruncationSet
        (radialThreshold 338) coordinateBound) := by
  rw [Set.disjoint_left]
  intro x hxCore hxTail
  obtain ⟨j, hj⟩ := hxTail.2
  exact (not_lt_of_ge hj) (hxCore.2 j)

theorem integral_gaussianCore338_eq :
    (∫ x : Fin 256 → ℝ in gaussianCore 338,
        halfGaussianProductDensity x) =
      gammaSurvivalNat 128 (radialThreshold 338) -
        ∫ x : Fin 256 → ℝ in
          halfGaussianTruncationSet
            (radialThreshold 338) coordinateBound,
          halfGaussianProductDensity x := by
  have hunion :=
    setIntegral_union gaussianCore338_disjoint_truncation
      (measurableSet_halfGaussianTruncationSet
        (radialThreshold 338) coordinateBound)
      integrable_halfGaussianProductDensity.integrableOn
      integrable_halfGaussianProductDensity.integrableOn
  rw [← gaussianRadialTail338_eq_union] at hunion
  have htail :
      (∫ x : Fin 256 → ℝ in gaussianRadialTail338,
          halfGaussianProductDensity x) =
        gammaSurvivalNat 128 (radialThreshold 338) := by
    simpa [gaussianRadialTail338, squaredRadius] using
      (integral_halfGaussianProductDensity_tail
        (radialThreshold_nonneg 338))
  rw [htail] at hunion
  linarith

theorem gammaShift338_lower :
    Real.exp (-radialShift) * gammaSurvivalNat 128 338 ≤
      gammaSurvivalNat 128 (radialThreshold 338) := by
  have h :=
    exp_neg_mul_gammaSurvivalNat_le 128
      (x := (338 : ℝ)) (δ := radialShift)
      (by norm_num) radialShift_nonneg
  simpa [radialThreshold] using h

/-- The coordinate truncation loss at `338` is at most the already-certified
loss at `336`, rewritten at the 130-bit scale. -/
theorem truncationMass338_lt :
    (∫ x : Fin 256 → ℝ in
        halfGaussianTruncationSet (radialThreshold 338) coordinateBound,
        halfGaussianProductDensity x) <
      (2 / 25 : ℝ) * (2 : ℝ)⁻¹ ^ 130 := by
  have hsubset :
      halfGaussianTruncationSet (radialThreshold 338) coordinateBound ⊆
        halfGaussianTruncationSet (radialThreshold 336) coordinateBound := by
    intro x hx
    refine ⟨?_, hx.2⟩
    unfold radialThreshold at hx ⊢
    norm_num at hx ⊢
    linarith [hx.1]
  have hmono :
      (∫ x : Fin 256 → ℝ in
          halfGaussianTruncationSet (radialThreshold 338) coordinateBound,
          halfGaussianProductDensity x) ≤
        ∫ x : Fin 256 → ℝ in
          halfGaussianTruncationSet (radialThreshold 336) coordinateBound,
          halfGaussianProductDensity x := by
    apply setIntegral_mono_set
      integrable_halfGaussianProductDensity.integrableOn
    · exact Filter.Eventually.of_forall fun x => by
        unfold halfGaussianProductDensity halfGaussianDensity
        positivity
    · exact Filter.Eventually.of_forall hsubset
  calc
    (∫ x : Fin 256 → ℝ in
        halfGaussianTruncationSet (radialThreshold 338) coordinateBound,
        halfGaussianProductDensity x) ≤
      ∫ x : Fin 256 → ℝ in
        halfGaussianTruncationSet (radialThreshold 336) coordinateBound,
        halfGaussianProductDensity x := hmono
    _ < (1 / 50 : ℝ) * (2 : ℝ)⁻¹ ^ 128 := truncationMass_lt
    _ = (2 / 25 : ℝ) * (2 : ℝ)⁻¹ ^ 130 := by
      norm_num [inv_pow]

theorem integral_gaussianCore338_gt :
    (∫ x : Fin 256 → ℝ in gaussianCore 338,
        halfGaussianProductDensity x) >
      Real.exp (-radialShift) *
          ((17 / 10 : ℝ) * (2 : ℝ)⁻¹ ^ 130) -
        (2 / 25 : ℝ) * (2 : ℝ)⁻¹ ^ 130 := by
  rw [integral_gaussianCore338_eq]
  have hgamma :
      Real.exp (-radialShift) *
          ((17 / 10 : ℝ) * (2 : ℝ)⁻¹ ^ 130) <
        Real.exp (-radialShift) *
          gammaSurvivalNat 128 338 :=
    mul_lt_mul_of_pos_left gammaSurvivalNat_128_338_gt
      (Real.exp_pos _)
  have hshift := gammaShift338_lower
  have htrunc := truncationMass338_lt
  linarith

/-! ## Tensor lower bound -/

theorem tensorLowerBound338Bits130_gt :
    ENNReal.ofReal
        (Real.exp (-(256 : ℝ) * localLoss) *
          ∫ x : Fin 256 → ℝ in gaussianCore 338,
            halfGaussianProductDensity x) >
      ((3 : ENNReal) / 2) * failureTarget 130 := by
  let target : ℝ := (2 : ℝ)⁻¹ ^ 130
  have hcore := integral_gaussianCore338_gt
  have hlocalExpPos :
      0 < Real.exp (-(256 : ℝ) * localLoss) :=
    Real.exp_pos _
  have hmul := mul_lt_mul_of_pos_left hcore hlocalExpPos
  have hlocalExpLe :
      Real.exp (-(256 : ℝ) * localLoss) ≤ 1 := by
    have harg : -(256 : ℝ) * localLoss ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by norm_num)
        localLoss_nonneg
    simpa using (Real.exp_le_exp.mpr harg)
  have hexpCombine :
      Real.exp (-(256 : ℝ) * localLoss) *
          Real.exp (-radialShift) =
        Real.exp (-totalLoss) := by
    rw [← Real.exp_add]
    unfold totalLoss
    congr 1
    ring
  have hreal :
      (3 / 2 : ℝ) * target <
        Real.exp (-(256 : ℝ) * localLoss) *
          ∫ x : Fin 256 → ℝ in gaussianCore 338,
            halfGaussianProductDensity x := by
    dsimp only [target]
    rw [mul_sub] at hmul
    rw [show
        Real.exp (-(256 : ℝ) * localLoss) *
            (Real.exp (-radialShift) *
              ((17 / 10 : ℝ) * (2 : ℝ)⁻¹ ^ 130)) =
          (Real.exp (-(256 : ℝ) * localLoss) *
              Real.exp (-radialShift)) *
            ((17 / 10 : ℝ) * (2 : ℝ)⁻¹ ^ 130) by ring] at hmul
    rw [hexpCombine] at hmul
    have htargetPos : 0 < (2 : ℝ)⁻¹ ^ 130 := by positivity
    have hmain :
        (17 / 10 : ℝ) * (14 / 15 : ℝ) *
              (2 : ℝ)⁻¹ ^ 130 -
            (2 / 25 : ℝ) * (2 : ℝ)⁻¹ ^ 130 <
          Real.exp (-totalLoss) *
              ((17 / 10 : ℝ) * (2 : ℝ)⁻¹ ^ 130) -
            Real.exp (-(256 : ℝ) * localLoss) *
              ((2 / 25 : ℝ) * (2 : ℝ)⁻¹ ^ 130) := by
      have hfirst :
          (17 / 10 : ℝ) * (14 / 15 : ℝ) *
                (2 : ℝ)⁻¹ ^ 130 <
            Real.exp (-totalLoss) *
              ((17 / 10 : ℝ) * (2 : ℝ)⁻¹ ^ 130) := by
        nlinarith [exp_neg_totalLoss_gt]
      have hsecond :
          Real.exp (-(256 : ℝ) * localLoss) *
                ((2 / 25 : ℝ) * (2 : ℝ)⁻¹ ^ 130) ≤
            (2 / 25 : ℝ) * (2 : ℝ)⁻¹ ^ 130 := by
        nlinarith
      linarith
    calc
      (3 / 2 : ℝ) * target <
          (17 / 10 : ℝ) * (14 / 15 : ℝ) *
              (2 : ℝ)⁻¹ ^ 130 -
            (2 / 25 : ℝ) * (2 : ℝ)⁻¹ ^ 130 := by
        dsimp only [target]
        nlinarith
      _ <
          Real.exp (-totalLoss) *
                ((17 / 10 : ℝ) * (2 : ℝ)⁻¹ ^ 130) -
            Real.exp (-(256 : ℝ) * localLoss) *
                ((2 / 25 : ℝ) * (2 : ℝ)⁻¹ ^ 130) := hmain
      _ <
          Real.exp (-(256 : ℝ) * localLoss) *
            ∫ x : Fin 256 → ℝ in gaussianCore 338,
              halfGaussianProductDensity x := hmul
  rw [failureTarget]
  have htargetENN :
      ENNReal.ofReal ((3 / 2 : ℝ) * target) =
        ((3 : ENNReal) / 2) * (2 : ENNReal)⁻¹ ^ 130 := by
    dsimp only [target]
    rw [ENNReal.ofReal_mul
      (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    rw [ENNReal.ofReal_div_of_pos
      (by norm_num : (0 : ℝ) < 2)]
    rw [ENNReal.ofReal_pow
      (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹) 130]
    rw [ENNReal.ofReal_inv_of_pos
      (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [← htargetENN]
  have hright :
      0 <
        Real.exp (-(256 : ℝ) * localLoss) *
          ∫ x : Fin 256 → ℝ in gaussianCore 338,
            halfGaussianProductDensity x := by
    have hleft : 0 < (3 / 2 : ℝ) * target := by
      dsimp only [target]
      positivity
    exact hleft.trans hreal
  exact (ENNReal.ofReal_lt_ofReal_iff hright).2 hreal

/-! ## Identification with the finite modular experiment -/

/-- The modular failure predicate at the proved endpoint `338`. -/
abbrev sparseUpper338MatrixFailure
    (J : Fin rowCount → Fin counterexampleDimension → ℤ) : Prop :=
  modularProjectionSqNorm counterexampleModulus J allOnesVector >
    338 * sqNorm allOnesVector

/-- The corresponding discrete row-sum predicate. -/
abbrev sparseUpper338RowSumFailure (z : Fin 256 → ℤ) : Prop :=
  338 * dimension < discreteSqNorm z

theorem sparseUpper338Failure_iff
    (seed : SparseSeed rowCount counterexampleDimension) :
    sparseUpper338MatrixFailure (sparseMatrix seed) ↔
      sparseUpper338RowSumFailure
        (fun j => sparseAllOnesRowSum (seed j)) := by
  unfold sparseUpper338MatrixFailure sparseUpper338RowSumFailure
  rw [modularProjectionSqNorm_sparseMatrix_counterexampleVector,
    sqNorm_allOnesVector]

theorem counterexample338EventProbability_eq :
    eventProbability
        (sparseRademacherMatrix rowCount counterexampleDimension)
        (fun J =>
          modularProjectionSqNorm counterexampleModulus J
              sparseUpperCounterexampleVector >
            338 * sqNorm sparseUpperCounterexampleVector) =
      sparseAllOnesRowSumsPMF.toMeasure
        {z | 338 * dimension < discreteSqNorm z} := by
  have hcompact :
    eventProbability
        (sparseRademacherMatrix rowCount counterexampleDimension)
        sparseUpper338MatrixFailure =
      sparseAllOnesRowSumsPMF.toMeasure
        {z | sparseUpper338RowSumFailure z} := by
    rw [sparseRademacherMatrix_eq_map_uniformSeed,
      sparseAllOnesRowSumsPMF_eq_map_uniformSeed,
      ← eventProbability_eq_toMeasure]
    exact eventProbability_map_congr _ _ _ _ _ sparseUpper338Failure_iff
  rw [show
      (fun J : Fin rowCount → Fin counterexampleDimension → ℤ =>
        modularProjectionSqNorm counterexampleModulus J
            sparseUpperCounterexampleVector >
          338 * sqNorm sparseUpperCounterexampleVector) =
        sparseUpper338MatrixFailure by
      funext J
      unfold sparseUpper338MatrixFailure
      rw [allOnesVector_eq_counterexampleVector],
    show
      {z : Fin 256 → ℤ | 338 * dimension < discreteSqNorm z} =
        {z | sparseUpper338RowSumFailure z} by rfl]
  exact hcompact

theorem sparseUpper338Bits130Counterexample_internal :
    SparseUpper338Bits130CounterexampleStatement := by
  dsimp only [SparseUpper338Bits130CounterexampleStatement]
  refine ⟨?_, ?_, ?_⟩
  · decide
  · intro hzero
    have hcoordinate := congrFun hzero
      (⟨0, by norm_num [counterexampleDimension, counterexampleSide]⟩ :
        Fin counterexampleDimension)
    norm_num [sparseUpperCounterexampleVector] at hcoordinate
  rw [counterexample338EventProbability_eq]
  exact tensorLowerBound338Bits130_gt.trans_le (tensorComparison 338)

end Counterexamples.SparseUpper.Internal

/-- At the proved upper endpoint `338`, an explicit finite balanced-ternary
experiment fails with probability greater than `(3/2) · 2⁻¹³⁰`. -/
theorem ternaryUpper338Bits130Counterexample :
    SparseUpper338Bits130CounterexampleStatement :=
  Counterexamples.SparseUpper.Internal.sparseUpper338Bits130Counterexample_internal

end CertifiedJL
