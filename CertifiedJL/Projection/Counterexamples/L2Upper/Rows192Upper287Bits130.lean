/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.Counterexamples.L2Upper.Rows192GaussianComparison
import CertifiedJL.Projection.Counterexamples.L2Upper.FlatWitnessGeometry
import CertifiedJL.Projection.Counterexamples.L2Upper.EvenEndpoint
import CertifiedJL.Projection.Counterexamples.L2Upper.EvenRadialEndpoint

-- See the corresponding note in `GaussianComparison`.
set_option Elab.async false

/-!
# The 130-bit obstruction at the balanced-ternary upper endpoint

This module specializes the finite half-Gaussian mesh comparison to the
maintained 192-row endpoint.  The shape-96 Gamma tail at `287` remains above
`2⁻¹³⁰`; an explicit finite balanced-ternary experiment inherits that strict
lower bound.
-/

open scoped BigOperators ENNReal

open MeasureTheory

namespace CertifiedJL
open Probability
namespace Counterexamples.SparseUpper.Rows192.Internal

/-! ## Gaussian mass above the shifted endpoint -/

/-- Half-Gaussian vectors above the shifted threshold `287`. -/
abbrev gaussianRadialTail287 : Set (Fin 192 → ℝ) :=
  EvenRadialEndpoint.gaussianRadialTail 287

theorem measurableSet_gaussianRadialTail287 :
    MeasurableSet gaussianRadialTail287 :=
  EvenRadialEndpoint.measurableSet_gaussianRadialTail 287

theorem gaussianRadialTail287_eq_union :
    gaussianRadialTail287 =
      gaussianCore 287 ∪
        HalfGaussian192.halfGaussianTruncationSet
          (radialThreshold 287) coordinateBound := by
  change
    EvenRadialEndpoint.gaussianRadialTail 287 =
      EvenGaussian.Internal.gaussianCore 287 ∪
        Probability.HalfGaussianEven.halfGaussianTruncationSet
          (EvenGaussian.Internal.radialThreshold 287)
          EvenGaussian.Internal.coordinateBound
  exact EvenRadialEndpoint.gaussianRadialTail_eq_union 287

theorem gaussianCore287_disjoint_truncation :
    Disjoint (gaussianCore 287)
      (HalfGaussian192.halfGaussianTruncationSet
        (radialThreshold 287) coordinateBound) := by
  change Disjoint
    (EvenGaussian.Internal.gaussianCore 287)
    (Probability.HalfGaussianEven.halfGaussianTruncationSet
      (EvenGaussian.Internal.radialThreshold 287)
      EvenGaussian.Internal.coordinateBound)
  exact EvenRadialEndpoint.gaussianCore_disjoint_truncation 287

theorem integral_gaussianCore287_eq :
    (∫ x : Fin 192 → ℝ in gaussianCore 287,
        HalfGaussian192.halfGaussianProductDensity x) =
      gammaSurvivalNat 96 (radialThreshold 287) -
        ∫ x : Fin 192 → ℝ in
          HalfGaussian192.halfGaussianTruncationSet
            (radialThreshold 287) coordinateBound,
          HalfGaussian192.halfGaussianProductDensity x := by
  change
    (∫ x : Fin 192 → ℝ in
        EvenGaussian.Internal.gaussianCore 287,
        Probability.HalfGaussianEven.halfGaussianProductDensity x) =
      gammaSurvivalNat 96
          (EvenGaussian.Internal.radialThreshold 287) -
        ∫ x : Fin 192 → ℝ in
          Probability.HalfGaussianEven.halfGaussianTruncationSet
            (EvenGaussian.Internal.radialThreshold 287)
            EvenGaussian.Internal.coordinateBound,
          Probability.HalfGaussianEven.halfGaussianProductDensity x
  exact
    EvenRadialEndpoint.integral_gaussianCore_eq_gamma_sub_truncation
      287 (by norm_num) (by norm_num)
      (EvenGaussian.Internal.radialThreshold_nonneg 287)

theorem gammaShift287_lower :
    Real.exp (-radialShift) * gammaSurvivalNat 96 287 ≤
      gammaSurvivalNat 96 (radialThreshold 287) := by
  have h :=
    exp_neg_mul_gammaSurvivalNat_le 96
      (x := (287 : ℝ)) (δ := radialShift)
      (by norm_num) radialShift_nonneg
  simpa [radialThreshold] using h

/-- The elementary Taylor estimate used in the 192-row truncation bound. -/
theorem nine_lt_exp_53_24 :
    (9 : ℝ) < Real.exp (53 / 24) := by
  refine lt_of_lt_of_le ?_
    (Real.sum_le_exp_of_nonneg (x := (53 / 24 : ℝ)) (by norm_num) 8)
  simp_rw [Finset.sum_range_succ, Nat.factorial_succ]
  norm_num

/-- A rational lower bound for the exponential at the retained truncation
exponent. -/
theorem exp_212_gt :
    (192 : ℝ) * 100_000 * 2 ^ 130 * (5 / 2 : ℝ) ^ 96 <
      Real.exp 212 := by
  have hpow : (9 : ℝ) ^ 96 < Real.exp (53 / 24 : ℝ) ^ 96 :=
    pow_lt_pow_left₀ nine_lt_exp_53_24 (by norm_num) (by norm_num)
  rw [← Real.exp_nat_mul] at hpow
  have hpow' : (9 : ℝ) ^ 96 < Real.exp 212 := by
    convert hpow using 1
    all_goals norm_num
  have hrational :
      (192 : ℝ) * 100_000 * 2 ^ 130 * (5 / 2 : ℝ) ^ 96 <
        9 ^ 96 := by norm_num
  exact hrational.trans hpow'

/-- The exact aggregate mesh and local-limit loss is below the artifact
margin `1/18000`. -/
theorem totalLoss_lt_one_div_18000 :
    totalLoss < (1 / 18000 : ℝ) := by
  norm_num [totalLoss, radialShift, coordinateBound, mesh,
    localLoss, binomialLogStepError, cutoff, dimension, side]

theorem localLoss_nonneg : 0 ≤ localLoss := by
  norm_num [localLoss, binomialLogStepError,
    cutoff, dimension, side]

theorem exp_neg_totalLoss_gt :
    (17999 / 18000 : ℝ) < Real.exp (-totalLoss) := by
  have hexp : 1 - totalLoss ≤ Real.exp (-totalLoss) := by
    simpa only [sub_eq_add_neg, add_comm] using
      Real.add_one_le_exp (-totalLoss)
  linarith [totalLoss_lt_one_div_18000]

/-- The coordinate truncation loss is below the artifact margin
`10⁻⁵ · 2⁻¹³⁰`. -/
theorem truncationMass287_lt :
    (∫ x : Fin 192 → ℝ in
        HalfGaussian192.halfGaussianTruncationSet (radialThreshold 287) coordinateBound,
        HalfGaussian192.halfGaussianProductDensity x) <
      (1 / 100_000 : ℝ) * (2 : ℝ)⁻¹ ^ 130 := by
  have hscale :
      (Real.sqrt Real.pi)⁻¹ /
          ((2 / 5 : ℝ) * coordinateBound) <
        Real.sqrt (5 / 2 : ℝ) := by
    have hsqrtPi : (1 : ℝ) < Real.sqrt Real.pi := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num)
        (by linarith [Real.pi_gt_three])
    have hinv : (Real.sqrt Real.pi)⁻¹ < (1 : ℝ) :=
      inv_lt_one_of_one_lt₀ hsqrtPi
    have hden : (1 : ℝ) < (2 / 5 : ℝ) * coordinateBound := by
      norm_num [coordinateBound, mesh, side]
    have hleft :
        (Real.sqrt Real.pi)⁻¹ /
            ((2 / 5 : ℝ) * coordinateBound) < 1 := by
      rw [div_lt_one (lt_trans (by norm_num) hden)]
      exact hinv.trans hden
    have hright : (1 : ℝ) < Real.sqrt (5 / 2 : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    exact hleft.trans hright
  have hraw :=
    HalfGaussian192.integral_halfGaussianTruncationSet_lt
      (a := radialThreshold 287) (b := coordinateBound)
      coordinateBound_pos hscale
  have hexponent :
      212 <
        (3 * radialThreshold 287 + 2 * coordinateBound ^ 2) / 5 := by
    norm_num [radialThreshold, radialShift, coordinateBound, mesh, side]
  have hexpMono :
      Real.exp
          (-(3 * radialThreshold 287 + 2 * coordinateBound ^ 2) / 5) <
        Real.exp (-212) := by
    rw [Real.exp_lt_exp]
    linarith
  refine hraw.trans <|
    (mul_lt_mul_of_pos_left hexpMono (by positivity)).trans ?_
  rw [Real.exp_neg]
  have hexp212 : 0 < Real.exp (212 : ℝ) := Real.exp_pos _
  rw [show
      192 * (5 / 2 : ℝ) ^ 96 * (Real.exp 212)⁻¹ =
        (192 * (5 / 2 : ℝ) ^ 96) / Real.exp 212 by
      simp only [div_eq_mul_inv]]
  rw [div_lt_iff₀ hexp212]
  have htargetPos :
      0 < (1 / 100_000 : ℝ) * (2 : ℝ)⁻¹ ^ 130 := by positivity
  calc
    192 * (5 / 2 : ℝ) ^ 96 =
        ((1 / 100_000 : ℝ) * (2 : ℝ)⁻¹ ^ 130) *
          ((192 : ℝ) * 100_000 * 2 ^ 130 * (5 / 2 : ℝ) ^ 96) := by
      norm_num [inv_pow]
    _ < ((1 / 100_000 : ℝ) * (2 : ℝ)⁻¹ ^ 130) *
          Real.exp 212 :=
      mul_lt_mul_of_pos_left exp_212_gt htargetPos

/-- Scalar parameters used by the shared even-endpoint assembly. -/
noncomputable def endpointData : Counterexamples.SparseUpper.EvenEndpoint.TensorData where
  rows := 192
  bits := 130
  gammaFactor := 7 / 5
  truncationFactor := 1 / 100_000
  lossFloor := 17999 / 18000

theorem integral_gaussianCore287_gt :
    (∫ x : Fin 192 → ℝ in gaussianCore 287,
        HalfGaussian192.halfGaussianProductDensity x) >
      Real.exp (-radialShift) *
          ((7 / 5 : ℝ) * (2 : ℝ)⁻¹ ^ 130) -
        (1 / 100_000 : ℝ) * (2 : ℝ)⁻¹ ^ 130 := by
  simpa [endpointData] using
    (Counterexamples.SparseUpper.EvenEndpoint.coreMass_gt endpointData
      integral_gaussianCore287_eq gammaSurvivalNat_96_287_gt
      gammaShift287_lower truncationMass287_lt)

/-! ## Tensor lower bound -/

theorem tensorLowerBound287Bits130_gt :
    ENNReal.ofReal
        (Real.exp (-(192 : ℝ) * localLoss) *
          ∫ x : Fin 192 → ℝ in gaussianCore 287,
            HalfGaussian192.halfGaussianProductDensity x) >
      failureTarget 130 := by
  simpa [endpointData] using
    (Counterexamples.SparseUpper.EvenEndpoint.tensorLowerBound_gt endpointData
      localLoss_nonneg
      (by
        unfold totalLoss
        simp [endpointData]
        ring)
      integral_gaussianCore287_gt
      (by norm_num [endpointData])
      (by norm_num [endpointData])
      exp_neg_totalLoss_gt
      (by norm_num [endpointData]))

/-! ## Identification with the finite modular experiment -/

theorem counterexample287EventProbability_eq :
    eventProbability
        (sparseRademacherMatrix 192 rows192L2UpperCounterexampleDimension)
        (fun J =>
          modularProjectionSqNorm rows192L2UpperCounterexampleModulus J
              rows192L2UpperCounterexampleVector >
            287 * sqNorm rows192L2UpperCounterexampleVector) =
      sparseAllOnesRowSumsPMF.toMeasure
        {z | 287 * dimension < discreteSqNorm z} := by
  calc
    _ = sparseAllOnesRowSumsPMF.toMeasure
          {z | 287 * dimension <
            Counterexamples.SparseUpper.FlatWitness.rowSqNorm z} :=
      Counterexamples.SparseUpper.FlatWitness.eventProbability_eq_of_specialization
        rows192L2UpperCounterexampleVector sparseAllOnesRowSumsPMF
        (by rfl) (by rfl) sparseAllOnesRowSumsPMF_eq_map_uniformSeed
    _ = _ := by rfl

theorem rows192L2Upper287Bits130Counterexample_internal :
    Rows192L2Upper287Bits130CounterexampleStatement := by
  dsimp only [Rows192L2Upper287Bits130CounterexampleStatement]
  apply Counterexamples.SparseUpper.FlatWitness.counterexample_of_specialization
    rows192L2UpperCounterexampleVector (by rfl) (by rfl)
  · norm_num [rows192L2UpperCounterexampleDimension,
      rows192L2UpperCounterexampleSide]
  · rw [counterexample287EventProbability_eq]
    exact tensorLowerBound287Bits130_gt.trans_le (tensorComparison 287)

end Counterexamples.SparseUpper.Rows192.Internal

/-- At threshold `287`, an explicit finite 192-row balanced-ternary
experiment fails with probability strictly greater than `2⁻¹³⁰`. -/
theorem ternaryL2UpperRows192Threshold287Bits130Counterexample :
    Rows192L2Upper287Bits130CounterexampleStatement :=
  Counterexamples.SparseUpper.Rows192.Internal.rows192L2Upper287Bits130Counterexample_internal

end CertifiedJL
