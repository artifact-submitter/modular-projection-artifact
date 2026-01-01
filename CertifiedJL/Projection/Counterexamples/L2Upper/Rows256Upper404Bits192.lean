/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.Counterexamples.L2Upper.Rows256GaussianComparison
import CertifiedJL.Projection.Counterexamples.L2Upper.FlatWitnessGeometry
import CertifiedJL.Projection.Counterexamples.L2Upper.EvenEndpoint
import CertifiedJL.Projection.Counterexamples.L2Upper.EvenRadialEndpoint
import CertifiedJL.Analysis.Gaussian.HighSecurityUpperGamma

-- See the corresponding note in `GaussianComparison`.
set_option Elab.async false

/-!
# The 192-bit obstruction at the balanced-ternary upper endpoint

This module specializes the finite half-Gaussian mesh comparison to the
maintained 256-row endpoint.  The shape-128 Gamma tail at `404` remains above
`2⁻¹⁹²`; an explicit finite balanced-ternary experiment inherits that strict
lower bound.
-/

open scoped BigOperators ENNReal

open MeasureTheory

namespace CertifiedJL
open Probability
namespace Counterexamples.SparseUpper.Rows256.Internal

/-! ## Gaussian mass above the shifted endpoint -/

/-- Half-Gaussian vectors above the shifted threshold `404`. -/
abbrev gaussianRadialTail404 : Set (Fin 256 → ℝ) :=
  EvenRadialEndpoint.gaussianRadialTail 404

theorem measurableSet_gaussianRadialTail404 :
    MeasurableSet gaussianRadialTail404 :=
  EvenRadialEndpoint.measurableSet_gaussianRadialTail 404

theorem gaussianRadialTail404_eq_union :
    gaussianRadialTail404 =
      gaussianCore 404 ∪
        halfGaussianTruncationSet
          (radialThreshold 404) coordinateBound := by
  change
    EvenRadialEndpoint.gaussianRadialTail 404 =
      EvenGaussian.Internal.gaussianCore 404 ∪
        Probability.HalfGaussianEven.halfGaussianTruncationSet
          (EvenGaussian.Internal.radialThreshold 404)
          EvenGaussian.Internal.coordinateBound
  exact EvenRadialEndpoint.gaussianRadialTail_eq_union 404

theorem gaussianCore404_disjoint_truncation :
    Disjoint (gaussianCore 404)
      (halfGaussianTruncationSet
        (radialThreshold 404) coordinateBound) := by
  change Disjoint
    (EvenGaussian.Internal.gaussianCore 404)
    (Probability.HalfGaussianEven.halfGaussianTruncationSet
      (EvenGaussian.Internal.radialThreshold 404)
      EvenGaussian.Internal.coordinateBound)
  exact EvenRadialEndpoint.gaussianCore_disjoint_truncation 404

theorem integral_gaussianCore404_eq :
    (∫ x : Fin 256 → ℝ in gaussianCore 404,
        halfGaussianProductDensity x) =
      gammaSurvivalNat 128 (radialThreshold 404) -
        ∫ x : Fin 256 → ℝ in
          halfGaussianTruncationSet
            (radialThreshold 404) coordinateBound,
          halfGaussianProductDensity x := by
  change
    (∫ x : Fin 256 → ℝ in
        EvenGaussian.Internal.gaussianCore 404,
        Probability.HalfGaussianEven.halfGaussianProductDensity x) =
      gammaSurvivalNat 128
          (EvenGaussian.Internal.radialThreshold 404) -
        ∫ x : Fin 256 → ℝ in
          Probability.HalfGaussianEven.halfGaussianTruncationSet
            (EvenGaussian.Internal.radialThreshold 404)
            EvenGaussian.Internal.coordinateBound,
          Probability.HalfGaussianEven.halfGaussianProductDensity x
  exact
    EvenRadialEndpoint.integral_gaussianCore_eq_gamma_sub_truncation
      404 (by norm_num) (by norm_num)
      (EvenGaussian.Internal.radialThreshold_nonneg 404)

theorem gammaShift404_lower :
    Real.exp (-radialShift) * gammaSurvivalNat 128 404 ≤
      gammaSurvivalNat 128 (radialThreshold 404) := by
  have h :=
    exp_neg_mul_gammaSurvivalNat_le 128
      (x := (404 : ℝ)) (δ := radialShift)
      (by norm_num) radialShift_nonneg
  simpa [radialThreshold] using h

/-- The elementary Taylor estimate used in the 256-row truncation bound. -/
theorem nine_lt_exp_141_64 :
    (9 : ℝ) < Real.exp (141 / 64) := by
  refine lt_of_lt_of_le ?_
    (Real.sum_le_exp_of_nonneg (x := (141 / 64 : ℝ)) (by norm_num) 8)
  simp_rw [Finset.sum_range_succ, Nat.factorial_succ]
  norm_num

/-- A rational lower bound for the exponential at the retained truncation
exponent. -/
theorem exp_282_gt :
    (256 : ℝ) * 1_000_000 * 2 ^ 192 * (5 / 2 : ℝ) ^ 128 <
      Real.exp 282 := by
  have hpow : (9 : ℝ) ^ 128 < Real.exp (141 / 64 : ℝ) ^ 128 :=
    pow_lt_pow_left₀ nine_lt_exp_141_64 (by norm_num) (by norm_num)
  rw [← Real.exp_nat_mul] at hpow
  have hpow' : (9 : ℝ) ^ 128 < Real.exp 282 := by
    convert hpow using 1
    all_goals norm_num
  have hrational :
      (256 : ℝ) * 1_000_000 * 2 ^ 192 * (5 / 2 : ℝ) ^ 128 <
        9 ^ 128 := by norm_num
  exact hrational.trans hpow'

/-- The exact aggregate mesh and local-limit loss is below the artifact
margin `1/9000`. -/
theorem totalLoss_lt_one_div_9000 :
    totalLoss < (1 / 9000 : ℝ) := by
  norm_num [totalLoss, radialShift, coordinateBound, mesh,
    localLoss, binomialLogStepError, cutoff, dimension, side]

theorem localLoss_nonneg : 0 ≤ localLoss := by
  norm_num [localLoss, binomialLogStepError,
    cutoff, dimension, side]

theorem exp_neg_totalLoss_gt :
    (8999 / 9000 : ℝ) < Real.exp (-totalLoss) := by
  have hexp : 1 - totalLoss ≤ Real.exp (-totalLoss) := by
    simpa only [sub_eq_add_neg, add_comm] using
      Real.add_one_le_exp (-totalLoss)
  linarith [totalLoss_lt_one_div_9000]

/-- The coordinate truncation loss is below the artifact margin
`10⁻⁶ · 2⁻¹⁹²`. -/
theorem truncationMass404_lt :
    (∫ x : Fin 256 → ℝ in
        halfGaussianTruncationSet (radialThreshold 404) coordinateBound,
        halfGaussianProductDensity x) <
      (1 / 1_000_000 : ℝ) * (2 : ℝ)⁻¹ ^ 192 := by
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
    integral_halfGaussianTruncationSet_lt
      (a := radialThreshold 404) (b := coordinateBound)
      coordinateBound_pos hscale
  have hexponent :
      282 <
        (3 * radialThreshold 404 + 2 * coordinateBound ^ 2) / 5 := by
    norm_num [radialThreshold, radialShift, coordinateBound, mesh, side]
  have hexpMono :
      Real.exp
          (-(3 * radialThreshold 404 + 2 * coordinateBound ^ 2) / 5) <
        Real.exp (-282) := by
    rw [Real.exp_lt_exp]
    linarith
  refine hraw.trans <|
    (mul_lt_mul_of_pos_left hexpMono (by positivity)).trans ?_
  rw [Real.exp_neg]
  have hexp282 : 0 < Real.exp (282 : ℝ) := Real.exp_pos _
  rw [show
      256 * (5 / 2 : ℝ) ^ 128 * (Real.exp 282)⁻¹ =
        (256 * (5 / 2 : ℝ) ^ 128) / Real.exp 282 by
      simp only [div_eq_mul_inv]]
  rw [div_lt_iff₀ hexp282]
  have htargetPos :
      0 < (1 / 1_000_000 : ℝ) * (2 : ℝ)⁻¹ ^ 192 := by positivity
  calc
    256 * (5 / 2 : ℝ) ^ 128 =
        ((1 / 1_000_000 : ℝ) * (2 : ℝ)⁻¹ ^ 192) *
          ((256 : ℝ) * 1_000_000 * 2 ^ 192 * (5 / 2 : ℝ) ^ 128) := by
      norm_num [inv_pow]
    _ < ((1 / 1_000_000 : ℝ) * (2 : ℝ)⁻¹ ^ 192) *
          Real.exp 282 :=
      mul_lt_mul_of_pos_left exp_282_gt htargetPos

/-- Scalar parameters used by the shared even-endpoint assembly. -/
noncomputable def endpointData : Counterexamples.SparseUpper.EvenEndpoint.TensorData where
  rows := 256
  bits := 192
  gammaFactor := 1089 / 1000
  truncationFactor := 1 / 1_000_000
  lossFloor := 8999 / 9000

theorem integral_gaussianCore404_gt :
    (∫ x : Fin 256 → ℝ in gaussianCore 404,
        halfGaussianProductDensity x) >
      Real.exp (-radialShift) *
          ((1089 / 1000 : ℝ) * (2 : ℝ)⁻¹ ^ 192) -
        (1 / 1_000_000 : ℝ) * (2 : ℝ)⁻¹ ^ 192 := by
  simpa [endpointData] using
    (Counterexamples.SparseUpper.EvenEndpoint.coreMass_gt endpointData
      integral_gaussianCore404_eq
      gammaRows256Threshold404Bits192_verified gammaShift404_lower
      truncationMass404_lt)

/-! ## Tensor lower bound -/

theorem tensorLowerBound404Bits192_gt :
    ENNReal.ofReal
        (Real.exp (-(256 : ℝ) * localLoss) *
          ∫ x : Fin 256 → ℝ in gaussianCore 404,
            halfGaussianProductDensity x) >
      failureTarget 192 := by
  simpa [endpointData] using
    (Counterexamples.SparseUpper.EvenEndpoint.tensorLowerBound_gt endpointData
      localLoss_nonneg
      (by
        unfold totalLoss
        simp [endpointData]
        ring)
      integral_gaussianCore404_gt
      (by norm_num [endpointData])
      (by norm_num [endpointData])
      exp_neg_totalLoss_gt
      (by norm_num [endpointData]))

/-! ## Identification with the finite modular experiment -/

theorem counterexample404EventProbability_eq :
    eventProbability
        (sparseRademacherMatrix 256 highSecurityL2UpperCounterexampleDimension)
        (fun J =>
          modularProjectionSqNorm highSecurityL2UpperCounterexampleModulus J
              highSecurityL2UpperCounterexampleVector >
            404 * sqNorm highSecurityL2UpperCounterexampleVector) =
      sparseAllOnesRowSumsPMF.toMeasure
        {z | 404 * dimension < discreteSqNorm z} := by
  calc
    _ = sparseAllOnesRowSumsPMF.toMeasure
          {z | 404 * dimension <
            Counterexamples.SparseUpper.FlatWitness.rowSqNorm z} :=
      Counterexamples.SparseUpper.FlatWitness.eventProbability_eq_of_specialization
        highSecurityL2UpperCounterexampleVector sparseAllOnesRowSumsPMF
        (by rfl) (by rfl) sparseAllOnesRowSumsPMF_eq_map_uniformSeed
    _ = _ := by rfl

theorem rows256L2Upper404Bits192Counterexample_internal :
    Rows256L2Upper404Bits192CounterexampleStatement := by
  dsimp only [Rows256L2Upper404Bits192CounterexampleStatement]
  apply Counterexamples.SparseUpper.FlatWitness.counterexample_of_specialization
    highSecurityL2UpperCounterexampleVector (by rfl) (by rfl)
  · norm_num [highSecurityL2UpperCounterexampleDimension,
      highSecurityL2UpperCounterexampleSide]
  · rw [counterexample404EventProbability_eq]
    exact tensorLowerBound404Bits192_gt.trans_le (tensorComparison 404)

end Counterexamples.SparseUpper.Rows256.Internal

/-- At threshold `404`, an explicit finite 256-row balanced-ternary
experiment fails with probability strictly greater than `2⁻¹⁹²`. -/
theorem ternaryL2UpperRows256Threshold404Bits192Counterexample :
    Rows256L2Upper404Bits192CounterexampleStatement :=
  Counterexamples.SparseUpper.Rows256.Internal.rows256L2Upper404Bits192Counterexample_internal

end CertifiedJL
