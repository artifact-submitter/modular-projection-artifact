/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.Counterexamples.L2Upper.Rows512GaussianComparison
import CertifiedJL.Projection.Counterexamples.L2Upper.FlatWitnessGeometry
import CertifiedJL.Projection.Counterexamples.L2Upper.EvenEndpoint
import CertifiedJL.Projection.Counterexamples.L2Upper.EvenRadialEndpoint
import CertifiedJL.Analysis.Gaussian.HighSecurityUpperGamma

-- See the corresponding note in `GaussianComparison`.
set_option Elab.async false

/-!
# The 256-bit obstruction at the balanced-ternary upper endpoint

This module specializes the finite half-Gaussian mesh comparison to the
maintained 512-row endpoint.  The shape-256 Gamma tail at `678` remains above
`2⁻²⁵⁶`; an explicit finite balanced-ternary experiment inherits that strict
lower bound.
-/

open scoped BigOperators ENNReal

open MeasureTheory

namespace CertifiedJL
open Probability
namespace Counterexamples.SparseUpper.Rows512.Internal.Threshold678

/-! ## Gaussian mass above the shifted endpoint -/

/-- Half-Gaussian vectors above the shifted threshold `678`. -/
abbrev gaussianRadialTail678 : Set (Fin 512 → ℝ) :=
  EvenRadialEndpoint.gaussianRadialTail 678

theorem measurableSet_gaussianRadialTail678 :
    MeasurableSet gaussianRadialTail678 :=
  EvenRadialEndpoint.measurableSet_gaussianRadialTail 678

theorem gaussianRadialTail678_eq_union :
    gaussianRadialTail678 =
      gaussianCore 678 ∪
        HalfGaussian512.halfGaussianTruncationSet
          (radialThreshold 678) coordinateBound := by
  change
    EvenRadialEndpoint.gaussianRadialTail 678 =
      EvenGaussian.Internal.gaussianCore 678 ∪
        Probability.HalfGaussianEven.halfGaussianTruncationSet
          (EvenGaussian.Internal.radialThreshold 678)
          EvenGaussian.Internal.coordinateBound
  exact EvenRadialEndpoint.gaussianRadialTail_eq_union 678

theorem gaussianCore678_disjoint_truncation :
    Disjoint (gaussianCore 678)
      (HalfGaussian512.halfGaussianTruncationSet
        (radialThreshold 678) coordinateBound) := by
  change Disjoint
    (EvenGaussian.Internal.gaussianCore 678)
    (Probability.HalfGaussianEven.halfGaussianTruncationSet
      (EvenGaussian.Internal.radialThreshold 678)
      EvenGaussian.Internal.coordinateBound)
  exact EvenRadialEndpoint.gaussianCore_disjoint_truncation 678

theorem integral_gaussianCore678_eq :
    (∫ x : Fin 512 → ℝ in gaussianCore 678,
        HalfGaussian512.halfGaussianProductDensity x) =
      gammaSurvivalNat 256 (radialThreshold 678) -
        ∫ x : Fin 512 → ℝ in
          HalfGaussian512.halfGaussianTruncationSet
            (radialThreshold 678) coordinateBound,
          HalfGaussian512.halfGaussianProductDensity x := by
  change
    (∫ x : Fin 512 → ℝ in
        EvenGaussian.Internal.gaussianCore 678,
        Probability.HalfGaussianEven.halfGaussianProductDensity x) =
      gammaSurvivalNat 256
          (EvenGaussian.Internal.radialThreshold 678) -
        ∫ x : Fin 512 → ℝ in
          Probability.HalfGaussianEven.halfGaussianTruncationSet
            (EvenGaussian.Internal.radialThreshold 678)
            EvenGaussian.Internal.coordinateBound,
          Probability.HalfGaussianEven.halfGaussianProductDensity x
  exact
    EvenRadialEndpoint.integral_gaussianCore_eq_gamma_sub_truncation
      678 (by norm_num) (by norm_num)
      (EvenGaussian.Internal.radialThreshold_nonneg 678)

theorem gammaShift678_lower :
    Real.exp (-radialShift) * gammaSurvivalNat 256 678 ≤
      gammaSurvivalNat 256 (radialThreshold 678) := by
  have h :=
    exp_neg_mul_gammaSurvivalNat_le 256
      (x := (678 : ℝ)) (δ := radialShift)
      (by norm_num) radialShift_nonneg
  simpa [radialThreshold] using h

/-- The elementary Taylor estimate used in the 512-row truncation bound. -/
theorem fivePointSeven_lt_exp_223_128 :
    (57 / 10 : ℝ) < Real.exp (223 / 128) := by
  refine lt_of_lt_of_le ?_
    (Real.sum_le_exp_of_nonneg (x := (223 / 128 : ℝ)) (by norm_num) 8)
  simp_rw [Finset.sum_range_succ, Nat.factorial_succ]
  norm_num

/-- A rational lower bound for the exponential at the retained truncation
exponent. -/
theorem exp_446_gt :
    (512 : ℝ) * 1_000_000 * 2 ^ 256 * (5 / 2 : ℝ) ^ 256 <
      Real.exp 446 := by
  have hpow : (57 / 10 : ℝ) ^ 256 < Real.exp (223 / 128 : ℝ) ^ 256 :=
    pow_lt_pow_left₀ fivePointSeven_lt_exp_223_128 (by norm_num) (by norm_num)
  rw [← Real.exp_nat_mul] at hpow
  have hpow' : (57 / 10 : ℝ) ^ 256 < Real.exp 446 := by
    convert hpow using 1
    all_goals norm_num
  have hrational :
      (512 : ℝ) * 1_000_000 * 2 ^ 256 * (5 / 2 : ℝ) ^ 256 <
        (57 / 10 : ℝ) ^ 256 := by norm_num
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
`10⁻⁶ · 2⁻²⁵⁶`. -/
theorem truncationMass678_lt :
    (∫ x : Fin 512 → ℝ in
        HalfGaussian512.halfGaussianTruncationSet (radialThreshold 678) coordinateBound,
        HalfGaussian512.halfGaussianProductDensity x) <
      (1 / 1_000_000 : ℝ) * (2 : ℝ)⁻¹ ^ 256 := by
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
    HalfGaussian512.integral_halfGaussianTruncationSet_lt
      (a := radialThreshold 678) (b := coordinateBound)
      coordinateBound_pos hscale
  have hexponent :
      446 <
        (3 * radialThreshold 678 + 2 * coordinateBound ^ 2) / 5 := by
    norm_num [radialThreshold, radialShift, coordinateBound, mesh, side]
  have hexpMono :
      Real.exp
          (-(3 * radialThreshold 678 + 2 * coordinateBound ^ 2) / 5) <
        Real.exp (-446) := by
    rw [Real.exp_lt_exp]
    linarith
  refine hraw.trans <|
    (mul_lt_mul_of_pos_left hexpMono (by positivity)).trans ?_
  rw [Real.exp_neg]
  have hexp446 : 0 < Real.exp (446 : ℝ) := Real.exp_pos _
  rw [show
      512 * (5 / 2 : ℝ) ^ 256 * (Real.exp 446)⁻¹ =
        (512 * (5 / 2 : ℝ) ^ 256) / Real.exp 446 by
      simp only [div_eq_mul_inv]]
  rw [div_lt_iff₀ hexp446]
  have htargetPos :
      0 < (1 / 1_000_000 : ℝ) * (2 : ℝ)⁻¹ ^ 256 := by positivity
  calc
    512 * (5 / 2 : ℝ) ^ 256 =
        ((1 / 1_000_000 : ℝ) * (2 : ℝ)⁻¹ ^ 256) *
          ((512 : ℝ) * 1_000_000 * 2 ^ 256 * (5 / 2 : ℝ) ^ 256) := by
      norm_num [inv_pow]
    _ < ((1 / 1_000_000 : ℝ) * (2 : ℝ)⁻¹ ^ 256) *
          Real.exp 446 :=
      mul_lt_mul_of_pos_left exp_446_gt htargetPos

/-- Scalar parameters used by the shared even-endpoint assembly. -/
noncomputable def endpointData : Counterexamples.SparseUpper.EvenEndpoint.TensorData where
  rows := 512
  bits := 256
  gammaFactor := 179 / 100
  truncationFactor := 1 / 1_000_000
  lossFloor := 8999 / 9000

theorem integral_gaussianCore678_gt :
    (∫ x : Fin 512 → ℝ in gaussianCore 678,
        HalfGaussian512.halfGaussianProductDensity x) >
      Real.exp (-radialShift) *
          ((179 / 100 : ℝ) * (2 : ℝ)⁻¹ ^ 256) -
        (1 / 1_000_000 : ℝ) * (2 : ℝ)⁻¹ ^ 256 := by
  simpa [endpointData] using
    (Counterexamples.SparseUpper.EvenEndpoint.coreMass_gt endpointData
      integral_gaussianCore678_eq
      gammaRows512Threshold678Bits256_verified gammaShift678_lower
      truncationMass678_lt)

/-! ## Tensor lower bound -/

theorem tensorLowerBound678Bits256_gt :
    ENNReal.ofReal
        (Real.exp (-(512 : ℝ) * localLoss) *
          ∫ x : Fin 512 → ℝ in gaussianCore 678,
            HalfGaussian512.halfGaussianProductDensity x) >
      failureTarget 256 := by
  simpa [endpointData] using
    (Counterexamples.SparseUpper.EvenEndpoint.tensorLowerBound_gt endpointData
      localLoss_nonneg
      (by
        unfold totalLoss
        simp [endpointData]
        ring)
      integral_gaussianCore678_gt
      (by norm_num [endpointData])
      (by norm_num [endpointData])
      exp_neg_totalLoss_gt
      (by norm_num [endpointData]))

/-! ## Identification with the finite modular experiment -/

theorem counterexample678EventProbability_eq :
    eventProbability
        (sparseRademacherMatrix 512 highSecurityL2UpperCounterexampleDimension)
        (fun J =>
          modularProjectionSqNorm highSecurityL2UpperCounterexampleModulus J
              highSecurityL2UpperCounterexampleVector >
            678 * sqNorm highSecurityL2UpperCounterexampleVector) =
      sparseAllOnesRowSumsPMF.toMeasure
        {z | 678 * dimension < discreteSqNorm z} := by
  calc
    _ = sparseAllOnesRowSumsPMF.toMeasure
          {z | 678 * dimension <
            Counterexamples.SparseUpper.FlatWitness.rowSqNorm z} :=
      Counterexamples.SparseUpper.FlatWitness.eventProbability_eq_of_specialization
        highSecurityL2UpperCounterexampleVector sparseAllOnesRowSumsPMF
        (by rfl) (by rfl) sparseAllOnesRowSumsPMF_eq_map_uniformSeed
    _ = _ := by rfl

theorem rows512L2Upper678Bits256Counterexample_internal :
    Rows512L2Upper678Bits256CounterexampleStatement := by
  dsimp only [Rows512L2Upper678Bits256CounterexampleStatement]
  apply Counterexamples.SparseUpper.FlatWitness.counterexample_of_specialization
    highSecurityL2UpperCounterexampleVector (by rfl) (by rfl)
  · norm_num [highSecurityL2UpperCounterexampleDimension,
      highSecurityL2UpperCounterexampleSide]
  · rw [counterexample678EventProbability_eq]
    exact tensorLowerBound678Bits256_gt.trans_le (tensorComparison 678)

end Counterexamples.SparseUpper.Rows512.Internal.Threshold678

open Counterexamples.SparseUpper.Rows512.Internal.Threshold678

/-- At threshold `678`, an explicit finite 512-row balanced-ternary
experiment fails with probability strictly greater than `2⁻²⁵⁶`. -/
theorem ternaryL2UpperRows512Threshold678Bits256Counterexample :
    Rows512L2Upper678Bits256CounterexampleStatement :=
  rows512L2Upper678Bits256Counterexample_internal

end CertifiedJL
