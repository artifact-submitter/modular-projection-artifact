/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.Counterexamples.L2Upper.GaussianComparison

-- See the corresponding note in `GaussianComparison`.
set_option Elab.async false

/-!
# Quantitative bounds for the sparse upper-336 counterexample

This module proves the exact Gamma-tail, coordinate-truncation, and rational
loss estimates used by the final sparse upper counterexample.
-/

open scoped BigOperators ENNReal

open MeasureTheory

namespace CertifiedJL
open Probability
namespace Counterexamples.SparseUpper.Internal

/-! ## Gamma mass retained by the bounded mesh region -/

/-- Half-Gaussian vectors above the shifted radial threshold. -/
def gaussianRadialTail : Set (Fin 256 → ℝ) :=
  {x | radialThreshold 336 < squaredRadius x}

theorem measurableSet_gaussianRadialTail :
    MeasurableSet gaussianRadialTail := by
  unfold gaussianRadialTail squaredRadius
  exact measurableSet_lt measurable_const
    (Finset.measurable_sum _ fun j _ =>
      (measurable_pi_apply j).pow_const 2)

theorem gaussianRadialTail_eq_union :
    gaussianRadialTail =
      gaussianCore 336 ∪
        halfGaussianTruncationSet
          (radialThreshold 336) coordinateBound := by
  ext x
  simp only [gaussianRadialTail, gaussianCore,
    halfGaussianTruncationSet, Set.mem_setOf_eq,
    Set.mem_union]
  constructor
  · intro hradial
    by_cases hcoord : ∀ j, |x j| < coordinateBound
    · exact Or.inl ⟨hradial, hcoord⟩
    · push Not at hcoord
      exact Or.inr ⟨hradial, hcoord⟩
  · rintro (h | h) <;> exact h.1

theorem gaussianCore_disjoint_truncation :
    Disjoint (gaussianCore 336)
      (halfGaussianTruncationSet
        (radialThreshold 336) coordinateBound) := by
  rw [Set.disjoint_left]
  intro x hxCore hxTail
  obtain ⟨j, hj⟩ := hxTail.2
  exact (not_lt_of_ge hj) (hxCore.2 j)

theorem integral_gaussianCore_eq :
    (∫ x : Fin 256 → ℝ in gaussianCore 336,
        halfGaussianProductDensity x) =
      gammaSurvivalNat 128 (radialThreshold 336) -
        ∫ x : Fin 256 → ℝ in
          halfGaussianTruncationSet
            (radialThreshold 336) coordinateBound,
          halfGaussianProductDensity x := by
  have hunion :=
    setIntegral_union gaussianCore_disjoint_truncation
      (measurableSet_halfGaussianTruncationSet
        (radialThreshold 336) coordinateBound)
      integrable_halfGaussianProductDensity.integrableOn
      integrable_halfGaussianProductDensity.integrableOn
  rw [← gaussianRadialTail_eq_union] at hunion
  have htail :
      (∫ x : Fin 256 → ℝ in gaussianRadialTail,
          halfGaussianProductDensity x) =
        gammaSurvivalNat 128 (radialThreshold 336) := by
    simpa [gaussianRadialTail, squaredRadius] using
      (integral_halfGaussianProductDensity_tail
        (radialThreshold_nonneg 336))
  rw [htail] at hunion
  linarith

theorem gammaShift_lower :
    Real.exp (-radialShift) * gammaSurvivalNat 128 336 ≤
      gammaSurvivalNat 128 (radialThreshold 336) := by
  have h :=
    exp_neg_mul_gammaSurvivalNat_le 128
      (x := (336 : ℝ)) (δ := radialShift)
      (by norm_num) radialShift_nonneg
  simpa [radialThreshold] using h

/--
The scale inequality needed by the one-coordinate Mills estimate.
-/
theorem coordinate_scale :
    (Real.sqrt Real.pi)⁻¹ /
        ((2 / 5 : ℝ) * coordinateBound) <
      Real.sqrt (5 / 2 : ℝ) := by
  have hsqrtPi :
      (1 : ℝ) < Real.sqrt Real.pi := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num)
      (by linarith [Real.pi_gt_three])
  have hinv : (Real.sqrt Real.pi)⁻¹ < (1 : ℝ) :=
    inv_lt_one_of_one_lt₀ hsqrtPi
  have hden :
      (1 : ℝ) < (2 / 5 : ℝ) * coordinateBound := by
    norm_num [coordinateBound, mesh, side]
  have hleft :
      (Real.sqrt Real.pi)⁻¹ /
          ((2 / 5 : ℝ) * coordinateBound) < 1 := by
    rw [div_lt_one (lt_trans (by norm_num) hden)]
    exact hinv.trans hden
  have hright :
      (1 : ℝ) < Real.sqrt (5 / 2 : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  exact hleft.trans hright

/-- Exact exponent appearing in the coordinate-truncation estimate. -/
theorem truncationExponent_gt :
    216 <
      (3 * radialThreshold 336 + 2 * coordinateBound ^ 2) / 5 := by
  norm_num [radialThreshold, radialShift, coordinateBound, mesh, side]

/-- The elementary integer comparison behind the final exponential bound. -/
theorem twentySeven_pow_comparison :
    (12_800 : ℝ) * 25 ^ 128 < 27 ^ 128 := by
  norm_num

/-- Concrete exponential lower bound used to eliminate transcendental data. -/
theorem exp_216_gt :
    (12_800 : ℝ) * 5 ^ 128 < Real.exp 216 := by
  have hpow :
      (27 / 5 : ℝ) ^ 128 <
        Real.exp (27 / 16 : ℝ) ^ 128 :=
    pow_lt_pow_left₀
      twentySeven_fifths_lt_exp_twentySeven_sixteenth
      (by positivity) (by norm_num)
  rw [← Real.exp_nat_mul] at hpow
  have hpow' :
      (27 / 5 : ℝ) ^ 128 < Real.exp 216 := by
    convert hpow using 1
    all_goals norm_num
  calc
    (12_800 : ℝ) * 5 ^ 128 <
        (27 / 5 : ℝ) ^ 128 := by
      rw [div_pow]
      rw [lt_div_iff₀ (by positivity)]
      calc
        (12_800 : ℝ) * 5 ^ 128 * 5 ^ 128 =
            12_800 * (5 ^ 128 * 5 ^ 128) := by ring
        _ =
            12_800 * 25 ^ 128 := by
          rw [← mul_pow]
          norm_num
        _ < 27 ^ 128 := twentySeven_pow_comparison
    _ < Real.exp 216 := hpow'

/--
The discarded half-Gaussian coordinate tail is below one fiftieth of the
target `2⁻¹²⁸`.
-/
theorem truncationMass_lt :
    (∫ x : Fin 256 → ℝ in
        halfGaussianTruncationSet (radialThreshold 336) coordinateBound,
        halfGaussianProductDensity x) <
      (1 / 50 : ℝ) * (2 : ℝ)⁻¹ ^ 128 := by
  have hraw :=
    integral_halfGaussianTruncationSet_lt
      (a := radialThreshold 336) (b := coordinateBound)
      coordinateBound_pos coordinate_scale
  have hexpMono :
      Real.exp
          (-(3 * radialThreshold 336 + 2 * coordinateBound ^ 2) / 5) <
        Real.exp (-216) := by
    rw [Real.exp_lt_exp]
    linarith [truncationExponent_gt]
  have hpositive :
      0 < 256 * (5 / 2 : ℝ) ^ 128 := by positivity
  refine hraw.trans <| (mul_lt_mul_of_pos_left hexpMono hpositive).trans ?_
  rw [Real.exp_neg]
  have hexp216 : 0 < Real.exp (216 : ℝ) := Real.exp_pos _
  rw [show
      256 * (5 / 2 : ℝ) ^ 128 * (Real.exp 216)⁻¹ =
        (256 * (5 / 2 : ℝ) ^ 128) / Real.exp 216 by
      simp only [div_eq_mul_inv]]
  rw [div_lt_iff₀ hexp216]
  have htargetPos :
      0 < (1 / 50 : ℝ) * (2 : ℝ)⁻¹ ^ 128 := by positivity
  calc
    256 * (5 / 2 : ℝ) ^ 128 =
        ((1 / 50 : ℝ) * (2 : ℝ)⁻¹ ^ 128) *
          ((12_800 : ℝ) * 5 ^ 128) := by
      norm_num [div_pow, inv_pow]
    _ < ((1 / 50 : ℝ) * (2 : ℝ)⁻¹ ^ 128) *
          Real.exp 216 :=
      mul_lt_mul_of_pos_left exp_216_gt htargetPos

/-- The exact aggregate loss remains below `1/15`. -/
theorem totalLoss_lt :
    totalLoss < (1 / 15 : ℝ) := by
  norm_num [totalLoss, radialShift, coordinateBound, mesh,
    localLoss, binomialLogStepError, cutoff, dimension, side]

theorem totalLoss_nonneg : 0 ≤ totalLoss := by
  norm_num [totalLoss, radialShift, coordinateBound, mesh,
    localLoss, binomialLogStepError, cutoff, dimension, side]

/-- Every unreduced row sum lies strictly inside the centered residue window. -/
theorem dimension_lt_half_modulus :
    dimension < (counterexampleModulus - 1) / 2 := by
  norm_num [dimension, side, counterexampleModulus]

theorem integral_gaussianCore_gt :
    (∫ x : Fin 256 → ℝ in gaussianCore 336,
        halfGaussianProductDensity x) >
      Real.exp (-radialShift) *
          ((3 / 2 : ℝ) * (2 : ℝ)⁻¹ ^ 128) -
        (1 / 50 : ℝ) * (2 : ℝ)⁻¹ ^ 128 := by
  rw [integral_gaussianCore_eq]
  have hgamma :
      Real.exp (-radialShift) *
          ((3 / 2 : ℝ) * (2 : ℝ)⁻¹ ^ 128) <
        Real.exp (-radialShift) *
          gammaSurvivalNat 128 336 :=
    mul_lt_mul_of_pos_left gammaSurvivalNat_128_336_gt
      (Real.exp_pos _)
  have hshift := gammaShift_lower
  have htrunc := truncationMass_lt
  linarith

theorem localLoss_nonneg : 0 ≤ localLoss := by
  norm_num [localLoss, binomialLogStepError,
    cutoff, dimension, side]

theorem exp_neg_totalLoss_gt :
    (14 / 15 : ℝ) < Real.exp (-totalLoss) := by
  have hexp :
      1 - totalLoss ≤ Real.exp (-totalLoss) := by
    simpa only [sub_eq_add_neg, add_comm] using
      Real.add_one_le_exp (-totalLoss)
  linarith [totalLoss_lt]

theorem tensorLowerBound_gt :
    ENNReal.ofReal
        (Real.exp (-(256 : ℝ) * localLoss) *
          ∫ x : Fin 256 → ℝ in gaussianCore 336,
            halfGaussianProductDensity x) >
      ((69 : ENNReal) / 50) *
        failureTarget securityBits := by
  let target : ℝ := (2 : ℝ)⁻¹ ^ 128
  have hcore := integral_gaussianCore_gt
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
      (69 / 50 : ℝ) * target <
        Real.exp (-(256 : ℝ) * localLoss) *
          ∫ x : Fin 256 → ℝ in gaussianCore 336,
            halfGaussianProductDensity x := by
    dsimp only [target]
    rw [mul_sub] at hmul
    rw [show
        Real.exp (-(256 : ℝ) * localLoss) *
            (Real.exp (-radialShift) *
              ((3 / 2 : ℝ) * (2 : ℝ)⁻¹ ^ 128)) =
          (Real.exp (-(256 : ℝ) * localLoss) *
              Real.exp (-radialShift)) *
            ((3 / 2 : ℝ) * (2 : ℝ)⁻¹ ^ 128) by ring] at hmul
    rw [hexpCombine] at hmul
    have htargetPos : 0 < (2 : ℝ)⁻¹ ^ 128 := by positivity
    have hmain :
        (3 / 2 : ℝ) * (14 / 15 : ℝ) *
              (2 : ℝ)⁻¹ ^ 128 -
            (1 / 50 : ℝ) * (2 : ℝ)⁻¹ ^ 128 <
          Real.exp (-totalLoss) *
              ((3 / 2 : ℝ) * (2 : ℝ)⁻¹ ^ 128) -
            Real.exp (-(256 : ℝ) * localLoss) *
              ((1 / 50 : ℝ) * (2 : ℝ)⁻¹ ^ 128) := by
      have hfirst :
          (3 / 2 : ℝ) * (14 / 15 : ℝ) *
                (2 : ℝ)⁻¹ ^ 128 <
            Real.exp (-totalLoss) *
              ((3 / 2 : ℝ) * (2 : ℝ)⁻¹ ^ 128) := by
        nlinarith [exp_neg_totalLoss_gt]
      have hsecond :
          Real.exp (-(256 : ℝ) * localLoss) *
                ((1 / 50 : ℝ) * (2 : ℝ)⁻¹ ^ 128) ≤
            (1 / 50 : ℝ) * (2 : ℝ)⁻¹ ^ 128 := by
        nlinarith
      linarith
    calc
      (69 / 50 : ℝ) * target =
          (3 / 2 : ℝ) * (14 / 15 : ℝ) *
              (2 : ℝ)⁻¹ ^ 128 -
            (1 / 50 : ℝ) * (2 : ℝ)⁻¹ ^ 128 := by
        dsimp only [target]
        ring
      _ <
          Real.exp (-totalLoss) *
                ((3 / 2 : ℝ) * (2 : ℝ)⁻¹ ^ 128) -
            Real.exp (-(256 : ℝ) * localLoss) *
                ((1 / 50 : ℝ) * (2 : ℝ)⁻¹ ^ 128) :=
        hmain
      _ <
          Real.exp (-(256 : ℝ) * localLoss) *
            ∫ x : Fin 256 → ℝ in gaussianCore 336,
              halfGaussianProductDensity x :=
        hmul
  rw [failureTarget, securityBits]
  have htargetENN :
      ENNReal.ofReal ((69 / 50 : ℝ) * target) =
        ((69 : ENNReal) / 50) *
          (2 : ENNReal)⁻¹ ^ 128 := by
    dsimp only [target]
    rw [ENNReal.ofReal_mul
      (by norm_num : (0 : ℝ) ≤ 69 / 50)]
    rw [ENNReal.ofReal_div_of_pos
      (by norm_num : (0 : ℝ) < 50)]
    rw [ENNReal.ofReal_pow
      (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹) 128]
    rw [ENNReal.ofReal_inv_of_pos
      (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [← htargetENN]
  have hright :
      0 <
        Real.exp (-(256 : ℝ) * localLoss) *
          ∫ x : Fin 256 → ℝ in gaussianCore 336,
            halfGaussianProductDensity x := by
    have hleft :
        0 < (69 / 50 : ℝ) * target := by
      dsimp only [target]
      positivity
    exact hleft.trans hreal
  exact (ENNReal.ofReal_lt_ofReal_iff hright).2 hreal

end Counterexamples.SparseUpper.Internal

end CertifiedJL
