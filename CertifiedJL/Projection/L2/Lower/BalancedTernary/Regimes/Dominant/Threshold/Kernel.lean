/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Unrestricted.Kernel
import CertifiedJL.Statements.L2.Lower
import CertifiedJL.Statements.Shared.Input

/-!
# Dominant-coordinate kernels at a public threshold

This file is the public-threshold analogue of the normalization layer in
`DominantKernel`.  It deliberately stops before any numerical certificate:
the threshold ratio `b² / A²` is kept independent of the residual ratio
`U / A²`.
-/

open scoped BigOperators

namespace CertifiedJL

/-- The public squared threshold divided by the selected amplitude squared. -/
noncomputable def dominantThresholdRatio {d : ℕ} (w : Fin d → ℤ)
    (i : Fin d) (inputThreshold : ℕ) : ℝ :=
  (inputThreshold : ℝ) ^ 2 / (dominantAmplitude w i : ℝ) ^ 2

theorem dominantThresholdRatio_nonneg {d : ℕ} (w : Fin d → ℤ)
    (i : Fin d) (inputThreshold : ℕ) :
    0 ≤ dominantThresholdRatio w i inputThreshold := by
  unfold dominantThresholdRatio
  positivity

theorem dominantThresholdRatio_pos {d : ℕ} (w : Fin d → ℤ)
    (i : Fin d) (inputThreshold : ℕ) (hi : w i ≠ 0)
    (hthreshold : 0 < inputThreshold) :
    0 < dominantThresholdRatio w i inputThreshold := by
  unfold dominantThresholdRatio
  have hA : (0 : ℝ) < dominantAmplitude w i := by
    exact_mod_cast dominantAmplitude_pos hi
  positivity

/-- Slack in the public norm constraint `r ≤ 1 + u`.  Cells in `(u, δ)`
coordinates preserve the cancellation at the critical `K = 29` boundary. -/
noncomputable def dominantThresholdSlack {d : ℕ} (w : Fin d → ℤ)
    (i : Fin d) (inputThreshold : ℕ) : ℝ :=
  1 + dominantResidualRatio w i -
    dominantThresholdRatio w i inputThreshold

/-- The empirically sharp overlap point between the elementary Laplace cells
and the retained-mode wrapped-Fourier bound. -/
def dominantThresholdFourierCutoff : ℚ := 651 / 1000

/-- The protocol norm premise is exactly the joint constraint `r ≤ 1 + u`. -/
theorem dominantThresholdRatio_le_one_add_residualRatio {d : ℕ}
    (w : Fin d → ℤ) (i : Fin d) (inputThreshold : ℕ)
    (hi : w i ≠ 0) (hnorm : InputThresholdAtMostNorm inputThreshold w) :
    dominantThresholdRatio w i inputThreshold ≤
      1 + dominantResidualRatio w i := by
  rw [one_add_dominantResidualRatio w i hi]
  unfold dominantThresholdRatio
  unfold InputThresholdAtMostNorm at hnorm
  have hA : (0 : ℝ) < (dominantAmplitude w i : ℝ) ^ 2 := by
    have : (0 : ℝ) < dominantAmplitude w i := by
      exact_mod_cast dominantAmplitude_pos hi
    positivity
  apply (div_le_div_iff_of_pos_right hA).2
  exact_mod_cast hnorm

theorem dominantThresholdSlack_nonneg {d : ℕ}
    (w : Fin d → ℤ) (i : Fin d) (inputThreshold : ℕ)
    (hi : w i ≠ 0) (hnorm : InputThresholdAtMostNorm inputThreshold w) :
    0 ≤ dominantThresholdSlack w i inputThreshold := by
  unfold dominantThresholdSlack
  linarith [dominantThresholdRatio_le_one_add_residualRatio
    w i inputThreshold hi hnorm]

/-- A rectangular `(u, δ)` cell gives a correlated upper endpoint for `r`. -/
theorem dominantThresholdRatio_le_of_residualRatio_le_of_slack_lower
    {d : ℕ} (w : Fin d → ℤ) (i : Fin d) (inputThreshold : ℕ)
    {upper slackLower : ℝ}
    (hu : dominantResidualRatio w i ≤ upper)
    (hslack : slackLower ≤ dominantThresholdSlack w i inputThreshold) :
    dominantThresholdRatio w i inputThreshold ≤
      1 + upper - slackLower := by
  unfold dominantThresholdSlack at hslack
  linarith

/-- The other two faces of a `(u, δ)` cell give a correlated lower endpoint
for `r`, hence a stronger normalized-modulus endpoint. -/
theorem dominantThresholdRatio_lower_of_residualRatio_lower_of_slack_le
    {d : ℕ} (w : Fin d → ℤ) (i : Fin d) (inputThreshold : ℕ)
    {lower slackUpper : ℝ}
    (hu : lower ≤ dominantResidualRatio w i)
    (hslack : dominantThresholdSlack w i inputThreshold ≤ slackUpper) :
    1 + lower - slackUpper ≤
      dominantThresholdRatio w i inputThreshold := by
  unfold dominantThresholdSlack at hslack
  linarith

theorem dominantResidualRatio_cutoff_cases {d : ℕ}
    (w : Fin d → ℤ) (i : Fin d) :
    dominantResidualRatio w i ≤ (dominantThresholdFourierCutoff : ℝ) ∨
      (dominantThresholdFourierCutoff : ℝ) ≤
        dominantResidualRatio w i :=
  le_total _ _

/-- The `49/50` dominant split caps the independent threshold ratio. -/
theorem dominantThresholdRatio_lt_dominantCap {d : ℕ}
    (w : Fin d → ℤ) (i : Fin d) (inputThreshold : ℕ)
    (hdominant : 49 * inputThreshold < 50 * (w i).natAbs) :
    dominantThresholdRatio w i inputThreshold < (2500 / 2401 : ℝ) := by
  have hA : (0 : ℝ) < dominantAmplitude w i := by
    have hpos : 0 < (w i).natAbs := by omega
    exact_mod_cast hpos
  have hratio : (inputThreshold : ℝ) /
      (dominantAmplitude w i : ℝ) < 50 / 49 := by
    rw [div_lt_iff₀ hA]
    have hdominantReal : (49 : ℝ) * inputThreshold <
        50 * dominantAmplitude w i := by
      exact_mod_cast hdominant
    norm_num
    nlinarith
  have hratio_nonneg : 0 ≤ (inputThreshold : ℝ) /
      (dominantAmplitude w i : ℝ) := by positivity
  have hcap_nonneg : (0 : ℝ) ≤ 50 / 49 := by norm_num
  have hsquare := (sq_lt_sq₀ hratio_nonneg hcap_nonneg).2 hratio
  norm_num [dominantThresholdRatio, div_pow] at hsquare ⊢
  exact hsquare

/-- Margin three gives the exact squared normalized-modulus inequality
`9 r ≤ (q/A)²`, without introducing an actual-norm cap. -/
theorem nine_mul_dominantThresholdRatio_le_modulusRatio_sq
    {q d : ℕ} (w : Fin d → ℤ) (i : Fin d) (inputThreshold : ℕ)
    (hi : w i ≠ 0) (hmargin : 3 * inputThreshold ≤ q) :
    9 * dominantThresholdRatio w i inputThreshold ≤
      ((q : ℝ) / (dominantAmplitude w i : ℝ)) ^ 2 := by
  have hA : (0 : ℝ) < dominantAmplitude w i := by
    exact_mod_cast dominantAmplitude_pos hi
  have hmarginReal : (3 : ℝ) * inputThreshold ≤ q := by
    exact_mod_cast hmargin
  unfold dominantThresholdRatio
  rw [div_pow]
  rw [show (9 : ℝ) * ((inputThreshold : ℝ) ^ 2 /
      (dominantAmplitude w i : ℝ) ^ 2) =
      (9 * (inputThreshold : ℝ) ^ 2) /
        (dominantAmplitude w i : ℝ) ^ 2 by ring]
  apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hA)).2
  nlinarith

/-- Exact normalized form of the strict public-threshold failure event at an
arbitrary squared-norm floor. -/
theorem dominantNormalizedThresholdFailure_iff_at {q m d : ℕ}
    (squaredNormFloor : ℕ)
    (J : Matrix (Fin m) (Fin d) ℤ) (w : Fin d → ℤ) (i : Fin d)
    (inputThreshold : ℕ) (hi : w i ≠ 0) :
    (∑ row, dominantNormalizedRowKernel q w i (J row) <
        squaredNormFloor * dominantThresholdRatio w i inputThreshold) ↔
      L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
        inputThreshold q w J := by
  rw [sum_dominantNormalizedRowKernel]
  unfold dominantThresholdRatio L2ThresholdLowerFailure
  simp only [NonnegativeRatio.ofNat]
  have hA : (0 : ℝ) < (dominantAmplitude w i : ℝ) ^ 2 := by
    have : (0 : ℝ) < dominantAmplitude w i := by
      exact_mod_cast dominantAmplitude_pos hi
    positivity
  rw [show (squaredNormFloor : ℝ) * ((inputThreshold : ℝ) ^ 2 /
      (dominantAmplitude w i : ℝ) ^ 2) =
      (squaredNormFloor * (inputThreshold : ℝ) ^ 2) /
        (dominantAmplitude w i : ℝ) ^ 2 by ring]
  rw [div_lt_div_iff_of_pos_right hA]
  simp only [one_mul]
  exact_mod_cast Iff.rfl

/-- Compatibility specialization of normalized threshold failure at squared norm
floor 29. -/
theorem dominantNormalizedThresholdFailure_iff {q m d : ℕ}
    (J : Matrix (Fin m) (Fin d) ℤ) (w : Fin d → ℤ) (i : Fin d)
    (inputThreshold : ℕ) (hi : w i ≠ 0) :
    (∑ row, dominantNormalizedRowKernel q w i (J row) <
        29 * dominantThresholdRatio w i inputThreshold) ↔
      L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
        inputThreshold q w J :=
  dominantNormalizedThresholdFailure_iff_at 29 J w i inputThreshold hi

/-- Fixed-activity negative-Laplace bound at an arbitrary row count and public
squared-norm floor. -/
theorem dominantConditional_thresholdFailure_le_activeInactiveKernels_at
    {q d : ℕ} (w : Fin d → ℤ) (i : Fin d) (hi : w i ≠ 0)
    (rows squaredNormFloor inputThreshold : ℕ)
    (activity : DominantActivity rows)
    (z L₀ L₁ : ℝ) (hz : 0 < z)
    (hrow : ∀ row,
      ∫ x, Real.exp (-z * dominantNormalizedRowKernel q w i x)
          ∂(dominantConditionalRowPMF i (activity row)).toMeasure ≤
        if activity row then L₁ else L₀) :
    (eventProbability (dominantConditionalMatrixPMF i activity)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
          inputThreshold q w)).toReal ≤
      Real.exp
          (squaredNormFloor * z * dominantThresholdRatio w i inputThreshold) *
        L₁ ^ (dominantActivityCount activity : ℕ) *
          L₀ ^ (rows - (dominantActivityCount activity : ℕ)) := by
  have hevent :
      (fun J : Matrix (Fin rows) (Fin d) ℤ =>
        ∑ row, dominantNormalizedRowKernel q w i (J row) <
          squaredNormFloor * dominantThresholdRatio w i inputThreshold) =
        L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
          inputThreshold q w := by
    funext J
    exact propext (dominantNormalizedThresholdFailure_iff_at
      squaredNormFloor J w i inputThreshold hi)
  rw [← hevent]
  have h := dominantConditional_eventProbability_le_activeInactiveKernels
    i activity (fun _ => dominantNormalizedRowKernel q w i) z
      (squaredNormFloor * dominantThresholdRatio w i inputThreshold) L₀ L₁ hz hrow
  calc
    _ ≤ Real.exp
          (z * (squaredNormFloor * dominantThresholdRatio w i inputThreshold)) *
        L₁ ^ (dominantActivityCount activity : ℕ) *
          L₀ ^ (rows - (dominantActivityCount activity : ℕ)) := h
    _ = _ := by
      congr 3
      ring

/-- Compatibility specialization of the fixed-activity threshold bound at 256
rows and squared-norm floor 29. -/
theorem dominantConditional_thresholdFailure_le_activeInactiveKernels
    {q d : ℕ} (w : Fin d → ℤ) (i : Fin d) (hi : w i ≠ 0)
    (inputThreshold : ℕ) (activity : DominantActivity 256)
    (z L₀ L₁ : ℝ) (hz : 0 < z)
    (hrow : ∀ row,
      ∫ x, Real.exp (-z * dominantNormalizedRowKernel q w i x)
          ∂(dominantConditionalRowPMF i (activity row)).toMeasure ≤
        if activity row then L₁ else L₀) :
    (eventProbability (dominantConditionalMatrixPMF i activity)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
          inputThreshold q w)).toReal ≤
      Real.exp
          (29 * z * dominantThresholdRatio w i inputThreshold) *
        L₁ ^ (dominantActivityCount activity : ℕ) *
          L₀ ^ (256 - (dominantActivityCount activity : ℕ)) :=
  dominantConditional_thresholdFailure_le_activeInactiveKernels_at
    w i hi 256 29 inputThreshold activity z L₀ L₁ hz hrow

end CertifiedJL
