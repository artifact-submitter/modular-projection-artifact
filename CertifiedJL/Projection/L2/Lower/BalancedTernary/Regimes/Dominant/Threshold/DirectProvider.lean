/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Spec
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Assembly
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.Analytic
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.Zero

/-! # Target-neutral low-residual dominant provider -/

open scoped ENNReal

namespace CertifiedJL

private theorem two_mul_coordinate_le_modulus_of_centered_at
    {q d : ℕ} {w : Fin d → ℤ} (hcentered : CenteredInput q w)
    (i : Fin d) : 2 * (w i).natAbs ≤ q := by
  have hi := hcentered i
  simp only [centeredInterval, Set.mem_Icc] at hi
  have habs : |w i| ≤ ((q / 2 : ℕ) : ℤ) := (abs_le).2 hi
  have hnat : (w i).natAbs ≤ q / 2 := by
    rw [Int.abs_eq_natAbs] at habs
    exact_mod_cast habs
  calc
    2 * (w i).natAbs ≤ 2 * (q / 2) := Nat.mul_le_mul_left 2 hnat
    _ ≤ q := Nat.mul_div_le q 2

/-- The generic direct-cell cover closes every positive residual ratio at
most `1/2`. -/
theorem sparseThresholdDominantHighActivity_direct_of_cover_at
    {rows squaredNormFloor : ℕ} {highBudget : ℝ}
    (directCover : CertificateContracts.SparseL2ThresholdDominantDirectCoverAt
      rows squaredNormFloor highBudget)
    (hbudget : 0 < highBudget)
    {q d : ℕ} (w : Fin d → ℤ) (inputThreshold : ℕ) (i : Fin d)
    (hq : Odd q) (hcentered : CenteredInput q w)
    (_hpositive : 0 < inputThreshold)
    (hnorm : InputThresholdAtMostNorm inputThreshold w)
    (hmargin : 3 * inputThreshold ≤ q)
    (hdominant : 49 * inputThreshold < 50 * (w i).natAbs)
    (huPositive : 0 < dominantResidualRatio w i)
    (huHalf : dominantResidualRatio w i ≤ 1 / 2) :
    eventProbability (sparseRademacherMatrix rows d)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
              inputThreshold q w J ∧
            squaredNormFloor ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ)) <
      ENNReal.ofReal highBudget := by
  have hi : w i ≠ 0 := by
    intro hiZero
    rw [hiZero] at hdominant
    simp at hdominant
  let u := dominantResidualRatio w i
  let r := dominantThresholdRatio w i inputThreshold
  let B := (q : ℝ) / (dominantAmplitude w i : ℝ)
  have hA : 0 < dominantAmplitude w i := dominantAmplitude_pos hi
  have hAReal : (0 : ℝ) < dominantAmplitude w i := by exact_mod_cast hA
  have huZero : 0 ≤ u := by
    dsimp [u, dominantResidualRatio]
    positivity
  have hrZero : 0 ≤ r :=
    dominantThresholdRatio_nonneg w i inputThreshold
  have hrUpper : r ≤ 2500 / 2401 :=
    (dominantThresholdRatio_lt_dominantCap
      w i inputThreshold hdominant).le
  have hrFeasible : r ≤ 1 + u :=
    dominantThresholdRatio_le_one_add_residualRatio
      w i inputThreshold hi hnorm
  have hBtwo : 2 ≤ B := by
    dsimp [B]
    apply (le_div_iff₀ hAReal).2
    exact_mod_cast
      two_mul_coordinate_le_modulus_of_centered_at hcentered i
  have hrModulus : 9 * r ≤ B ^ 2 :=
    nine_mul_dominantThresholdRatio_le_modulusRatio_sq
      w i inputThreshold hi hmargin
  obtain ⟨entry, hentryValid, hcover⟩ := directCover u r B huZero
        (by simpa [u] using huHalf) hrZero hrUpper hrFeasible hBtwo hrModulus
  rcases hcover with ⟨huLower, huUpper, hrCell, hBCell, hmajorant⟩
  have hevent := dominantThresholdHighActivity_le_thresholdCell_at
    w i inputThreshold rows squaredNormFloor (entry.cell.decodeAt rows)
      hq hi (entry.cell.validAt rows hentryValid)
      (by simpa [u] using huPositive)
      huLower huUpper hrCell hBCell
  have hreal :
      (eventProbability (sparseRademacherMatrix rows d)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
              inputThreshold q w J ∧
            squaredNormFloor ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ))).toReal < highBudget :=
    hevent.trans_lt hmajorant
  rw [← ENNReal.toReal_lt_toReal
    (by
      unfold eventProbability
      exact PMF.apply_ne_top _ _)
    ENNReal.ofReal_ne_top]
  simpa [ENNReal.toReal_ofReal hbudget.le] using hreal

/-- The generic direct provider, including its exact zero-residual endpoint. -/
theorem sparseThresholdDominantHighActivity_lowResidual_of_cover_at
    {rows squaredNormFloor : ℕ} {highBudget : ℝ}
    (directCover : CertificateContracts.SparseL2ThresholdDominantDirectCoverAt
      rows squaredNormFloor highBudget)
    (hbudget : 0 < highBudget)
    {q d : ℕ} (w : Fin d → ℤ) (inputThreshold : ℕ) (i : Fin d)
    (hq : Odd q) (hcentered : CenteredInput q w)
    (hpositive : 0 < inputThreshold)
    (hnorm : InputThresholdAtMostNorm inputThreshold w)
    (hmargin : 3 * inputThreshold ≤ q)
    (hdominant : 49 * inputThreshold < 50 * (w i).natAbs)
    (huHalf : dominantResidualRatio w i ≤ 1 / 2) :
    eventProbability (sparseRademacherMatrix rows d)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
              inputThreshold q w J ∧
            squaredNormFloor ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ)) <
      ENNReal.ofReal highBudget := by
  have hi : w i ≠ 0 := by
    intro hiZero
    rw [hiZero] at hdominant
    simp at hdominant
  by_cases huZero : dominantResidualRatio w i = 0
  · rw [sparseThresholdDominantHighActivity_zeroResidual_probability_eq_zero_at
      w inputThreshold i rows squaredNormFloor hq hcentered hnorm hi huZero]
    exact ENNReal.ofReal_pos.mpr hbudget
  · exact sparseThresholdDominantHighActivity_direct_of_cover_at
      directCover hbudget w inputThreshold i hq hcentered hpositive hnorm hmargin
        hdominant
        (lt_of_le_of_ne
          (by
            unfold dominantResidualRatio
            positivity)
          (Ne.symm huZero)) huHalf

/-- Compatibility wrapper for the fixed-tilt replay structure. -/
theorem sparseThresholdDominantHighActivity_direct_of_replay_at
    {rows squaredNormFloor : ℕ} {highBudget : ℝ}
    (replay : CertificateContracts.SparseL2ThresholdDominantReplayAt
      rows squaredNormFloor highBudget)
    (hbudget : 0 < highBudget)
    {q d : ℕ} (w : Fin d → ℤ) (inputThreshold : ℕ) (i : Fin d)
    (hq : Odd q) (hcentered : CenteredInput q w)
    (hpositive : 0 < inputThreshold)
    (hnorm : InputThresholdAtMostNorm inputThreshold w)
    (hmargin : 3 * inputThreshold ≤ q)
    (hdominant : 49 * inputThreshold < 50 * (w i).natAbs)
    (huPositive : 0 < dominantResidualRatio w i)
    (huHalf : dominantResidualRatio w i ≤ 1 / 2) :
    eventProbability (sparseRademacherMatrix rows d)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
              inputThreshold q w J ∧
            squaredNormFloor ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ)) <
      ENNReal.ofReal highBudget :=
  sparseThresholdDominantHighActivity_direct_of_cover_at replay.directCover
    hbudget w inputThreshold i hq hcentered hpositive hnorm hmargin hdominant
      huPositive huHalf

/-- Compatibility wrapper for the fixed-tilt replay structure. -/
theorem sparseThresholdDominantHighActivity_lowResidual_of_replay_at
    {rows squaredNormFloor : ℕ} {highBudget : ℝ}
    (replay : CertificateContracts.SparseL2ThresholdDominantReplayAt
      rows squaredNormFloor highBudget)
    (hbudget : 0 < highBudget)
    {q d : ℕ} (w : Fin d → ℤ) (inputThreshold : ℕ) (i : Fin d)
    (hq : Odd q) (hcentered : CenteredInput q w)
    (hpositive : 0 < inputThreshold)
    (hnorm : InputThresholdAtMostNorm inputThreshold w)
    (hmargin : 3 * inputThreshold ≤ q)
    (hdominant : 49 * inputThreshold < 50 * (w i).natAbs)
    (huHalf : dominantResidualRatio w i ≤ 1 / 2) :
    eventProbability (sparseRademacherMatrix rows d)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
              inputThreshold q w J ∧
            squaredNormFloor ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ)) <
      ENNReal.ofReal highBudget :=
  sparseThresholdDominantHighActivity_lowResidual_of_cover_at replay.directCover
    hbudget w inputThreshold i hq hcentered hpositive hnorm hmargin hdominant
      huHalf

end CertifiedJL
