/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.RetainedProvider
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.SingletonFourier128

/-! # Target-neutral high-residual dominant Fourier provider -/

open scoped ENNReal
open MeasureTheory

namespace CertifiedJL

private theorem two_mul_coordinate_le_modulus_of_centered_fourier_at
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

private theorem two_lt_dominant_modulus_ratio_at
    {q d : ℕ} {w : Fin d → ℤ} (i : Fin d)
    (hq : Odd q) (hcentered : CenteredInput q w) (hi : w i ≠ 0) :
    2 < (q : ℝ) / (dominantAmplitude w i : ℝ) := by
  let A := dominantAmplitude w i
  have hA : 0 < A := dominantAmplitude_pos hi
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  have hle : 2 * A ≤ q := by
    simpa [A, dominantAmplitude] using
      two_mul_coordinate_le_modulus_of_centered_fourier_at hcentered i
  have hne : 2 * A ≠ q := by
    intro heq
    obtain ⟨k, hk⟩ := hq
    omega
  have hlt : 2 * A < q := lt_of_le_of_ne hle hne
  apply (lt_div_iff₀ hAreal).2
  exact_mod_cast hlt

/-- Generic Fourier/retained provider for residual ratio at least `1/2`. -/
theorem sparseThresholdDominantHighActivity_fourierHighResidual_of_replay_at
    {rows squaredNormFloor : ℕ} {highBudget : ℝ}
    (replay : CertificateContracts.SparseL2ThresholdDominantReplayAt
      rows squaredNormFloor highBudget)
    (hbudget : 0 < highBudget)
    {q d : ℕ} (w : Fin d → ℤ) (inputThreshold : ℕ) (i : Fin d)
    (hq : Odd q) (hcentered : CenteredInput q w)
    (hinputThreshold : 0 < inputThreshold) (hi : w i ≠ 0)
    (hdominant : 49 * inputThreshold < 50 * (w i).natAbs)
    (hmax : ∀ j, (w j).natAbs ^ 2 ≤ (w i).natAbs ^ 2)
    (hresidual : (1 / 2 : ℝ) ≤ dominantResidualRatio w i)
    (hmargin : 3 * inputThreshold ≤ q) :
    eventProbability (sparseRademacherMatrix rows d)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
              inputThreshold q w J ∧
            squaredNormFloor ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ)) <
      ENNReal.ofReal highBudget := by
  let A := dominantAmplitude w i
  let B := (q : ℝ) / (A : ℝ)
  let r := (inputThreshold : ℝ) ^ 2 / (A : ℝ) ^ 2
  have hA : 0 < A := dominantAmplitude_pos hi
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  have hB2 : 2 < B := by
    simpa [B, A] using
      two_lt_dominant_modulus_ratio_at i hq hcentered hi
  have hrModulus : 9 * r ≤ B ^ 2 := by
    simpa [r, B, A, dominantThresholdRatio] using
      nine_mul_dominantThresholdRatio_le_modulusRatio_sq
        w i inputThreshold hi hmargin
  by_cases hB3 : 3 ≤ B
  · exact sparseThresholdDominantHighActivity_retained_of_replay_at
      replay hbudget w inputThreshold i hq hinputThreshold hi hdominant hmax
        hresidual (by simpa [B, A] using hB3)
  have hB3le : B ≤ 3 := le_of_not_ge hB3
  obtain ⟨support, hlower, hupper, hdichotomy⟩ :=
    exists_halfCutoff_dominantRemainder_subprofile_with_dichotomy
      w i hi hresidual hmax
  rcases hdichotomy with hlarge | hcap
  · obtain ⟨j, _hj, hlarge, _hjUpper⟩ := hlarge
    by_cases hB5 : B ≤ 5 / 2
    · obtain ⟨cell, _hcellMem, hcellLower, hcellUpper, hrCell,
          hcellPos, hratio⟩ :=
        replay.singletonFourierCover hB2.le hB5 hrModulus
      have hrowBase :=
        sparseRow_centeredGaussian_le_dominantSingletonLowFourierRow
          w i j (z := (9 / 4 : ℝ)) hq hi (by norm_num)
            (by simpa [B, A] using hB2) hmax hlarge
      have hrowCell :=
        thresholdDominantSingletonLowFourierRow_le_cell
          hcellPos hcellLower hcellUpper (by norm_num : (0 : ℝ) < 9 / 4)
      have hrow :
          (∫ row, Real.exp (-((9 / 4 : ℝ) / (A : ℝ) ^ 2) *
              sparseLowerRowKernel q w row)
              ∂(sparseRademacherRow d).toMeasure) ≤
            thresholdDominantSingletonLowFourierCellRow
              (cell.lower : ℝ) (cell.upper : ℝ) (9 / 4) :=
        hrowBase.trans (by simpa [B, A] using hrowCell)
      exact sparseThresholdDominantHighActivity_of_rowKernel_at
        rows squaredNormFloor w inputThreshold i (9 / 4)
          (thresholdDominantSingletonLowFourierCellRow
            (cell.lower : ℝ) (cell.upper : ℝ) (9 / 4))
          (cell.thresholdUpper : ℝ) hbudget hinputThreshold hi (by norm_num)
            (by simpa [r] using hrCell) hrow hratio
    · have hB5lower : 5 / 2 ≤ B := le_of_not_ge hB5
      obtain ⟨cell, _hcellMem, hcellLower, hcellUpper, hrCell,
          hcellLowerTwo, hcellUpperThree, hratio⟩ :=
        replay.cappedFourierCover hB2.le hB3le hrModulus
      have hrowBase :=
        sparseRow_centeredGaussian_le_dominantLargeSingletonFourierRow
          w i j (z := (9 / 4 : ℝ)) hq hi (by norm_num)
            (by simpa [B, A] using hB5lower) hmax hlarge
      have hrowCell := thresholdDominantCappedFourierRow_le_cell
        hcellLowerTwo hcellLower hcellUpper hcellUpperThree
          (by norm_num : (0 : ℝ) < 9 / 4)
      have hrow :
          (∫ row, Real.exp (-((9 / 4 : ℝ) / (A : ℝ) ^ 2) *
              sparseLowerRowKernel q w row)
              ∂(sparseRademacherRow d).toMeasure) ≤
            thresholdDominantCappedFourierCellRow
              (cell.lower : ℝ) (cell.upper : ℝ) (9 / 4) :=
        hrowBase.trans (by simpa [B, A] using hrowCell)
      exact sparseThresholdDominantHighActivity_of_rowKernel_at
        rows squaredNormFloor w inputThreshold i (9 / 4)
          (thresholdDominantCappedFourierCellRow
            (cell.lower : ℝ) (cell.upper : ℝ) (9 / 4))
          (cell.thresholdUpper : ℝ) hbudget hinputThreshold hi (by norm_num)
            (by simpa [r] using hrCell) hrow hratio
  · obtain ⟨cell, _hcellMem, hcellLower, hcellUpper, hrCell,
        hcellLowerTwo, hcellUpperThree, hratio⟩ :=
      replay.cappedFourierCover hB2.le hB3le hrModulus
    have hrowBase := sparseRow_centeredGaussian_le_dominantCappedFourierRow
      w i support (z := (9 / 4 : ℝ)) hq hi (by norm_num)
        (by simpa [B, A] using hB2) hmax hlower hcap
    have hrowCell := thresholdDominantCappedFourierRow_le_cell
      hcellLowerTwo hcellLower hcellUpper hcellUpperThree
        (by norm_num : (0 : ℝ) < 9 / 4)
    have hrow :
        (∫ row, Real.exp (-((9 / 4 : ℝ) / (A : ℝ) ^ 2) *
            sparseLowerRowKernel q w row)
            ∂(sparseRademacherRow d).toMeasure) ≤
          thresholdDominantCappedFourierCellRow
            (cell.lower : ℝ) (cell.upper : ℝ) (9 / 4) :=
      hrowBase.trans (by simpa [B, A] using hrowCell)
    exact sparseThresholdDominantHighActivity_of_rowKernel_at
      rows squaredNormFloor w inputThreshold i (9 / 4)
        (thresholdDominantCappedFourierCellRow
          (cell.lower : ℝ) (cell.upper : ℝ) (9 / 4))
        (cell.thresholdUpper : ℝ) hbudget hinputThreshold hi (by norm_num)
          (by simpa [r] using hrCell) hrow hratio

/-- Generic Fourier/retained provider with target-selected singleton and
capped Fourier tilts. -/
theorem sparseThresholdDominantHighActivity_fourierHighResidual_of_tiltedReplay_at
    {rows squaredNormFloor : ℕ} {singletonTilt cappedTilt highBudget : ℝ}
    (replay : CertificateContracts.SparseL2ThresholdDominantTiltedReplayAt
      rows squaredNormFloor singletonTilt cappedTilt highBudget)
    (hbudget : 0 < highBudget)
    {q d : ℕ} (w : Fin d → ℤ) (inputThreshold : ℕ) (i : Fin d)
    (hq : Odd q) (hcentered : CenteredInput q w)
    (hinputThreshold : 0 < inputThreshold) (hi : w i ≠ 0)
    (hdominant : 49 * inputThreshold < 50 * (w i).natAbs)
    (hmax : ∀ j, (w j).natAbs ^ 2 ≤ (w i).natAbs ^ 2)
    (hresidual : (1 / 2 : ℝ) ≤ dominantResidualRatio w i)
    (hmargin : 3 * inputThreshold ≤ q) :
    eventProbability (sparseRademacherMatrix rows d)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
              inputThreshold q w J ∧
            squaredNormFloor ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ)) <
      ENNReal.ofReal highBudget := by
  let A := dominantAmplitude w i
  let B := (q : ℝ) / (A : ℝ)
  let r := (inputThreshold : ℝ) ^ 2 / (A : ℝ) ^ 2
  have hA : 0 < A := dominantAmplitude_pos hi
  have hB2 : 2 < B := by
    simpa [B, A] using
      two_lt_dominant_modulus_ratio_at i hq hcentered hi
  have hrModulus : 9 * r ≤ B ^ 2 := by
    simpa [r, B, A, dominantThresholdRatio] using
      nine_mul_dominantThresholdRatio_le_modulusRatio_sq
        w i inputThreshold hi hmargin
  by_cases hB3 : 3 ≤ B
  · exact sparseThresholdDominantHighActivity_retained_of_geometry_at
      replay.retainedGeometry replay.retainedFinalRatio hbudget w
        inputThreshold i hq hinputThreshold hi hdominant hmax hresidual
          (by simpa [B, A] using hB3)
  have hB3le : B ≤ 3 := le_of_not_ge hB3
  obtain ⟨support, hlower, hupper, hdichotomy⟩ :=
    exists_halfCutoff_dominantRemainder_subprofile_with_dichotomy
      w i hi hresidual hmax
  rcases hdichotomy with hlarge | hcap
  · obtain ⟨j, _hj, hlarge, _hjUpper⟩ := hlarge
    by_cases hB5 : B ≤ 5 / 2
    · obtain ⟨L, U, thresholdUpper, hcellLower, hcellUpper, hrCell,
          hcellLowerTwo, hcellUpperThree, hratio⟩ :=
        replay.singletonFourierCover hB2.le hB5 hrModulus
      have hrowBase :=
        sparseRow_centeredGaussian_le_dominantSingletonPhaseFourierRow
          w i j (z := singletonTilt) hq hi replay.singletonTiltPositive
            (by simpa [B, A] using hB2) hmax hlarge
      have hrowCell :=
        thresholdDominantSingletonPhaseFourierRow_le_cell
          hcellLowerTwo hcellLower hcellUpper hcellUpperThree
            replay.singletonTiltPositive
      have hrow :
          (∫ row, Real.exp (-(singletonTilt / (A : ℝ) ^ 2) *
              sparseLowerRowKernel q w row)
              ∂(sparseRademacherRow d).toMeasure) ≤
            thresholdDominantSingletonPhaseFourierCellRow
              L U singletonTilt :=
        hrowBase.trans (by simpa [B, A] using hrowCell)
      exact sparseThresholdDominantHighActivity_of_rowKernel_at
        rows squaredNormFloor w inputThreshold i singletonTilt
          (thresholdDominantSingletonPhaseFourierCellRow
            L U singletonTilt)
          thresholdUpper hbudget hinputThreshold hi
            replay.singletonTiltPositive (by simpa [r] using hrCell)
              hrow hratio
    · have hB5lower : 5 / 2 ≤ B := le_of_not_ge hB5
      obtain ⟨L, U, thresholdUpper, hcellLower, hcellUpper, hrCell,
          hcellLowerTwo, hcellUpperThree, hratio⟩ :=
        replay.cappedFourierCover hB2.le hB3le hrModulus
      have hrowBase :=
        sparseRow_centeredGaussian_le_dominantLargeSingletonFourierRow
          w i j (z := cappedTilt) hq hi replay.cappedTiltPositive
            (by simpa [B, A] using hB5lower) hmax hlarge
      have hrowCell := thresholdDominantCappedFourierRow_le_cell
        hcellLowerTwo hcellLower hcellUpper hcellUpperThree
          replay.cappedTiltPositive
      have hrow :
          (∫ row, Real.exp (-(cappedTilt / (A : ℝ) ^ 2) *
              sparseLowerRowKernel q w row)
              ∂(sparseRademacherRow d).toMeasure) ≤
            thresholdDominantCappedFourierCellRow L U cappedTilt :=
        hrowBase.trans (by simpa [B, A] using hrowCell)
      exact sparseThresholdDominantHighActivity_of_rowKernel_at
        rows squaredNormFloor w inputThreshold i cappedTilt
          (thresholdDominantCappedFourierCellRow L U cappedTilt)
          thresholdUpper hbudget hinputThreshold hi replay.cappedTiltPositive
            (by simpa [r] using hrCell) hrow hratio
  · obtain ⟨L, U, thresholdUpper, hcellLower, hcellUpper, hrCell,
        hcellLowerTwo, hcellUpperThree, hratio⟩ :=
      replay.cappedFourierCover hB2.le hB3le hrModulus
    have hrowBase := sparseRow_centeredGaussian_le_dominantCappedFourierRow
      w i support (z := cappedTilt) hq hi replay.cappedTiltPositive
        (by simpa [B, A] using hB2) hmax hlower hcap
    have hrowCell := thresholdDominantCappedFourierRow_le_cell
      hcellLowerTwo hcellLower hcellUpper hcellUpperThree
        replay.cappedTiltPositive
    have hrow :
        (∫ row, Real.exp (-(cappedTilt / (A : ℝ) ^ 2) *
            sparseLowerRowKernel q w row)
            ∂(sparseRademacherRow d).toMeasure) ≤
          thresholdDominantCappedFourierCellRow L U cappedTilt :=
      hrowBase.trans (by simpa [B, A] using hrowCell)
    exact sparseThresholdDominantHighActivity_of_rowKernel_at
      rows squaredNormFloor w inputThreshold i cappedTilt
        (thresholdDominantCappedFourierCellRow L U cappedTilt)
        thresholdUpper hbudget hinputThreshold hi replay.cappedTiltPositive
          (by simpa [r] using hrCell) hrow hratio

end CertifiedJL
