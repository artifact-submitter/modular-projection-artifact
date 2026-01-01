/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Spec
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.RetainedProvider128
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.SingletonFourier128

/-! # High-residual dominant Fourier provider at 128 bits -/

open scoped ENNReal
open MeasureTheory

namespace CertifiedJL

private theorem two_mul_coordinate_le_modulus_of_centered_fourier
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

private theorem two_lt_dominant_modulus_ratio
    {q d : ℕ} {w : Fin d → ℤ} (i : Fin d)
    (hq : Odd q) (hcentered : CenteredInput q w) (hi : w i ≠ 0) :
    2 < (q : ℝ) / (dominantAmplitude w i : ℝ) := by
  let A := dominantAmplitude w i
  have hA : 0 < A := dominantAmplitude_pos hi
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  have hle : 2 * A ≤ q := by
    simpa [A, dominantAmplitude] using
      two_mul_coordinate_le_modulus_of_centered_fourier hcentered i
  have hne : 2 * A ≠ q := by
    intro heq
    obtain ⟨k, hk⟩ := hq
    omega
  have hlt : 2 * A < q := lt_of_le_of_ne hle hne
  apply (lt_div_iff₀ hAreal).2
  exact_mod_cast hlt

/-- Generic unconditional Fourier-row endgame for a dominant high-activity
event.  The activity condition is discarded only after the row bound has
retained the dominant coordinate. -/
private theorem sparseThresholdDominantHighActivity128_of_fourierRow
    {q d : ℕ} (w : Fin d → ℤ) (inputThreshold : ℕ) (i : Fin d)
    (z K thresholdUpper : ℝ)
    (hinputThreshold : 0 < inputThreshold) (hi : w i ≠ 0)
    (hz : 0 < z)
    (hthreshold : (inputThreshold : ℝ) ^ 2 /
        (dominantAmplitude w i : ℝ) ^ 2 ≤ thresholdUpper)
    (hrow :
      (∫ row, Real.exp (-(z / (dominantAmplitude w i : ℝ) ^ 2) *
          sparseLowerRowKernel q w row)
          ∂(sparseRademacherRow d).toMeasure) ≤ K)
    (hratio : Real.exp (29 * z * thresholdUpper) * K ^ 256 <
      (187 / 200 : ℝ) * (2 : ℝ)⁻¹ ^ 128) :
    eventProbability (sparseRademacherMatrix 256 d)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
              inputThreshold q w J ∧
            29 ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ)) <
      sparseThreshold128HighActivityBudget := by
  let A := dominantAmplitude w i
  let s : ℝ := z * (inputThreshold : ℝ) ^ 2 / (A : ℝ) ^ 2
  have hA : 0 < A := dominantAmplitude_pos hi
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  have hbReal : (0 : ℝ) < inputThreshold := by exact_mod_cast hinputThreshold
  have hs : 0 < s := by dsimp [s]; positivity
  have hcoefficient : s / (inputThreshold : ℝ) ^ 2 =
      z / (A : ℝ) ^ 2 := by
    dsimp [s]
    field_simp
  have hrowThreshold :
      ∫ row, Real.exp
          (-(s / (inputThreshold : ℝ) ^ 2) * sparseLowerRowKernel q w row)
          ∂(sparseRademacherRow d).toMeasure ≤ K := by
    simpa only [hcoefficient] using hrow
  have hfull := ternaryThresholdLowerTail_from_rowKernelIntegral
    q d w inputThreshold s K hinputThreshold hs hrowThreshold
  have hsUpper : s ≤ z * thresholdUpper := by
    dsimp [s]
    calc
      z * (inputThreshold : ℝ) ^ 2 / (A : ℝ) ^ 2 =
          z * ((inputThreshold : ℝ) ^ 2 / (A : ℝ) ^ 2) := by ring
      _ ≤ z * thresholdUpper :=
        mul_le_mul_of_nonneg_left hthreshold hz.le
  have hratioActual : Real.exp (29 * s) * K ^ 256 <
      (187 / 200 : ℝ) * (2 : ℝ)⁻¹ ^ 128 := by
    have hKpow : 0 ≤ K ^ 256 := by
      simpa using (even_two_mul 128).pow_nonneg K
    apply (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsUpper (by norm_num)))
      hKpow).trans_lt
    simpa only [mul_assoc] using hratio
  have hfullStrict :
      (eventProbability (sparseRademacherMatrix 256 d)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
          inputThreshold q w)).toReal <
        (187 / 200 : ℝ) * (2 : ℝ)⁻¹ ^ 128 :=
    hfull.trans_lt hratioActual
  have hjoint :
      eventProbability (sparseRademacherMatrix 256 d)
          (fun J =>
            L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
                inputThreshold q w J ∧
              29 ≤ (dominantActivityCount
                (matrixDominantActivity i J) : ℕ)) ≤
        eventProbability (sparseRademacherMatrix 256 d)
          (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
            inputThreshold q w) := by
    apply eventProbability_mono
    intro J hJ
    exact hJ.1
  rw [← ENNReal.toReal_lt_toReal
    (by
      unfold eventProbability
      exact PMF.apply_ne_top _ _)
    (by
      unfold sparseThreshold128HighActivityBudget failureTarget
      finiteness)]
  calc
    _ ≤ (eventProbability (sparseRademacherMatrix 256 d)
          (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
            inputThreshold q w)).toReal :=
      ENNReal.toReal_mono
        (by
          unfold eventProbability
          exact PMF.apply_ne_top _ _) hjoint
    _ < (187 / 200 : ℝ) * (2 : ℝ)⁻¹ ^ 128 := hfullStrict
    _ = sparseThreshold128HighActivityBudget.toReal := by
      simp [sparseThreshold128HighActivityBudget, failureTarget]

theorem sparseThresholdDominantHighActivity128_fourierHighResidual_of_replay
    (replay : CertificateContracts.SparseL2ThresholdDominantReplay128)
    {q d : ℕ} (w : Fin d → ℤ) (inputThreshold : ℕ) (i : Fin d)
    (hq : Odd q) (hcentered : CenteredInput q w)
    (hinputThreshold : 0 < inputThreshold) (hi : w i ≠ 0)
    (hdominant : 49 * inputThreshold < 50 * (w i).natAbs)
    (hmax : ∀ j, (w j).natAbs ^ 2 ≤ (w i).natAbs ^ 2)
    (hresidual : (1 / 2 : ℝ) ≤ dominantResidualRatio w i)
    (hmargin : 3 * inputThreshold ≤ q) :
    eventProbability (sparseRademacherMatrix 256 d)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
              inputThreshold q w J ∧
            29 ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ)) <
      sparseThreshold128HighActivityBudget := by
  let A := dominantAmplitude w i
  let B := (q : ℝ) / (A : ℝ)
  let r := (inputThreshold : ℝ) ^ 2 / (A : ℝ) ^ 2
  have hA : 0 < A := dominantAmplitude_pos hi
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  have hB2 : 2 < B := by
    simpa [B, A] using
      two_lt_dominant_modulus_ratio i hq hcentered hi
  have hrModulus : 9 * r ≤ B ^ 2 := by
    simpa [r, B, A, dominantThresholdRatio] using
      nine_mul_dominantThresholdRatio_le_modulusRatio_sq
        w i inputThreshold hi hmargin
  by_cases hB3 : 3 ≤ B
  · exact sparseThresholdDominantHighActivity128_retained_of_replay replay
      w inputThreshold i hq hinputThreshold hi hdominant hmax hresidual
        (by simpa [B, A] using hB3)
  have hB3le : B ≤ 3 := le_of_not_ge hB3
  obtain ⟨support, hlower, hupper, hdichotomy⟩ :=
    exists_halfCutoff_dominantRemainder_subprofile_with_dichotomy
      w i hi hresidual hmax
  rcases hdichotomy with hlarge | hcap
  · obtain ⟨j, hj, hlarge, hjUpper⟩ := hlarge
    by_cases hB5 : B ≤ 5 / 2
    · obtain ⟨cell, hcellMem, hcellLower, hcellUpper, hrCell,
          hcellCertified⟩ :=
        replay.singletonFourierCover hB2.le hB5 hrModulus
      have hcellPos :=
        SparseThresholdDominant.SingletonFourierNumeric128.certifiedCheck_geometry
          cell hcellCertified
      have hrowBase :=
        sparseRow_centeredGaussian_le_dominantSingletonLowFourierRow
          w i j (z := (9 / 4 : ℝ)) hq hi (by norm_num)
            (by simpa [B, A] using hB2)
            hmax hlarge
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
      have hratio :=
        SparseThresholdDominant.SingletonFourierNumeric128.certifiedCheck_sound
          cell hcellCertified
      exact sparseThresholdDominantHighActivity128_of_fourierRow
        w inputThreshold i (9 / 4)
          (thresholdDominantSingletonLowFourierCellRow
            (cell.lower : ℝ) (cell.upper : ℝ) (9 / 4))
          (cell.thresholdUpper : ℝ) hinputThreshold hi (by norm_num)
            (by simpa [r] using hrCell) hrow
            (by simpa [SparseThresholdDominant.SingletonFourierNumeric128.z]
              using hratio)
    · have hB5lower : 5 / 2 ≤ B := le_of_not_ge hB5
      obtain ⟨cell, hcellMem, hcellLower, hcellUpper, hrCell,
          hcellCertified⟩ :=
        replay.cappedFourierCover hB2.le hB3le hrModulus
      have hgeometry :=
        SparseThresholdDominant.CappedFourierNumeric128.certifiedCheck_geometry
          cell hcellCertified
      have hrowBase :=
        sparseRow_centeredGaussian_le_dominantLargeSingletonFourierRow
          w i j (z := (9 / 4 : ℝ)) hq hi (by norm_num)
            (by simpa [B, A] using hB5lower)
            hmax hlarge
      have hrowCell := thresholdDominantCappedFourierRow_le_cell
        hgeometry.1 hcellLower hcellUpper hgeometry.2
          (by norm_num : (0 : ℝ) < 9 / 4)
      have hrow :
          (∫ row, Real.exp (-((9 / 4 : ℝ) / (A : ℝ) ^ 2) *
              sparseLowerRowKernel q w row)
              ∂(sparseRademacherRow d).toMeasure) ≤
            thresholdDominantCappedFourierCellRow
              (cell.lower : ℝ) (cell.upper : ℝ) (9 / 4) :=
        hrowBase.trans (by simpa [B, A] using hrowCell)
      have hratio :=
        SparseThresholdDominant.CappedFourierNumeric128.certifiedCheck_sound
          cell hcellCertified
      exact sparseThresholdDominantHighActivity128_of_fourierRow
        w inputThreshold i (9 / 4)
          (thresholdDominantCappedFourierCellRow
            (cell.lower : ℝ) (cell.upper : ℝ) (9 / 4))
          (cell.thresholdUpper : ℝ) hinputThreshold hi (by norm_num)
            (by simpa [r] using hrCell) hrow
            (by simpa [SparseThresholdDominant.CappedFourierNumeric128.z]
              using hratio)
  · obtain ⟨cell, hcellMem, hcellLower, hcellUpper, hrCell,
        hcellCertified⟩ :=
      replay.cappedFourierCover hB2.le hB3le hrModulus
    have hgeometry :=
      SparseThresholdDominant.CappedFourierNumeric128.certifiedCheck_geometry
        cell hcellCertified
    have hrowBase := sparseRow_centeredGaussian_le_dominantCappedFourierRow
      w i support (z := (9 / 4 : ℝ)) hq hi (by norm_num)
        (by simpa [B, A] using hB2)
        hmax hlower hcap
    have hrowCell := thresholdDominantCappedFourierRow_le_cell
      hgeometry.1 hcellLower hcellUpper hgeometry.2
        (by norm_num : (0 : ℝ) < 9 / 4)
    have hrow :
        (∫ row, Real.exp (-((9 / 4 : ℝ) / (A : ℝ) ^ 2) *
            sparseLowerRowKernel q w row)
            ∂(sparseRademacherRow d).toMeasure) ≤
          thresholdDominantCappedFourierCellRow
            (cell.lower : ℝ) (cell.upper : ℝ) (9 / 4) :=
      hrowBase.trans (by simpa [B, A] using hrowCell)
    have hratio :=
      SparseThresholdDominant.CappedFourierNumeric128.certifiedCheck_sound
        cell hcellCertified
    exact sparseThresholdDominantHighActivity128_of_fourierRow
      w inputThreshold i (9 / 4)
        (thresholdDominantCappedFourierCellRow
          (cell.lower : ℝ) (cell.upper : ℝ) (9 / 4))
        (cell.thresholdUpper : ℝ) hinputThreshold hi (by norm_num)
          (by simpa [r] using hrCell) hrow
          (by simpa [SparseThresholdDominant.CappedFourierNumeric128.z]
            using hratio)

end CertifiedJL
