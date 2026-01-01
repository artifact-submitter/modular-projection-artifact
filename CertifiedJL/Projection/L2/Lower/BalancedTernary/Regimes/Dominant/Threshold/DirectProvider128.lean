/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Spec
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Soundness.ThresholdBits128
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.Analytic
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.Zero

/-!
# Low-residual dominant provider at 128 bits

This module translates the public threshold hypotheses into the three
dimensionless parameters used by the exact low-residual cover.  The cover
itself contains no fallback cell: its checked binary tree returns a cell only
after proving all four faces and the independent normalized-modulus endpoint.
-/

open scoped ENNReal

namespace CertifiedJL

private theorem two_mul_coordinate_le_modulus_of_centered
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

/-- The exact direct-cell cover closes every positive residual ratio at most
`1/2`, uniformly over the full public-threshold domain. -/
theorem sparseThresholdDominantHighActivity128_direct_of_replay
    (replay : CertificateContracts.SparseL2ThresholdDominantReplay128)
    {q d : ℕ} (w : Fin d → ℤ) (inputThreshold : ℕ) (i : Fin d)
    (hq : Odd q) (hcentered : CenteredInput q w)
    (_hpositive : 0 < inputThreshold)
    (hnorm : InputThresholdAtMostNorm inputThreshold w)
    (hmargin : 3 * inputThreshold ≤ q)
    (hdominant : 49 * inputThreshold < 50 * (w i).natAbs)
    (huPositive : 0 < dominantResidualRatio w i)
    (huHalf : dominantResidualRatio w i ≤ 1 / 2) :
    eventProbability (sparseRademacherMatrix 256 d)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
              inputThreshold q w J ∧
            29 ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ)) <
      sparseThreshold128HighActivityBudget := by
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
  have hrZero : 0 ≤ r := by
    exact dominantThresholdRatio_nonneg w i inputThreshold
  have hrUpper : r ≤ 2500 / 2401 :=
    (dominantThresholdRatio_lt_dominantCap w i inputThreshold hdominant).le
  have hrFeasible : r ≤ 1 + u :=
    dominantThresholdRatio_le_one_add_residualRatio
      w i inputThreshold hi hnorm
  have hBtwo : 2 ≤ B := by
    dsimp [B]
    apply (le_div_iff₀ hAReal).2
    have hcoordinate := two_mul_coordinate_le_modulus_of_centered hcentered i
    exact_mod_cast hcoordinate
  have hrModulus : 9 * r ≤ B ^ 2 := by
    exact nine_mul_dominantThresholdRatio_le_modulusRatio_sq
      w i inputThreshold hi hmargin
  obtain ⟨entry, hentryValid, huLower, huUpper, hrCell, hBCell,
      hmajorant⟩ := replay.directCover u r B huZero (by simpa [u] using huHalf)
        hrZero hrUpper hrFeasible hBtwo hrModulus
  have hevent := dominantThresholdHighActivity_le_thresholdCell
    w i inputThreshold entry.cell.decode hq hi hentryValid.1
      (by simpa [u] using huPositive) huLower huUpper hrCell hBCell
  have hreal :
      (eventProbability (sparseRademacherMatrix 256 d)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
              inputThreshold q w J ∧
            29 ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ))).toReal <
        (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) :=
    hevent.trans_lt hmajorant
  rw [← ENNReal.toReal_lt_toReal
    (by
      unfold eventProbability
      exact PMF.apply_ne_top _ _)
    (by
      unfold sparseThreshold128HighActivityBudget failureTarget
      finiteness)]
  calc
    _ < (((187 / (200 * 2 ^ 128) : ℚ) : ℝ)) := hreal
    _ = sparseThreshold128HighActivityBudget.toReal := by
      simp [sparseThreshold128HighActivityBudget, failureTarget]
      norm_num [div_pow]

/-- The direct low-residual provider, including the exact zero-residual
endpoint.  Keeping this split behind one theorem prevents downstream
assemblies from overlooking the degenerate profile. -/
theorem sparseThresholdDominantHighActivity128_lowResidual_of_replay
    (replay : CertificateContracts.SparseL2ThresholdDominantReplay128)
    {q d : ℕ} (w : Fin d → ℤ) (inputThreshold : ℕ) (i : Fin d)
    (hq : Odd q) (hcentered : CenteredInput q w)
    (hpositive : 0 < inputThreshold)
    (hnorm : InputThresholdAtMostNorm inputThreshold w)
    (hmargin : 3 * inputThreshold ≤ q)
    (hdominant : 49 * inputThreshold < 50 * (w i).natAbs)
    (huHalf : dominantResidualRatio w i ≤ 1 / 2) :
    eventProbability (sparseRademacherMatrix 256 d)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29)
              inputThreshold q w J ∧
            29 ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ)) <
      sparseThreshold128HighActivityBudget := by
  have hi : w i ≠ 0 := by
    intro hiZero
    rw [hiZero] at hdominant
    simp at hdominant
  by_cases huZero : dominantResidualRatio w i = 0
  · rw [sparseThresholdDominantHighActivity_zeroResidual_probability_eq_zero
      w inputThreshold i hq hcentered hnorm hi huZero]
    norm_num [sparseThreshold128HighActivityBudget, failureTarget]
    exact ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _
  · exact sparseThresholdDominantHighActivity128_direct_of_replay replay
      w inputThreshold i hq hcentered hpositive hnorm hmargin hdominant
        (lt_of_le_of_ne
          (by
            unfold dominantResidualRatio
            positivity)
          (Ne.symm huZero)) huHalf

end CertifiedJL
