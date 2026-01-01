/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.CappedFourierCover256Bits192

/-! # Certified capped-Fourier selector for the 256-row, 192-bit endpoint -/

namespace CertifiedJL
namespace SparseThresholdDominant
namespace CappedFourierCover256Bits192

open CappedFourierNumeric256Bits192

set_option maxRecDepth 100000 in
theorem cells_certified : cells.all certifiedCheck = true := by
  decide +kernel

/-- Reusable analytic row enclosures for target-only replay. -/
theorem cells_safe : cells.all safeCheck = true := by
  have hcertified := cells_certified
  rw [List.all_eq_true] at hcertified ⊢
  intro cell hmem
  exact safeCheck_of_certifiedCheck (hcertified cell hmem)

theorem certified_of_mem {cell : Cell} (hmem : cell ∈ cells) :
    certifiedCheck cell = true := by
  have h := cells_certified
  rw [List.all_eq_true] at h
  exact h cell hmem

private theorem threshold_le_of_modulus_upper {B r U : ℝ}
    (hB : 0 ≤ B) (hBU : B ≤ U) (hr : 9 * r ≤ B ^ 2) :
    r ≤ U ^ 2 / 9 := by
  have hprod : 0 ≤ (U - B) * (U + B) :=
    mul_nonneg (sub_nonneg.mpr hBU) (by linarith)
  nlinarith

/-- The twenty closed cells cover every normalized modulus in `[2,3]`.
The threshold coordinate is transported from `9r ≤ B²` to the selected
cell's upper endpoint. -/
theorem exists_certified_cell {B r : ℝ}
    (hB2 : 2 ≤ B) (hB3 : B ≤ 3) (hr : 9 * r ≤ B ^ 2) :
    ∃ cell : Cell, cell ∈ cells ∧
      (cell.lower : ℝ) ≤ B ∧ B ≤ cell.upper ∧
      r ≤ cell.thresholdUpper ∧ certifiedCheck cell = true := by
  by_cases h00 : B ≤ (41 / 20 : ℝ)
  · refine ⟨cell00, by simp [cells], ?_, ?_, ?_, (certified_of_mem (by simp [cells]))⟩
    · norm_num [cell00]
      linarith
    · norm_num [cell00] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h00 hr
      norm_num [cell00] at ⊢ hthreshold
      exact hthreshold
  by_cases h01 : B ≤ (42 / 20 : ℝ)
  · refine ⟨cell01, by simp [cells], ?_, ?_, ?_, (certified_of_mem (by simp [cells]))⟩
    · norm_num [cell01]
      linarith
    · norm_num [cell01] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h01 hr
      norm_num [cell01] at ⊢ hthreshold
      exact hthreshold
  by_cases h02 : B ≤ (43 / 20 : ℝ)
  · refine ⟨cell02, by simp [cells], ?_, ?_, ?_, (certified_of_mem (by simp [cells]))⟩
    · norm_num [cell02]
      linarith
    · norm_num [cell02] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h02 hr
      norm_num [cell02] at ⊢ hthreshold
      exact hthreshold
  by_cases h03 : B ≤ (44 / 20 : ℝ)
  · refine ⟨cell03, by simp [cells], ?_, ?_, ?_, (certified_of_mem (by simp [cells]))⟩
    · norm_num [cell03]
      linarith
    · norm_num [cell03] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h03 hr
      norm_num [cell03] at ⊢ hthreshold
      exact hthreshold
  by_cases h04 : B ≤ (45 / 20 : ℝ)
  · refine ⟨cell04, by simp [cells], ?_, ?_, ?_, (certified_of_mem (by simp [cells]))⟩
    · norm_num [cell04]
      linarith
    · norm_num [cell04] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h04 hr
      norm_num [cell04] at ⊢ hthreshold
      exact hthreshold
  by_cases h05 : B ≤ (46 / 20 : ℝ)
  · refine ⟨cell05, by simp [cells], ?_, ?_, ?_, (certified_of_mem (by simp [cells]))⟩
    · norm_num [cell05]
      linarith
    · norm_num [cell05] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h05 hr
      norm_num [cell05] at ⊢ hthreshold
      exact hthreshold
  by_cases h06 : B ≤ (47 / 20 : ℝ)
  · refine ⟨cell06, by simp [cells], ?_, ?_, ?_, (certified_of_mem (by simp [cells]))⟩
    · norm_num [cell06]
      linarith
    · norm_num [cell06] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h06 hr
      norm_num [cell06] at ⊢ hthreshold
      exact hthreshold
  by_cases h07 : B ≤ (48 / 20 : ℝ)
  · refine ⟨cell07, by simp [cells], ?_, ?_, ?_, (certified_of_mem (by simp [cells]))⟩
    · norm_num [cell07]
      linarith
    · norm_num [cell07] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h07 hr
      norm_num [cell07] at ⊢ hthreshold
      exact hthreshold
  by_cases h08 : B ≤ (49 / 20 : ℝ)
  · refine ⟨cell08, by simp [cells], ?_, ?_, ?_, (certified_of_mem (by simp [cells]))⟩
    · norm_num [cell08]
      linarith
    · norm_num [cell08] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h08 hr
      norm_num [cell08] at ⊢ hthreshold
      exact hthreshold
  by_cases h09 : B ≤ (50 / 20 : ℝ)
  · refine ⟨cell09, by simp [cells], ?_, ?_, ?_, (certified_of_mem (by simp [cells]))⟩
    · norm_num [cell09]
      linarith
    · norm_num [cell09] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h09 hr
      norm_num [cell09] at ⊢ hthreshold
      exact hthreshold
  by_cases h10 : B ≤ (51 / 20 : ℝ)
  · refine ⟨cell10, by simp [cells], ?_, ?_, ?_, (certified_of_mem (by simp [cells]))⟩
    · norm_num [cell10]
      linarith
    · norm_num [cell10] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h10 hr
      norm_num [cell10] at ⊢ hthreshold
      exact hthreshold
  by_cases h11 : B ≤ (52 / 20 : ℝ)
  · refine ⟨cell11, by simp [cells], ?_, ?_, ?_, (certified_of_mem (by simp [cells]))⟩
    · norm_num [cell11]
      linarith
    · norm_num [cell11] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h11 hr
      norm_num [cell11] at ⊢ hthreshold
      exact hthreshold
  by_cases h12 : B ≤ (53 / 20 : ℝ)
  · refine ⟨cell12, by simp [cells], ?_, ?_, ?_, (certified_of_mem (by simp [cells]))⟩
    · norm_num [cell12]
      linarith
    · norm_num [cell12] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h12 hr
      norm_num [cell12] at ⊢ hthreshold
      exact hthreshold
  by_cases h13 : B ≤ (54 / 20 : ℝ)
  · refine ⟨cell13, by simp [cells], ?_, ?_, ?_, (certified_of_mem (by simp [cells]))⟩
    · norm_num [cell13]
      linarith
    · norm_num [cell13] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h13 hr
      norm_num [cell13] at ⊢ hthreshold
      exact hthreshold
  by_cases h14 : B ≤ (55 / 20 : ℝ)
  · refine ⟨cell14, by simp [cells], ?_, ?_, ?_, (certified_of_mem (by simp [cells]))⟩
    · norm_num [cell14]
      linarith
    · norm_num [cell14] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h14 hr
      norm_num [cell14] at ⊢ hthreshold
      exact hthreshold
  by_cases h15 : B ≤ (56 / 20 : ℝ)
  · refine ⟨cell15, by simp [cells], ?_, ?_, ?_, (certified_of_mem (by simp [cells]))⟩
    · norm_num [cell15]
      linarith
    · norm_num [cell15] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h15 hr
      norm_num [cell15] at ⊢ hthreshold
      exact hthreshold
  by_cases h16 : B ≤ (57 / 20 : ℝ)
  · refine ⟨cell16, by simp [cells], ?_, ?_, ?_, (certified_of_mem (by simp [cells]))⟩
    · norm_num [cell16]
      linarith
    · norm_num [cell16] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h16 hr
      norm_num [cell16] at ⊢ hthreshold
      exact hthreshold
  by_cases h17 : B ≤ (58 / 20 : ℝ)
  · refine ⟨cell17, by simp [cells], ?_, ?_, ?_, (certified_of_mem (by simp [cells]))⟩
    · norm_num [cell17]
      linarith
    · norm_num [cell17] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h17 hr
      norm_num [cell17] at ⊢ hthreshold
      exact hthreshold
  by_cases h18 : B ≤ (59 / 20 : ℝ)
  · refine ⟨cell18, by simp [cells], ?_, ?_, ?_, (certified_of_mem (by simp [cells]))⟩
    · norm_num [cell18]
      linarith
    · norm_num [cell18] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h18 hr
      norm_num [cell18] at ⊢ hthreshold
      exact hthreshold
  · refine ⟨cell19, by simp [cells], ?_, ?_, ?_, (certified_of_mem (by simp [cells]))⟩
    · norm_num [cell19]
      linarith
    · norm_num [cell19] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) hB3 hr
      norm_num [cell19] at ⊢ hthreshold
      exact hthreshold

end CappedFourierCover256Bits192
end SparseThresholdDominant
end CertifiedJL
