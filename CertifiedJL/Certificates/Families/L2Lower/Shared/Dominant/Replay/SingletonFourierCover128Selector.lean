/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.SingletonFourierCover128Verified

/-! # Gap-free selector for the low-singleton modulus cover -/

namespace CertifiedJL
namespace SparseThresholdDominant
namespace SingletonFourierCover128

open SingletonFourierNumeric128

private theorem threshold_le_of_modulus_upper {B r U : ℝ}
    (hB : 0 ≤ B) (hBU : B ≤ U) (hr : 9 * r ≤ B ^ 2) :
    r ≤ U ^ 2 / 9 := by
  have hprod : 0 ≤ (U - B) * (U + B) :=
    mul_nonneg (sub_nonneg.mpr hBU) (by linarith)
  nlinarith

/-- The ten closed cells cover every normalized modulus in `[2,5/2]`. -/
theorem exists_certified_cell {B r : ℝ}
    (hB2 : 2 ≤ B) (hB5 : B ≤ 5 / 2) (hr : 9 * r ≤ B ^ 2) :
    ∃ cell : Cell, cell ∈ cells ∧
      (cell.lower : ℝ) ≤ B ∧ B ≤ cell.upper ∧
      r ≤ cell.thresholdUpper ∧ certifiedCheck cell = true := by
  by_cases h00 : B ≤ (41 / 20 : ℝ)
  · refine ⟨cell00, by simp [cells], ?_, ?_, ?_, cell00_certified⟩
    · norm_num [cell00]
      linarith
    · norm_num [cell00] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h00 hr
      norm_num [cell00] at ⊢ hthreshold
      exact hthreshold
  by_cases h01 : B ≤ (42 / 20 : ℝ)
  · refine ⟨cell01, by simp [cells], ?_, ?_, ?_, cell01_certified⟩
    · norm_num [cell01]
      linarith
    · norm_num [cell01] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h01 hr
      norm_num [cell01] at ⊢ hthreshold
      exact hthreshold
  by_cases h02 : B ≤ (43 / 20 : ℝ)
  · refine ⟨cell02, by simp [cells], ?_, ?_, ?_, cell02_certified⟩
    · norm_num [cell02]
      linarith
    · norm_num [cell02] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h02 hr
      norm_num [cell02] at ⊢ hthreshold
      exact hthreshold
  by_cases h03 : B ≤ (44 / 20 : ℝ)
  · refine ⟨cell03, by simp [cells], ?_, ?_, ?_, cell03_certified⟩
    · norm_num [cell03]
      linarith
    · norm_num [cell03] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h03 hr
      norm_num [cell03] at ⊢ hthreshold
      exact hthreshold
  by_cases h04 : B ≤ (45 / 20 : ℝ)
  · refine ⟨cell04, by simp [cells], ?_, ?_, ?_, cell04_certified⟩
    · norm_num [cell04]
      linarith
    · norm_num [cell04] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h04 hr
      norm_num [cell04] at ⊢ hthreshold
      exact hthreshold
  by_cases h05 : B ≤ (46 / 20 : ℝ)
  · refine ⟨cell05, by simp [cells], ?_, ?_, ?_, cell05_certified⟩
    · norm_num [cell05]
      linarith
    · norm_num [cell05] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h05 hr
      norm_num [cell05] at ⊢ hthreshold
      exact hthreshold
  by_cases h06 : B ≤ (47 / 20 : ℝ)
  · refine ⟨cell06, by simp [cells], ?_, ?_, ?_, cell06_certified⟩
    · norm_num [cell06]
      linarith
    · norm_num [cell06] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h06 hr
      norm_num [cell06] at ⊢ hthreshold
      exact hthreshold
  by_cases h07 : B ≤ (48 / 20 : ℝ)
  · refine ⟨cell07, by simp [cells], ?_, ?_, ?_, cell07_certified⟩
    · norm_num [cell07]
      linarith
    · norm_num [cell07] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h07 hr
      norm_num [cell07] at ⊢ hthreshold
      exact hthreshold
  by_cases h08 : B ≤ (49 / 20 : ℝ)
  · refine ⟨cell08, by simp [cells], ?_, ?_, ?_, cell08_certified⟩
    · norm_num [cell08]
      linarith
    · norm_num [cell08] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) h08 hr
      norm_num [cell08] at ⊢ hthreshold
      exact hthreshold
  · refine ⟨cell09, by simp [cells], ?_, ?_, ?_, cell09_certified⟩
    · norm_num [cell09]
      linarith
    · norm_num [cell09] at ⊢
      linarith
    · have hthreshold := threshold_le_of_modulus_upper (by linarith) hB5 hr
      norm_num [cell09] at ⊢ hthreshold
      exact hthreshold

end SingletonFourierCover128
end SparseThresholdDominant
end CertifiedJL
