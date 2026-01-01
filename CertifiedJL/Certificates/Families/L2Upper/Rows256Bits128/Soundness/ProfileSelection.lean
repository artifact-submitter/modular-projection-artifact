/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.Core
import Mathlib.Tactic

/-! # Exact profile coverage for the centered-hybrid manifest -/

namespace CertifiedJL
namespace SparseUpperHybrid

/-- The 18 adjacent manifest boxes cover the entire low-profile interval. -/
theorem exists_certificate_for_profile
    {profile : ℝ} (hprofileNonneg : 0 ≤ profile)
    (hprofileUpper : profile ≤ 1 / 20) :
    ∃ certificate ∈ certificateBoxes,
      profile ∈ Set.Icc (certificate.box.profileLeft : ℝ)
        (certificate.box.profileRight : ℝ) := by
  by_cases h0 : profile ≤ (1 / 4096 : ℝ)
  · refine ⟨certificateBoxes.getD 0 default, ?_, ?_⟩
    · norm_num [certificateBoxes]
    · norm_num [certificateBoxes, replayBox]
      exact ⟨hprofileNonneg, h0⟩
  by_cases h1 : profile ≤ (1 / 2048 : ℝ)
  · refine ⟨certificateBoxes.getD 1 default, ?_, ?_⟩
    · norm_num [certificateBoxes]
    · norm_num [certificateBoxes, replayBox]
      exact ⟨le_of_not_ge h0, h1⟩
  by_cases h2 : profile ≤ (3 / 4096 : ℝ)
  · refine ⟨certificateBoxes.getD 2 default, ?_, ?_⟩
    · norm_num [certificateBoxes]
    · norm_num [certificateBoxes, replayBox]
      exact ⟨le_of_not_ge h1, h2⟩
  by_cases h3 : profile ≤ (1 / 1024 : ℝ)
  · refine ⟨certificateBoxes.getD 3 default, ?_, ?_⟩
    · norm_num [certificateBoxes]
    · norm_num [certificateBoxes, replayBox]
      exact ⟨le_of_not_ge h2, h3⟩
  by_cases h4 : profile ≤ (5 / 4096 : ℝ)
  · refine ⟨certificateBoxes.getD 4 default, ?_, ?_⟩
    · norm_num [certificateBoxes]
    · norm_num [certificateBoxes, replayBox]
      exact ⟨le_of_not_ge h3, h4⟩
  by_cases h5 : profile ≤ (3 / 2048 : ℝ)
  · refine ⟨certificateBoxes.getD 5 default, ?_, ?_⟩
    · norm_num [certificateBoxes]
    · norm_num [certificateBoxes, replayBox]
      exact ⟨le_of_not_ge h4, h5⟩
  by_cases h6 : profile ≤ (7 / 4096 : ℝ)
  · refine ⟨certificateBoxes.getD 6 default, ?_, ?_⟩
    · norm_num [certificateBoxes]
    · norm_num [certificateBoxes, replayBox]
      exact ⟨le_of_not_ge h5, h6⟩
  by_cases h7 : profile ≤ (1 / 512 : ℝ)
  · refine ⟨certificateBoxes.getD 7 default, ?_, ?_⟩
    · norm_num [certificateBoxes]
    · norm_num [certificateBoxes, replayBox]
      exact ⟨le_of_not_ge h6, h7⟩
  by_cases h8 : profile ≤ (5 / 2048 : ℝ)
  · refine ⟨certificateBoxes.getD 8 default, ?_, ?_⟩
    · norm_num [certificateBoxes]
    · norm_num [certificateBoxes, replayBox]
      exact ⟨le_of_not_ge h7, h8⟩
  by_cases h9 : profile ≤ (3 / 1024 : ℝ)
  · refine ⟨certificateBoxes.getD 9 default, ?_, ?_⟩
    · norm_num [certificateBoxes]
    · norm_num [certificateBoxes, replayBox]
      exact ⟨le_of_not_ge h8, h9⟩
  by_cases h10 : profile ≤ (1 / 256 : ℝ)
  · refine ⟨certificateBoxes.getD 10 default, ?_, ?_⟩
    · norm_num [certificateBoxes]
    · norm_num [certificateBoxes, replayBox]
      exact ⟨le_of_not_ge h9, h10⟩
  by_cases h11 : profile ≤ (3 / 512 : ℝ)
  · refine ⟨certificateBoxes.getD 11 default, ?_, ?_⟩
    · norm_num [certificateBoxes]
    · norm_num [certificateBoxes, replayBox]
      exact ⟨le_of_not_ge h10, h11⟩
  by_cases h12 : profile ≤ (1 / 128 : ℝ)
  · refine ⟨certificateBoxes.getD 12 default, ?_, ?_⟩
    · norm_num [certificateBoxes]
    · norm_num [certificateBoxes, replayBox]
      exact ⟨le_of_not_ge h11, h12⟩
  by_cases h13 : profile ≤ (3 / 256 : ℝ)
  · refine ⟨certificateBoxes.getD 13 default, ?_, ?_⟩
    · norm_num [certificateBoxes]
    · norm_num [certificateBoxes, replayBox]
      exact ⟨le_of_not_ge h12, h13⟩
  by_cases h14 : profile ≤ (1 / 64 : ℝ)
  · refine ⟨certificateBoxes.getD 14 default, ?_, ?_⟩
    · norm_num [certificateBoxes]
    · norm_num [certificateBoxes, replayBox]
      exact ⟨le_of_not_ge h13, h14⟩
  by_cases h15 : profile ≤ (3 / 128 : ℝ)
  · refine ⟨certificateBoxes.getD 15 default, ?_, ?_⟩
    · norm_num [certificateBoxes]
    · norm_num [certificateBoxes, replayBox]
      exact ⟨le_of_not_ge h14, h15⟩
  by_cases h16 : profile ≤ (1 / 32 : ℝ)
  · refine ⟨certificateBoxes.getD 16 default, ?_, ?_⟩
    · norm_num [certificateBoxes]
    · norm_num [certificateBoxes, replayBox]
      exact ⟨le_of_not_ge h15, h16⟩
  · refine ⟨certificateBoxes.getD 17 default, ?_, ?_⟩
    · norm_num [certificateBoxes]
    · norm_num [certificateBoxes, replayBox]
      exact ⟨le_of_not_ge h16, hprofileUpper⟩


end SparseUpperHybrid
end CertifiedJL
