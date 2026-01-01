/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.CappedFourierCover128RowCaps

/-! # Replayed capped-Fourier cover for 512 rows at 256 bits -/

namespace CertifiedJL.SparseThresholdDominant.CappedFourierCover512Bits256

open CappedFourierNumeric128 CappedFourierCover128

def budget : ℚ := 24 / (25 * 2 ^ 256)

set_option maxRecDepth 100000 in
theorem cells_certified :
    cells.all (certifiedCheckAt 512 57 budget) = true := by
  change cells.all (fun cell => safeCheck cell &&
    TargetNumeric.certifiedCheckAt 512 57 z
      cell.thresholdUpper cell.rowUpper budget) = true
  exact TargetNumeric.all_and_eq_true_of_all cells safeCheck _
    CappedFourierCover128.cells_safe (by decide +kernel)

theorem certified_of_mem {cell : Cell} (hmem : cell ∈ cells) :
    certifiedCheckAt 512 57 budget cell = true := by
  have h := cells_certified
  rw [List.all_eq_true] at h
  exact h cell hmem

/-- The inherited no-gap modulus cover, replayed at this target. -/
theorem exists_cover_cell {B r : ℝ}
    (hB2 : 2 ≤ B) (hB3 : B ≤ 3) (hr : 9 * r ≤ B ^ 2) :
    ∃ cell : Cell, cell ∈ cells ∧
      (cell.lower : ℝ) ≤ B ∧ B ≤ cell.upper ∧
      r ≤ cell.thresholdUpper ∧
      (2 : ℝ) ≤ cell.lower ∧ (cell.upper : ℝ) ≤ 3 ∧
      Real.exp (57 * (z : ℝ) * (cell.thresholdUpper : ℝ)) *
          thresholdDominantCappedFourierCellRow
            (cell.lower : ℝ) (cell.upper : ℝ) z ^ 512 <
        (budget : ℝ) := by
  obtain ⟨cell, hmem, hlower, hupper, hthreshold, _⟩ :=
    CappedFourierCover128.exists_certified_cell hB2 hB3 hr
  have hcert := certified_of_mem hmem
  have hgeometry := certifiedCheckAt_geometry 512 57 budget cell hcert
  exact ⟨cell, hmem, hlower, hupper, hthreshold, hgeometry.1,
    hgeometry.2, certifiedCheckAt_sound 512 57 budget cell hcert⟩

end CertifiedJL.SparseThresholdDominant.CappedFourierCover512Bits256
