/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.SingletonFourierCover128RowCaps

/-! # Replayed singleton-Fourier cover for 512 rows, floor 73, and 193 bits -/

namespace CertifiedJL.SparseThresholdDominant.SingletonFourierCover512Floor73Bits193

open SingletonFourierNumeric128 SingletonFourierCover128

def budget : ℚ := 99999 / (100000 * 2 ^ 193)

-- Kernel normalization of the full finite cover needs additional recursion depth.
set_option maxRecDepth 100000 in
theorem cells_certified :
    cells.all (certifiedCheckAt 512 73 budget) = true := by
  change cells.all (fun cell => safeCheck cell &&
    TargetNumeric.certifiedCheckAt 512 73 z
      cell.thresholdUpper cell.rowUpper budget) = true
  exact TargetNumeric.all_and_eq_true_of_all cells safeCheck _
    SingletonFourierCover128.cells_safe (by decide +kernel)

theorem certified_of_mem {cell : Cell} (hmem : cell ∈ cells) :
    certifiedCheckAt 512 73 budget cell = true := by
  have h := cells_certified
  rw [List.all_eq_true] at h
  exact h cell hmem

/-- The inherited no-gap modulus cover, replayed at this target. -/
theorem exists_cover_cell {B r : ℝ}
    (hB2 : 2 ≤ B) (hB5 : B ≤ 5 / 2) (hr : 9 * r ≤ B ^ 2) :
    ∃ cell : Cell, cell ∈ cells ∧
      (cell.lower : ℝ) ≤ B ∧ B ≤ cell.upper ∧
      r ≤ cell.thresholdUpper ∧
      (0 : ℝ) < cell.lower ∧
      Real.exp (73 * (z : ℝ) * (cell.thresholdUpper : ℝ)) *
          thresholdDominantSingletonLowFourierCellRow
            (cell.lower : ℝ) (cell.upper : ℝ) z ^ 512 <
        (budget : ℝ) := by
  obtain ⟨cell, hmem, hlower, hupper, hthreshold, _⟩ :=
    SingletonFourierCover128.exists_certified_cell hB2 hB5 hr
  have hcert := certified_of_mem hmem
  exact ⟨cell, hmem, hlower, hupper, hthreshold,
    certifiedCheckAt_geometry 512 73 budget cell hcert,
    certifiedCheckAt_sound 512 73 budget cell hcert⟩

end CertifiedJL.SparseThresholdDominant.SingletonFourierCover512Floor73Bits193
