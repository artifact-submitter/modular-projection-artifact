/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.SingletonFourierCover128RowCaps

/-! # Replayed singleton-Fourier cover for 384 rows at 192 bits

The interval geometry and row enclosures are inherited from the 128-bit
certificate. Only the target-dependent exponential and power comparison is
replayed at 384 rows, squared-norm floor 43, and the 192-bit high-activity budget.
-/

namespace CertifiedJL.SparseThresholdDominant.SingletonFourierCover384Bits192

open SingletonFourierNumeric128 SingletonFourierCover128

def budget : ℚ := 19 / (20 * 2 ^ 192)

set_option maxRecDepth 100000 in
theorem cells_certified :
    cells.all (certifiedCheckAt 384 43 budget) = true := by
  change cells.all (fun cell => safeCheck cell &&
    TargetNumeric.certifiedCheckAt 384 43 z
      cell.thresholdUpper cell.rowUpper budget) = true
  exact TargetNumeric.all_and_eq_true_of_all cells safeCheck _
    SingletonFourierCover128.cells_safe (by decide +kernel)

theorem certified_of_mem {cell : Cell} (hmem : cell ∈ cells) :
    certifiedCheckAt 384 43 budget cell = true := by
  have h := cells_certified
  rw [List.all_eq_true] at h
  exact h cell hmem

/-- The inherited no-gap modulus cover, replayed at the 384/43 target. -/
theorem exists_cover_cell {B r : ℝ}
    (hB2 : 2 ≤ B) (hB5 : B ≤ 5 / 2) (hr : 9 * r ≤ B ^ 2) :
    ∃ cell : Cell, cell ∈ cells ∧
      (cell.lower : ℝ) ≤ B ∧ B ≤ cell.upper ∧
      r ≤ cell.thresholdUpper ∧
      (0 : ℝ) < cell.lower ∧
      Real.exp (43 * (z : ℝ) * (cell.thresholdUpper : ℝ)) *
          thresholdDominantSingletonLowFourierCellRow
            (cell.lower : ℝ) (cell.upper : ℝ) z ^ 384 <
        (budget : ℝ) := by
  obtain ⟨cell, hmem, hlower, hupper, hthreshold, _⟩ :=
    SingletonFourierCover128.exists_certified_cell hB2 hB5 hr
  have hcert := certified_of_mem hmem
  exact ⟨cell, hmem, hlower, hupper, hthreshold,
    certifiedCheckAt_geometry 384 43 budget cell hcert,
    certifiedCheckAt_sound 384 43 budget cell hcert⟩

end CertifiedJL.SparseThresholdDominant.SingletonFourierCover384Bits192
