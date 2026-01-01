/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.CappedFourierCover256Bits192Selector
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.SingletonPhaseFourierCover256Bits192Selector
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Soundness.TargetNumeric

/-!
# Target-selected Fourier covers for 192 rows, floor 12, and 128 bits

The analytic row enclosures and modulus cells are inherited from the compact
256-row endpoint.  The shared target checker replays only the exponential,
the 192nd power, and the new high-activity budget.
-/

namespace CertifiedJL.SparseThresholdDominant

namespace CappedFourierCover192Bits128

open CappedFourierNumeric256Bits192

def budget : ℚ := 19 / (20 * 2 ^ 128)

def targetCheck (cell : Cell) : Bool :=
  safeCheck cell &&
    TargetNumeric.certifiedCheckAt 192 12 z cell.thresholdUpper
      cell.rowUpper budget

set_option maxRecDepth 100000 in
theorem cells_certified :
    CappedFourierCover256Bits192.cells.all targetCheck = true := by
  change CappedFourierCover256Bits192.cells.all (fun cell =>
    safeCheck cell && TargetNumeric.certifiedCheckAt 192 12 z
      cell.thresholdUpper cell.rowUpper budget) = true
  exact TargetNumeric.all_and_eq_true_of_all
    CappedFourierCover256Bits192.cells safeCheck _
    CappedFourierCover256Bits192.cells_safe (by decide +kernel)

theorem targetCheck_of_mem {cell : Cell}
    (hmem : cell ∈ CappedFourierCover256Bits192.cells) :
    targetCheck cell = true := by
  have h := cells_certified
  rw [List.all_eq_true] at h
  exact h cell hmem

theorem targetCheck_sound (cell : Cell) (hcheck : targetCheck cell = true) :
    Real.exp (12 * (z : ℝ) * (cell.thresholdUpper : ℝ)) *
        thresholdDominantCappedFourierCellRow
          (cell.lower : ℝ) (cell.upper : ℝ) z ^ 192 <
      (budget : ℝ) := by
  have hchecks : safeCheck cell = true ∧
      TargetNumeric.certifiedCheckAt 192 12 z cell.thresholdUpper
        cell.rowUpper budget = true := by
    simpa only [targetCheck, Bool.and_eq_true] using hcheck
  have hrow := semanticRow_bounds_of_safeCheck cell hchecks.1
  exact TargetNumeric.certifiedCheckAt_sound 192 12 z cell.thresholdUpper
    cell.rowUpper budget
    (thresholdDominantCappedFourierCellRow
      (cell.lower : ℝ) (cell.upper : ℝ) z)
    hrow.1 hrow.2 hchecks.2

/-- The inherited twenty-cell modulus cover, replayed at the 192/12/128
target. -/
theorem exists_cover_cell {B r : ℝ}
    (hB2 : 2 ≤ B) (hB3 : B ≤ 3) (hr : 9 * r ≤ B ^ 2) :
    ∃ cell : Cell, cell ∈ CappedFourierCover256Bits192.cells ∧
      (cell.lower : ℝ) ≤ B ∧ B ≤ cell.upper ∧
      r ≤ cell.thresholdUpper ∧
      (2 : ℝ) ≤ cell.lower ∧ (cell.upper : ℝ) ≤ 3 ∧
      Real.exp (12 * (z : ℝ) * (cell.thresholdUpper : ℝ)) *
          thresholdDominantCappedFourierCellRow
            (cell.lower : ℝ) (cell.upper : ℝ) z ^ 192 <
        (budget : ℝ) := by
  obtain ⟨cell, hmem, hlower, hupper, hthreshold, hold⟩ :=
    CappedFourierCover256Bits192.exists_certified_cell hB2 hB3 hr
  have hgeometry := certifiedCheck_geometry cell hold
  exact ⟨cell, hmem, hlower, hupper, hthreshold, hgeometry.1,
    hgeometry.2, targetCheck_sound cell (targetCheck_of_mem hmem)⟩

end CappedFourierCover192Bits128

namespace SingletonPhaseFourierCover192Bits128

open SingletonPhaseFourierNumeric256Bits192

def budget : ℚ := 19 / (20 * 2 ^ 128)

def targetCheck (cell : Cell) : Bool :=
  safeCheck cell &&
    TargetNumeric.certifiedCheckAt 192 12 z cell.thresholdUpper
      cell.rowUpper budget

set_option maxRecDepth 100000 in
theorem cells_certified :
    SingletonPhaseFourierCover256Bits192.cells.all targetCheck = true := by
  change SingletonPhaseFourierCover256Bits192.cells.all (fun cell =>
    safeCheck cell && TargetNumeric.certifiedCheckAt 192 12 z
      cell.thresholdUpper cell.rowUpper budget) = true
  exact TargetNumeric.all_and_eq_true_of_all
    SingletonPhaseFourierCover256Bits192.cells safeCheck _
    SingletonPhaseFourierCover256Bits192.cells_safe (by decide +kernel)

theorem targetCheck_of_mem {cell : Cell}
    (hmem : cell ∈ SingletonPhaseFourierCover256Bits192.cells) :
    targetCheck cell = true := by
  have h := cells_certified
  rw [List.all_eq_true] at h
  exact h cell hmem

theorem targetCheck_sound (cell : Cell) (hcheck : targetCheck cell = true) :
    Real.exp (12 * (z : ℝ) * (cell.thresholdUpper : ℝ)) *
        thresholdDominantSingletonPhaseFourierCellRow
          (cell.lower : ℝ) (cell.upper : ℝ) z ^ 192 <
      (budget : ℝ) := by
  have hchecks : safeCheck cell = true ∧
      TargetNumeric.certifiedCheckAt 192 12 z cell.thresholdUpper
        cell.rowUpper budget = true := by
    simpa only [targetCheck, Bool.and_eq_true] using hcheck
  have hrow := semanticRow_bounds_of_safeCheck cell hchecks.1
  exact TargetNumeric.certifiedCheckAt_sound 192 12 z cell.thresholdUpper
    cell.rowUpper budget
    (thresholdDominantSingletonPhaseFourierCellRow
      (cell.lower : ℝ) (cell.upper : ℝ) z)
    hrow.1 hrow.2 hchecks.2

/-- The inherited ten-cell singleton modulus cover, replayed at the
192/12/128 target. -/
theorem exists_cover_cell {B r : ℝ}
    (hB2 : 2 ≤ B) (hB5 : B ≤ 5 / 2) (hr : 9 * r ≤ B ^ 2) :
    ∃ cell : Cell, cell ∈ SingletonPhaseFourierCover256Bits192.cells ∧
      (cell.lower : ℝ) ≤ B ∧ B ≤ cell.upper ∧
      r ≤ cell.thresholdUpper ∧
      (2 : ℝ) ≤ cell.lower ∧ (cell.upper : ℝ) ≤ 3 ∧
      Real.exp (12 * (z : ℝ) * (cell.thresholdUpper : ℝ)) *
          thresholdDominantSingletonPhaseFourierCellRow
            (cell.lower : ℝ) (cell.upper : ℝ) z ^ 192 <
        (budget : ℝ) := by
  obtain ⟨cell, hmem, hlower, hupper, hthreshold, hold⟩ :=
    SingletonPhaseFourierCover256Bits192.exists_certified_cell hB2 hB5 hr
  have hgeometry := certifiedCheck_geometry cell hold
  exact ⟨cell, hmem, hlower, hupper, hthreshold, hgeometry.1,
    hgeometry.2, targetCheck_sound cell (targetCheck_of_mem hmem)⟩

end SingletonPhaseFourierCover192Bits128

end CertifiedJL.SparseThresholdDominant
