/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.Instances.SoundnessCommon
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows192Bits128Threshold287

/-!
# Soundness facts for the 192-row, 128-bit, threshold-287 instance

All facts here are independent of the expensive generated endpoint replay.
The final low-profile theorem is parameterized only by the grouped cell and
row-majorant bridges supplied by the replay/soundness integration layer.
-/

namespace CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287Soundness

open Set
open CertifiedJL.SparseUpperContourFamily.Instances
open CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287

set_option maxRecDepth 100000
set_option exponentiation.threshold 1024

theorem profilePartitionCheck_eq_true :
    profilePartitionCheck profileBoxes highProfile.profileMinimum = true := by
  decide +kernel

theorem profileCover :
    ProfilePartitionCovers profileBoxes (highProfile.profileMinimum : ℝ) :=
  profilePartitionCheck_sound profilePartitionCheck_eq_true

theorem lowTargets : ∀ box ∈ profileBoxes, box.target ≤ 1 := by
  intro box hbox
  simp only [profileBoxes, List.mem_cons, List.not_mem_nil, or_false] at hbox
  rcases hbox with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [profileBox]

theorem highTarget : highProfile.target ≤ 1 := by
  norm_num [highProfile]

theorem lowProfileFacts : ∀ box ∈ profileBoxes,
    LowProfileFacts parameters box := by
  intro box hbox
  simp only [profileBoxes, List.mem_cons, List.not_mem_nil, or_false] at hbox
  rcases hbox with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    constructor <;>
    norm_num [profileBox, parameters, Parameters.rows,
      UpperContourKernel.phiLower, List.range_succ, Even]
  all_goals exact ⟨96, by norm_num⟩

theorem segmentGeometryCheck_eq_true : ∀ box ∈ profileBoxes,
    segmentGeometryCheck box = true := by
  intro box hbox
  simp only [profileBoxes, List.mem_cons, List.not_mem_nil, or_false] at hbox
  rcases hbox with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

theorem boxChunkCoverageCheck_eq_true : ∀ box ∈ profileBoxes,
    boxChunkCoverageCheck box = true := by
  intro box hbox
  simp only [profileBoxes, List.mem_cons, List.not_mem_nil, or_false] at hbox
  rcases hbox with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

theorem rowExpressionBaseCheck_eq_true : ∀ box ∈ profileBoxes,
    rowExpressionBaseCheck parameters box = true := by
  intro box hbox
  simp only [profileBoxes, List.mem_cons, List.not_mem_nil, or_false] at hbox
  rcases hbox with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

theorem lambdaSquareBaseCheck_eq_true : ∀ box ∈ profileBoxes,
    lambdaSquareBaseCheck parameters box = true := by
  intro box hbox
  simp only [profileBoxes, List.mem_cons, List.not_mem_nil, or_false] at hbox
  rcases hbox with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

theorem profileBox_realCapUpper_contains
    {box : ProfileBox} (hbox : box ∈ profileBoxes) {profile : ℝ}
    (hprofile : profile ∈ Icc (box.profileLeft : ℝ)
      (box.profileRight : ℝ)) :
    (realCapUpper parameters.precision box.profileLeft box.lam).Contains
      (realRowDeficitCap
        (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ)))) := by
  simp only [profileBoxes, List.mem_cons, List.not_mem_nil, or_false] at hbox
  rcases hbox with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contains_realCapUpper_of_eq_zero parameters.precision _ profile
    · simpa [profileBox] using hprofile.1
    · norm_num [profileBox]
    · norm_num [profileBox]
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  all_goals
    apply contains_realCapUpper_of_ne_zero parameters.precision _ _ profile
    · norm_num [profileBox]
    · norm_num [profileBox]
    · exact hprofile.1
    · norm_num [profileBox]
    · norm_num [profileBox]
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel

theorem highProfileFacts : HighProfileFacts parameters highProfile where
  profileMinimum_nonneg := by norm_num [highProfile]
  lam_nonneg := by norm_num [highProfile]
  lam_lt_one := by norm_num [highProfile]
  exponent_nonneg := by norm_num [parameters, highProfile]
  rows_even := ⟨96, by norm_num [parameters, Parameters.rows]⟩
  capContains := by
    intro profile hprofile
    apply contains_realCapUpper_of_ne_zero parameters.precision _ _ profile
    · norm_num [highProfile]
    · norm_num [highProfile]
    · exact hprofile
    · norm_num [highProfile]
    · norm_num [highProfile]
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel

theorem highSound : HighProfileBoxSound parameters highProfile :=
  highProfileBoxSound_of_facts highProfileFacts

def threshold : NonnegativeRatio := NonnegativeRatio.ofNat 287

theorem threshold_eq :
    threshold.toReal = (parameters.threshold : ℝ) := by
  norm_num [threshold, NonnegativeRatio.toReal, NonnegativeRatio.ofNat,
    parameters]

/-- Exact final application once the grouped cell and row-majorant bridges are
available from the integration layer. -/
theorem lowSound_of_segmentedCells
    (hcell : ∀ box ∈ profileBoxes, ∀ chunk ∈ boxChunkPlan box, ∀ offset,
      offset < chunk.count →
      (gaussianCell parameters box
        (box.segments.getD chunk.segmentIndex default)
        (chunk.start + offset)).Contains
      (gaussianCellRectangleValue parameters box
        (box.segments.getD chunk.segmentIndex default)
        (chunk.start + offset)))
    (hrow : ∀ box ∈ profileBoxes, ∀ profile : ℝ,
      profile ∈ Icc (box.profileLeft : ℝ) (box.profileRight : ℝ) →
      ∀ segment ∈ box.segments, ∀ index < segment.count,
      ∀ frequency ∈ Ioc ((segment.cellLeft index : ℚ) : ℝ)
        ((segment.cellRight index : ℚ) : ℝ),
      sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
        gaussianCellRowUpperValue parameters box segment index) :
    ∀ box ∈ profileBoxes, LowProfileBoxSound parameters box := by
  intro box hbox
  exact lowProfileBoxSound_of_segmentedCells
    (lowProfileFacts box hbox)
    (segmentGeometryCheck_eq_true box hbox)
    (boxChunkCoverageCheck_eq_true box hbox)
    (hcell box hbox)
    (fun profile hprofile ↦
      profileBox_realCapUpper_contains hbox hprofile)
    (hrow box hbox)

/-- Complete low-profile soundness from four box-level checks and the analytic
real-cap enclosure. -/
theorem lowSound : ∀ box ∈ profileBoxes, LowProfileBoxSound parameters box := by
  intro box hbox
  exact lowProfileBoxSound_of_checks
    (lowProfileFacts box hbox)
    (segmentGeometryCheck_eq_true box hbox)
    (boxChunkCoverageCheck_eq_true box hbox)
    (rowExpressionBaseCheck_eq_true box hbox)
    (lambdaSquareBaseCheck_eq_true box hbox)
    (fun profile hprofile ↦ profileBox_realCapUpper_contains hbox hprofile)

end CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287Soundness
