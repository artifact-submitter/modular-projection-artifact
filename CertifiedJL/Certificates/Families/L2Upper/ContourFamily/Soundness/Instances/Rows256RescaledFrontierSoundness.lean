/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.Instances.Rows256Bits152Threshold365Soundness
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Rows256RescaledFrontier

/-! # Shared soundness for rescaled 256-row upper-contour endpoints -/

namespace CertifiedJL.SparseUpperContourFamily.Instances.Rows256RescaledFrontierSoundness

open Set
open CertifiedJL.SparseUpperContourFamily.Instances
open CertifiedJL.SparseUpperContourFamily.Instances.Rows256RescaledFrontier

theorem profileCover :
    ProfilePartitionCovers profileBoxes (highProfile.profileMinimum : ℝ) :=
  Rows256Bits152Threshold365Soundness.profileCover

theorem lowTargets : ∀ box ∈ profileBoxes, box.target ≤ 1 :=
  Rows256Bits152Threshold365Soundness.lowTargets

theorem highTarget : highProfile.target ≤ 1 :=
  Rows256Bits152Threshold365Soundness.highTarget

theorem lowProfileFacts (endpoint : Endpoint)
    (hthreshold : 338 ≤ (parameters endpoint).threshold) :
    ∀ box ∈ profileBoxes, LowProfileFacts (parameters endpoint) box := by
  intro box hbox
  simp only [profileBoxes, Rows256Bits152Threshold365.profileBoxes,
    List.mem_cons, List.not_mem_nil, or_false] at hbox
  rcases hbox with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    refine
      { profileLeft_nonneg := by norm_num [profileBox]
        profileLeft_le_right := by norm_num [profileBox]
        theta_nonneg := by norm_num [profileBox]
        theta_le := by norm_num [profileBox]
        phi_pos := by
          norm_num [profileBox, UpperContourKernel.phiLower, List.range_succ]
        lam_pos := by norm_num [profileBox]
        lam_lt_one := by norm_num [profileBox]
        sigma_pos := by norm_num [profileBox]
        exponent_nonneg := ?_
        rows_even := ⟨128, by norm_num [parameters, Parameters.rows]⟩ }
    norm_num [profileBox, parameters] at hthreshold ⊢
    nlinarith

theorem segmentGeometryCheck_eq_true : ∀ box ∈ profileBoxes,
    segmentGeometryCheck box = true :=
  Rows256Bits152Threshold365Soundness.segmentGeometryCheck_eq_true

theorem boxChunkCoverageCheck_eq_true : ∀ box ∈ profileBoxes,
    boxChunkCoverageCheck box = true :=
  Rows256Bits152Threshold365Soundness.boxChunkCoverageCheck_eq_true

theorem rowExpressionBaseCheck_eq_true (endpoint : Endpoint) :
    ∀ box ∈ profileBoxes,
      rowExpressionBaseCheck (parameters endpoint) box = true := by
  intro box hbox
  change rowExpressionBaseCheck
    Rows256Bits152Threshold365.parameters box = true
  exact Rows256Bits152Threshold365Soundness.rowExpressionBaseCheck_eq_true
    box hbox

theorem lambdaSquareBaseCheck_eq_true (endpoint : Endpoint) :
    ∀ box ∈ profileBoxes,
      lambdaSquareBaseCheck (parameters endpoint) box = true := by
  intro box hbox
  change lambdaSquareBaseCheck
    Rows256Bits152Threshold365.parameters box = true
  exact Rows256Bits152Threshold365Soundness.lambdaSquareBaseCheck_eq_true
    box hbox

theorem profileBox_realCapUpper_contains (endpoint : Endpoint)
    {box : ProfileBox} (hbox : box ∈ profileBoxes) {profile : ℝ}
    (hprofile : profile ∈ Icc (box.profileLeft : ℝ)
      (box.profileRight : ℝ)) :
    (realCapUpper (parameters endpoint).precision box.profileLeft box.lam).Contains
      (realRowDeficitCap
        (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ)))) := by
  simpa [parameters, Rows256Bits152Threshold365.parameters] using
    Rows256Bits152Threshold365Soundness.profileBox_realCapUpper_contains hbox hprofile

theorem highProfileFacts (endpoint : Endpoint)
    (hthreshold : 0 ≤ (parameters endpoint).threshold) :
    HighProfileFacts (parameters endpoint) highProfile where
  profileMinimum_nonneg := by norm_num [highProfile, Rows256Bits152Threshold365.highProfile]
  lam_nonneg := by norm_num [highProfile, Rows256Bits152Threshold365.highProfile]
  lam_lt_one := by norm_num [highProfile, Rows256Bits152Threshold365.highProfile]
  exponent_nonneg := by
    norm_num [highProfile, Rows256Bits152Threshold365.highProfile]
    positivity
  rows_even := ⟨128, by norm_num [parameters, Parameters.rows]⟩
  capContains := by
    intro profile hprofile
    simpa [parameters, Rows256Bits152Threshold365.parameters] using
      Rows256Bits152Threshold365Soundness.highProfileFacts.capContains profile hprofile

theorem highSound (endpoint : Endpoint)
    (hthreshold : 0 ≤ (parameters endpoint).threshold) :
    HighProfileBoxSound (parameters endpoint) highProfile :=
  highProfileBoxSound_of_facts (highProfileFacts endpoint hthreshold)

theorem lowSound (endpoint : Endpoint)
    (hthreshold : 338 ≤ (parameters endpoint).threshold) :
    ∀ box ∈ profileBoxes, LowProfileBoxSound (parameters endpoint) box := by
  intro box hbox
  exact lowProfileBoxSound_of_checks
    (lowProfileFacts endpoint hthreshold box hbox)
    (segmentGeometryCheck_eq_true box hbox)
    (boxChunkCoverageCheck_eq_true box hbox)
    (rowExpressionBaseCheck_eq_true endpoint box hbox)
    (lambdaSquareBaseCheck_eq_true endpoint box hbox)
    (fun profile hprofile =>
      profileBox_realCapUpper_contains endpoint hbox hprofile)

end CertifiedJL.SparseUpperContourFamily.Instances.Rows256RescaledFrontierSoundness
