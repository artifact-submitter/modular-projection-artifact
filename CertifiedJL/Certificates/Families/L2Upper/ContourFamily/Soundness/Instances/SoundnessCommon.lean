/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.AnalyticSoundness
import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Common

/-!
# Shared lightweight soundness checks for concrete upper-contour instances

This module packages exact profile-partition checking independently of all
quadrature-cell replay. Concrete instances discharge the Boolean check by
kernel reduction and obtain the real `ProfilePartitionCovers` proposition.
-/

namespace CertifiedJL.SparseUpperContourFamily.Instances

/-- A nonempty list of profile boxes forms an exact consecutive chain from
`start` to `finish`. -/
def ProfileChain (start finish : ℚ) : List ProfileBox → Prop
  | [] => False
  | [box] =>
      box.profileLeft = start ∧
      box.profileLeft ≤ box.profileRight ∧
      box.profileRight = finish
  | box :: next :: rest =>
      box.profileLeft = start ∧
      box.profileLeft ≤ box.profileRight ∧
      ProfileChain box.profileRight finish (next :: rest)

/-- Executable checker for an exact consecutive profile chain. -/
def profileChainCheck (start finish : ℚ) : List ProfileBox → Bool
  | [] => false
  | [box] =>
      decide (box.profileLeft = start) &&
      decide (box.profileLeft ≤ box.profileRight) &&
      decide (box.profileRight = finish)
  | box :: next :: rest =>
      decide (box.profileLeft = start) &&
      decide (box.profileLeft ≤ box.profileRight) &&
      profileChainCheck box.profileRight finish (next :: rest)

theorem profileChainCheck_eq_true_iff
    (start finish : ℚ) (boxes : List ProfileBox) :
    profileChainCheck start finish boxes = true ↔
      ProfileChain start finish boxes := by
  induction boxes generalizing start finish with
  | nil => simp [profileChainCheck, ProfileChain]
  | cons box rest ih =>
      cases rest with
      | nil => simp [profileChainCheck, ProfileChain, and_assoc]
      | cons next tail =>
          simp only [profileChainCheck, ProfileChain, Bool.and_eq_true,
            decide_eq_true_eq, ih]
          tauto

/-- Executable exact-profile-partition checker starting at zero. -/
def profilePartitionCheck (boxes : List ProfileBox) (finish : ℚ) : Bool :=
  profileChainCheck 0 finish boxes

private theorem profileChain_covers
    {start finish : ℚ} {boxes : List ProfileBox}
    (hchain : ProfileChain start finish boxes) :
    ∀ profile : ℝ, profile ∈ Set.Icc (start : ℝ) (finish : ℝ) →
      ∃ box ∈ boxes,
        profile ∈ Set.Icc (box.profileLeft : ℝ) (box.profileRight : ℝ) := by
  induction boxes generalizing start finish with
  | nil => simp [ProfileChain] at hchain
  | cons box rest ih =>
      cases rest with
      | nil =>
          simp only [ProfileChain] at hchain
          rcases hchain with ⟨hstart, _hvalid, hfinish⟩
          intro profile hprofile
          refine ⟨box, by simp, ?_⟩
          constructor
          · have hstartReal : (box.profileLeft : ℝ) = (start : ℝ) := by
              exact_mod_cast hstart
            rw [hstartReal]
            exact hprofile.1
          · have hfinishReal : (box.profileRight : ℝ) = (finish : ℝ) := by
              exact_mod_cast hfinish
            rw [hfinishReal]
            exact hprofile.2
      | cons next tail =>
          simp only [ProfileChain] at hchain
          rcases hchain with ⟨hstart, _hvalid, hrest⟩
          intro profile hprofile
          by_cases hbox : profile ≤ (box.profileRight : ℝ)
          · refine ⟨box, by simp, ?_⟩
            constructor
            · have hstartReal : (box.profileLeft : ℝ) = (start : ℝ) := by
                exact_mod_cast hstart
              rw [hstartReal]
              exact hprofile.1
            · exact hbox
          · obtain ⟨found, hfound, hinterval⟩ :=
              ih hrest profile ⟨le_of_not_ge hbox, hprofile.2⟩
            exact ⟨found, by simp [hfound], hinterval⟩

/-- A successful profile-chain check proves the real profile cover expected by
`CheckedCertificate`. -/
theorem profilePartitionCheck_sound
    {boxes : List ProfileBox} {finish : ℚ}
    (hcheck : profilePartitionCheck boxes finish = true) :
    ProfilePartitionCovers boxes (finish : ℝ) := by
  have hchain : ProfileChain 0 finish boxes := by
    exact (profileChainCheck_eq_true_iff 0 finish boxes).mp hcheck
  intro profile hprofile
  exact profileChain_covers hchain profile (by simpa using hprofile)

end CertifiedJL.SparseUpperContourFamily.Instances
