/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Soundness.Soundness
import CertifiedJL.Tests.Generated.SparseUpperContourFamilyFixture.Replay.Verified

/-!
# Analytic-boundary fixture for the upper-contour family generator

The fixture has zero rows and a positive threshold, so its normalized failure
event is empty.  This gives a small, non-axiomatic test that generated numeric
checks, explicit `LowProfileBoxSound` / `HighProfileBoxSound` proofs, and the
generic `CheckedCertificate` assembly are connected in the right direction.
-/

namespace CertifiedJL.Tests.SparseUpperContourFamilyFixtureSoundness

open scoped BigOperators
open SparseUpperContourFamily

private abbrev fixtureParameters :=
  CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters
private abbrev fixtureBoxes :=
  CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes
private abbrev fixtureHighProfile :=
  CertifiedJL.Tests.SparseUpperContourFamilyFixture.highProfile

theorem profileCover :
    ProfilePartitionCovers fixtureBoxes
      (fixtureHighProfile.profileMinimum : ℝ) := by
  intro profile hprofile
  by_cases hquarter : profile ≤ (1 / 4 : ℝ)
  · refine ⟨fixtureBoxes.getD 0 default, ?_, ?_⟩
    · norm_num [fixtureBoxes,
        CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes]
    · constructor
      · simpa [fixtureBoxes,
          CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes] using
          hprofile.1
      · norm_num [fixtureBoxes,
          CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes] at hquarter ⊢
        exact hquarter
  · refine ⟨fixtureBoxes.getD 1 default, ?_, ?_⟩
    · norm_num [fixtureBoxes,
        CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes]
    · constructor
      · have hquarter' := le_of_not_ge hquarter
        norm_num [fixtureBoxes,
          CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes] at hquarter' ⊢
        exact hquarter'
      · have hhalf := hprofile.2
        norm_num [fixtureHighProfile,
          CertifiedJL.Tests.SparseUpperContourFamilyFixture.highProfile] at hhalf
        norm_num [fixtureBoxes,
          CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes] at ⊢
        exact hhalf

theorem lowTargets : ∀ box ∈ fixtureBoxes, box.target ≤ 1 := by
  intro box hbox
  simp only [fixtureBoxes,
    CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes,
    List.mem_cons, List.not_mem_nil,
    or_false] at hbox
  rcases hbox with rfl | rfl <;> norm_num

theorem highTarget : fixtureHighProfile.target ≤ 1 := by
  norm_num [fixtureHighProfile,
    CertifiedJL.Tests.SparseUpperContourFamilyFixture.highProfile]

private theorem scaledProbability_eq_zero
    {d : ℕ} (a : Fin d → ℝ) :
    scaledUpperTailProbability fixtureParameters a = 0 := by
  unfold scaledUpperTailProbability
  change (2 : ℝ) ^ 0 *
    (eventProbability (sparseRademacherMatrix 0 d)
      (fun J ↦ (100 : ℝ) < realProjectionSqNorm a J)).toReal = 0
  have hpredicate :
      (fun J : Matrix (Fin 0) (Fin d) ℤ ↦
        (100 : ℝ) < realProjectionSqNorm a J) =
        (fun _ : Fin 0 → Fin d → ℤ ↦ False) := by
    funext J
    simp [realProjectionSqNorm]
  have hevent := congrArg (eventProbability (sparseRademacherMatrix 0 d)) hpredicate
  have hfalse :
      eventProbability (sparseRademacherMatrix 0 d)
        (fun _ : Fin 0 → Fin d → ℤ ↦ False) = 0 :=
    eventProbability_false _
  calc
    _ = (2 : ℝ) ^ 0 *
        (eventProbability (sparseRademacherMatrix 0 d)
          (fun _ : Fin 0 → Fin d → ℤ ↦ False)).toReal :=
      congrArg (fun probability : ENNReal ↦
        (2 : ℝ) ^ 0 * probability.toReal) hevent
    _ = 0 := by rw [hfalse]; simp

theorem lowSound : ∀ box ∈ fixtureBoxes,
    LowProfileBoxSound fixtureParameters box := by
  intro box hbox d a _hnorm _hprofile
  rw [scaledProbability_eq_zero a]
  simp only [fixtureBoxes,
    CertifiedJL.Tests.SparseUpperContourFamilyFixture.profileBoxes,
    List.mem_cons, List.not_mem_nil,
    or_false] at hbox
  rcases hbox with rfl | rfl
  · have hhi : 0 ≤ (boxBound fixtureParameters
        (fixtureBoxes.getD 0 default)).hi := by
      decide +kernel
    unfold Interval.upperRat Dyadic.toRat
    push_cast
    positivity
  · have hhi : 0 ≤ (boxBound fixtureParameters
        (fixtureBoxes.getD 1 default)).hi := by
      decide +kernel
    unfold Interval.upperRat Dyadic.toRat
    push_cast
    positivity

theorem highSound :
    HighProfileBoxSound fixtureParameters fixtureHighProfile := by
  intro d a _hnorm _hprofile
  rw [scaledProbability_eq_zero a]
  have hhi : 0 ≤
      (highProfileBound fixtureParameters fixtureHighProfile).hi := by
    decide +kernel
  unfold Interval.upperRat Dyadic.toRat
  push_cast
  positivity

def threshold : NonnegativeRatio := NonnegativeRatio.ofNat 100

theorem threshold_eq :
    threshold.toReal = (fixtureParameters.threshold : ℝ) := by
  norm_num [threshold, NonnegativeRatio.toReal, NonnegativeRatio.ofNat,
    fixtureParameters,
    CertifiedJL.Tests.SparseUpperContourFamilyFixture.parameters]

end CertifiedJL.Tests.SparseUpperContourFamilyFixtureSoundness
