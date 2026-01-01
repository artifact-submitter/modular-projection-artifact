/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Numeric.Core
import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperFinal
import CertifiedJL.Statements.L2.Upper

/-!
# Soundness assembly for parameterized balanced-ternary upper contours

This module is the reusable semantic boundary for the high-security contour
family.  Arithmetic instances provide Boolean checks for segmented low-profile
boxes and the independent high-profile endpoint.  Their analytic soundness
proofs provide enclosures of the corresponding security-scaled probabilities.
The theorem below combines those facts into the generic normalized
balanced-ternary upper-tail statement.

The enclosure hypotheses are deliberately explicit: a successful executable
check proves a strict inequality for the interval endpoint, but it does not by
itself prove that the interval encloses the analytic contour.  Generated
instances must establish that connection using the row-majorant, quadrature,
and tail lemmas.  Consequently this layer adds no axiom or numerical trust
boundary.
-/

open scoped ENNReal BigOperators

namespace CertifiedJL.SparseUpperContourFamily

open Set

/-- The normalized balanced-ternary upper-tail proposition represented by a
family parameter record. -/
def NormalizedUpperTailAt (parameters : Parameters) : Prop :=
  ∀ (d : ℕ) (a : Fin d → ℝ),
    ∑ i, a i ^ 2 = 1 →
    eventProbability
        (sparseRademacherMatrix parameters.rows d)
        (fun J ↦ (parameters.threshold : ℝ) <
          realProjectionSqNorm a J) <
      failureTarget parameters.securityBits

/-- The exact real probability after multiplying by the factored security
scale represented by `parameters`. -/
noncomputable def scaledUpperTailProbability
    (parameters : Parameters) {d : ℕ} (a : Fin d → ℝ) : ℝ :=
  (2 : ℝ) ^ parameters.securityBits *
    (eventProbability
      (sparseRademacherMatrix parameters.rows d)
      (fun J ↦ (parameters.threshold : ℝ) <
        realProjectionSqNorm a J)).toReal

/-- A list of low-profile boxes covers every real profile between zero and the
high-profile cutoff. -/
def ProfilePartitionCovers
    (boxes : List ProfileBox) (profileCutoff : ℝ) : Prop :=
  ∀ profile : ℝ, profile ∈ Icc 0 profileCutoff →
    ∃ box ∈ boxes,
      profile ∈ Icc (box.profileLeft : ℝ) (box.profileRight : ℝ)

/-- Semantic soundness of one segmented low-profile endpoint.  The executable
`boxBound` must enclose the security-scaled probability throughout the box's
profile interval. -/
def LowProfileBoxSound
    (parameters : Parameters) (box : ProfileBox) : Prop :=
  ∀ (d : ℕ) (a : Fin d → ℝ),
    ∑ i, a i ^ 2 = 1 →
    sparseProfileFourthMoment a ∈
      Icc (box.profileLeft : ℝ) (box.profileRight : ℝ) →
    scaledUpperTailProbability parameters a ≤
      ((boxBound parameters box).upperRat : ℝ)

/-- Semantic soundness of the independent high-profile endpoint. -/
def HighProfileBoxSound
    (parameters : Parameters) (box : HighProfileBox) : Prop :=
  ∀ (d : ℕ) (a : Fin d → ℝ),
    ∑ i, a i ^ 2 = 1 →
    (box.profileMinimum : ℝ) ≤ sparseProfileFourthMoment a →
    scaledUpperTailProbability parameters a ≤
      ((highProfileBound parameters box).upperRat : ℝ)

/-- A complete checked certificate at the semantic assembly boundary.

The two Boolean fields are the kernel-replayed numerical decisions.  The two
soundness fields are proof obligations, not trusted data: concrete instances
must derive them from the analytic contour and real-axis estimates. -/
structure CheckedCertificate (parameters : Parameters) where
  lowBoxes : List ProfileBox
  highBox : HighProfileBox
  profileCover :
    ProfilePartitionCovers lowBoxes (highBox.profileMinimum : ℝ)
  lowTargets : ∀ box ∈ lowBoxes, box.target ≤ 1
  highTarget : highBox.target ≤ 1
  lowChecks : allBoxesCheck parameters lowBoxes = true
  highCheck : highProfileCheck parameters highBox = true
  lowSound : ∀ box ∈ lowBoxes, LowProfileBoxSound parameters box
  highSound : HighProfileBoxSound parameters highBox

/-- A successful low-profile Boolean check proves its strict rational endpoint
inequality. -/
theorem boxCheck_sound
    {parameters : Parameters} {box : ProfileBox}
    (hcheck : boxCheck parameters box = true) :
    (boxBound parameters box).upperRat < box.target := by
  exact Interval.upperLTCheck_sound (by
    simpa only [boxCheck] using hcheck)

/-- The aggregate Boolean replay supplies the strict endpoint inequality for
every member of the checked low-profile partition. -/
theorem allBoxesCheck_sound
    {parameters : Parameters} {boxes : List ProfileBox}
    (hcheck : allBoxesCheck parameters boxes = true)
    {box : ProfileBox} (hbox : box ∈ boxes) :
    (boxBound parameters box).upperRat < box.target := by
  have hlisted :
      boxCheck parameters box ∈ boxes.map (boxCheck parameters) :=
    List.mem_map.mpr ⟨box, hbox, rfl⟩
  have hboxCheck := (List.all_eq_true.mp hcheck)
    (boxCheck parameters box) hlisted
  exact boxCheck_sound (by simpa only [id_eq] using hboxCheck)

/-- A successful high-profile Boolean check proves its strict rational endpoint
inequality. -/
theorem highProfileCheck_sound
    {parameters : Parameters} {box : HighProfileBox}
    (hcheck : highProfileCheck parameters box = true) :
    (highProfileBound parameters box).upperRat < box.target := by
  exact Interval.upperLTCheck_sound (by
    simpa only [highProfileCheck] using hcheck)

private theorem upperTail_lt_failureTarget_of_scaled_lt_one
    (parameters : Parameters) {d : ℕ} (a : Fin d → ℝ)
    (hscaled : scaledUpperTailProbability parameters a < 1) :
    eventProbability
        (sparseRademacherMatrix parameters.rows d)
        (fun J ↦ (parameters.threshold : ℝ) <
          realProjectionSqNorm a J) <
      failureTarget parameters.securityBits := by
  apply eventProbability_lt_failureTarget_of_toReal_lt
  have hscale : 0 < (2 : ℝ) ^ parameters.securityBits := by positivity
  calc
    (eventProbability
        (sparseRademacherMatrix parameters.rows d)
        (fun J ↦ (parameters.threshold : ℝ) <
          realProjectionSqNorm a J)).toReal <
        1 / (2 : ℝ) ^ parameters.securityBits := by
      apply (lt_div_iff₀ hscale).2
      simpa only [scaledUpperTailProbability, mul_comm] using hscaled
    _ = (2 : ℝ)⁻¹ ^ parameters.securityBits := by
      rw [one_div, inv_pow]

/-- Kernel-checked segmented low-profile boxes and the checked high-profile
endpoint imply the generic normalized balanced-ternary upper tail. -/
theorem normalizedUpperTail_of_checkedCertificate
    {parameters : Parameters} (certificate : CheckedCertificate parameters) :
    NormalizedUpperTailAt parameters := by
  intro d a hnorm
  by_cases hprofile :
      sparseProfileFourthMoment a ≤ (certificate.highBox.profileMinimum : ℝ)
  · have hprofileNonneg : 0 ≤ sparseProfileFourthMoment a :=
      sparseProfileFourthMoment_nonneg a
    obtain ⟨box, hbox, hboxProfile⟩ := certificate.profileCover
      (sparseProfileFourthMoment a) ⟨hprofileNonneg, hprofile⟩
    have henclosure := certificate.lowSound box hbox d a hnorm hboxProfile
    have hendpointRat := allBoxesCheck_sound certificate.lowChecks hbox
    have hendpoint :
        ((boxBound parameters box).upperRat : ℝ) < (box.target : ℝ) := by
      exact_mod_cast hendpointRat
    have htarget : (box.target : ℝ) ≤ 1 := by
      exact_mod_cast certificate.lowTargets box hbox
    apply upperTail_lt_failureTarget_of_scaled_lt_one parameters a
    exact henclosure.trans_lt (hendpoint.trans_le htarget)
  · have hhighProfile :
        (certificate.highBox.profileMinimum : ℝ) ≤
          sparseProfileFourthMoment a :=
      le_of_not_ge hprofile
    have henclosure := certificate.highSound d a hnorm hhighProfile
    have hendpointRat := highProfileCheck_sound certificate.highCheck
    have hendpoint :
        ((highProfileBound parameters certificate.highBox).upperRat : ℝ) <
          (certificate.highBox.target : ℝ) := by
      exact_mod_cast hendpointRat
    have htarget : (certificate.highBox.target : ℝ) ≤ 1 := by
      exact_mod_cast certificate.highTarget
    apply upperTail_lt_failureTarget_of_scaled_lt_one parameters a
    exact henclosure.trans_lt (hendpoint.trans_le htarget)

/-- Convert the generic normalized result to the public modular squared-
Euclidean upper-tail schema.  The conversion is modulus-independent: reducing
coordinates modulo `q` can only decrease their squared magnitude. -/
theorem l2UpperTailAt_of_normalizedUpperTail
    {parameters : Parameters} (threshold : NonnegativeRatio)
    (hthreshold : threshold.toReal = (parameters.threshold : ℝ))
    (hnormalized : NormalizedUpperTailAt parameters) :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := parameters.rows
        threshold := threshold }
      (failureTarget parameters.securityBits) := by
  intro q d w
  simp only [ProjectionDistribution.matrixPMF_balancedTernary]
  by_cases hw : w = 0
  · have hzero :
        eventProbability (sparseRademacherMatrix parameters.rows d)
            (L2UpperFailure threshold q w) ≤
          eventProbability (sparseRademacherMatrix parameters.rows d)
            (fun _ ↦ False) := by
      apply eventProbability_mono
      intro J hJ
      simp [L2UpperFailure, hw, modularProjectionSqNorm, sqNorm, rowDot,
        centeredMod, ZMod.valMinAbs_zero] at hJ
    calc
      eventProbability (sparseRademacherMatrix parameters.rows d)
          (L2UpperFailure threshold q w) ≤
          eventProbability (sparseRademacherMatrix parameters.rows d)
            (fun _ ↦ False) := hzero
      _ = 0 := eventProbability_false _
      _ < failureTarget parameters.securityBits := by
        unfold failureTarget
        rw [pos_iff_ne_zero]
        exact pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by norm_num))
  · apply (eventProbability_mono
        (p := sparseRademacherMatrix parameters.rows d)
        (fun J hfailure ↦ ?_)).trans_lt
      (hnormalized d (sparseUpperNormalizedCoefficient w)
        (sum_sq_sparseUpperNormalizedCoefficient w hw))
    have hrowNat :
        threshold.numerator * sqNorm w <
          threshold.denominator * projectionSqNorm J w := by
      exact hfailure.trans_le
        (Nat.mul_le_mul_left threshold.denominator
          (modularProjectionSqNorm_le_projectionSqNorm J w))
    have hrow :
        (threshold.numerator : ℝ) * (sqNorm w : ℝ) <
          (threshold.denominator : ℝ) * (projectionSqNorm J w : ℝ) := by
      exact_mod_cast hrowNat
    have hden : 0 < (threshold.denominator : ℝ) := by
      exact_mod_cast threshold.denominator_pos
    have hV : 0 < (sqNorm w : ℝ) := by
      exact_mod_cast (sqNorm_pos_iff w).2 hw
    rw [realProjectionSqNorm_eq_projectionSqNorm_div J w hw,
      ← hthreshold, NonnegativeRatio.toReal]
    exact (div_lt_div_iff₀ hden hV).2 (by
      simpa only [mul_comm] using hrow)

/-- A checked family certificate yields the public balanced-ternary modular
upper-tail theorem at any exact ratio representing its rational threshold. -/
theorem l2UpperTailAt_of_checkedCertificate
    {parameters : Parameters} (certificate : CheckedCertificate parameters)
    (threshold : NonnegativeRatio)
    (hthreshold : threshold.toReal = (parameters.threshold : ℝ)) :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := parameters.rows
        threshold := threshold }
      (failureTarget parameters.securityBits) :=
  l2UpperTailAt_of_normalizedUpperTail threshold hthreshold
    (normalizedUpperTail_of_checkedCertificate certificate)

end CertifiedJL.SparseUpperContourFamily
