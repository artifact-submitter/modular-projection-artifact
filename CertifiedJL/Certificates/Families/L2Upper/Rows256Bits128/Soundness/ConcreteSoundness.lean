/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.FiniteSoundness
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.HyperbolicChecks
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.TailSoundness
import Mathlib.Tactic

/-!
# Concrete soundness facts for the centered-hybrid manifest

All transcendental and interval side conditions in this file are discharged
once per profile box.  Frequency-cell replay remains purely arithmetic.
-/

namespace CertifiedJL
namespace SparseUpperHybrid

open UpperContourKernel

set_option maxRecDepth 100000

private theorem toReal_mono {p : ℕ} {a b : ℤ} (h : a ≤ b) :
    Dyadic.toReal p a ≤ Dyadic.toReal p b := by
  unfold Dyadic.toReal
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)

private theorem toReal_min (p : ℕ) (a b : ℤ) :
    Dyadic.toReal p (min a b) = min (Dyadic.toReal p a) (Dyadic.toReal p b) := by
  by_cases h : a ≤ b
  · rw [min_eq_left h, min_eq_left (toReal_mono h)]
  · have h' : b ≤ a := le_of_not_ge h
    rw [min_eq_right h', min_eq_right (toReal_mono h')]

private theorem toReal_max (p : ℕ) (a b : ℤ) :
    Dyadic.toReal p (max a b) = max (Dyadic.toReal p a) (Dyadic.toReal p b) := by
  by_cases h : a ≤ b
  · rw [max_eq_right h, max_eq_right (toReal_mono h)]
  · have h' : b ≤ a := le_of_not_ge h
    rw [max_eq_left h', max_eq_left (toReal_mono h')]

private theorem interval_hi_nonneg_of_contains_nonneg
    {p : ℕ} {I : Interval p} {x : ℝ} (hx : 0 ≤ x) (hI : I.Contains x) :
    0 ≤ I.hi := by
  have hreal : 0 ≤ Dyadic.toReal p I.hi := hx.trans hI.2
  rw [Dyadic.toReal] at hreal
  have hs : (0 : ℝ) < Dyadic.scale p := by exact_mod_cast Dyadic.scale_pos p
  have : (0 : ℝ) ≤ I.hi := by
    by_contra hneg
    have hiNeg : (I.hi : ℝ) < 0 := lt_of_not_ge hneg
    exact (not_le_of_gt (div_neg_of_neg_of_pos hiNeg hs)) hreal
  exact_mod_cast this

/-- Elementary rational facts shared by every manifest box. -/
theorem certificateBox_numeric_facts
    {certificate : CertificateBox} (hcertificate : certificate ∈ certificateBoxes) :
    0 ≤ certificate.box.profileLeft ∧
    certificate.box.profileLeft ≤ certificate.box.profileRight ∧
    0 < certificate.box.lam ∧ certificate.box.lam < 1 ∧
    0 < certificate.box.uniformCount ∧
    0 < certificate.box.uniformHalfWidth := by
  simp only [certificateBoxes, List.mem_cons, List.not_mem_nil, or_false] at hcertificate
  rcases hcertificate with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [replayBox]

/-- Every manifest box semantically encloses its U8 row cap throughout the
profile interval. -/
theorem certificateBox_realCapUpper_contains
    {certificate : CertificateBox} (hcertificate : certificate ∈ certificateBoxes)
    {profile : ℝ}
    (hprofile : profile ∈ Set.Icc (certificate.box.profileLeft : ℝ)
      (certificate.box.profileRight : ℝ)) :
    (realCapUpper precision certificate.box.profileLeft
      certificate.box.lam).Contains
      (realRowDeficitCap
        (Real.sqrt profile * (certificate.box.lam : ℝ) /
          (1 - (certificate.box.lam : ℝ)))) := by
  have hcase := hcertificate
  simp only [certificateBoxes, List.mem_cons, List.not_mem_nil, or_false] at hcase
  rcases hcase with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hu := upperBounds_realCapUpper precision
      0 (625 / 1000) profile (by norm_num) hprofile.1
      (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
    constructor
    · rw [realCapUpper, if_pos rfl]
      simp only [Dyadic.toReal_zero]
      unfold realRowDeficitCap
      positivity
    · exact hu
  all_goals
    apply contains_realCapUpper_of_ne_zero precision _ _ profile
    · norm_num [replayBox]
    · norm_num [replayBox]
    · exact hprofile.1
    · norm_num [replayBox]
    · norm_num [replayBox]
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel

/-- Arbitrary-start version of the sparse row-cell consumer used by the
optimized heterogeneous frequency meshes. -/
theorem sparseUpperContourRowMajorant_le_hybridCellRowUpperValue
    (box : ProfileBox) (segment : Segment) (index : ℕ)
    (profile frequency : ℝ)
    (hprofileLeftNonneg : (0 : ℝ) ≤ box.profileLeft)
    (hprofile : profile ∈ Set.Icc (box.profileLeft : ℝ) (box.profileRight : ℝ))
    (hlam : (box.lam : ℝ) < 1)
    (hleft :
      (rowExpressionOnCell box.profileLeft
        (segment.start + index * segment.mesh)
        (segment.start + index * segment.mesh + segment.mesh) box.lam).Contains
        (normalizedFourthOrderRowBound rowCoefficients
          box.profileLeft box.lam frequency))
    (hright :
      (rowExpressionOnCell box.profileRight
        (segment.start + index * segment.mesh)
        (segment.start + index * segment.mesh + segment.mesh) box.lam).Contains
        (normalizedFourthOrderRowBound rowCoefficients
          box.profileRight box.lam frequency))
    (hcap : (realCapUpper precision box.profileLeft box.lam).Contains
      (realRowDeficitCap
        (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ))))) :
    sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
      hybridCellRowUpperValue box segment index := by
  have hleftCanonical :
      sparseUpperFourthOrderNormalizedMajorant
          (box.profileLeft : ℝ) (box.lam : ℝ) frequency ≤
        Dyadic.toReal precision
          (rowExpressionOnCell box.profileLeft
            (segment.start + index * segment.mesh)
            (segment.start + index * segment.mesh + segment.mesh) box.lam).hi := by
    rw [← normalizedFourthOrderRowBound_eq_sparseUpperMajorant
      box.profileLeft box.lam frequency hlam]
    exact hleft.2
  have hrightCanonical :
      sparseUpperFourthOrderNormalizedMajorant
          (box.profileRight : ℝ) (box.lam : ℝ) frequency ≤
        Dyadic.toReal precision
          (rowExpressionOnCell box.profileRight
            (segment.start + index * segment.mesh)
            (segment.start + index * segment.mesh + segment.mesh) box.lam).hi := by
    rw [← normalizedFourthOrderRowBound_eq_sparseUpperMajorant
      box.profileRight box.lam frequency hlam]
    exact hright.2
  have hconvex :=
    (convexOn_sparseUpperFourthOrderNormalizedMajorant
      (frequency := frequency) hlam).le_max_of_mem_Icc
      (show (box.profileLeft : ℝ) ∈ Set.Ici 0 by exact hprofileLeftNonneg)
      (show (box.profileRight : ℝ) ∈ Set.Ici 0 by
        exact hprofileLeftNonneg.trans (hprofile.1.trans hprofile.2))
      hprofile
  have hU4 : sparseUpperFourthOrderNormalizedMajorant profile
      (box.lam : ℝ) frequency ≤
      Dyadic.toReal precision
        (max
          (rowExpressionOnCell box.profileLeft
            (segment.start + index * segment.mesh)
            (segment.start + index * segment.mesh + segment.mesh) box.lam).hi
          (rowExpressionOnCell box.profileRight
            (segment.start + index * segment.mesh)
            (segment.start + index * segment.mesh + segment.mesh) box.lam).hi) := by
    rw [toReal_max]
    exact hconvex.trans (max_le_max hleftCanonical hrightCanonical)
  have hU8 : realRowDeficitCap
        (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ))) ≤
      Dyadic.toReal precision
        (realCapUpper precision box.profileLeft box.lam).hi := hcap.2
  rw [sparseUpperContourRowMajorant, hybridCellRowUpperValue, toReal_min]
  simpa only [min_comm] using min_le_min hU4 hU8

/-- The shared row evaluator is sound on every manifest frequency cell. -/
theorem certificateBox_rowExpression_contains
    {certificate : CertificateBox} (hcertificate : certificate ∈ certificateBoxes)
    (segment : Segment) (hsegment : segment ∈ certificate.segments)
    (profileQ : ℚ) (hprofileQ : 0 ≤ profileQ) (index : ℕ)
    (frequency : ℝ)
    (hfrequency : frequency ∈ Set.Ioc
      (((segment.start + index * segment.mesh : ℚ) : ℝ))
      (((segment.start + (index + 1) * segment.mesh : ℚ) : ℝ))) :
    (rowExpressionOnCell profileQ
      (segment.start + index * segment.mesh)
      (segment.start + index * segment.mesh + segment.mesh)
      certificate.box.lam).Contains
      (normalizedFourthOrderRowBound rowCoefficients
        profileQ certificate.box.lam frequency) := by
  let frequencyLeft : ℚ := segment.start + index * segment.mesh
  let frequencyRight : ℚ := frequencyLeft + segment.mesh
  let frequencyInterval := Interval.enclose precision frequencyLeft frequencyRight
  have hsegmentFacts : 0 ≤ segment.start ∧ 0 < segment.mesh := by
    have hc := hcertificate
    simp only [certificateBoxes, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [mkSegments, replayBox, List.mem_cons, List.not_mem_nil,
        or_false] at hsegment <;>
      rcases hsegment with rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hleftNonneg : 0 ≤ frequencyLeft := by
    dsimp only [frequencyLeft]
    exact add_nonneg hsegmentFacts.1
      (mul_nonneg (by positivity) hsegmentFacts.2.le)
  have hleftRight : frequencyLeft ≤ frequencyRight := by
    dsimp only [frequencyRight]
    exact le_add_of_nonneg_right hsegmentFacts.2.le
  have hfrequencyInterval : frequencyInterval.Contains (frequencyLeft : ℝ) :=
    Interval.contains_enclose ⟨le_rfl, by exact_mod_cast hleftRight⟩
  have hfrequencyValid : frequencyInterval.Valid :=
    Interval.valid_of_contains hfrequencyInterval
  have hfrequencyLo : 0 ≤ frequencyInterval.lo :=
    Dyadic.roundDown_nonneg hleftNonneg
  have hsquareLo : 0 ≤ frequencyInterval.square.lo :=
    Interval.square_lo_nonneg_of_lo_nonneg hfrequencyValid hfrequencyLo
  have hnumeric := certificateBox_numeric_facts hcertificate
  have honeMinusLo : 0 ≤
      (frac precision (1 - certificate.box.lam)).lo :=
    Dyadic.roundDown_nonneg (sub_nonneg.mpr hnumeric.2.2.2.1.le)
  have honeSquarePos : 0 <
      (frac precision
        ((1 - certificate.box.lam) * (1 - certificate.box.lam))).lo := by
    have hc := hcertificate
    simp only [certificateBoxes, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide +kernel
  have hdenominator : 0 <
      (frac precision
        ((1 - certificate.box.lam) * (1 - certificate.box.lam)) +
          frequencyInterval.square).lo :=
    add_pos_of_pos_of_nonneg honeSquarePos hsquareLo
  have hgaussianDenominator : 0 <
      ((frac precision
        ((1 - certificate.box.lam) * (1 - certificate.box.lam)) +
          frequencyInterval.square).sqrt.sqrt).lo :=
    Interval.sqrt_lo_pos_of_lo_pos (Interval.sqrt_lo_pos_of_lo_pos hdenominator)
  have hrho : 0 ≤
      (frac precision (certificate.box.lam * certificate.box.lam) +
        frequencyInterval.square).lo := by
    exact add_nonneg
      (Dyadic.roundDown_nonneg (mul_self_nonneg certificate.box.lam)) hsquareLo
  apply contains_normalizedFourthOrderRowBound
  · exact_mod_cast hnumeric.2.2.2.1
  · constructor
    · simpa only [frequencyLeft] using hfrequency.1.le
    · have hr : (frequencyRight : ℝ) =
          ((segment.start + (index + 1) * segment.mesh : ℚ) : ℝ) := by
        dsimp only [frequencyRight, frequencyLeft]
        push_cast
        ring
      rw [hr]
      exact hfrequency.2
  · exact honeMinusLo
  · exact hdenominator
  · exact hgaussianDenominator
  · exact hrho
  · exact Or.inr (Dyadic.roundDown_nonneg hprofileQ)

/-- Concrete row-majorant bound for every manifest cell. -/
theorem certificateBox_rowMajorant_le
    {certificate : CertificateBox} (hcertificate : certificate ∈ certificateBoxes)
    {profile : ℝ}
    (hprofile : profile ∈ Set.Icc (certificate.box.profileLeft : ℝ)
      (certificate.box.profileRight : ℝ))
    (segment : Segment) (hsegment : segment ∈ certificate.segments)
    (index : ℕ) (frequency : ℝ)
    (hfrequency : frequency ∈ Set.Ioc
      (((segment.start + index * segment.mesh : ℚ) : ℝ))
      (((segment.start + (index + 1) * segment.mesh : ℚ) : ℝ))) :
    sparseUpperContourRowMajorant profile (certificate.box.lam : ℝ) frequency ≤
      hybridCellRowUpperValue certificate.box segment index := by
  apply sparseUpperContourRowMajorant_le_hybridCellRowUpperValue
  · exact_mod_cast (certificateBox_numeric_facts hcertificate).1
  · exact hprofile
  · exact_mod_cast (certificateBox_numeric_facts hcertificate).2.2.2.1
  · apply certificateBox_rowExpression_contains hcertificate segment hsegment
    · exact (certificateBox_numeric_facts hcertificate).1
    · exact hfrequency
  · apply certificateBox_rowExpression_contains hcertificate segment hsegment
    · exact (certificateBox_numeric_facts hcertificate).1.trans
        (certificateBox_numeric_facts hcertificate).2.1
    · exact hfrequency
  · exact certificateBox_realCapUpper_contains hcertificate hprofile

/-- The rational Taylor surrogate bounds the exact hyperbolic sine once per
manifest box. -/
theorem certificateBox_sinh_le
    {certificate : CertificateBox} (hcertificate : certificate ∈ certificateBoxes) :
    Real.sinh
      ((certificate.box.uniformHalfWidth * certificate.box.lam : ℚ) : ℝ) ≤
      (sinhUpper
        (certificate.box.uniformHalfWidth * certificate.box.lam) : ℝ) := by
  simp only [certificateBoxes, List.mem_cons, List.not_mem_nil, or_false] at hcertificate
  rcases hcertificate with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [replayBox]
  · convert HyperbolicChecks.box00_sinh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box01_sinh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box02_sinh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box03_sinh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box04_sinh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box05_sinh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box06_sinh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box07_sinh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box08_sinh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box09_sinh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box10_sinh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box11_sinh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box12_sinh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box13_sinh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box14_sinh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box15_sinh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box16_sinh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box17_sinh_le using 1 <;> norm_num

/-- The rational Taylor surrogate bounds the exact hyperbolic cosine once
per manifest box. -/
theorem certificateBox_cosh_le
    {certificate : CertificateBox} (hcertificate : certificate ∈ certificateBoxes) :
    Real.cosh
      ((certificate.box.uniformHalfWidth * certificate.box.lam : ℚ) : ℝ) ≤
      (coshUpper
        (certificate.box.uniformHalfWidth * certificate.box.lam) : ℝ) := by
  simp only [certificateBoxes, List.mem_cons, List.not_mem_nil, or_false] at hcertificate
  rcases hcertificate with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [replayBox]
  · convert HyperbolicChecks.box00_cosh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box01_cosh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box02_cosh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box03_cosh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box04_cosh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box05_cosh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box06_cosh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box07_cosh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box08_cosh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box09_cosh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box10_cosh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box11_cosh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box12_cosh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box13_cosh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box14_cosh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box15_cosh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box16_cosh_le using 1 <;> norm_num
  · convert HyperbolicChecks.box17_cosh_le using 1 <;> norm_num

/-- Unpack the executable interval side-condition checker. -/
theorem hybridCellSideCheck_sound
    {box : ProfileBox} {segment : Segment} {index : ℕ}
    (hcheck : hybridCellSideCheck box segment index = true) :
    let frequencyLeft := segment.start + index * segment.mesh
    let sinhBound := frac precision
      (sinhUpper (box.uniformHalfWidth * box.lam))
    let sineSquareUpper := min 1 ((box.uniformHalfWidth * frequencyLeft) ^ 2)
    let compactNumerator := sinhBound.square + frac precision sineSquareUpper
    let compactBase := frac precision (box.lam ^ 2 + frequencyLeft ^ 2)
    let compactDenominator := frac precision box.uniformHalfWidth * compactBase.sqrt
    0 ≤ compactNumerator.lo ∧ 0 ≤ compactBase.lo ∧
      0 < compactDenominator.lo ∧ 0 < compactBase.sqrt.lo := by
  simp only [hybridCellSideCheck, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  exact ⟨hcheck.1.1.1, hcheck.1.1.2, hcheck.1.2, hcheck.2⟩

/-- The compact centered-uniform factor is sound on every checked manifest
cell. -/
theorem certificateBox_compactNoise_bounds
    {certificate : CertificateBox} (hcertificate : certificate ∈ certificateBoxes)
    (segment : Segment) (hsegment : segment ∈ certificate.segments)
    (index : ℕ) (frequency : ℝ)
    (hfrequency : frequency ∈ Set.Ioc
      (((segment.start + index * segment.mesh : ℚ) : ℝ))
      (((segment.start + (index + 1) * segment.mesh : ℚ) : ℝ)))
    (hcheck : hybridCellSideCheck certificate.box segment index = true) :
    ‖centeredUniformLaplace (certificate.box.uniformHalfWidth : ℝ)
        (certificate.box.lam : ℝ) frequency‖ ^ certificate.box.uniformCount ≤
      ((compactNoiseUpper certificate.box
        (segment.start + index * segment.mesh)).upperRat : ℝ) := by
  have hsegmentFacts : 0 ≤ segment.start ∧ 0 < segment.mesh := by
    have hc := hcertificate
    simp only [certificateBoxes, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [mkSegments, List.mem_cons, List.not_mem_nil, or_false] at hsegment <;>
      rcases hsegment with rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hleftNonneg : 0 ≤
      (((segment.start + index * segment.mesh : ℚ) : ℝ)) := by
    push_cast
    exact add_nonneg (by exact_mod_cast hsegmentFacts.1)
      (mul_nonneg (by positivity) (by exact_mod_cast hsegmentFacts.2.le))
  have hsides := hybridCellSideCheck_sound hcheck
  apply compactNoiseUpper_bounds
  · exact_mod_cast (certificateBox_numeric_facts hcertificate).2.2.2.2.2
  · exact_mod_cast (certificateBox_numeric_facts hcertificate).2.2.1
  · exact hleftNonneg
  · exact hfrequency.1.le
  · exact certificateBox_sinh_le hcertificate
  · exact hsides.1
  · exact hsides.2.1
  · exact hsides.2.2.1

/-- Every checked hybrid cell upper-bounds its literal analytic rectangle. -/
theorem certificateBox_hybridCellRectangle_le_upperRat
    {certificate : CertificateBox} (hcertificate : certificate ∈ certificateBoxes)
    {profile : ℝ}
    (hprofile : profile ∈ Set.Icc (certificate.box.profileLeft : ℝ)
      (certificate.box.profileRight : ℝ))
    (segment : Segment) (hsegment : segment ∈ certificate.segments)
    (index : ℕ)
    (hcheck : hybridCellSideCheck certificate.box segment index = true) :
    hybridCellRectangleValue certificate.box segment index ≤
      ((hybridCell certificate.box segment index).upperRat : ℝ) := by
  let left : ℚ := segment.start + index * segment.mesh
  let right : ℚ := left + segment.mesh
  let rowUpper : ℤ :=
    min (realCapUpper precision certificate.box.profileLeft
      certificate.box.lam).hi
      (max
        (rowExpressionOnCell certificate.box.profileLeft
          left right certificate.box.lam).hi
        (rowExpressionOnCell certificate.box.profileRight
          left right certificate.box.lam).hi)
  have hsegmentFacts : 0 ≤ segment.start ∧ 0 < segment.mesh := by
    have hc := hcertificate
    simp only [certificateBoxes, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [mkSegments, List.mem_cons, List.not_mem_nil, or_false] at hsegment <;>
      rcases hsegment with rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hrightMem : (right : ℝ) ∈ Set.Ioc (left : ℝ) (right : ℝ) := by
    constructor
    · exact_mod_cast (lt_add_of_pos_right left hsegmentFacts.2)
    · exact le_rfl
  have hrightExpected : (right : ℝ) =
      (((segment.start + (index + 1) * segment.mesh : ℚ) : ℝ)) := by
    dsimp only [right, left]
    push_cast
    ring
  have hfrequency : (right : ℝ) ∈ Set.Ioc
      (((segment.start + index * segment.mesh : ℚ) : ℝ))
      (((segment.start + (index + 1) * segment.mesh : ℚ) : ℝ)) := by
    simpa only [left, hrightExpected] using hrightMem
  have hrow := certificateBox_rowMajorant_le hcertificate hprofile
    segment hsegment index (right : ℝ) hfrequency
  have hprofileNonneg : 0 ≤ profile := by
    have hleftReal : (0 : ℝ) ≤ certificate.box.profileLeft := by
      exact_mod_cast (certificateBox_numeric_facts hcertificate).1
    exact hleftReal.trans hprofile.1
  have hrowActualNonneg : 0 ≤ sparseUpperContourRowMajorant profile
      (certificate.box.lam : ℝ) (right : ℝ) :=
    sparseUpperContourRowMajorant_nonneg hprofileNonneg
      (by exact_mod_cast (certificateBox_numeric_facts hcertificate).2.2.1.le)
      (by exact_mod_cast (certificateBox_numeric_facts hcertificate).2.2.2.1)
  have hrowValueNonneg : 0 ≤
      hybridCellRowUpperValue certificate.box segment index :=
    hrowActualNonneg.trans hrow
  have hrowI : (Interval.mk 0 rowUpper : Interval precision).Contains
      (hybridCellRowUpperValue certificate.box segment index) := by
    constructor
    · simp only [Dyadic.toReal_zero]
      exact hrowValueNonneg
    · simp only [hybridCellRowUpperValue, rowUpper, left, right]
      exact le_rfl
  have hrowPower := Interval.contains_squareN hrowI 8
  have hrowUpper : hybridCellRowUpperValue certificate.box segment index ^ rows ≤
      ((((Interval.mk 0 rowUpper : Interval precision).squareN 8).upperRat : ℚ) : ℝ) := by
    have hp := hrowPower.2
    rw [Interval.iterSquare_eq_pow_two_pow] at hp
    change hybridCellRowUpperValue certificate.box segment index ^ 256 ≤ _
    norm_num at hp
    simpa only [Interval.upperRat, Dyadic.cast_toRat] using hp
  have hcompact := certificateBox_compactNoise_bounds hcertificate segment
    hsegment index (right : ℝ) hfrequency hcheck
  have hcompactNonneg : 0 ≤ ((compactNoiseUpper certificate.box
      (segment.start + index * segment.mesh)).upperRat : ℝ) :=
    (by positivity : 0 ≤ ‖centeredUniformLaplace
      (certificate.box.uniformHalfWidth : ℝ) (certificate.box.lam : ℝ)
      (right : ℝ)‖ ^ certificate.box.uniformCount).trans hcompact
  have hsides := hybridCellSideCheck_sound hcheck
  have hbaseContains : (frac precision
      (certificate.box.lam ^ 2 + left ^ 2)).Contains
      (((certificate.box.lam ^ 2 + left ^ 2 : ℚ) : ℝ)) := by
    simpa only [frac] using Interval.contains_ofRat precision
      (certificate.box.lam ^ 2 + left ^ 2)
  have hsqrtContains : (frac precision
      (certificate.box.lam ^ 2 + left ^ 2)).sqrt.Contains
      (Real.sqrt (((certificate.box.lam ^ 2 + left ^ 2 : ℚ) : ℝ))) :=
    Interval.contains_sqrt (by simpa only [left] using hsides.2.1)
      hbaseContains
  have hinverseContains : (inverseSqrtAtLeft precision left
      certificate.box.lam).Contains
      (1 / Real.sqrt (((certificate.box.lam ^ 2 + left ^ 2 : ℚ) : ℝ))) := by
    simpa only [inverseSqrtAtLeft, pow_two, one_div] using
      Interval.contains_reciprocal_of_pos
        (by simpa only [left] using hsides.2.2.2) hsqrtContains
  have hinverse : 1 / Real.sqrt ((certificate.box.lam : ℝ) ^ 2 +
        (((segment.start + index * segment.mesh : ℚ) : ℝ)) ^ 2) ≤
      ((inverseSqrtAtLeft precision
        (segment.start + index * segment.mesh) certificate.box.lam).upperRat : ℝ) := by
    have hu := hinverseContains.2
    simpa only [left, Interval.upperRat, Dyadic.cast_toRat,
      Rat.cast_add, Rat.cast_pow] using hu
  apply hybridCellRectangleValue_le_upperRat
  · exact_mod_cast hsegmentFacts.2.le
  · exact pow_nonneg hrowValueNonneg rows
  · simpa only [rowUpper, left, right] using hrowUpper
  · exact hcompactNonneg
  · exact hinverse

end SparseUpperHybrid
end CertifiedJL
