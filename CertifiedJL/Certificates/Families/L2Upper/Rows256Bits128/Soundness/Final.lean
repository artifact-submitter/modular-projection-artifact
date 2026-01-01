/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.AggregationSoundness
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Spec
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.PrefactorSoundness
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ProfileSelection
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.HighProfile
import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperPeanoFinal

/-! # Final centered-hybrid sparse upper-tail theorem -/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace CertifiedJL
namespace SparseUpperHybrid

open UpperContourKernel

private theorem upperRat_add (I J : DInterval precision) :
    (((I + J).upperRat : ℚ) : ℝ) =
      (I.upperRat : ℝ) + (J.upperRat : ℝ) := by
  change (Dyadic.toRat precision (I.hi + J.hi) : ℝ) =
    (Dyadic.toRat precision I.hi : ℝ) +
      (Dyadic.toRat precision J.hi : ℝ)
  rw [Dyadic.toRat_add]
  norm_num

/-- Uniform finite-integral wrapper for all heterogeneous manifest meshes. -/
theorem certificate_finiteIntegral_le_rectangleSums
    {certificate : CertificateBox} (hcertificate : certificate ∈ certificateBoxes)
    {profile : ℝ} (hprofile : 0 ≤ profile)
    (hrow : ∀ segment ∈ certificate.segments,
      SegmentRowBounds certificate.box profile segment)
    (hcompact : ∀ segment ∈ certificate.segments,
      SegmentCompactBounds certificate.box segment) :
    (∫ frequency : ℝ in Set.Ioc 0 (cutoff : ℝ),
      actualHybridIntegrand certificate.box profile frequency) ≤
      (certificate.segments.map
        (segmentRectangleSum certificate.box)).sum := by
  simp only [certificateBoxes, List.mem_cons, List.not_mem_nil, or_false] at hcertificate
  rcases hcertificate with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply integral_Ioc_zero_cutoff_le_certificate_rectangleSums _ _ 220 50 20 4 1
    · rfl
    · exact hprofile
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact hrow
    · exact hcompact
  · apply integral_Ioc_zero_cutoff_le_certificate_rectangleSums _ _ 280 50 20 6 1
    · rfl
    · exact hprofile
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact hrow
    · exact hcompact
  · apply integral_Ioc_zero_cutoff_le_certificate_rectangleSums _ _ 300 50 20 4 1
    · rfl
    · exact hprofile
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact hrow
    · exact hcompact
  · apply integral_Ioc_zero_cutoff_le_certificate_rectangleSums _ _ 280 50 30 4 1
    · rfl
    · exact hprofile
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact hrow
    · exact hcompact
  · apply integral_Ioc_zero_cutoff_le_certificate_rectangleSums _ _ 280 50 20 4 1
    · rfl
    · exact hprofile
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact hrow
    · exact hcompact
  · apply integral_Ioc_zero_cutoff_le_certificate_rectangleSums _ _ 260 50 25 4 1
    · rfl
    · exact hprofile
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact hrow
    · exact hcompact
  · apply integral_Ioc_zero_cutoff_le_certificate_rectangleSums _ _ 220 50 40 6 1
    · rfl
    · exact hprofile
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact hrow
    · exact hcompact
  · apply integral_Ioc_zero_cutoff_le_certificate_rectangleSums _ _ 220 50 25 4 1
    · rfl
    · exact hprofile
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact hrow
    · exact hcompact
  · apply integral_Ioc_zero_cutoff_le_certificate_rectangleSums _ _ 280 50 30 4 1
    · rfl
    · exact hprofile
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact hrow
    · exact hcompact
  · apply integral_Ioc_zero_cutoff_le_certificate_rectangleSums _ _ 200 50 35 4 1
    · rfl
    · exact hprofile
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact hrow
    · exact hcompact
  · apply integral_Ioc_zero_cutoff_le_certificate_rectangleSums _ _ 240 50 40 4 1
    · rfl
    · exact hprofile
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact hrow
    · exact hcompact
  · apply integral_Ioc_zero_cutoff_le_certificate_rectangleSums _ _ 280 50 30 4 1
    · rfl
    · exact hprofile
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact hrow
    · exact hcompact
  · apply integral_Ioc_zero_cutoff_le_certificate_rectangleSums _ _ 125 13 9 1 1
    · rfl
    · exact hprofile
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact hrow
    · exact hcompact
  · apply integral_Ioc_zero_cutoff_le_certificate_rectangleSums _ _ 126 21 5 1 1
    · rfl
    · exact hprofile
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact hrow
    · exact hcompact
  · apply integral_Ioc_zero_cutoff_le_certificate_rectangleSums _ _ 48 11 2 1 1
    · rfl
    · exact hprofile
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact hrow
    · exact hcompact
  · apply integral_Ioc_zero_cutoff_le_certificate_rectangleSums _ _ 40 13 2 1 1
    · rfl
    · exact hprofile
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact hrow
    · exact hcompact
  · apply integral_Ioc_zero_cutoff_le_certificate_rectangleSums _ _ 16 11 1 1 1
    · rfl
    · exact hprofile
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact hrow
    · exact hcompact
  · apply integral_Ioc_zero_cutoff_le_certificate_rectangleSums _ _ 19 4 1 1 1
    · rfl
    · exact hprofile
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num [replayBox]
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact hrow
    · exact hcompact

/-- The reflected finite-plus-tail interval contains the complete positive
frequency analytic integral for every profile assigned to its manifest box. -/
theorem certificate_finiteTail_contains_actualIntegral
    (verified : CertificateContracts.SparseL2UpperHybrid)
    {certificate : CertificateBox} (hcertificate : certificate ∈ certificateBoxes)
    {profile : ℝ}
    (hprofile : profile ∈ Set.Icc (certificate.box.profileLeft : ℝ)
      (certificate.box.profileRight : ℝ)) :
    (finiteIntegralFrom
      ((certificateChunkPlan certificate).map
        (certificateChunkValue certificate)) + tail certificate.box).Contains
      (∫ frequency : ℝ in Set.Ioi 0,
        actualHybridIntegrand certificate.box profile frequency) := by
  have hnumeric := certificateBox_numeric_facts hcertificate
  have hprofileLeftNonneg : (0 : ℝ) ≤ certificate.box.profileLeft := by
    exact_mod_cast hnumeric.1
  have hprofileNonneg : 0 ≤ profile := hprofileLeftNonneg.trans hprofile.1
  have hh : 0 < (certificate.box.uniformHalfWidth : ℝ) := by
    exact_mod_cast hnumeric.2.2.2.2.2
  have hlam : 0 < (certificate.box.lam : ℝ) := by
    exact_mod_cast hnumeric.2.2.1
  have hlamOne : (certificate.box.lam : ℝ) < 1 := by
    exact_mod_cast hnumeric.2.2.2.1
  have hcount : 0 < certificate.box.uniformCount := hnumeric.2.2.2.2.1
  have hcertificateFacts := verified certificate hcertificate
  have hchecks := hcertificateFacts.2.1
  have hrow : ∀ segment ∈ certificate.segments,
      SegmentRowBounds certificate.box profile segment := by
    intro segment hsegment index _ frequency hfrequency
    exact certificateBox_rowMajorant_le hcertificate hprofile
      segment hsegment index frequency hfrequency
  have hcompact : ∀ segment ∈ certificate.segments,
      SegmentCompactBounds certificate.box segment := by
    intro segment hsegment index hindex frequency hfrequency
    exact certificateBox_compactNoise_bounds hcertificate segment hsegment
      index frequency hfrequency (hchecks segment hsegment index hindex)
  have hfinite :
      (∫ frequency : ℝ in Set.Ioc 0 (cutoff : ℝ),
        actualHybridIntegrand certificate.box profile frequency) ≤
        ((finiteIntegralFrom
          ((certificateChunkPlan certificate).map
            (certificateChunkValue certificate))).upperRat : ℝ) := by
    exact (certificate_finiteIntegral_le_rectangleSums hcertificate
      hprofileNonneg hrow hcompact).trans
        (certificate_rectangleSums_le_finiteIntegralFrom_upperRat
          hcertificate hprofile hchecks)
  have htail :
      (∫ frequency : ℝ in Set.Ioi (cutoff : ℝ),
        actualHybridIntegrand certificate.box profile frequency) ≤
        ((tail certificate.box).upperRat : ℝ) := by
    exact integral_Ioi_actualHybridIntegrand_le_tail_upperRat
      certificate.box profile hprofileNonneg hh hlam hlamOne hcount
        (certificateBox_realCapUpper_contains hcertificate hprofile)
        (certificateBox_cosh_le hcertificate)
  have hint := integrable_actualHybridIntegrand certificate.box profile
    hprofileNonneg hh hlam hlamOne
  have hsplit := intervalIntegral.integral_interval_add_Ioi
    (f := actualHybridIntegrand certificate.box profile)
    (a := 0) (b := (cutoff : ℝ)) hint.integrableOn hint.integrableOn
  rw [intervalIntegral.integral_of_le (by norm_num [cutoff])] at hsplit
  constructor
  · rw [hcertificateFacts.2.2]
    simp only [Dyadic.toReal_zero]
    apply setIntegral_nonneg measurableSet_Ioi
    intro frequency _
    unfold actualHybridIntegrand
    have hrowNonneg :=
      sparseUpperContourRowMajorant_nonneg
        hprofileNonneg hlam.le hlamOne
        (frequency := frequency)
    positivity [hrowNonneg]
  · rw [← Dyadic.cast_toRat]
    change _ ≤ (((finiteIntegralFrom
      ((certificateChunkPlan certificate).map
        (certificateChunkValue certificate)) + tail certificate.box).upperRat : ℚ) : ℝ)
    rw [upperRat_add]
    rw [← hsplit]
    exact add_le_add hfinite htail

/-- A selected centered-hybrid box closes the complete scaled low-profile
probability endpoint once supplied with the analytic fourth-order row bound. -/
theorem sparseUpper_lowProfile_of_certificate
    (verified : CertificateContracts.SparseL2UpperHybrid)
    {d : ℕ} (a : Fin d → ℝ)
    (hnorm : ∑ i, a i ^ 2 = 1)
    {certificate : CertificateBox} (hcertificate : certificate ∈ certificateBoxes)
    (hprofile : sparseProfileFourthMoment a ∈
      Set.Icc (certificate.box.profileLeft : ℝ)
        (certificate.box.profileRight : ℝ))
    (hfourth : ∀ frequency : ℝ,
      Real.sqrt (1 - (certificate.box.lam : ℝ)) *
          ‖quadraticComplexMGF
            (fun row : Fin d → ℤ => realRowDot row a)
            (sparseRademacherRow d).toMeasure
            ((certificate.box.lam : ℝ) + frequency * Complex.I)‖ ≤
        sparseUpperFourthOrderNormalizedMajorant
          (sparseProfileFourthMoment a)
          (certificate.box.lam : ℝ) frequency) :
    eventProbability (sparseRademacherMatrix rows d)
        (fun J => (threshold : ℝ) < realProjectionSqNorm a J) <
      failureTarget securityBits := by
  let analyticIntegral : ℝ :=
    ∫ frequency : ℝ in Set.Ioi 0,
      actualHybridIntegrand certificate.box
        (sparseProfileFourthMoment a) frequency
  have hcertificateFacts := verified certificate hcertificate
  have hintegral := certificate_finiteTail_contains_actualIntegral
    verified hcertificate hprofile
  have hintegralNonneg : 0 ≤ analyticIntegral := by
    have hlower := hintegral.1
    change Dyadic.toReal precision _ ≤ analyticIntegral at hlower
    rw [hcertificateFacts.2.2] at hlower
    simpa only [Dyadic.toReal_zero] using hlower
  have hprefactor := prefactor_contains_rationalPrefactorValue hcertificate
  have hproduct := Interval.contains_mul hprefactor hintegral
  have hproductUpper :
      rationalPrefactorValue certificate.box * analyticIntegral ≤
        ((certificateBound certificate).upperRat : ℝ) := by
    simpa only [certificateBound, boxBoundFrom, Interval.upperRat,
      Dyadic.cast_toRat] using hproduct.2
  have hactualProduct :
      actualPrefactorValue certificate.box * analyticIntegral ≤
        rationalPrefactorValue certificate.box * analyticIntegral :=
    mul_le_mul_of_nonneg_right
      (actualPrefactorValue_le_rationalPrefactorValue certificate.box)
      hintegralNonneg
  have hboundReal : ((certificateBound certificate).upperRat : ℝ) < 1 := by
    exact_mod_cast hcertificateFacts.1
  have hendpoint :
      actualPrefactorValue certificate.box * analyticIntegral < 1 :=
    hactualProduct.trans_lt (hproductUpper.trans_lt hboundReal)
  have hnumeric := certificateBox_numeric_facts hcertificate
  have hh : 0 < (certificate.box.uniformHalfWidth : ℝ) := by
    exact_mod_cast hnumeric.2.2.2.2.2
  have hlam : 0 < (certificate.box.lam : ℝ) := by
    exact_mod_cast hnumeric.2.2.1
  have hlamOne : (certificate.box.lam : ℝ) < 1 := by
    exact_mod_cast hnumeric.2.2.2.1
  have hscaled := scaled_sparseMatrix_toReal_le_actualHybridEndpoint
    a certificate.box hnorm hfourth hh hlam hlamOne
  have hscaledLt :
      (2 ^ securityBits : ℝ) *
        (eventProbability (sparseRademacherMatrix rows d)
          (fun J => (threshold : ℝ) < realProjectionSqNorm a J)).toReal < 1 :=
    hscaled.trans_lt (by simpa only [analyticIntegral] using hendpoint)
  apply eventProbability_lt_failureTarget_of_toReal_lt
  have hscale : 0 < (2 ^ securityBits : ℝ) := by positivity
  calc
    (eventProbability (sparseRademacherMatrix rows d)
        (fun J => (threshold : ℝ) < realProjectionSqNorm a J)).toReal
        < 1 / (2 ^ securityBits : ℝ) :=
      (lt_div_iff₀ hscale).2 (by simpa [mul_comm] using hscaledLt)
    _ = (2 : ℝ)⁻¹ ^ securityBits := by
      rw [one_div, inv_pow]

/-- The unconditional fourth-order sparse-row estimate supplies the analytic
premise for whichever centered-hybrid box covers the low-profile vector. -/
theorem sparseUpper_lowProfile
    (verified : CertificateContracts.SparseL2UpperHybrid)
    {d : ℕ} (a : Fin d → ℝ)
    (hnorm : ∑ i, a i ^ 2 = 1)
    (hprofileUpper : sparseProfileFourthMoment a ≤ 1 / 20) :
    eventProbability (sparseRademacherMatrix rows d)
        (fun J => (threshold : ℝ) < realProjectionSqNorm a J) <
      failureTarget securityBits := by
  have hprofileNonneg : 0 ≤ sparseProfileFourthMoment a := by
    unfold sparseProfileFourthMoment
    positivity
  obtain ⟨certificate, hcertificate, hprofile⟩ :=
    exists_certificate_for_profile hprofileNonneg hprofileUpper
  apply sparseUpper_lowProfile_of_certificate verified a hnorm hcertificate hprofile
  intro frequency
  apply normalized_rowMGF_le_fourthOrderMajorant_of_error
  simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, mul_one,
    sub_zero, add_zero] using
    sparseUpper_fourthOrder a hnorm
      (s := (certificate.box.lam : ℝ) + frequency * Complex.I)
      (by
        simpa using
          (show (0 : ℝ) ≤ certificate.box.lam by
            exact_mod_cast (certificateBox_numeric_facts hcertificate).2.2.1.le))
      (by
        simpa using
          (show (certificate.box.lam : ℝ) < 1 by
            exact_mod_cast (certificateBox_numeric_facts hcertificate).2.2.2.1))

/-- The retained high-profile endpoint is a small standalone arithmetic
check; it does not import or replay the superseded low-profile contour mesh. -/
private theorem highProfile_upperRat_lt :
    highProfileBound.upperRat < 1 / 2 := by
  apply Interval.upperLTCheck_sound
  decide +kernel

/-- Fully kernel-checked `128`-bit balanced-ternary upper-tail theorem
at the public threshold `338`. -/
theorem sparseUpper128_of_verified
    (verified : CertificateContracts.SparseL2UpperHybrid) :
    SparseUpper128Statement := by
  apply sparseUpper128_of_profileSplit
  · intro d a hnorm hprofile
    exact sparseUpper_lowProfile verified a hnorm hprofile
  · intro d a hnorm hprofile
    exact sparseUpper_highProfile_of_verified
      d a hnorm hprofile highProfile_upperRat_lt

end SparseUpperHybrid
end CertifiedJL
