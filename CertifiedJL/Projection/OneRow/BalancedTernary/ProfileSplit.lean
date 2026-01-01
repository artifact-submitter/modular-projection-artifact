/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.OneRow975.Finite.ProfileSplit
import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Soundness.Assembly
import CertifiedJL.Projection.OneRow.BalancedTernary.Analytic
import CertifiedJL.Probability.Distributions.Rademacher.RademacherProfileChernoff
import CertifiedJL.Probability.Distributions.Rademacher.RademacherProfileBound
import CertifiedJL.Probability.Distributions.Rademacher.RademacherFourthMomentProfile

/-!
# Profile-split assembly of the sparse one-row theorem

This file removes the universal moderate-Lyapunov requirement from the exact
`39/4` result.  The fourth-moment profile `B` selects one of three branches:

* `B ≤ 67/500`: the analytic small-Lyapunov theorem;
* `67/500 < B < 32/125`: the retained 24-cell Prawitz certificate;
* `32/125 ≤ B`: an elementary entropy-aware Chernoff bound.
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace CertifiedJL

open Probability
open SparseOneRowProfileSplit

private theorem threshold_pos :
    0 < sparseOneRowRademacherThreshold := by
  unfold sparseOneRowRademacherThreshold
  positivity

private theorem lyapunovProfileEnvelope_mono
    {B C : ℝ} (hB : 0 ≤ B) (hBC : B ≤ C) :
    B ^ 2 *
        Real.cosh (sparseOneRowRademacherThreshold * B ^ 2) ^ 3 ≤
      C ^ 2 *
        Real.cosh (sparseOneRowRademacherThreshold * C ^ 2) ^ 3 := by
  have hC : 0 ≤ C := hB.trans hBC
  have hsquare : B ^ 2 ≤ C ^ 2 :=
    (sq_le_sq₀ hB hC).mpr hBC
  have harg :
      sparseOneRowRademacherThreshold * B ^ 2 ≤
        sparseOneRowRademacherThreshold * C ^ 2 :=
    mul_le_mul_of_nonneg_left hsquare threshold_pos.le
  have hcosh :
      Real.cosh (sparseOneRowRademacherThreshold * B ^ 2) ≤
        Real.cosh (sparseOneRowRademacherThreshold * C ^ 2) := by
    rw [Real.cosh_le_cosh]
    rw [abs_of_nonneg (mul_nonneg threshold_pos.le (sq_nonneg B)),
      abs_of_nonneg (mul_nonneg threshold_pos.le (sq_nonneg C))]
    exact harg
  exact mul_le_mul hsquare
    (pow_le_pow_left₀ (Real.cosh_pos _).le hcosh 3)
    (pow_nonneg (Real.cosh_pos _).le 3) (sq_nonneg C)

private theorem profileRoot_eq_sq
    {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (B : ℝ)
    (hfourth : ∑ i, b i ^ 4 = B ^ 4) :
    Real.sqrt (∑ i, b i ^ 4) = B ^ 2 := by
  rw [hfourth]
  have hpow : B ^ 4 = (B ^ 2) ^ 2 := by ring
  rw [hpow, Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg B)]

private theorem lyapunovRatio_lt_small_of_profile_le
    {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1)
    (hprofile : rademacherFourthMomentProfile b ≤
      (smallProfileCutoff : ℝ)) :
    rademacherLyapunovRatio b sparseOneRowRademacherThreshold <
      (1 : ℝ) / 50 := by
  let B := rademacherFourthMomentProfile b
  have hB0 : 0 ≤ B := rademacherFourthMomentProfile_nonneg b
  have hfourth : ∑ i, b i ^ 4 = B ^ 4 := by
    simpa [B] using (rademacherFourthMomentProfile_pow_four b).symm
  have hroot := profileRoot_eq_sq b B hfourth
  have hL := rademacherLyapunovRatio_le
    b sparseOneRowRademacherThreshold hnorm
  rw [hroot] at hL
  calc
    rademacherLyapunovRatio b sparseOneRowRademacherThreshold ≤
        B ^ 2 *
          Real.cosh (sparseOneRowRademacherThreshold * B ^ 2) ^ 3 := hL
    _ ≤ (smallProfileCutoff : ℝ) ^ 2 *
          Real.cosh
            (sparseOneRowRademacherThreshold *
              (smallProfileCutoff : ℝ) ^ 2) ^ 3 :=
      lyapunovProfileEnvelope_mono hB0 (by simpa [B] using hprofile)
    _ < (1 : ℝ) / 50 := small_cutoff_lyapunov_envelope_lt

private theorem lyapunovRatio_lt_moderateUpper_of_profile_lt
    {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1)
    (hprofile : rademacherFourthMomentProfile b <
      (largeProfileCutoff : ℝ)) :
    rademacherLyapunovRatio b sparseOneRowRademacherThreshold <
      (moderateLyapunovUpper : ℝ) := by
  let B := rademacherFourthMomentProfile b
  have hB0 : 0 ≤ B := rademacherFourthMomentProfile_nonneg b
  have hfourth : ∑ i, b i ^ 4 = B ^ 4 := by
    simpa [B] using (rademacherFourthMomentProfile_pow_four b).symm
  have hroot := profileRoot_eq_sq b B hfourth
  have hL := rademacherLyapunovRatio_le
    b sparseOneRowRademacherThreshold hnorm
  rw [hroot] at hL
  calc
    rademacherLyapunovRatio b sparseOneRowRademacherThreshold ≤
        B ^ 2 *
          Real.cosh (sparseOneRowRademacherThreshold * B ^ 2) ^ 3 := hL
    _ ≤ (largeProfileCutoff : ℝ) ^ 2 *
          Real.cosh
            (sparseOneRowRademacherThreshold *
              (largeProfileCutoff : ℝ) ^ 2) ^ 3 :=
      lyapunovProfileEnvelope_mono hB0 (by simpa [B] using hprofile.le)
    _ < (moderateLyapunovUpper : ℝ) :=
      large_cutoff_lyapunov_envelope_lt

private theorem upperTail_lt_of_profile_lt_large
    (moderate : ∀ C ∈ TyurinModerate.moderateGridCells,
      TyurinModerate.CellCertified C)
    (envelope : ∀ y : ℝ, 0 ≤ y →
      y ≤ (largeProfileCutoff : ℝ) →
      SparseOneRowCertificate.scalarEnvelope y <
        (SparseOneRowCertificate.target : ℝ))
    {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1)
    (hprofile : rademacherFourthMomentProfile b <
      (largeProfileCutoff : ℝ)) :
    eventProbability (rademacherPMF ι)
        (fun seed => sparseOneRowRademacherThreshold < rademacherSum b seed) <
      failureTarget 142 := by
  let B := rademacherFourthMomentProfile b
  have hB0 : 0 ≤ B := rademacherFourthMomentProfile_nonneg b
  have hBupper : B ≤ (largeProfileCutoff : ℝ) := by
    simpa [B] using hprofile.le
  have hLupper :
      rademacherLyapunovRatio b sparseOneRowRademacherThreshold ≤
        (19707 : ℝ) / 100000 := by
    have h := lyapunovRatio_lt_moderateUpper_of_profile_lt b hnorm hprofile
    simpa [moderateLyapunovUpper] using h.le
  have hK :
      kolmogorovDistance
          (rademacherTiltedStandardizedLaw b sparseOneRowRademacherThreshold)
          (gaussianReal 0 1) ≤
        (3 / 5 : ℝ) *
          rademacherLyapunovRatio b sparseOneRowRademacherThreshold := by
    by_cases hsmallProfile : B ≤ (smallProfileCutoff : ℝ)
    · apply rademacherTiltedStandardizedLaw_le_threeFifths_mul_of_small
        b sparseOneRowRademacherThreshold hnorm
      exact (lyapunovRatio_lt_small_of_profile_le b hnorm
        (by simpa [B] using hsmallProfile)).le
    · exact
        TyurinModerate.rademacherTiltedStandardizedLaw_le_threeFifths_mul_of_gridCertified_of_le
          moderate b sparseOneRowRademacherThreshold hnorm hLupper
  have htail :=
    rademacherUpperTail_toReal_le_profile b threshold_pos
      (by norm_num : (0 : ℝ) ≤ 3 / 5) hB0 hnorm
      (abs_le_rademacherFourthMomentProfile b)
      (by simpa [B] using
        (rademacherFourthMomentProfile_pow_four b).symm)
      hK
  have hscalar := sparseOneRow_profile_le_scalarEnvelope hB0
  have hcert := envelope B hB0 hBupper
  have hreal :
      (eventProbability (rademacherPMF ι)
        (fun seed => sparseOneRowRademacherThreshold <
          rademacherSum b seed)).toReal <
        (SparseOneRowCertificate.target : ℝ) :=
    htail.trans_lt (hscalar.trans_lt hcert)
  rw [← ENNReal.toReal_lt_toReal
    (by
      unfold eventProbability
      exact PMF.apply_ne_top _ _)
    (by simp [failureTarget])]
  simpa [failureTarget, SparseOneRowCertificate.target] using hreal

private theorem upperTail_lt_of_large_profile
    {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1)
    (hprofile : (largeProfileCutoff : ℝ) ≤
      rademacherFourthMomentProfile b) :
    eventProbability (rademacherPMF ι)
        (fun seed => sparseOneRowRademacherThreshold < rademacherSum b seed) <
      failureTarget 142 := by
  let B := rademacherFourthMomentProfile b
  have hB0 : 0 ≤ B := rademacherFourthMomentProfile_nonneg b
  have hfourth : ∑ i, b i ^ 4 = B ^ 4 := by
    simpa [B] using (rademacherFourthMomentProfile_pow_four b).symm
  have htail :=
    rademacherSum_upperTail_toReal_le_entropyProfile b threshold_pos.le hB0
      hnorm (abs_le_rademacherFourthMomentProfile b) hfourth
  have hcutoff0 :
      0 ≤ sparseOneRowRademacherThreshold * (largeProfileCutoff : ℝ) :=
    mul_nonneg threshold_pos.le
      (by norm_num [largeProfileCutoff,
        SparseOneRowCertificate.certifiedProfileUpper])
  have hBarg0 : 0 ≤ sparseOneRowRademacherThreshold * B :=
    mul_nonneg threshold_pos.le hB0
  have hargle :
      sparseOneRowRademacherThreshold * (largeProfileCutoff : ℝ) ≤
        sparseOneRowRademacherThreshold * B :=
    mul_le_mul_of_nonneg_left (by simpa [B] using hprofile) threshold_pos.le
  have hdefect := monotoneOn_rademacherEntropyDefect
    (Set.mem_Ici.mpr hcutoff0) (Set.mem_Ici.mpr hBarg0) hargle
  have hexp :
      Real.exp
          (-sparseOneRowRademacherThreshold ^ 2 / 2 -
            rademacherEntropyDefect (sparseOneRowRademacherThreshold * B)) ≤
        Real.exp
          (-sparseOneRowRademacherThreshold ^ 2 / 2 -
            rademacherEntropyDefect
              (sparseOneRowRademacherThreshold * largeProfileCutoff)) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hreal :
      (eventProbability (rademacherPMF ι)
        (fun seed => sparseOneRowRademacherThreshold <
          rademacherSum b seed)).toReal <
        (SparseOneRowCertificate.target : ℝ) :=
    htail.trans (by simpa [B] using hexp) |>.trans_lt
      large_cutoff_chernoff_lt_target
  rw [← ENNReal.toReal_lt_toReal
    (by
      unfold eventProbability
      exact PMF.apply_ne_top _ _)
    (by simp [failureTarget])]
  simpa [failureTarget, SparseOneRowCertificate.target] using hreal

/--
The bounded moderate and scalar certificates imply the exact normalized
one-sided theorem.  No universal all-profile normal approximation is needed.
-/
theorem normalizedRademacher975Upper_of_profileSplit
    (moderate : ∀ C ∈ TyurinModerate.moderateGridCells,
      TyurinModerate.CellCertified C)
    (envelope : ∀ y : ℝ, 0 ≤ y →
      y ≤ (largeProfileCutoff : ℝ) →
      SparseOneRowCertificate.scalarEnvelope y <
        (SparseOneRowCertificate.target : ℝ)) :
    NormalizedRademacher975UpperStatement := by
  intro ι _ b hnorm
  by_cases hlarge :
      (largeProfileCutoff : ℝ) ≤ rademacherFourthMomentProfile b
  · exact upperTail_lt_of_large_profile b hnorm hlarge
  · have hprofile :
        rademacherFourthMomentProfile b < (largeProfileCutoff : ℝ) :=
      lt_of_not_ge hlarge
    exact upperTail_lt_of_profile_lt_large moderate envelope b hnorm hprofile

end CertifiedJL
