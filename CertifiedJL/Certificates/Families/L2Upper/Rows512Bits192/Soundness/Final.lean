/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows512Bits192.Soundness.Soundness
import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperFinal
import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperPeanoFinal
import Mathlib.Tactic

/-!
# Final sparse upper-tail certificate assembly

This module is the deliberate meeting point of the certificate and analytic
layers.  It converts the reflected endpoints into the public strict
probability statement without exposing certificate premises downstream.
-/

open scoped BigOperators ENNReal

namespace CertifiedJL
namespace SparseUpperContour

set_option maxRecDepth 100000
set_option exponentiation.threshold 1024

private theorem profileBox_profile_facts {box : ProfileBox}
    (hbox : box ∈ profileBoxes) :
    0 ≤ box.profileLeft ∧ box.profileLeft ≤ box.profileRight := by
  simp only [profileBoxes, List.mem_cons, List.not_mem_nil, or_false] at hbox
  rcases hbox with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num

/-- Every generated profile box semantically encloses its U8 cap throughout
the box. -/
theorem profileBox_realCapUpper_contains
    {box : ProfileBox} (hbox : box ∈ profileBoxes) {profile : ℝ}
    (hprofile : profile ∈ Set.Icc (box.profileLeft : ℝ)
      (box.profileRight : ℝ)) :
    (realCapUpper contourPrecision box.profileLeft box.lam).Contains
      (realRowDeficitCap
        (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ)))) := by
  simp only [profileBoxes, List.mem_cons, List.not_mem_nil, or_false] at hbox
  rcases hbox with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hu := upperBounds_realCapUpper contourPrecision 0 (579 / 1000)
      profile (by norm_num) hprofile.1 (by norm_num) (by norm_num)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
    constructor
    · rw [realCapUpper, if_pos rfl]
      simp only [Dyadic.toReal_zero]
      have hv : 0 ≤ Real.sqrt profile * (((579 / 1000 : ℚ) : ℝ)) /
          (1 - (((579 / 1000 : ℚ) : ℝ))) := by
        have hp : 0 ≤ profile := by simpa using hprofile.1
        positivity
      unfold realRowDeficitCap
      positivity
    · exact hu
  all_goals
    apply contains_realCapUpper_of_ne_zero contourPrecision _ _ profile
    · norm_num
    · norm_num
    · exact hprofile.1
    · norm_num
    · norm_num
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel

private theorem profileBox_rowExpression_contains
    {box : ProfileBox} (hbox : box ∈ profileBoxes) (profileQ : ℚ)
    (hprofileQ : 0 ≤ profileQ) (index : ℕ) (frequency : ℝ)
    (hfrequency : frequency ∈
      Set.Ioc ((index : ℝ) / 100) (((index + 1 : ℕ) : ℝ) / 100)) :
    (rowExpressionOnCell profileQ (index * (1 / 100))
      ((index + 1) * (1 / 100)) box.lam).Contains
      (UpperContourKernel.normalizedFourthOrderRowBound rowCoefficients
        profileQ box.lam frequency) := by
  let frequencyLeft : ℚ := index * (1 / 100)
  let frequencyRight : ℚ := (index + 1) * (1 / 100)
  let frequencyInterval := Interval.enclose contourPrecision
    frequencyLeft frequencyRight
  have hleftNonneg : 0 ≤ frequencyLeft := by
    dsimp only [frequencyLeft]
    positivity
  have hleftRight : frequencyLeft ≤ frequencyRight := by
    dsimp only [frequencyLeft, frequencyRight]
    norm_num
  have hfrequencyInterval : frequencyInterval.Contains (frequencyLeft : ℝ) :=
    Interval.contains_enclose ⟨le_rfl, by exact_mod_cast hleftRight⟩
  have hfrequencyValid : frequencyInterval.Valid :=
    Interval.valid_of_contains hfrequencyInterval
  have hfrequencyLo : 0 ≤ frequencyInterval.lo := by
    exact Dyadic.roundDown_nonneg hleftNonneg
  have hsquareLo : 0 ≤ frequencyInterval.square.lo :=
    Interval.square_lo_nonneg_of_lo_nonneg hfrequencyValid hfrequencyLo
  have honeMinusLo : 0 ≤
      (UpperContourKernel.frac contourPrecision (1 - box.lam)).lo := by
    exact Dyadic.roundDown_nonneg (by
      obtain ⟨_, _, _, _, hlamOne, _, _, _⟩ := profileBox_numeric_facts hbox
      linarith)
  have honeSquarePos : 0 <
      (UpperContourKernel.frac contourPrecision
        ((1 - box.lam) * (1 - box.lam))).lo := by
    have hcase := hbox
    simp only [profileBoxes, List.mem_cons, List.not_mem_nil, or_false] at hcase
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide +kernel
  have hdenominator : 0 <
      (UpperContourKernel.frac contourPrecision
        ((1 - box.lam) * (1 - box.lam)) + frequencyInterval.square).lo :=
    add_pos_of_pos_of_nonneg honeSquarePos hsquareLo
  have hgaussianDenominator : 0 <
      ((UpperContourKernel.frac contourPrecision
        ((1 - box.lam) * (1 - box.lam)) + frequencyInterval.square).sqrt.sqrt).lo :=
    Interval.sqrt_lo_pos_of_lo_pos (Interval.sqrt_lo_pos_of_lo_pos hdenominator)
  have hrho : 0 ≤
      (UpperContourKernel.frac contourPrecision (box.lam * box.lam) +
        frequencyInterval.square).lo := by
    apply add_nonneg
    · exact Dyadic.roundDown_nonneg (mul_self_nonneg box.lam)
    · exact hsquareLo
  have hprofileLo : profileQ = 0 ∨
      0 ≤ (UpperContourKernel.frac contourPrecision profileQ).lo := by
    exact Or.inr (Dyadic.roundDown_nonneg hprofileQ)
  apply UpperContourKernel.contains_normalizedFourthOrderRowBound
  · obtain ⟨_, _, _, _, hlamOne, _, _, _⟩ := profileBox_numeric_facts hbox
    exact_mod_cast hlamOne
  · push_cast
    norm_num
    constructor
    · calc
        (index : ℝ) * (1 / 100) = (index : ℝ) / 100 := by ring
        _ ≤ frequency := hfrequency.1.le
    · calc
        frequency ≤ (((index + 1 : ℕ) : ℝ) / 100) := hfrequency.2
        _ = ((index : ℝ) + 1) * (1 / 100) := by push_cast; ring
  · exact honeMinusLo
  · exact hdenominator
  · exact hgaussianDenominator
  · exact hrho
  · exact hprofileLo

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

private theorem normalizedFourthOrderRowBound_nonneg
    (profile lam : ℚ) (frequency : ℝ) (hprofile : 0 ≤ profile)
    (hlam : (lam : ℝ) < 1) :
    0 ≤ UpperContourKernel.normalizedFourthOrderRowBound
      rowCoefficients profile lam frequency := by
  rw [normalizedFourthOrderRowBound_eq_sparseUpperMajorant profile lam frequency hlam]
  unfold sparseUpperFourthOrderNormalizedMajorant
  have hd8 := quadraticExpDerivativeMajorant_nonneg (m := 8)
    (norm_nonneg ((lam : ℝ) + frequency * Complex.I)) hlam
  have hd6 := quadraticExpDerivativeMajorant_nonneg (m := 6)
    (norm_nonneg ((lam : ℝ) + frequency * Complex.I)) hlam
  have hsqrtProfile : 0 ≤ Real.sqrt (profile : ℝ) := Real.sqrt_nonneg _
  positivity

/-- Generic interval soundness discharges the canonical row-majorant
rectangle for every generated box and mesh cell. -/
theorem profileBox_rowMajorant_le_gaussianCellRowUpperValue
    {box : ProfileBox} (hbox : box ∈ profileBoxes) {profile frequency : ℝ}
    (hprofile : profile ∈ Set.Icc (box.profileLeft : ℝ)
      (box.profileRight : ℝ)) (index : ℕ)
    (hfrequency : frequency ∈
      Set.Ioc ((index : ℝ) / 100) (((index + 1 : ℕ) : ℝ) / 100)) :
    sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ≤
      gaussianCellRowUpperValue box.profileLeft box.profileRight
        box.lam (1 / 100) index := by
  apply sparseUpperContourRowMajorant_le_gaussianCellRowUpperValue
  · exact_mod_cast (profileBox_profile_facts hbox).1
  · exact hprofile
  · obtain ⟨_, _, _, _, hlamOne, _, _, _⟩ := profileBox_numeric_facts hbox
    exact_mod_cast hlamOne
  · exact profileBox_rowExpression_contains hbox box.profileLeft
      (profileBox_profile_facts hbox).1 index frequency hfrequency
  · exact profileBox_rowExpression_contains hbox box.profileRight
      ((profileBox_profile_facts hbox).1.trans (profileBox_profile_facts hbox).2)
      index frequency hfrequency
  · exact profileBox_realCapUpper_contains hbox hprofile

/-- Every literal Gaussian cell from every generated box encloses its encoded
rectangle value. -/
theorem profileBox_gaussianCell_contains_rectangle
    {box : ProfileBox} (hbox : box ∈ profileBoxes) (index : ℕ) :
    (gaussianCell box.profileLeft box.profileRight box.lam box.sigma
      (1 / 100) index).Contains
    (gaussianCellRectangleValue box.profileLeft box.profileRight
      box.lam box.sigma (1 / 100) index) := by
  have hrightMem : (((index + 1 : ℕ) : ℝ) / 100) ∈
      Set.Ioc ((index : ℝ) / 100) (((index + 1 : ℕ) : ℝ) / 100) := by
    constructor
    · exact div_lt_div_of_pos_right (by exact_mod_cast index.lt_succ_self)
        (by norm_num)
    · exact le_rfl
  have hleftExpr := profileBox_rowExpression_contains hbox box.profileLeft
    (profileBox_profile_facts hbox).1 index
      (((index + 1 : ℕ) : ℝ) / 100) hrightMem
  have hrightExpr := profileBox_rowExpression_contains hbox box.profileRight
    ((profileBox_profile_facts hbox).1.trans (profileBox_profile_facts hbox).2)
      index (((index + 1 : ℕ) : ℝ) / 100) hrightMem
  have hleftHi : 0 ≤
      (rowExpressionOnCell box.profileLeft (index * (1 / 100))
        ((index + 1) * (1 / 100)) box.lam).hi :=
    interval_hi_nonneg_of_contains_nonneg
      (normalizedFourthOrderRowBound_nonneg box.profileLeft box.lam _
        (profileBox_profile_facts hbox).1
        (by obtain ⟨_, _, _, _, hlamOne, _, _, _⟩ := profileBox_numeric_facts hbox;
            exact_mod_cast hlamOne)) hleftExpr
  have hrightHi : 0 ≤
      (rowExpressionOnCell box.profileRight (index * (1 / 100))
        ((index + 1) * (1 / 100)) box.lam).hi :=
    interval_hi_nonneg_of_contains_nonneg
      (normalizedFourthOrderRowBound_nonneg box.profileRight box.lam _
        ((profileBox_profile_facts hbox).1.trans (profileBox_profile_facts hbox).2)
        (by obtain ⟨_, _, _, _, hlamOne, _, _, _⟩ := profileBox_numeric_facts hbox;
            exact_mod_cast hlamOne)) hrightExpr
  have hcap := profileBox_realCapUpper_contains hbox
    (profile := (box.profileLeft : ℝ)) ⟨le_rfl, by
      exact_mod_cast (by
        simp only [profileBoxes, List.mem_cons, List.not_mem_nil, or_false] at hbox
        rcases hbox with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          norm_num : box.profileLeft ≤ box.profileRight)⟩
  have hcapValueNonneg : 0 ≤ realRowDeficitCap
      (Real.sqrt (box.profileLeft : ℝ) * (box.lam : ℝ) /
        (1 - (box.lam : ℝ))) := by
    have hprofileLeft : 0 ≤ (box.profileLeft : ℝ) := by
      exact_mod_cast (profileBox_profile_facts hbox).1
    obtain ⟨_, _, _, hlam, hlamOne, _, _, _⟩ := profileBox_numeric_facts hbox
    have hv : 0 ≤ Real.sqrt (box.profileLeft : ℝ) * (box.lam : ℝ) /
        (1 - (box.lam : ℝ)) := by
      exact div_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (by exact_mod_cast hlam.le))
        (sub_nonneg.mpr (by exact_mod_cast hlamOne.le))
    unfold realRowDeficitCap
    positivity
  have hcapHi : 0 ≤ (realCapUpper contourPrecision box.profileLeft box.lam).hi :=
    interval_hi_nonneg_of_contains_nonneg hcapValueNonneg hcap
  apply gaussianCell_contains_rectangle
  · exact le_min hcapHi (hleftHi.trans (le_max_left _ _))
  · apply Dyadic.roundDown_nonneg
    exact add_nonneg (mul_self_nonneg box.lam)
      (mul_self_nonneg (index * (1 / 100 : ℚ)))
  · apply Interval.sqrt_lo_pos_of_lo_pos
    apply Dyadic.roundDown_pos
    have hfixed : 1 ≤ box.lam * box.lam * Dyadic.scale contourPrecision := by
      have hcase := hbox
      simp only [profileBoxes, List.mem_cons, List.not_mem_nil, or_false] at hcase
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide +kernel
    have hfreq : 0 ≤ (index * (1 / 100 : ℚ)) * (index * (1 / 100 : ℚ)) :=
      mul_self_nonneg _
    nlinarith [mul_nonneg hfreq (by positivity : (0 : ℚ) ≤ Dyadic.scale contourPrecision)]

/-- The low-profile endpoint with all generated certificate obligations
discharged, leaving only the analytic fourth-order MGF majorant. -/
theorem sparseUpper_lowProfile_of_fourth_of_verified
    {d : ℕ} (a : Fin d → ℝ)
    (hnorm : ∑ i, a i ^ 2 = 1)
    (hprofile : sparseProfileFourthMoment a ≤ 1 / 20)
    (hfourth : ∀ box ∈ profileBoxes, ∀ frequency : ℝ,
      Real.sqrt (1 - (box.lam : ℝ)) *
          ‖quadraticComplexMGF
            (fun row : Fin d → ℤ => realRowDot row a)
            (sparseRademacherRow d).toMeasure
            ((box.lam : ℝ) + frequency * Complex.I)‖ ≤
        sparseUpperFourthOrderNormalizedMajorant
          (sparseProfileFourthMoment a) (box.lam : ℝ) frequency)
    (hverified : ∀ box ∈ profileBoxes,
      (boxBound box).upperRat < box.target) :
    eventProbability (sparseRademacherMatrix rows d)
        (fun J => (threshold : ℝ) < realProjectionSqNorm a J) <
      failureTarget securityBits := by
  apply sparseUpper_lowProfile a hnorm hprofile hfourth
  · intro box hbox index
    exact profileBox_gaussianCell_contains_rectangle hbox index
  · intro box hbox hprofileMem
    exact profileBox_realCapUpper_contains hbox hprofileMem
  · intro box hbox hprofileMem index _ frequency hfrequency
    exact profileBox_rowMajorant_le_gaussianCellRowUpperValue hbox hprofileMem
      index hfrequency
  · intro box hbox
    exact hverified box hbox

/-- The reflected high-profile endpoint closes the complete strict
`192`-bit high-profile branch. -/
theorem sparseUpper_highProfile_of_verified
    (d : ℕ) (a : Fin d → ℝ)
    (hnorm : ∑ i, a i ^ 2 = 1)
    (hprofile : (1 / 20 : ℝ) ≤ sparseProfileFourthMoment a)
    (hverified : highProfileBound.upperRat < 1 / 2) :
    eventProbability (sparseRademacherMatrix rows d)
        (fun J => (threshold : ℝ) <
          realProjectionSqNorm a J) <
      failureTarget securityBits := by
  apply eventProbability_lt_failureTarget_of_toReal_lt
  let lam : ℝ := 583 / 1000
  have hle := sparseRademacherMatrix_realProjectionSqNorm_toReal_le_realDeficit_at_profileLeft
    (m := rows) a (threshold := (threshold : ℝ))
      (lambda := lam) (profileLeft := 1 / 20) (by norm_num [lam])
      (by norm_num [lam]) hnorm hprofile
  have hscaled := highProfileScaledEndpoint_lt_half
    (profile := (1 / 20 : ℝ)) le_rfl hverified
  have hsqrt : Real.sqrt (1 - lam) ^ 2 = 1 - lam := by
    rw [Real.sq_sqrt]
    norm_num [lam]
  have hsqrtPos : 0 < Real.sqrt (1 - lam) := by
    exact Real.sqrt_pos.2 (by norm_num [lam])
  have hinvSq :
      (1 / Real.sqrt (1 - lam)) ^ 2 = 1 / (1 - lam) := by
    rw [div_pow, one_pow, hsqrt]
  have hinvPow :
      (1 / Real.sqrt (1 - lam)) ^ rows =
        (1 / (1 - lam)) ^ (rows / 2) := by
    calc
      (1 / Real.sqrt (1 - lam)) ^ rows =
          ((1 / Real.sqrt (1 - lam)) ^ 2) ^ 256 := by
        simpa only [rows] using
          pow_mul (1 / Real.sqrt (1 - lam)) 2 256
      _ = (1 / (1 - lam)) ^ 256 := by rw [hinvSq]
      _ = (1 / (1 - lam)) ^ (rows / 2) := by
        norm_num [rows]
  have hendpoint :
      Real.exp (-lam * (threshold : ℝ)) *
          ((1 / Real.sqrt (1 - lam)) *
            realRowDeficitCap
              (Real.sqrt (1 / 20 : ℝ) * lam / (1 - lam))) ^ rows =
        highProfileScaledEndpoint (1 / 20 : ℝ) /
          (2 : ℝ) ^ securityBits := by
    rw [mul_pow, hinvPow, highProfileScaledEndpoint]
    norm_num only [lam, threshold, rows,
      securityBits, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg,
      Rat.cast_mul]
    ring
  have hscaledOne : highProfileScaledEndpoint (1 / 20 : ℝ) < 1 :=
    hscaled.trans (by norm_num)
  calc
    (eventProbability (sparseRademacherMatrix rows d)
        (fun J => (threshold : ℝ) <
          realProjectionSqNorm a J)).toReal ≤
        Real.exp (-lam * (threshold : ℝ)) *
          ((1 / Real.sqrt (1 - lam)) *
            realRowDeficitCap
              (Real.sqrt (1 / 20 : ℝ) * lam / (1 - lam))) ^ rows := hle
    _ = highProfileScaledEndpoint (1 / 20 : ℝ) /
        (2 : ℝ) ^ securityBits := hendpoint
    _ < 1 / (2 : ℝ) ^ securityBits := by
      exact div_lt_div_of_pos_right hscaledOne (by positivity)
    _ = (2 : ℝ)⁻¹ ^ securityBits := by
      rw [inv_pow]
      simp [one_div]

/-- The unconditional fourth-order row comparison supplies the analytic
premise for the verified 512-row low-profile contour. -/
theorem sparseUpper_lowProfile_of_verified
    {d : ℕ} (a : Fin d → ℝ)
    (hnorm : ∑ i, a i ^ 2 = 1)
    (hprofile : sparseProfileFourthMoment a ≤ 1 / 20)
    (hverified : ∀ box ∈ profileBoxes,
      (boxBound box).upperRat < box.target) :
    eventProbability (sparseRademacherMatrix rows d)
        (fun J => (threshold : ℝ) < realProjectionSqNorm a J) <
      failureTarget securityBits := by
  apply sparseUpper_lowProfile_of_fourth_of_verified a hnorm hprofile
  · intro box hbox frequency
    apply normalized_rowMGF_le_fourthOrderMajorant_of_error
    obtain ⟨_, _, _, hlam, hlamOne, _, _, _⟩ :=
      profileBox_numeric_facts hbox
    have hsNonneg : 0 ≤
        ((((box.lam : ℝ) : ℂ) + (frequency : ℂ) * Complex.I).re) := by
      simpa using (show (0 : ℝ) ≤ (box.lam : ℝ) by
        exact_mod_cast hlam.le)
    have hsLt :
        ((((box.lam : ℝ) : ℂ) + (frequency : ℂ) * Complex.I).re) < 1 := by
      simpa using (show (box.lam : ℝ) < 1 by
        exact_mod_cast hlamOne)
    simpa using sparseUpper_fourthOrder a hnorm hsNonneg hsLt
  · exact hverified

/-- Complete normalized 512-row, 192-bit upper tail at strict threshold 607,
assuming the kernel-checked ten-box and high-profile endpoint replays. -/
theorem sparseUpper_normalized607_of_verified
    {d : ℕ} (a : Fin d → ℝ)
    (hnorm : ∑ i, a i ^ 2 = 1)
    (hverified : ∀ box ∈ profileBoxes,
      (boxBound box).upperRat < box.target)
    (hhigh : highProfileBound.upperRat < 1 / 2) :
    eventProbability (sparseRademacherMatrix rows d)
        (fun J => (threshold : ℝ) < realProjectionSqNorm a J) <
      failureTarget securityBits := by
  by_cases hprofile : sparseProfileFourthMoment a ≤ 1 / 20
  · exact sparseUpper_lowProfile_of_verified a hnorm hprofile hverified
  · exact sparseUpper_highProfile_of_verified d a hnorm
      (le_of_not_ge hprofile) hhigh

end SparseUpperContour

end CertifiedJL
