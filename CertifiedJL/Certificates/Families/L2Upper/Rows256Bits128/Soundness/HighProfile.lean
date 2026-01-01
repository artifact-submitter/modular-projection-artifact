/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.RowSoundness
import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperFinal
import Mathlib.Tactic

/-!
# Standalone high-profile sparse upper-tail certificate

This module retains only the real-axis high-profile branch of the former
sparse upper-tail certificate. It deliberately has no dependency on the
retired low-profile contour mesh or its soundness layer.
-/

open scoped BigOperators ENNReal

namespace CertifiedJL
namespace SparseUpperHybrid

open MeasureTheory ProbabilityTheory Set

/-- Independent fractional precision for the high-profile real-axis bound. -/
def highProfilePrecision : ℕ := 384

/-- Separate high-profile U8/Chernoff endpoint at 384 bits. -/
def highProfileBound : UpperContourKernel.DInterval highProfilePrecision :=
  let lam : ℚ := 131 / 200
  let cap := realCapUpper highProfilePrecision (1 / 20) lam
  UpperContourKernel.frac highProfilePrecision (2 ^ securityBits) *
    Exp.negUpper highProfilePrecision (lam * threshold) 34 *
    UpperContourKernel.frac highProfilePrecision (1 / (1 - lam) ^ (rows / 2)) *
    cap.squareN 8

/-- The literal real value evaluated by the independent high-profile
certificate, including the `2^128` scaling used by its strict endpoint check. -/
noncomputable def highProfileScaledEndpoint (profile : ℝ) : ℝ :=
  let lam : ℚ := 131 / 200
  (2 ^ securityBits : ℝ) * Real.exp (-(lam * threshold : ℚ)) *
    ((1 / (1 - lam) ^ (rows / 2) : ℚ) : ℝ) *
    realRowDeficitCap
      (Real.sqrt profile * (lam : ℝ) / (1 - (lam : ℝ))) ^ rows

/-- The checked high-profile interval encloses its literal scaled U8/Chernoff
endpoint for every profile at least `1/20`. -/
theorem highProfileBound_contains_scaledEndpoint
    {profile : ℝ} (hprofile : (1 / 20 : ℝ) ≤ profile) :
    highProfileBound.Contains (highProfileScaledEndpoint profile) := by
  let lam : ℚ := 131 / 200
  have hcap : (realCapUpper highProfilePrecision (1 / 20) lam).Contains
      (realRowDeficitCap
        (Real.sqrt profile * (lam : ℝ) / (1 - (lam : ℝ)))) := by
    apply contains_realCapUpper_of_ne_zero
    · norm_num
    · norm_num
    · norm_num at hprofile ⊢
      exact hprofile
    · norm_num [lam]
    · norm_num [lam]
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  have hscale := Interval.contains_ofRat highProfilePrecision
    (2 ^ securityBits : ℚ)
  have hexponential := Exp.negUpper_contains (p := highProfilePrecision)
    (k := 34) (x := lam * threshold) (by norm_num [lam, threshold])
  have hgaussian := Interval.contains_ofRat highProfilePrecision
    (1 / (1 - lam) ^ (rows / 2) : ℚ)
  have hcapPower := Interval.contains_squareN hcap 8
  have hproduct := Interval.contains_mul
    (Interval.contains_mul (Interval.contains_mul hscale hexponential) hgaussian)
      hcapPower
  simpa [highProfileBound, highProfileScaledEndpoint, lam, rows,
    UpperContourKernel.frac,
    Interval.iterSquare_eq_pow_two_pow] using hproduct

/-- The kernel-checked high-profile replay turns its literal scaled endpoint
into a strict real inequality. -/
theorem highProfileScaledEndpoint_lt_half
    {profile : ℝ} (hprofile : (1 / 20 : ℝ) ≤ profile)
    (hverified : highProfileBound.upperRat < 1 / 2) :
    highProfileScaledEndpoint profile < 1 / 2 := by
  have hcontains := highProfileBound_contains_scaledEndpoint hprofile
  calc
    highProfileScaledEndpoint profile ≤ (highProfileBound.upperRat : ℝ) := by
      simpa only [Interval.upperRat, Dyadic.cast_toRat] using hcontains.2
    _ < 1 / 2 := by
      have hreal : (highProfileBound.upperRat : ℝ) < (((1 / 2 : ℚ) : ℝ)) := by
        exact_mod_cast hverified
      simpa using hreal

/-- The reflected high-profile endpoint closes the complete strict
`128`-bit high-profile branch. -/
theorem sparseUpper_highProfile_of_verified
    (d : ℕ) (a : Fin d → ℝ)
    (hnorm : ∑ i, a i ^ 2 = 1)
    (hprofile : (1 / 20 : ℝ) ≤ sparseProfileFourthMoment a)
    (hverified : highProfileBound.upperRat < 1 / 2) :
    eventProbability (sparseRademacherMatrix rowCount d)
        (fun J => (sparseUpperThreshold : ℝ) <
          realProjectionSqNorm a J) <
      failureTarget securityBits := by
  apply eventProbability_lt_failureTarget_of_toReal_lt
  let lam : ℝ := 131 / 200
  have hle := sparseRademacherMatrix_realProjectionSqNorm_toReal_le_realDeficit_at_profileLeft
    (m := rowCount) a (threshold := sparseUpperThreshold)
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
      (1 / Real.sqrt (1 - lam)) ^ rowCount =
        (1 / (1 - lam)) ^ (rowCount / 2) := by
    calc
      (1 / Real.sqrt (1 - lam)) ^ rowCount =
          ((1 / Real.sqrt (1 - lam)) ^ 2) ^ 128 := by
        simpa only [rowCount] using
          pow_mul (1 / Real.sqrt (1 - lam)) 2 128
      _ = (1 / (1 - lam)) ^ 128 := by rw [hinvSq]
      _ = (1 / (1 - lam)) ^ (rowCount / 2) := by
        norm_num [rowCount]
  have hendpoint :
      Real.exp (-lam * sparseUpperThreshold) *
          ((1 / Real.sqrt (1 - lam)) *
            realRowDeficitCap
              (Real.sqrt (1 / 20 : ℝ) * lam / (1 - lam))) ^ rowCount =
        highProfileScaledEndpoint (1 / 20 : ℝ) /
          (2 : ℝ) ^ securityBits := by
    rw [mul_pow, hinvPow, highProfileScaledEndpoint]
    norm_num only [lam, sparseUpperThreshold, threshold, rowCount, rows,
      securityBits, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg,
      Rat.cast_mul]
    ring
  have hscaledOne : highProfileScaledEndpoint (1 / 20 : ℝ) < 1 :=
    hscaled.trans (by norm_num)
  calc
    (eventProbability (sparseRademacherMatrix rowCount d)
        (fun J => (sparseUpperThreshold : ℝ) <
          realProjectionSqNorm a J)).toReal ≤
        Real.exp (-lam * sparseUpperThreshold) *
          ((1 / Real.sqrt (1 - lam)) *
            realRowDeficitCap
              (Real.sqrt (1 / 20 : ℝ) * lam / (1 - lam))) ^ rowCount := hle
    _ = highProfileScaledEndpoint (1 / 20 : ℝ) /
        (2 : ℝ) ^ securityBits := hendpoint
    _ < 1 / (2 : ℝ) ^ securityBits := by
      exact div_lt_div_of_pos_right hscaledOne (by positivity)
    _ = (2 : ℝ)⁻¹ ^ securityBits := by
      rw [inv_pow]
      simp [one_div]

end SparseUpperHybrid
end CertifiedJL
