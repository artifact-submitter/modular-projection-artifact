/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Transcendental.Trigonometric.Pi
import CertifiedJL.Certificates.Families.OneRow975.Finite.LocalSoundness
import CertifiedJL.Model.Distributions.BalancedTernary.Duplication
import CertifiedJL.Probability.Distributions.Rademacher.RademacherEntropyProfile

/-!
# Exact profile split for the sparse one-row theorem

At the fixed threshold `(39/4) * sqrt 2`, only the middle fourth-moment
profile band needs the moderate-Lyapunov certificate.  The two endpoint
checks in this file are tiny kernel-reduced interval certificates:

* `B ≤ 67/500` forces the tilted Lyapunov ratio below `1/50`;
* `B ≥ 32/125` is closed directly by the entropy-aware Chernoff bound.

The gap between the rounded exploratory cutoffs `0.135` and `0.255` and the
committed rationals is deliberate: the rounded values miss the strict target
by less than one percent.
-/

namespace CertifiedJL
namespace SparseOneRowProfileSplit

open Probability
open SparseOneRowCertificate

/-- Upper endpoint of the analytic small-Lyapunov profile regime. -/
def smallProfileCutoff : ℚ := 67 / 500

/-- Lower endpoint of the direct profile-aware Chernoff regime. -/
def largeProfileCutoff : ℚ := certifiedProfileUpper

/-- Upper Lyapunov endpoint covered by the retained Prawitz cells. -/
def moderateLyapunovUpper : ℚ := 19707 / 100000

/-- Interval upper bound for `B² cosh(x B²)³` at the small-profile cutoff. -/
def smallLyapunovUpper : DInterval :=
  let b2 := smallProfileCutoff ^ 2
  let c := coshUpper (xUpper * b2)
  ratInterval b2 * (c * c * c)

/-- Interval upper bound for `B² cosh(x B²)³` at the large-profile cutoff. -/
def moderateLyapunovEndpointUpper : DInterval :=
  let b2 := largeProfileCutoff ^ 2
  let c := coshUpper (xUpper * b2)
  ratInterval b2 * (c * c * c)

/-- Interval upper bound for the entropy-Chernoff expression at `B=32/125`. -/
def largeChernoffUpper : DInterval :=
  let b := largeProfileCutoff
  Exp.negUpper precision (exponentRate * (1 + b ^ 2)) squarings *
    coshUpper (xUpper * b)

/-- The small-profile endpoint is strictly inside the analytic `1/50` regime. -/
theorem smallLyapunovUpper_check :
    Interval.upperLTCheck smallLyapunovUpper (1 / 50) = true := by
  decide +kernel

/-- The middle profile band stays inside the retained moderate grid. -/
theorem moderateLyapunovEndpointUpper_check :
    Interval.upperLTCheck moderateLyapunovEndpointUpper
      moderateLyapunovUpper = true := by
  decide +kernel

/-- The direct Chernoff endpoint is strictly below the one-sided target. -/
theorem largeChernoffUpper_check :
    Interval.upperLTCheck largeChernoffUpper target = true := by
  decide +kernel

private theorem threshold_nonneg :
    0 ≤ sparseOneRowRademacherThreshold := by
  unfold sparseOneRowRademacherThreshold
  positivity

private theorem threshold_le_xUpper :
    sparseOneRowRademacherThreshold ≤ (xUpper : ℝ) := by
  change (39 / 4 : ℝ) * Real.sqrt 2 ≤ (13789 / 1000 : ℚ)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    (sparseOneRowThreshold_lt_13789_div_1000).le

private theorem cutoff_sq_cosh_cube_lt
    (cutoff bound : ℚ)
    (upper : DInterval)
    (hcutoff0 : 0 ≤ cutoff)
    (hcutoff1 : cutoff ≤ 1)
    (hupper : upper =
      let b2 := cutoff ^ 2
      let c := coshUpper (xUpper * b2)
      ratInterval b2 * (c * c * c))
    (hcheck : Interval.upperLTCheck upper bound = true) :
    (cutoff : ℝ) ^ 2 *
        Real.cosh (sparseOneRowRademacherThreshold * (cutoff : ℝ) ^ 2) ^ 3 <
      (bound : ℝ) := by
  let b2 : ℚ := cutoff ^ 2
  let c := coshUpper (xUpper * b2)
  have hb20 : (0 : ℚ) ≤ b2 := sq_nonneg cutoff
  have harg0 : (0 : ℚ) ≤ xUpper * b2 :=
    mul_nonneg xUpper_nonneg hb20
  have hb2le : b2 ≤ 1 := by
    nlinarith
  have hargle : xUpper * b2 ≤ xUpper := by
    exact mul_le_of_le_one_right xUpper_nonneg hb2le
  have hb2contains :
      (ratInterval b2).Contains (b2 : ℝ) :=
    Interval.contains_ofRat precision b2
  have hccontains :
      c.Contains (Real.cosh (xUpper * b2 : ℚ)) :=
    coshUpper_contains_of_le_xUpper harg0 hargle
  have hcubecontains :
      (c * c * c).Contains (Real.cosh (xUpper * b2 : ℚ) ^ 3) := by
    simpa [pow_succ] using
      Interval.contains_mul (Interval.contains_mul hccontains hccontains) hccontains
  have hendpointContains :
      upper.Contains
        ((b2 : ℝ) * Real.cosh (xUpper * b2 : ℚ) ^ 3) := by
    rw [hupper]
    exact Interval.contains_mul hb2contains hcubecontains
  have hendpoint :
      (b2 : ℝ) * Real.cosh (xUpper * b2 : ℚ) ^ 3 < (bound : ℝ) :=
    Interval.lt_of_contains_of_upperLTCheck hendpointContains hcheck
  have harg :
      sparseOneRowRademacherThreshold * (cutoff : ℝ) ^ 2 ≤
        (xUpper : ℝ) * (cutoff : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right threshold_le_xUpper (sq_nonneg _)
  have hcosh :
      Real.cosh (sparseOneRowRademacherThreshold * (cutoff : ℝ) ^ 2) ≤
        Real.cosh ((xUpper : ℝ) * (cutoff : ℝ) ^ 2) := by
    rw [Real.cosh_le_cosh]
    rw [abs_of_nonneg (mul_nonneg threshold_nonneg (sq_nonneg _)),
      abs_of_nonneg (mul_nonneg (by exact_mod_cast xUpper_nonneg) (sq_nonneg _))]
    exact harg
  have hcube := pow_le_pow_left₀ (Real.cosh_pos _).le hcosh 3
  have hscaled := mul_le_mul_of_nonneg_left hcube (sq_nonneg (cutoff : ℝ))
  exact hscaled.trans_lt (by simpa [b2, pow_two] using hendpoint)

/-- Exact endpoint inequality used to enter the analytic small-L branch. -/
theorem small_cutoff_lyapunov_envelope_lt :
    (smallProfileCutoff : ℝ) ^ 2 *
        Real.cosh
          (sparseOneRowRademacherThreshold *
            (smallProfileCutoff : ℝ) ^ 2) ^ 3 <
      (1 : ℝ) / 50 := by
  have h := cutoff_sq_cosh_cube_lt
    smallProfileCutoff (1 / 50) smallLyapunovUpper
      (by norm_num [smallProfileCutoff])
      (by norm_num [smallProfileCutoff]) rfl
      smallLyapunovUpper_check
  norm_num at h ⊢
  exact h

/-- Exact endpoint inequality bounding the whole middle profile band. -/
theorem large_cutoff_lyapunov_envelope_lt :
    (largeProfileCutoff : ℝ) ^ 2 *
        Real.cosh
          (sparseOneRowRademacherThreshold *
            (largeProfileCutoff : ℝ) ^ 2) ^ 3 <
      (moderateLyapunovUpper : ℝ) := by
  apply cutoff_sq_cosh_cube_lt
    largeProfileCutoff moderateLyapunovUpper
      moderateLyapunovEndpointUpper
      (by norm_num [largeProfileCutoff, certifiedProfileUpper])
      (by norm_num [largeProfileCutoff, certifiedProfileUpper]) rfl
  exact moderateLyapunovEndpointUpper_check

/-- Exact direct-Chernoff inequality at the large-profile cutoff. -/
theorem large_cutoff_chernoff_lt_target :
    Real.exp
        (-sparseOneRowRademacherThreshold ^ 2 / 2 -
          rademacherEntropyDefect
            (sparseOneRowRademacherThreshold * largeProfileCutoff)) <
      (target : ℝ) := by
  let b : ℚ := largeProfileCutoff
  have hb0 : (0 : ℚ) ≤ b := by
    norm_num [b, largeProfileCutoff, certifiedProfileUpper]
  have hb1 : b ≤ 1 := by
    norm_num [b, largeProfileCutoff, certifiedProfileUpper]
  have harg0 : (0 : ℚ) ≤ xUpper * b :=
    mul_nonneg xUpper_nonneg hb0
  have hargle : xUpper * b ≤ xUpper :=
    mul_le_of_le_one_right xUpper_nonneg hb1
  have hexp :
      (Exp.negUpper precision (exponentRate * (1 + b ^ 2)) squarings).Contains
        (Real.exp (-(exponentRate * (1 + b ^ 2) : ℚ))) := by
    apply Exp.negUpper_contains
    exact mul_nonneg exponentRate_nonneg (by positivity)
  have hcosh :
      (coshUpper (xUpper * b)).Contains
        (Real.cosh (xUpper * b : ℚ)) :=
    coshUpper_contains_of_le_xUpper harg0 hargle
  have hcontains :
      largeChernoffUpper.Contains
        (Real.exp (-(exponentRate * (1 + b ^ 2) : ℚ)) *
          Real.cosh (xUpper * b : ℚ)) := by
    simpa [largeChernoffUpper, b] using Interval.contains_mul hexp hcosh
  have hnumeric :
      Real.exp (-(exponentRate * (1 + b ^ 2) : ℚ)) *
          Real.cosh (xUpper * b : ℚ) < (target : ℝ) :=
    Interval.lt_of_contains_of_upperLTCheck hcontains largeChernoffUpper_check
  have hcoshMono :
      Real.cosh (sparseOneRowRademacherThreshold * (b : ℝ)) ≤
        Real.cosh ((xUpper : ℝ) * (b : ℝ)) := by
    rw [Real.cosh_le_cosh]
    rw [abs_of_nonneg (mul_nonneg threshold_nonneg (by exact_mod_cast hb0)),
      abs_of_nonneg
        (mul_nonneg (by exact_mod_cast xUpper_nonneg) (by exact_mod_cast hb0))]
    exact mul_le_mul_of_nonneg_right threshold_le_xUpper (by exact_mod_cast hb0)
  have hrexp :
      -sparseOneRowRademacherThreshold ^ 2 / 2 -
          rademacherEntropyDefect
            (sparseOneRowRademacherThreshold * (b : ℝ)) =
        -(exponentRate : ℝ) * (1 + (b : ℝ) ^ 2) +
          Real.log
            (Real.cosh (sparseOneRowRademacherThreshold * (b : ℝ))) := by
    unfold rademacherEntropyDefect
    have hx2 : sparseOneRowRademacherThreshold ^ 2 / 2 =
        (exponentRate : ℝ) := by
      unfold sparseOneRowRademacherThreshold exponentRate
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hx2' : sparseOneRowRademacherThreshold ^ 2 =
        2 * (exponentRate : ℝ) := by linarith
    rw [mul_pow, hx2']
    ring
  rw [hrexp, Real.exp_add,
    Real.exp_log (Real.cosh_pos _)]
  have hscaled :
      Real.exp (-(exponentRate : ℝ) * (1 + (b : ℝ) ^ 2)) *
          Real.cosh (sparseOneRowRademacherThreshold * (b : ℝ)) ≤
        Real.exp (-(exponentRate : ℝ) * (1 + (b : ℝ) ^ 2)) *
          Real.cosh ((xUpper : ℝ) * (b : ℝ)) :=
    mul_le_mul_of_nonneg_left hcoshMono (Real.exp_nonneg _)
  have hnumeric' :
      Real.exp (-(exponentRate : ℝ) * (1 + (b : ℝ) ^ 2)) *
          Real.cosh ((xUpper : ℝ) * (b : ℝ)) < (target : ℝ) := by
    norm_num at hnumeric ⊢
    exact hnumeric
  exact hscaled.trans_lt hnumeric'

end SparseOneRowProfileSplit
end CertifiedJL
