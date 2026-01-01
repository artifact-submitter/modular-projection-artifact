/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.NormalApproximation.Rademacher.TiltedRademacherMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Lattice.Fold

/-!
# The deterministic small-Lyapunov reduction

This file isolates the algebraic part of the small-L branch in Tyurin's
non-identically-distributed Berry--Esseen argument.  It deliberately does not
assume or prove the local analytic normal-approximation estimate.

For standardized centered tilted signs, every coordinate variance `vᵢ` and
third absolute moment `mᵢ` satisfy `vᵢ³ ≤ mᵢ²`.  Consequently, if `L` is the
sum of the third absolute moments, then

`maxᵢ vᵢ ≤ L ^ (2 / 3)`.

Deleting a coordinate of maximal variance leaves variance `1 - maxᵢ vᵢ`.
The exact rescaling factor is therefore `(1 - maxᵢ vᵢ)⁻¹`; the
distribution-free factor `(1 - L ^ (2 / 3))⁻¹` is an upper bound for it, not
an equality in general.  Both quantities are named below to keep this
distinction explicit.

The final part of the file checks, over the reals, the rational arithmetic
which turns Prawitz's local estimate with decimal constants
`0.27283, 0.19948, 0.09116, 0.00095` into the coarser
`0.473, 0.092, 0.004` bound used for `L ≤ 1/50`.
-/

open scoped BigOperators

namespace CertifiedJL
namespace Probability

section CoordinateMoments

universe u_1

variable {ι : Type u_1} [Fintype ι]

/-- Variance of one coordinate in the standardized tilted-sign sum. -/
noncomputable def standardizedTiltedCoordinateVariance
    (u a : ι → ℝ) (i : ι) : ℝ :=
  (a i / tiltedRademacherStdDev u a) ^ 2 *
    (1 - Real.tanh (u i) ^ 2)

/-- Third absolute centered moment of one standardized tilted-sign coordinate. -/
noncomputable def standardizedTiltedCoordinateThirdMoment
    (u a : ι → ℝ) (i : ι) : ℝ :=
  |a i / tiltedRademacherStdDev u a| ^ 3 *
    (1 - Real.tanh (u i) ^ 4)

theorem standardizedTiltedCoordinateVariance_nonneg
    (u a : ι → ℝ) (i : ι) :
    0 ≤ standardizedTiltedCoordinateVariance u a i := by
  unfold standardizedTiltedCoordinateVariance
  exact mul_nonneg (sq_nonneg _)
    (sub_nonneg.mpr (Real.tanh_sq_lt_one _).le)

theorem standardizedTiltedCoordinateThirdMoment_nonneg
    (u a : ι → ℝ) (i : ι) :
    0 ≤ standardizedTiltedCoordinateThirdMoment u a i := by
  unfold standardizedTiltedCoordinateThirdMoment
  exact mul_nonneg (by positivity)
    (one_sub_tanh_fourth_nonneg (u i))

/--
For a centered biased sign, the cube of the variance is at most the square
of the third absolute moment.
-/
theorem standardizedTiltedCoordinateVariance_cube_le_thirdMoment_sq
    (u a : ι → ℝ) (i : ι) :
    standardizedTiltedCoordinateVariance u a i ^ 3 ≤
      standardizedTiltedCoordinateThirdMoment u a i ^ 2 := by
  let c : ℝ := a i / tiltedRademacherStdDev u a
  let t : ℝ := Real.tanh (u i)
  have ht : t ^ 2 ≤ 1 := (Real.tanh_sq_lt_one (u i)).le
  have hcore : (1 - t ^ 2) ^ 3 ≤
      ((1 - t ^ 2) * (1 + t ^ 2)) ^ 2 := by
    have hbase : 1 - t ^ 2 ≤ (1 + t ^ 2) ^ 2 := by
      nlinarith [sq_nonneg (t ^ 2)]
    calc
      (1 - t ^ 2) ^ 3 =
          (1 - t ^ 2) ^ 2 * (1 - t ^ 2) := by ring
      _ ≤ (1 - t ^ 2) ^ 2 * (1 + t ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hbase (sq_nonneg _)
      _ = ((1 - t ^ 2) * (1 + t ^ 2)) ^ 2 := by ring
  have hc : 0 ≤ |c| ^ 6 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hcore hc
  unfold standardizedTiltedCoordinateVariance
    standardizedTiltedCoordinateThirdMoment
  change (c ^ 2 * (1 - t ^ 2)) ^ 3 ≤
    (|c| ^ 3 * (1 - t ^ 4)) ^ 2
  rw [show 1 - t ^ 4 = (1 - t ^ 2) * (1 + t ^ 2) by ring]
  calc
    (c ^ 2 * (1 - t ^ 2)) ^ 3 =
        |c| ^ 6 * (1 - t ^ 2) ^ 3 := by
      rw [mul_pow]
      nth_rewrite 1 [← sq_abs c]
      ring
    _ ≤ |c| ^ 6 * ((1 - t ^ 2) * (1 + t ^ 2)) ^ 2 := hscaled
    _ = (|c| ^ 3 * ((1 - t ^ 2) * (1 + t ^ 2))) ^ 2 := by ring

theorem sum_standardizedTiltedCoordinateThirdMoment
    (u a : ι → ℝ) :
    ∑ i, standardizedTiltedCoordinateThirdMoment u a i =
      tiltedRademacherThirdMomentSum u
        (fun i => a i / tiltedRademacherStdDev u a) := by
  rfl

theorem sum_standardizedTiltedCoordinateVariance_eq_one
    (u a : ι → ℝ) (ha : ∃ i, a i ≠ 0) :
    ∑ i, standardizedTiltedCoordinateVariance u a i = 1 := by
  simpa only [standardizedTiltedCoordinateVariance] using
    standardizedTiltedRademacherVariance_eq_one u a ha

/-- The exponent `2/3` is packaged once to avoid accidental natural division. -/
noncomputable def lyapunovVarianceCap (L : ℝ) : ℝ :=
  L ^ (2 / 3 : ℝ)

theorem lyapunovVarianceCap_nonneg {L : ℝ} (hL : 0 ≤ L) :
    0 ≤ lyapunovVarianceCap L := by
  unfold lyapunovVarianceCap
  exact Real.rpow_nonneg hL _

theorem lyapunovVarianceCap_cube
    {L : ℝ} (hL : 0 ≤ L) :
    lyapunovVarianceCap L ^ 3 = L ^ 2 := by
  unfold lyapunovVarianceCap
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hL]
  norm_num

/--
Every standardized coordinate variance is bounded by the two-thirds power
of the total third absolute moment.
-/
theorem standardizedTiltedCoordinateVariance_le_lyapunovVarianceCap
    (u a : ι → ℝ) (i : ι) :
    standardizedTiltedCoordinateVariance u a i ≤
      lyapunovVarianceCap
        (tiltedRademacherThirdMomentSum u
          (fun j => a j / tiltedRademacherStdDev u a)) := by
  let v : ℝ := standardizedTiltedCoordinateVariance u a i
  let m : ℝ := standardizedTiltedCoordinateThirdMoment u a i
  let L : ℝ := tiltedRademacherThirdMomentSum u
    (fun j => a j / tiltedRademacherStdDev u a)
  have hv : 0 ≤ v :=
    standardizedTiltedCoordinateVariance_nonneg u a i
  have hm : 0 ≤ m :=
    standardizedTiltedCoordinateThirdMoment_nonneg u a i
  have hL : 0 ≤ L :=
    tiltedRademacherThirdMomentSum_nonneg u
      (fun j => a j / tiltedRademacherStdDev u a)
  have hmL : m ≤ L := by
    unfold m L
    rw [← sum_standardizedTiltedCoordinateThirdMoment]
    exact Finset.single_le_sum
      (fun j _ => standardizedTiltedCoordinateThirdMoment_nonneg u a j)
      (Finset.mem_univ i)
  have hcubic : v ^ 3 ≤ L ^ 2 := by
    calc
      v ^ 3 ≤ m ^ 2 :=
        standardizedTiltedCoordinateVariance_cube_le_thirdMoment_sq u a i
      _ ≤ L ^ 2 := by nlinarith
  apply (pow_le_pow_iff_left₀ hv (lyapunovVarianceCap_nonneg hL)
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  rw [lyapunovVarianceCap_cube hL]
  exact hcubic

/-- Maximum standardized coordinate variance over a nonempty finite family. -/
noncomputable def maximalStandardizedTiltedCoordinateVariance
    [Nonempty ι] (u a : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (standardizedTiltedCoordinateVariance u a)

theorem maximalStandardizedTiltedCoordinateVariance_le_lyapunovVarianceCap
    [Nonempty ι] (u a : ι → ℝ) :
    maximalStandardizedTiltedCoordinateVariance u a ≤
      lyapunovVarianceCap
        (tiltedRademacherThirdMomentSum u
          (fun j => a j / tiltedRademacherStdDev u a)) := by
  unfold maximalStandardizedTiltedCoordinateVariance
  rw [Finset.sup'_le_iff]
  intro i _
  exact standardizedTiltedCoordinateVariance_le_lyapunovVarianceCap u a i

theorem exists_coordinate_eq_maximalStandardizedTiltedCoordinateVariance
    [Nonempty ι] (u a : ι → ℝ) :
    ∃ i,
      standardizedTiltedCoordinateVariance u a i =
        maximalStandardizedTiltedCoordinateVariance u a := by
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (standardizedTiltedCoordinateVariance u a)
  exact ⟨i, hi.symm⟩

/--
Deleting a coordinate attaining the maximum leaves exactly one minus the
maximum variance.
-/
theorem exists_maximalCoordinate_sum_variance_erase
    [Nonempty ι] [DecidableEq ι]
    (u a : ι → ℝ) (ha : ∃ i, a i ≠ 0) :
    ∃ i,
      standardizedTiltedCoordinateVariance u a i =
          maximalStandardizedTiltedCoordinateVariance u a ∧
        ∑ j ∈ Finset.univ.erase i,
            standardizedTiltedCoordinateVariance u a j =
          1 - maximalStandardizedTiltedCoordinateVariance u a := by
  obtain ⟨i, hi⟩ :=
    exists_coordinate_eq_maximalStandardizedTiltedCoordinateVariance u a
  refine ⟨i, hi, ?_⟩
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  rw [sum_standardizedTiltedCoordinateVariance_eq_one u a ha, hi]

/--
The coordinatewise bound specialized to the Esscher tilt.  Here the total
third absolute moment is definitionally the tilted Rademacher Lyapunov ratio.
-/
theorem maximalStandardizedTiltedCoordinateVariance_le_rademacherLyapunovCap
    [Nonempty ι] (b : ι → ℝ) (x : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1) :
    maximalStandardizedTiltedCoordinateVariance
        (fun i => x * b i) b ≤
      lyapunovVarianceCap (rademacherLyapunovRatio b x) := by
  have hmax :=
    maximalStandardizedTiltedCoordinateVariance_le_lyapunovVarianceCap
      (fun i => x * b i) b
  rw [tiltedRademacherThirdMomentSum_standardized_specialize b x hnorm] at hmax
  exact hmax

end CoordinateMoments

section DeletedCoordinate

/-- Exact inverse-variance rescaling after deleting a coordinate of variance `v`. -/
noncomputable def deletedCoordinateLambda (v : ℝ) : ℝ :=
  (1 - v)⁻¹

/--
Distribution-free upper envelope for the deleted-coordinate rescaling,
expressed only through the Lyapunov ratio.
-/
noncomputable def smallLyapunovLambda (L : ℝ) : ℝ :=
  (1 - lyapunovVarianceCap L)⁻¹

theorem deletedCoordinateLambda_le_smallLyapunovLambda
    {v L : ℝ} (hv : v ≤ lyapunovVarianceCap L)
    (hcap : lyapunovVarianceCap L < 1) :
    deletedCoordinateLambda v ≤ smallLyapunovLambda L := by
  have hvden : 0 < 1 - v := by
    linarith
  unfold deletedCoordinateLambda smallLyapunovLambda
  exact (inv_le_inv₀ hvden (sub_pos.mpr hcap)).2
    (sub_le_sub_left hv 1)

theorem deletedMaximalCoordinateLambda_le_smallLyapunovLambda
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (b : ι → ℝ) (x : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1)
    (hcap : lyapunovVarianceCap (rademacherLyapunovRatio b x) < 1) :
    deletedCoordinateLambda
        (maximalStandardizedTiltedCoordinateVariance
          (fun i => x * b i) b) ≤
      smallLyapunovLambda (rademacherLyapunovRatio b x) := by
  exact deletedCoordinateLambda_le_smallLyapunovLambda
    (maximalStandardizedTiltedCoordinateVariance_le_rademacherLyapunovCap
      b x hnorm)
    hcap

end DeletedCoordinate

section PrawitzArithmetic

/--
The right-hand side of Prawitz's local estimate (I.52), with every decimal
written as the exact rational represented by that decimal.
-/
noncomputable def prawitzI52Majorant
    (hatEpsilon epsilonPrime epsilonSecond : ℝ) : ℝ :=
  (27283 / 100000 : ℝ) * hatEpsilon +
    (19948 / 100000 : ℝ) * epsilonPrime +
    (9116 / 100000 : ℝ) * epsilonSecond +
    (95 / 100000 : ℝ) * (hatEpsilon + epsilonPrime) ^ 2

/-- Coarsened one-variable form of the Prawitz majorant. -/
noncomputable def coarsePrawitzMajorant (hatEpsilon : ℝ) : ℝ :=
  (473 / 1000 : ℝ) * hatEpsilon +
    (92 / 1000 : ℝ) * hatEpsilon ^ (4 / 3 : ℝ) +
    (4 / 1000 : ℝ) * hatEpsilon ^ 2

/--
Purely algebraic consequence of (I.52).  The premise named `hlocal` isolates
the analytic estimate proved by the downstream small-Lyapunov modules.
-/
theorem le_coarsePrawitzMajorant_of_le_i52
    {distance hatEpsilon epsilonPrime epsilonSecond : ℝ}
    (hlocal :
      distance ≤
        prawitzI52Majorant hatEpsilon epsilonPrime epsilonSecond)
    (hhat : 0 ≤ hatEpsilon)
    (hprime : 0 ≤ epsilonPrime)
    (hprime_le : epsilonPrime ≤ hatEpsilon)
    (hsecond_le :
      epsilonSecond ≤ epsilonPrime ^ (4 / 3 : ℝ)) :
    distance ≤ coarsePrawitzMajorant hatEpsilon := by
  have hpow :
      epsilonPrime ^ (4 / 3 : ℝ) ≤
        hatEpsilon ^ (4 / 3 : ℝ) :=
    Real.rpow_le_rpow hprime hprime_le (by norm_num)
  have hsum : hatEpsilon + epsilonPrime ≤ 2 * hatEpsilon := by
    linarith
  have hsum_nonneg : 0 ≤ hatEpsilon + epsilonPrime := by linarith
  have htwice_nonneg : 0 ≤ 2 * hatEpsilon := by positivity
  have hsquare :
      (hatEpsilon + epsilonPrime) ^ 2 ≤
        (2 * hatEpsilon) ^ 2 :=
    (sq_le_sq₀ hsum_nonneg htwice_nonneg).2 hsum
  unfold prawitzI52Majorant at hlocal
  unfold coarsePrawitzMajorant
  calc
    distance ≤
        (27283 / 100000 : ℝ) * hatEpsilon +
          (19948 / 100000 : ℝ) * epsilonPrime +
          (9116 / 100000 : ℝ) * epsilonSecond +
          (95 / 100000 : ℝ) *
            (hatEpsilon + epsilonPrime) ^ 2 := hlocal
    _ ≤
        (27283 / 100000 : ℝ) * hatEpsilon +
          (19948 / 100000 : ℝ) * hatEpsilon +
          (9116 / 100000 : ℝ) *
            hatEpsilon ^ (4 / 3 : ℝ) +
          (95 / 100000 : ℝ) * (2 * hatEpsilon) ^ 2 := by
      gcongr
      exact hsecond_le.trans hpow
    _ ≤
        (473 / 1000 : ℝ) * hatEpsilon +
          (92 / 1000 : ℝ) * hatEpsilon ^ (4 / 3 : ℝ) +
          (4 / 1000 : ℝ) * hatEpsilon ^ 2 := by
      have hhatPow : 0 ≤ hatEpsilon ^ (4 / 3 : ℝ) := by positivity
      nlinarith [sq_nonneg hatEpsilon]

/--
The coefficient obtained after inserting
`hatEpsilon = lambda^(3/2) L` into the coarsened Prawitz estimate and
dividing by `L`.
-/
noncomputable def smallLyapunovCoarseCoefficient (L : ℝ) : ℝ :=
  (473 / 1000 : ℝ) * smallLyapunovLambda L ^ (3 / 2 : ℝ) +
    (92 / 1000 : ℝ) * smallLyapunovLambda L ^ 2 *
      L ^ (1 / 3 : ℝ) +
    (4 / 1000 : ℝ) * smallLyapunovLambda L ^ 3 * L

/--
Exact algebra behind the coefficient form: after substituting
`hatEpsilon = lambda^(3/2) L`, the coarsened majorant is `L` times the
displayed small-L coefficient.
-/
theorem coarsePrawitzMajorant_tilted_eq
    {L : ℝ} (hL : 0 ≤ L)
    (hlambda : 0 ≤ smallLyapunovLambda L) :
    coarsePrawitzMajorant
        (smallLyapunovLambda L ^ (3 / 2 : ℝ) * L) =
      L * smallLyapunovCoarseCoefficient L := by
  let lambda : ℝ := smallLyapunovLambda L
  have hlambda' : 0 ≤ lambda := by
    simpa only [lambda] using hlambda
  have hlambda32 : 0 ≤ lambda ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg hlambda' _
  have hfirst :
      (lambda ^ (3 / 2 : ℝ)) ^ (4 / 3 : ℝ) =
        lambda ^ 2 := by
    rw [← Real.rpow_mul hlambda']
    norm_num
  have hsecond :
      L ^ (4 / 3 : ℝ) = L * L ^ (1 / 3 : ℝ) := by
    rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num,
      Real.rpow_add_of_nonneg hL (by norm_num) (by norm_num),
      Real.rpow_one]
  have hthird :
      (lambda ^ (3 / 2 : ℝ)) ^ 2 = lambda ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlambda']
    norm_num
  unfold coarsePrawitzMajorant smallLyapunovCoarseCoefficient
  change
    (473 / 1000 : ℝ) * (lambda ^ (3 / 2 : ℝ) * L) +
        (92 / 1000 : ℝ) *
          (lambda ^ (3 / 2 : ℝ) * L) ^ (4 / 3 : ℝ) +
        (4 / 1000 : ℝ) * (lambda ^ (3 / 2 : ℝ) * L) ^ 2 =
      L *
        ((473 / 1000 : ℝ) * lambda ^ (3 / 2 : ℝ) +
          (92 / 1000 : ℝ) * lambda ^ 2 * L ^ (1 / 3 : ℝ) +
          (4 / 1000 : ℝ) * lambda ^ 3 * L)
  rw [Real.mul_rpow hlambda32 hL, hfirst, hsecond, mul_pow, hthird]
  ring

theorem lyapunov_one_third_le_seven_over_twentyFive
    {L : ℝ} (hL : 0 ≤ L) (hsmall : L ≤ 1 / 50) :
    L ^ (1 / 3 : ℝ) ≤ 7 / 25 := by
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hL _)
    (by norm_num : (0 : ℝ) ≤ 7 / 25)
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  have hcube :
      (L ^ (1 / 3 : ℝ)) ^ 3 = L := by
    simpa only [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num] using
      Real.rpow_inv_natCast_pow hL (by norm_num : (3 : ℕ) ≠ 0)
  rw [hcube]
  calc
    L ≤ 1 / 50 := hsmall
    _ ≤ (7 / 25 : ℝ) ^ 3 := by norm_num

theorem lyapunovVarianceCap_le_fortyNine_over_sixHundredTwentyFive
    {L : ℝ} (hL : 0 ≤ L) (hsmall : L ≤ 1 / 50) :
    lyapunovVarianceCap L ≤ 49 / 625 := by
  unfold lyapunovVarianceCap
  have hsquare :
      L ^ (2 / 3 : ℝ) = (L ^ (1 / 3 : ℝ)) ^ 2 := by
    simpa only [show (2 / 3 : ℝ) = (1 / 3 : ℝ) * (2 : ℕ) by norm_num] using
      Real.rpow_mul_natCast hL (1 / 3 : ℝ) 2
  rw [hsquare]
  have hroot :=
    lyapunov_one_third_le_seven_over_twentyFive hL hsmall
  calc
    (L ^ (1 / 3 : ℝ)) ^ 2 ≤ (7 / 25 : ℝ) ^ 2 :=
      (sq_le_sq₀ (Real.rpow_nonneg hL _)
        (by norm_num : (0 : ℝ) ≤ 7 / 25)).2 hroot
    _ = 49 / 625 := by norm_num

theorem smallLyapunovLambda_le_sixHundredTwentyFive_over_fiveHundredSeventySix
    {L : ℝ} (hL : 0 ≤ L) (hsmall : L ≤ 1 / 50) :
    smallLyapunovLambda L ≤ 625 / 576 := by
  have hcap :=
    lyapunovVarianceCap_le_fortyNine_over_sixHundredTwentyFive hL hsmall
  have hden : 0 < 1 - lyapunovVarianceCap L := by
    linarith
  unfold smallLyapunovLambda
  rw [show (625 / 576 : ℝ) = (576 / 625 : ℝ)⁻¹ by norm_num]
  exact (inv_le_inv₀ hden (by norm_num : (0 : ℝ) < 576 / 625)).2
    (by linarith)

theorem smallLyapunovLambda_nonneg
    {L : ℝ} (hL : 0 ≤ L) (hsmall : L ≤ 1 / 50) :
    0 ≤ smallLyapunovLambda L := by
  have hcap :=
    lyapunovVarianceCap_le_fortyNine_over_sixHundredTwentyFive hL hsmall
  have hden : 0 < 1 - lyapunovVarianceCap L := by
    linarith
  unfold smallLyapunovLambda
  exact inv_nonneg.mpr hden.le

theorem smallLyapunovLambda_threeHalves_le
    {L : ℝ} (hL : 0 ≤ L) (hsmall : L ≤ 1 / 50) :
    smallLyapunovLambda L ^ (3 / 2 : ℝ) ≤
      (625 / 576 : ℝ) * (25 / 24 : ℝ) := by
  have hlambda :=
    smallLyapunovLambda_le_sixHundredTwentyFive_over_fiveHundredSeventySix
      hL hsmall
  have hlambda0 := smallLyapunovLambda_nonneg hL hsmall
  have hlambdaPos : 0 < smallLyapunovLambda L := by
    have hcap :=
      lyapunovVarianceCap_le_fortyNine_over_sixHundredTwentyFive hL hsmall
    unfold smallLyapunovLambda
    exact inv_pos.mpr (by linarith)
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add hlambdaPos]
  rw [Real.rpow_one, show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
  have hsqrt :
      smallLyapunovLambda L ^ ((2 : ℝ)⁻¹) ≤ 25 / 24 := by
    apply (pow_le_pow_iff_left₀ (by positivity)
      (by norm_num : (0 : ℝ) ≤ 25 / 24)
      (by norm_num : (2 : ℕ) ≠ 0)).mp
    have hsquare :
        (smallLyapunovLambda L ^ ((2 : ℝ)⁻¹)) ^ 2 =
          smallLyapunovLambda L :=
      Real.rpow_inv_natCast_pow hlambda0 (by norm_num : (2 : ℕ) ≠ 0)
    rw [hsquare]
    exact hlambda.trans_eq (by norm_num)
  calc
    smallLyapunovLambda L *
        smallLyapunovLambda L ^ ((2 : ℝ)⁻¹) ≤
        (625 / 576 : ℝ) *
          smallLyapunovLambda L ^ ((2 : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_right hlambda (by positivity)
    _ ≤ (625 / 576 : ℝ) * (25 / 24 : ℝ) :=
      mul_le_mul_of_nonneg_left hsqrt (by norm_num)

/--
The local Prawitz estimate's side condition is automatic on the small-L
branch: both epsilon terms are at most the tilted Lyapunov quantity, and
twice that quantity is at most `1/5`.
-/
theorem two_mul_smallLyapunovHatEpsilon_le_one_fifth
    {L : ℝ} (hL : 0 ≤ L) (hsmall : L ≤ 1 / 50) :
    2 * (smallLyapunovLambda L ^ (3 / 2 : ℝ) * L) ≤ 1 / 5 := by
  have hlambda32 :=
    smallLyapunovLambda_threeHalves_le hL hsmall
  have hpow_nonneg :
      0 ≤ smallLyapunovLambda L ^ (3 / 2 : ℝ) := by
    exact Real.rpow_nonneg (smallLyapunovLambda_nonneg hL hsmall) _
  calc
    2 * (smallLyapunovLambda L ^ (3 / 2 : ℝ) * L) ≤
        2 * (((625 / 576 : ℝ) * (25 / 24 : ℝ)) * (1 / 50 : ℝ)) := by
      gcongr
    _ ≤ 1 / 5 := by norm_num

theorem smallLyapunovLocalSideCondition
    {L epsilonPrime : ℝ}
    (hL : 0 ≤ L) (hsmall : L ≤ 1 / 50)
    (hprime_le :
      epsilonPrime ≤ smallLyapunovLambda L ^ (3 / 2 : ℝ) * L) :
    smallLyapunovLambda L ^ (3 / 2 : ℝ) * L + epsilonPrime ≤
      1 / 5 := by
  have htwice :=
    two_mul_smallLyapunovHatEpsilon_le_one_fifth hL hsmall
  linarith

/-- The coarsened small-L coefficient is strictly below `3/5` on `L ≤ 1/50`. -/
theorem smallLyapunovCoarseCoefficient_lt_three_fifths
    {L : ℝ} (hL : 0 ≤ L) (hsmall : L ≤ 1 / 50) :
    smallLyapunovCoarseCoefficient L < 3 / 5 := by
  have hlambda :=
    smallLyapunovLambda_le_sixHundredTwentyFive_over_fiveHundredSeventySix
      hL hsmall
  have hlambda0 := smallLyapunovLambda_nonneg hL hsmall
  have hlambda32 :=
    smallLyapunovLambda_threeHalves_le hL hsmall
  have hroot :=
    lyapunov_one_third_le_seven_over_twentyFive hL hsmall
  have hlambdaSq :
      smallLyapunovLambda L ^ 2 ≤ (625 / 576 : ℝ) ^ 2 := by
    nlinarith
  have hlambdaCube :
      smallLyapunovLambda L ^ 3 ≤ (625 / 576 : ℝ) ^ 3 := by
    exact (pow_le_pow_iff_left₀ hlambda0 (by norm_num)
      (by norm_num : (3 : ℕ) ≠ 0)).mpr hlambda
  unfold smallLyapunovCoarseCoefficient
  calc
    (473 / 1000 : ℝ) * smallLyapunovLambda L ^ (3 / 2 : ℝ) +
          (92 / 1000 : ℝ) * smallLyapunovLambda L ^ 2 *
            L ^ (1 / 3 : ℝ) +
          (4 / 1000 : ℝ) * smallLyapunovLambda L ^ 3 * L
        ≤
        (473 / 1000 : ℝ) * ((625 / 576 : ℝ) * (25 / 24 : ℝ)) +
          (92 / 1000 : ℝ) * (625 / 576 : ℝ) ^ 2 * (7 / 25 : ℝ) +
          (4 / 1000 : ℝ) * (625 / 576 : ℝ) ^ 3 * (1 / 50 : ℝ) := by
      gcongr
    _ < 3 / 5 := by norm_num

theorem coarsePrawitzMajorant_tilted_lt_three_fifths_mul
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ 1 / 50) :
    coarsePrawitzMajorant
        (smallLyapunovLambda L ^ (3 / 2 : ℝ) * L) <
      (3 / 5 : ℝ) * L := by
  rw [coarsePrawitzMajorant_tilted_eq hL.le
    (smallLyapunovLambda_nonneg hL.le hsmall)]
  rw [mul_comm L]
  exact mul_lt_mul_of_pos_right
    (smallLyapunovCoarseCoefficient_lt_three_fifths hL.le hsmall)
    hL

/--
Shipping form of the deterministic reduction.  Once the local analytic
estimate (I.52) supplies `hlocal`, its moment comparisons alone imply the
strict Berry--Esseen coefficient `3/5` throughout `0 < L ≤ 1/50`.
-/
theorem lt_three_fifths_mul_of_le_prawitzI52
    {distance L epsilonPrime epsilonSecond : ℝ}
    (hL : 0 < L) (hsmall : L ≤ 1 / 50)
    (hlocal :
      distance ≤
        prawitzI52Majorant
          (smallLyapunovLambda L ^ (3 / 2 : ℝ) * L)
          epsilonPrime epsilonSecond)
    (hprime : 0 ≤ epsilonPrime)
    (hprime_le :
      epsilonPrime ≤ smallLyapunovLambda L ^ (3 / 2 : ℝ) * L)
    (hsecond_le :
      epsilonSecond ≤ epsilonPrime ^ (4 / 3 : ℝ)) :
    distance < (3 / 5 : ℝ) * L := by
  have hhat : 0 ≤
      smallLyapunovLambda L ^ (3 / 2 : ℝ) * L :=
    mul_nonneg
      (Real.rpow_nonneg
        (smallLyapunovLambda_nonneg hL.le hsmall) _)
      hL.le
  exact (le_coarsePrawitzMajorant_of_le_i52
      hlocal hhat hprime hprime_le hsecond_le).trans_lt
    (coarsePrawitzMajorant_tilted_lt_three_fifths_mul hL hsmall)

end PrawitzArithmetic

end Probability
end CertifiedJL
