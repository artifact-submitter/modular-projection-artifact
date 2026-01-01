/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.NormalApproximation.Lyapunov.SmallLyapunovReduction
import CertifiedJL.Probability.NormalApproximation.Tyurin.ProductEnvelope
import CertifiedJL.Analysis.Fourier.Prawitz.GaussianTerms
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Moment parameters for the small-Lyapunov analytic estimate

This file supplies the exact moment comparisons needed when Prawitz's local
normal-approximation estimate is applied after deleting a coordinate of
maximal variance.

For standardized coordinate variances `vᵢ`, write

* `τ = ∑ᵢ vᵢ^(3/2)`;
* `q = ∑ᵢ vᵢ²`.

The special two-point structure gives `vᵢ^(3/2) ≤ mᵢ`, where `mᵢ` is the
third absolute centered moment.  Hence `τ ≤ L`.  Convexity then gives the
second comparison `q ≤ τ^(4/3)`.  After rescaling by the deleted-coordinate
variance, these become exactly `ε' ≤ ε̂` and `ε'' ≤ (ε')^(4/3)`.

No normal-approximation or Fourier theorem is assumed here: every result in
this file is a finite-sum or real-power identity.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CertifiedJL
namespace Probability

section FinitePowerSums

universe u_1

variable {ι : Type u_1}

/--
For nonnegative summands and exponent at least one, the sum of powers is at
most the corresponding power of the sum.
-/
theorem sum_rpow_le_rpow_sum
    (s : Finset ι) (f : ι → ℝ) {p : ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hp : 1 ≤ p) :
    ∑ i ∈ s, f i ^ p ≤ (∑ i ∈ s, f i) ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using Real.zero_rpow_nonneg p
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      have hfi : 0 ≤ f i := hf i (Finset.mem_insert_self i s)
      have hsum : 0 ≤ ∑ j ∈ s, f j :=
        Finset.sum_nonneg fun j hj =>
          hf j (Finset.mem_insert_of_mem hj)
      calc
        f i ^ p + ∑ j ∈ s, f j ^ p ≤
            f i ^ p + (∑ j ∈ s, f j) ^ p := by
          gcongr
          exact ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
        _ ≤ (f i + ∑ j ∈ s, f j) ^ p :=
          Real.add_rpow_le_rpow_add hfi hsum hp

end FinitePowerSums

section DeletedCoordinateMomentParameters

universe u_1

variable {ι : Type u_1} [Fintype ι]

/-- Sum of the three-halves powers of standardized coordinate variances. -/
noncomputable def standardizedTiltedVarianceThreeHalvesSum
    (u a : ι → ℝ) : ℝ :=
  ∑ i, standardizedTiltedCoordinateVariance u a i ^ (3 / 2 : ℝ)

/-- Sum of the squares of standardized coordinate variances. -/
noncomputable def standardizedTiltedVarianceSquareSum
    (u a : ι → ℝ) : ℝ :=
  ∑ i, standardizedTiltedCoordinateVariance u a i ^ 2

/-- Three-halves variance sum after deleting coordinate `i`. -/
noncomputable def standardizedTiltedVarianceThreeHalvesSumErase
    [DecidableEq ι] (u a : ι → ℝ) (i : ι) : ℝ :=
  ∑ j ∈ Finset.univ.erase i,
    standardizedTiltedCoordinateVariance u a j ^ (3 / 2 : ℝ)

/-- Squared-variance sum after deleting coordinate `i`. -/
noncomputable def standardizedTiltedVarianceSquareSumErase
    [DecidableEq ι] (u a : ι → ℝ) (i : ι) : ℝ :=
  ∑ j ∈ Finset.univ.erase i,
    standardizedTiltedCoordinateVariance u a j ^ 2

theorem standardizedTiltedVarianceThreeHalvesSum_nonneg
    (u a : ι → ℝ) :
    0 ≤ standardizedTiltedVarianceThreeHalvesSum u a := by
  unfold standardizedTiltedVarianceThreeHalvesSum
  exact Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg
      (standardizedTiltedCoordinateVariance_nonneg u a i) _

theorem standardizedTiltedVarianceSquareSum_nonneg
    (u a : ι → ℝ) :
    0 ≤ standardizedTiltedVarianceSquareSum u a := by
  unfold standardizedTiltedVarianceSquareSum
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

theorem standardizedTiltedVarianceThreeHalvesSumErase_nonneg
    [DecidableEq ι] (u a : ι → ℝ) (i : ι) :
    0 ≤ standardizedTiltedVarianceThreeHalvesSumErase u a i := by
  unfold standardizedTiltedVarianceThreeHalvesSumErase
  exact Finset.sum_nonneg fun j _ =>
    Real.rpow_nonneg
      (standardizedTiltedCoordinateVariance_nonneg u a j) _

theorem standardizedTiltedVarianceSquareSumErase_nonneg
    [DecidableEq ι] (u a : ι → ℝ) (i : ι) :
    0 ≤ standardizedTiltedVarianceSquareSumErase u a i := by
  unfold standardizedTiltedVarianceSquareSumErase
  exact Finset.sum_nonneg fun j _ => sq_nonneg _

/--
For one centered two-point coordinate, the variance to the three-halves
power is at most the third absolute centered moment.
-/
theorem standardizedTiltedCoordinateVariance_rpow_threeHalves_le_thirdMoment
    (u a : ι → ℝ) (i : ι) :
    standardizedTiltedCoordinateVariance u a i ^ (3 / 2 : ℝ) ≤
      standardizedTiltedCoordinateThirdMoment u a i := by
  let v := standardizedTiltedCoordinateVariance u a i
  let m := standardizedTiltedCoordinateThirdMoment u a i
  have hv : 0 ≤ v :=
    standardizedTiltedCoordinateVariance_nonneg u a i
  have hm : 0 ≤ m :=
    standardizedTiltedCoordinateThirdMoment_nonneg u a i
  have hsquare :
      (v ^ (3 / 2 : ℝ)) ^ 2 = v ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv]
    norm_num
  apply (sq_le_sq₀ (Real.rpow_nonneg hv _) hm).mp
  rw [hsquare]
  exact standardizedTiltedCoordinateVariance_cube_le_thirdMoment_sq u a i

/-- The auxiliary third-power variance sum is bounded by the Lyapunov sum. -/
theorem standardizedTiltedVarianceThreeHalvesSum_le_thirdMomentSum
    (u a : ι → ℝ) :
    standardizedTiltedVarianceThreeHalvesSum u a ≤
      tiltedRademacherThirdMomentSum u
        (fun i => a i / tiltedRademacherStdDev u a) := by
  rw [← sum_standardizedTiltedCoordinateThirdMoment]
  unfold standardizedTiltedVarianceThreeHalvesSum
  exact Finset.sum_le_sum fun i _ =>
    standardizedTiltedCoordinateVariance_rpow_threeHalves_le_thirdMoment
      u a i

/--
The squared-variance sum is controlled by the three-halves-variance sum to
the four-thirds power.
-/
theorem standardizedTiltedVarianceSquareSum_le_threeHalvesSum_rpow
    (u a : ι → ℝ) :
    standardizedTiltedVarianceSquareSum u a ≤
      standardizedTiltedVarianceThreeHalvesSum u a ^ (4 / 3 : ℝ) := by
  let v : ι → ℝ := fun i =>
    standardizedTiltedCoordinateVariance u a i
  have hv (i : ι) : 0 ≤ v i :=
    standardizedTiltedCoordinateVariance_nonneg u a i
  have hpower (i : ι) :
      (v i ^ (3 / 2 : ℝ)) ^ (4 / 3 : ℝ) = v i ^ 2 := by
    rw [← Real.rpow_mul (hv i)]
    norm_num
  unfold standardizedTiltedVarianceSquareSum
    standardizedTiltedVarianceThreeHalvesSum
  change (∑ i, v i ^ 2) ≤ (∑ i, v i ^ (3 / 2 : ℝ)) ^ (4 / 3 : ℝ)
  rw [← Finset.sum_congr rfl fun i _ => hpower i]
  exact sum_rpow_le_rpow_sum Finset.univ
    (fun i => v i ^ (3 / 2 : ℝ))
    (fun i _ => Real.rpow_nonneg (hv i) _)
    (by norm_num)

/--
The deleted squared-variance sum is controlled by the deleted
three-halves-variance sum itself; no relaxation to the full family is needed.
-/
theorem standardizedTiltedVarianceSquareSumErase_le_threeHalvesSumErase_rpow
    [DecidableEq ι] (u a : ι → ℝ) (i : ι) :
    standardizedTiltedVarianceSquareSumErase u a i ≤
      standardizedTiltedVarianceThreeHalvesSumErase u a i ^
        (4 / 3 : ℝ) := by
  let v : ι → ℝ := fun j =>
    standardizedTiltedCoordinateVariance u a j
  have hv (j : ι) : 0 ≤ v j :=
    standardizedTiltedCoordinateVariance_nonneg u a j
  have hpower (j : ι) :
      (v j ^ (3 / 2 : ℝ)) ^ (4 / 3 : ℝ) = v j ^ 2 := by
    rw [← Real.rpow_mul (hv j)]
    norm_num
  unfold standardizedTiltedVarianceSquareSumErase
    standardizedTiltedVarianceThreeHalvesSumErase
  change (∑ j ∈ Finset.univ.erase i, v j ^ 2) ≤
    (∑ j ∈ Finset.univ.erase i, v j ^ (3 / 2 : ℝ)) ^ (4 / 3 : ℝ)
  rw [← Finset.sum_congr rfl fun j _ => hpower j]
  exact sum_rpow_le_rpow_sum (Finset.univ.erase i)
    (fun j => v j ^ (3 / 2 : ℝ))
    (fun j _ => Real.rpow_nonneg (hv j) _)
    (by norm_num)

/-- Deleting a coordinate cannot increase the three-halves variance sum. -/
theorem standardizedTiltedVarianceThreeHalvesSumErase_le
    [DecidableEq ι] (u a : ι → ℝ) (i : ι) :
    standardizedTiltedVarianceThreeHalvesSumErase u a i ≤
      standardizedTiltedVarianceThreeHalvesSum u a := by
  unfold standardizedTiltedVarianceThreeHalvesSumErase
    standardizedTiltedVarianceThreeHalvesSum
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  exact sub_le_self _
    (Real.rpow_nonneg
      (standardizedTiltedCoordinateVariance_nonneg u a i) _)

end DeletedCoordinateMomentParameters

section RescaledPrawitzParameters

/-- Prawitz's exact deleted-coordinate rescaling parameter. -/
noncomputable def deletedCoordinateHatEpsilon (v L : ℝ) : ℝ :=
  deletedCoordinateLambda v ^ (3 / 2 : ℝ) * L

/-- Exact deleted-coordinate `ε'` before replacing the rescaling by its envelope. -/
noncomputable def deletedCoordinateEpsilonPrime
    (v tau : ℝ) : ℝ :=
  deletedCoordinateLambda v ^ (3 / 2 : ℝ) * tau

/-- Exact deleted-coordinate `ε''` before replacing the rescaling by its envelope. -/
noncomputable def deletedCoordinateEpsilonSecond
    (v q : ℝ) : ℝ :=
  deletedCoordinateLambda v ^ 2 * q

/-- Prawitz's `ε̂`, using the distribution-free deleted-coordinate envelope. -/
noncomputable def smallLyapunovHatEpsilon (L : ℝ) : ℝ :=
  smallLyapunovLambda L ^ (3 / 2 : ℝ) * L

/--
Prawitz's `ε'` for a variance-three-halves sum `τ`, using the
distribution-free deleted-coordinate envelope.
-/
noncomputable def smallLyapunovEpsilonPrime (L tau : ℝ) : ℝ :=
  smallLyapunovLambda L ^ (3 / 2 : ℝ) * tau

/--
Prawitz's `ε''` for a squared-variance sum `q`, using the
distribution-free deleted-coordinate envelope.
-/
noncomputable def smallLyapunovEpsilonSecond (L q : ℝ) : ℝ :=
  smallLyapunovLambda L ^ 2 * q

theorem deletedCoordinateLambda_nonneg
    {v : ℝ} (hv : v < 1) :
    0 ≤ deletedCoordinateLambda v := by
  unfold deletedCoordinateLambda
  exact (inv_pos.mpr (sub_pos.mpr hv)).le

theorem smallLyapunovEpsilonPrime_nonneg
    {L tau : ℝ} (hL : 0 ≤ L) (hsmall : L ≤ 1 / 50)
    (htau : 0 ≤ tau) :
    0 ≤ smallLyapunovEpsilonPrime L tau := by
  unfold smallLyapunovEpsilonPrime
  exact mul_nonneg
    (Real.rpow_nonneg (smallLyapunovLambda_nonneg hL hsmall) _)
    htau

theorem smallLyapunovEpsilonPrime_le_hatEpsilon
    {L tau : ℝ} (hL : 0 ≤ L) (hsmall : L ≤ 1 / 50)
    (htau : tau ≤ L) :
    smallLyapunovEpsilonPrime L tau ≤ smallLyapunovHatEpsilon L := by
  unfold smallLyapunovEpsilonPrime smallLyapunovHatEpsilon
  exact mul_le_mul_of_nonneg_left htau
    (Real.rpow_nonneg (smallLyapunovLambda_nonneg hL hsmall) _)

theorem smallLyapunovEpsilonSecond_le_prime_rpow
    {L tau q : ℝ} (hL : 0 ≤ L) (hsmall : L ≤ 1 / 50)
    (htau : 0 ≤ tau) (hq : q ≤ tau ^ (4 / 3 : ℝ)) :
    smallLyapunovEpsilonSecond L q ≤
      smallLyapunovEpsilonPrime L tau ^ (4 / 3 : ℝ) := by
  have hlambda : 0 ≤ smallLyapunovLambda L :=
    smallLyapunovLambda_nonneg hL hsmall
  have hlambda32 :
      0 ≤ smallLyapunovLambda L ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg hlambda _
  have hlambdaPower :
      (smallLyapunovLambda L ^ (3 / 2 : ℝ)) ^ (4 / 3 : ℝ) =
        smallLyapunovLambda L ^ 2 := by
    rw [← Real.rpow_mul hlambda]
    norm_num
  unfold smallLyapunovEpsilonSecond smallLyapunovEpsilonPrime
  rw [Real.mul_rpow hlambda32 htau, hlambdaPower]
  exact mul_le_mul_of_nonneg_left hq (sq_nonneg _)

/--
Replacing the exact deleted-coordinate rescaling by the small-Lyapunov
envelope only enlarges `ε̂`.
-/
theorem deletedCoordinateHatEpsilon_le_smallLyapunovHatEpsilon
    {v L : ℝ} (hL : 0 ≤ L)
    (hv : v ≤ lyapunovVarianceCap L)
    (hcap : lyapunovVarianceCap L < 1) :
    deletedCoordinateHatEpsilon v L ≤ smallLyapunovHatEpsilon L := by
  have hv1 : v < 1 := hv.trans_lt hcap
  have hlambda :=
    deletedCoordinateLambda_le_smallLyapunovLambda hv hcap
  have hlambda0 := deletedCoordinateLambda_nonneg hv1
  have henv0 : 0 ≤ smallLyapunovLambda L := by
    unfold smallLyapunovLambda
    exact (inv_pos.mpr (sub_pos.mpr hcap)).le
  unfold deletedCoordinateHatEpsilon smallLyapunovHatEpsilon
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow hlambda0 hlambda (by norm_num)) hL

/--
Replacing the exact deleted-coordinate rescaling by its envelope only
enlarges `ε'`.
-/
theorem deletedCoordinateEpsilonPrime_le_smallLyapunovEpsilonPrime
    {v L tau : ℝ} (htau : 0 ≤ tau)
    (hv : v ≤ lyapunovVarianceCap L)
    (hcap : lyapunovVarianceCap L < 1) :
    deletedCoordinateEpsilonPrime v tau ≤
      smallLyapunovEpsilonPrime L tau := by
  have hv1 : v < 1 := hv.trans_lt hcap
  have hlambda :=
    deletedCoordinateLambda_le_smallLyapunovLambda hv hcap
  have hlambda0 := deletedCoordinateLambda_nonneg hv1
  unfold deletedCoordinateEpsilonPrime smallLyapunovEpsilonPrime
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow hlambda0 hlambda (by norm_num)) htau

/--
Replacing the exact deleted-coordinate rescaling by its envelope only
enlarges `ε''`.
-/
theorem deletedCoordinateEpsilonSecond_le_smallLyapunovEpsilonSecond
    {v L q : ℝ} (hq : 0 ≤ q)
    (hv : v ≤ lyapunovVarianceCap L)
    (hcap : lyapunovVarianceCap L < 1) :
    deletedCoordinateEpsilonSecond v q ≤
      smallLyapunovEpsilonSecond L q := by
  have hv1 : v < 1 := hv.trans_lt hcap
  have hlambda :=
    deletedCoordinateLambda_le_smallLyapunovLambda hv hcap
  have hlambda0 := deletedCoordinateLambda_nonneg hv1
  have henv0 : 0 ≤ smallLyapunovLambda L := by
    unfold smallLyapunovLambda
    exact (inv_pos.mpr (sub_pos.mpr hcap)).le
  unfold deletedCoordinateEpsilonSecond smallLyapunovEpsilonSecond
  exact mul_le_mul_of_nonneg_right
    ((pow_le_pow_iff_left₀ hlambda0 henv0
      (by norm_num : (2 : ℕ) ≠ 0)).mpr hlambda)
    hq

/-- The exact Prawitz majorant is monotone in its three nonnegative inputs. -/
theorem prawitzI52Majorant_mono
    {hat₁ hat₂ prime₁ prime₂ second₁ second₂ : ℝ}
    (hhat0 : 0 ≤ hat₁) (hprime0 : 0 ≤ prime₁)
    (hhat : hat₁ ≤ hat₂) (hprime : prime₁ ≤ prime₂)
    (hsecond : second₁ ≤ second₂) :
    prawitzI52Majorant hat₁ prime₁ second₁ ≤
      prawitzI52Majorant hat₂ prime₂ second₂ := by
  have hsum0 : 0 ≤ hat₁ + prime₁ := add_nonneg hhat0 hprime0
  have hsum : hat₁ + prime₁ ≤ hat₂ + prime₂ := add_le_add hhat hprime
  have hsum20 : 0 ≤ hat₂ + prime₂ := hsum0.trans hsum
  unfold prawitzI52Majorant
  gcongr

/--
A local estimate stated with the exact deletion factor implies the same
estimate with the distribution-free small-Lyapunov envelope.
-/
theorem le_envelopedPrawitzI52_of_le_deletedCoordinatePrawitzI52
    {distance v L tau q : ℝ}
    (hL : 0 ≤ L) (htau : 0 ≤ tau) (hq : 0 ≤ q)
    (hv : v ≤ lyapunovVarianceCap L)
    (hcap : lyapunovVarianceCap L < 1)
    (hlocal :
      distance ≤ prawitzI52Majorant
        (deletedCoordinateHatEpsilon v L)
        (deletedCoordinateEpsilonPrime v tau)
        (deletedCoordinateEpsilonSecond v q)) :
    distance ≤ prawitzI52Majorant
      (smallLyapunovHatEpsilon L)
      (smallLyapunovEpsilonPrime L tau)
      (smallLyapunovEpsilonSecond L q) := by
  refine hlocal.trans (prawitzI52Majorant_mono ?_ ?_ ?_ ?_ ?_)
  · exact mul_nonneg
      (Real.rpow_nonneg
        (deletedCoordinateLambda_nonneg (hv.trans_lt hcap)) _)
      hL
  · exact mul_nonneg
      (Real.rpow_nonneg
        (deletedCoordinateLambda_nonneg (hv.trans_lt hcap)) _)
      htau
  · exact deletedCoordinateHatEpsilon_le_smallLyapunovHatEpsilon
      hL hv hcap
  · exact deletedCoordinateEpsilonPrime_le_smallLyapunovEpsilonPrime
      htau hv hcap
  · exact deletedCoordinateEpsilonSecond_le_smallLyapunovEpsilonSecond
      hq hv hcap

/--
End-to-end deterministic wrapper for the exact deleted-coordinate form of
Prawitz's estimate.  The only premise of analytic content is `hlocal`; all
moment comparisons and all numerical arithmetic are discharged here.
-/
theorem lt_three_fifths_mul_of_le_deletedCoordinatePrawitzI52
    {distance v L tau q : ℝ}
    (hL : 0 < L) (hsmall : L ≤ 1 / 50)
    (htau : 0 ≤ tau) (htauL : tau ≤ L)
    (hq : 0 ≤ q) (hqTau : q ≤ tau ^ (4 / 3 : ℝ))
    (hv : v ≤ lyapunovVarianceCap L)
    (hlocal :
      distance ≤ prawitzI52Majorant
        (deletedCoordinateHatEpsilon v L)
        (deletedCoordinateEpsilonPrime v tau)
        (deletedCoordinateEpsilonSecond v q)) :
    distance < (3 / 5 : ℝ) * L := by
  have hcap : lyapunovVarianceCap L < 1 := by
    have hcapBound :=
      lyapunovVarianceCap_le_fortyNine_over_sixHundredTwentyFive
        hL.le hsmall
    linarith
  have henveloped :=
    le_envelopedPrawitzI52_of_le_deletedCoordinatePrawitzI52
      hL.le htau hq hv hcap hlocal
  exact lt_three_fifths_mul_of_le_prawitzI52
    hL hsmall henveloped
    (smallLyapunovEpsilonPrime_nonneg hL.le hsmall htau)
    (smallLyapunovEpsilonPrime_le_hatEpsilon hL.le hsmall htauL)
    (smallLyapunovEpsilonSecond_le_prime_rpow
      hL.le hsmall htau hqTau)

end RescaledPrawitzParameters

section SpecializedMomentPackage

universe u_1

variable {ι : Type u_1} [Fintype ι]

/--
The sharp deleted-coordinate characteristic-function majorant for the
standardized Esscher tilt of a Rademacher sum.

Keeping this expression as a named function lets the Prawitz integration
layer consume the exact coordinate-wise damping, without replacing it by a
coarse common exponential envelope.
-/
noncomputable def tiltedRademacherGaussianCFMajorant
    (b : ι → ℝ) (x t : ℝ) : ℝ :=
  let u : ι → ℝ := fun i => x * b i
  let c : ι → ℝ := fun i => b i / tiltedRademacherStdDev u b
  ∑ i,
    (if |t * c i| ≤ 1 then (5 / 12 : ℝ) else 7 / 6) *
      biasedSignThirdMomentTerm (u i) (c i) * |t| ^ 3 *
      Real.exp
        (-((tiltedRademacherLocalVariance u c t -
            if |t * c i| ≤ 1 then
              biasedSignVarianceTerm (u i) (c i)
            else 0) * t ^ 2) / 5)

/--
Sharp distribution-specific characteristic-function comparison used in the
small-L Prawitz integral.  The deleted-coordinate exponential remains inside
the sum; in particular, this theorem does not make the quantitatively fatal
replacement by a common `7/6 · L · exp(-t²/10)` envelope.
-/
theorem norm_charFun_rademacherTiltedStandardizedLaw_sub_gaussian_exact_le
    (b : ι → ℝ) (x t : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1) :
    let u : ι → ℝ := fun i => x * b i
    let c : ι → ℝ := fun i => b i / tiltedRademacherStdDev u b
    ‖charFun (rademacherTiltedStandardizedLaw b x) t -
        ((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ)‖ ≤
      ∑ i,
        (if |t * c i| ≤ 1 then (5 / 12 : ℝ) else 7 / 6) *
          biasedSignThirdMomentTerm (u i) (c i) * |t| ^ 3 *
          Real.exp
            (-((tiltedRademacherLocalVariance u c t -
                if |t * c i| ≤ 1 then
                  biasedSignVarianceTerm (u i) (c i)
                else 0) * t ^ 2) / 5) := by
  dsimp only
  let u : ι → ℝ := fun i => x * b i
  let c : ι → ℝ := fun i => b i / tiltedRademacherStdDev u b
  have ha : ∃ i, b i ≠ 0 := by
    by_contra h
    push Not at h
    have hb : b = 0 := funext h
    subst b
    simp at hnorm
  have hvariance :
      ∑ i, biasedSignVarianceTerm (u i) (c i) = 1 := by
    simpa [biasedSignVarianceTerm, u, c] using
      standardizedTiltedRademacherVariance_eq_one
        (fun i => x * b i) b ha
  rw [← standardizedTiltedRademacherPMF_toMeasure_specialize b x,
    ← standardizedTiltedRademacherChar_eq_charFun,
    standardizedTiltedRademacherChar_eq_prod]
  rw [← show
    (∏ i, biasedSignGaussianChar (u i) (c i) t) =
      ((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ) by
    rw [prod_biasedSignGaussianChar_eq, hvariance]
    congr 2
    ring]
  simpa only [u, c] using
    norm_prod_centeredBiasedSignChar_sub_prod_gaussian_le_deletedVariance
      (fun i => x * b i)
      (fun i => b i /
        tiltedRademacherStdDev (fun j => x * b j) b) t

/--
Named-majorant form of the sharp characteristic-function comparison.
-/
theorem norm_charFun_rademacherTiltedStandardizedLaw_sub_gaussian_le_majorant
    (b : ι → ℝ) (x t : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1) :
    ‖charFun (rademacherTiltedStandardizedLaw b x) t -
        ((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ)‖ ≤
      tiltedRademacherGaussianCFMajorant b x t := by
  simpa only [tiltedRademacherGaussianCFMajorant] using
    norm_charFun_rademacherTiltedStandardizedLaw_sub_gaussian_exact_le
      b x t hnorm

/--
The exact sharp characteristic-function envelope inserted into the core
Prawitz discrepancy integrand.

This theorem is the interface between the probability-specific product
estimate and the remaining one-dimensional integration problem.
-/
theorem prawitzCoreDiscrepancyTerm_rademacherTiltedStandardizedLaw_le
    (b : ι → ℝ) (x U₀ U t : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1) :
    prawitzCoreDiscrepancyTerm
        (rademacherTiltedStandardizedLaw b x)
        (gaussianReal 0 1) U₀ U t ≤
      if |t| ≤ U₀ then
        ‖scaledPrawitzKernel U t‖ *
          tiltedRademacherGaussianCFMajorant b x t
      else 0 := by
  unfold prawitzCoreDiscrepancyTerm
  split_ifs with ht
  · apply mul_le_mul_of_nonneg_left
    · rw [charFun_standardGaussian]
      exact
        norm_charFun_rademacherTiltedStandardizedLaw_sub_gaussian_le_majorant
          b x t hnorm
    · exact norm_nonneg _
  · exact le_rfl

/--
All deterministic inputs for deleting an arbitrary Esscher-tilted
coordinate.  In particular, the local analytic theorem may use the moments
of the actually retained coordinates, rather than the larger full-family
sums.
-/
theorem esscherDeletedCoordinateSmallLyapunovInputs
    [DecidableEq ι]
    (b : ι → ℝ) (x : ℝ) (i : ι)
    (hnorm : ∑ j, b j ^ 2 = 1) :
    let L := rademacherLyapunovRatio b x
    let v :=
      standardizedTiltedCoordinateVariance (fun j => x * b j) b i
    let tau :=
      standardizedTiltedVarianceThreeHalvesSumErase
        (fun j => x * b j) b i
    let q :=
      standardizedTiltedVarianceSquareSumErase
        (fun j => x * b j) b i
    v ≤ lyapunovVarianceCap L ∧
      0 ≤ tau ∧ tau ≤ L ∧
      0 ≤ q ∧ q ≤ tau ^ (4 / 3 : ℝ) := by
  dsimp only
  have htauFull :
      standardizedTiltedVarianceThreeHalvesSum
          (fun j => x * b j) b ≤
        rademacherLyapunovRatio b x := by
    rw [← tiltedRademacherThirdMomentSum_standardized_specialize
      b x hnorm]
    exact standardizedTiltedVarianceThreeHalvesSum_le_thirdMomentSum _ _
  have hvariance :
      standardizedTiltedCoordinateVariance (fun j => x * b j) b i ≤
        lyapunovVarianceCap (rademacherLyapunovRatio b x) := by
    have h :=
      standardizedTiltedCoordinateVariance_le_lyapunovVarianceCap
        (fun j => x * b j) b i
    rw [tiltedRademacherThirdMomentSum_standardized_specialize
      b x hnorm] at h
    exact h
  exact ⟨
    hvariance,
    standardizedTiltedVarianceThreeHalvesSumErase_nonneg _ _ _,
    (standardizedTiltedVarianceThreeHalvesSumErase_le
      (fun j => x * b j) b i).trans htauFull,
    standardizedTiltedVarianceSquareSumErase_nonneg _ _ _,
    standardizedTiltedVarianceSquareSumErase_le_threeHalvesSumErase_rpow
      (fun j => x * b j) b i⟩

/--
Shipping wrapper for an Esscher-tilted Rademacher sum: once the local
analytic estimate is proved for the law obtained by deleting coordinate
`i`, all its moment and constant obligations imply the sharp `3/5`
small-Lyapunov bound.
-/
theorem esscher_lt_three_fifths_mul_of_deletedCoordinatePrawitzI52
    [DecidableEq ι]
    (b : ι → ℝ) (x distance : ℝ) (i : ι)
    (hnorm : ∑ j, b j ^ 2 = 1)
    (hL : 0 < rademacherLyapunovRatio b x)
    (hsmall : rademacherLyapunovRatio b x ≤ 1 / 50)
    (hlocal :
      distance ≤ prawitzI52Majorant
        (deletedCoordinateHatEpsilon
          (standardizedTiltedCoordinateVariance
            (fun j => x * b j) b i)
          (rademacherLyapunovRatio b x))
        (deletedCoordinateEpsilonPrime
          (standardizedTiltedCoordinateVariance
            (fun j => x * b j) b i)
          (standardizedTiltedVarianceThreeHalvesSumErase
            (fun j => x * b j) b i))
        (deletedCoordinateEpsilonSecond
          (standardizedTiltedCoordinateVariance
            (fun j => x * b j) b i)
          (standardizedTiltedVarianceSquareSumErase
            (fun j => x * b j) b i))) :
    distance < (3 / 5 : ℝ) * rademacherLyapunovRatio b x := by
  obtain ⟨hv, htau, htauL, hq, hqTau⟩ :=
    esscherDeletedCoordinateSmallLyapunovInputs b x i hnorm
  exact lt_three_fifths_mul_of_le_deletedCoordinatePrawitzI52
    hL hsmall htau htauL hq hqTau hv hlocal

/--
The complete pair of moment comparisons needed by the local Prawitz
estimate, specialized to the Esscher tilt of a normalized Rademacher sum.
-/
theorem esscherSmallLyapunovMomentComparisons
    (b : ι → ℝ) (x : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1)
    (hsmall : rademacherLyapunovRatio b x ≤ 1 / 50) :
    let L := rademacherLyapunovRatio b x
    let tau :=
      standardizedTiltedVarianceThreeHalvesSum
        (fun i => x * b i) b
    let q :=
      standardizedTiltedVarianceSquareSum
        (fun i => x * b i) b
    0 ≤ smallLyapunovEpsilonPrime L tau ∧
      smallLyapunovEpsilonPrime L tau ≤ smallLyapunovHatEpsilon L ∧
      smallLyapunovEpsilonSecond L q ≤
        smallLyapunovEpsilonPrime L tau ^ (4 / 3 : ℝ) := by
  dsimp only
  have hL :
      0 ≤ rademacherLyapunovRatio b x :=
    rademacherLyapunovRatio_nonneg b x
  have htau :
      0 ≤ standardizedTiltedVarianceThreeHalvesSum
        (fun i => x * b i) b :=
    standardizedTiltedVarianceThreeHalvesSum_nonneg _ _
  have htauL :
      standardizedTiltedVarianceThreeHalvesSum
          (fun i => x * b i) b ≤
        rademacherLyapunovRatio b x := by
    rw [← tiltedRademacherThirdMomentSum_standardized_specialize
      b x hnorm]
    exact standardizedTiltedVarianceThreeHalvesSum_le_thirdMomentSum _ _
  have hq :
      standardizedTiltedVarianceSquareSum
          (fun i => x * b i) b ≤
        standardizedTiltedVarianceThreeHalvesSum
            (fun i => x * b i) b ^ (4 / 3 : ℝ) :=
    standardizedTiltedVarianceSquareSum_le_threeHalvesSum_rpow _ _
  exact ⟨
    smallLyapunovEpsilonPrime_nonneg hL hsmall htau,
    smallLyapunovEpsilonPrime_le_hatEpsilon hL hsmall htauL,
    smallLyapunovEpsilonSecond_le_prime_rpow hL hsmall htau hq⟩

end SpecializedMomentPackage

end Probability
end CertifiedJL
