/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Distributions.Rademacher.BiasedSignProduct
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Characteristic functions of tilted Rademacher sums

This file packages the exact characteristic function of a centered,
variance-normalized finite sum of exponentially tilted Rademacher signs.
It is the distribution-specific input to the Prawitz smoothing argument.
-/

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace CertifiedJL
namespace Probability

/-- Characteristic function of `a * (ε - tanh u)` for a sign biased by `u`. -/
noncomputable def centeredBiasedSignChar
    (u a t : ℝ) : ℂ :=
  ∑ e : Bool, (biasedSignWeight u e : ℂ) *
    Complex.exp (((t * a * (biasedSignValue e - Real.tanh u) : ℝ) : ℂ) * Complex.I)

/--
Exact elementary characteristic function of a centered biased sign.

The phase has norm one.  The remaining factor is the uncentered biased-sign
characteristic function and exposes all distribution-specific information.
-/
theorem centeredBiasedSignChar_eq
    (u a t : ℝ) :
    centeredBiasedSignChar u a t =
      Complex.exp (((-(t * a * Real.tanh u) : ℝ) : ℂ) * Complex.I) *
        ((Real.cos (t * a) : ℂ) +
          (Real.tanh u : ℂ) * (Real.sin (t * a) : ℂ) * Complex.I) := by
  rw [show centeredBiasedSignChar u a t =
      (biasedSignNegWeight u : ℂ) *
          Complex.exp (((t * a * (-1 - Real.tanh u) : ℝ) : ℂ) * Complex.I) +
        (biasedSignPosWeight u : ℂ) *
          Complex.exp (((t * a * (1 - Real.tanh u) : ℝ) : ℂ) * Complex.I) by
    simp [centeredBiasedSignChar, biasedSignWeight, biasedSignValue, add_comm]]
  have hneg :
      (((t * a * (-1 - Real.tanh u) : ℝ) : ℂ) * Complex.I) =
        (((-(t * a * Real.tanh u) : ℝ) : ℂ) * Complex.I) +
          (((-(t * a) : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  have hpos :
      (((t * a * (1 - Real.tanh u) : ℝ) : ℂ) * Complex.I) =
        (((-(t * a * Real.tanh u) : ℝ) : ℂ) * Complex.I) +
          ((((t * a) : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hneg, hpos, Complex.exp_add, Complex.exp_add]
  have hcoordNeg :
      Complex.exp (((-(t * a) : ℝ) : ℂ) * Complex.I) =
        (Real.cos (t * a) : ℂ) - (Real.sin (t * a) : ℂ) * Complex.I := by
    rw [Complex.exp_ofReal_mul_I]
    simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
    ring
  have hcoordPos :
      Complex.exp ((((t * a) : ℝ) : ℂ) * Complex.I) =
        (Real.cos (t * a) : ℂ) + (Real.sin (t * a) : ℂ) * Complex.I :=
    Complex.exp_ofReal_mul_I _
  rw [hcoordNeg, hcoordPos]
  unfold biasedSignNegWeight biasedSignPosWeight
  push_cast
  ring

/-- The centering phase in `centeredBiasedSignChar_eq` has norm one. -/
theorem norm_centeredBiasedSignPhase (u a t : ℝ) :
    ‖Complex.exp (((-(t * a * Real.tanh u) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

/-- Exact squared modulus of the centered biased-sign characteristic function. -/
theorem norm_centeredBiasedSignChar_sq
    (u a t : ℝ) :
    ‖centeredBiasedSignChar u a t‖ ^ 2 =
      Real.cos (t * a) ^ 2 +
        Real.tanh u ^ 2 * Real.sin (t * a) ^ 2 := by
  rw [centeredBiasedSignChar_eq, norm_mul, norm_centeredBiasedSignPhase, one_mul]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, mul_zero, Complex.ofReal_im, zero_mul, sub_zero, add_zero,
    Complex.add_im, add_comm, Complex.mul_im, mul_one, zero_add]
  ring

section Product

universe u_1

variable {ι : Type u_1} [Fintype ι]

/-- Total variance of a weighted family of independent biased signs. -/
noncomputable def tiltedRademacherVariance
    (u a : ι → ℝ) : ℝ :=
  ∑ i, a i ^ 2 * (1 - Real.tanh (u i) ^ 2)

/-- The standard deviation used to normalize a tilted Rademacher sum. -/
noncomputable def tiltedRademacherStdDev
    (u a : ι → ℝ) : ℝ :=
  √(tiltedRademacherVariance u a)

/--
The centered finite tilted Rademacher sum divided by its standard deviation.

Lean's real division is total, so this definition also has a value when every
coefficient vanishes.  The Prawitz lane uses it only through
`tiltedRademacherStdDev_pos_of_sum_sq_eq_one`.
-/
noncomputable def standardizedTiltedRademacherSum
    (u a : ι → ℝ) (bits : ι → Bool) : ℝ :=
  ∑ i, (a i / tiltedRademacherStdDev u a) *
    (biasedSignValue (bits i) - Real.tanh (u i))

/-- The PMF of the standardized tilted Rademacher expression. -/
noncomputable def standardizedTiltedRademacherPMF
    (u a : ι → ℝ) : PMF ℝ :=
  (biasedSignProductPMF u).map
    (standardizedTiltedRademacherSum u a)

/--
The finite expectation defining the characteristic function of the
standardized tilted sum.
-/
noncomputable def standardizedTiltedRademacherChar
    (u a : ι → ℝ) (t : ℝ) : ℂ :=
  ∑' bits, ((biasedSignProductPMF u bits).toReal : ℂ) *
    Complex.exp
      (((t * standardizedTiltedRademacherSum u a bits : ℝ) : ℂ) * Complex.I)

omit [Fintype ι] in
/-- Every coordinate contribution to the tilted variance is nonnegative. -/
theorem tiltedRademacherVariance_term_nonneg
    (u a : ι → ℝ) (i : ι) :
    0 ≤ a i ^ 2 * (1 - Real.tanh (u i) ^ 2) :=
  mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (Real.tanh_sq_lt_one _).le)

/-- The variance-normalization denominator is always nonnegative. -/
theorem tiltedRademacherVariance_nonneg
    (u a : ι → ℝ) :
    0 ≤ tiltedRademacherVariance u a := by
  unfold tiltedRademacherVariance
  exact Finset.sum_nonneg fun i _ =>
    tiltedRademacherVariance_term_nonneg u a i

/-- A nonzero coefficient makes the tilted variance strictly positive. -/
theorem tiltedRademacherVariance_pos
    (u a : ι → ℝ) (ha : ∃ i, a i ≠ 0) :
    0 < tiltedRademacherVariance u a := by
  obtain ⟨i, hi⟩ := ha
  unfold tiltedRademacherVariance
  apply Finset.sum_pos'
  · exact fun j _ => tiltedRademacherVariance_term_nonneg u a j
  · refine ⟨i, Finset.mem_univ i, mul_pos ?_ ?_⟩
    · exact sq_pos_of_ne_zero hi
    · exact sub_pos.mpr (Real.tanh_sq_lt_one (u i))

/-- A nonzero coefficient makes the standard deviation strictly positive. -/
theorem tiltedRademacherStdDev_pos
    (u a : ι → ℝ) (ha : ∃ i, a i ≠ 0) :
    0 < tiltedRademacherStdDev u a := by
  exact Real.sqrt_pos.2 (tiltedRademacherVariance_pos u a ha)

/-- A nonzero coefficient makes the normalization denominator nonzero. -/
theorem tiltedRademacherStdDev_ne_zero
    (u a : ι → ℝ) (ha : ∃ i, a i ≠ 0) :
    tiltedRademacherStdDev u a ≠ 0 :=
  ne_of_gt (tiltedRademacherStdDev_pos u a ha)

/-- Unit squared coefficient mass guarantees a positive tilted variance. -/
theorem tiltedRademacherVariance_pos_of_sum_sq_eq_one
    (u a : ι → ℝ) (ha : ∑ i, a i ^ 2 = 1) :
    0 < tiltedRademacherVariance u a := by
  apply tiltedRademacherVariance_pos u a
  by_contra h
  push Not at h
  have hazero : a = 0 := by
    funext i
    exact h i
  subst a
  simp at ha

/-- Unit squared coefficient mass guarantees a positive standard deviation. -/
theorem tiltedRademacherStdDev_pos_of_sum_sq_eq_one
    (u a : ι → ℝ) (ha : ∑ i, a i ^ 2 = 1) :
    0 < tiltedRademacherStdDev u a :=
  Real.sqrt_pos.2
    (tiltedRademacherVariance_pos_of_sum_sq_eq_one u a ha)

/-- Unit squared coefficient mass makes the normalization denominator nonzero. -/
theorem tiltedRademacherStdDev_ne_zero_of_sum_sq_eq_one
    (u a : ι → ℝ) (ha : ∑ i, a i ^ 2 = 1) :
    tiltedRademacherStdDev u a ≠ 0 :=
  ne_of_gt (tiltedRademacherStdDev_pos_of_sum_sq_eq_one u a ha)

/-- Squaring the standard deviation recovers the tilted variance. -/
theorem tiltedRademacherStdDev_sq
    (u a : ι → ℝ) :
    tiltedRademacherStdDev u a ^ 2 =
      tiltedRademacherVariance u a := by
  exact Real.sq_sqrt (tiltedRademacherVariance_nonneg u a)

/--
Dividing every coefficient by the tilted standard deviation makes the sum
of the coordinate variances exactly one.
-/
theorem tiltedRademacherVariance_standardized_eq_one
    (u a : ι → ℝ) (ha : ∃ i, a i ≠ 0) :
    tiltedRademacherVariance u
        (fun i => a i / tiltedRademacherStdDev u a) = 1 := by
  unfold tiltedRademacherVariance
  simp_rw [div_pow]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  rw [tiltedRademacherStdDev_sq]
  exact div_self (ne_of_gt (tiltedRademacherVariance_pos u a ha))

/-- The standardized finite sum is measurable on its finite sample space. -/
theorem measurable_standardizedTiltedRademacherSum
    (u a : ι → ℝ) :
    Measurable (standardizedTiltedRademacherSum u a) :=
  measurable_of_finite _

/-- The standardized finite sum is almost-everywhere measurable. -/
theorem aemeasurable_standardizedTiltedRademacherSum
    (u a : ι → ℝ) :
    AEMeasurable (standardizedTiltedRademacherSum u a)
      (biasedSignProductPMF u).toMeasure :=
  (measurable_standardizedTiltedRademacherSum u a).aemeasurable

/--
The PMF law and the measure-theoretic pushforward law of the standardized
sum agree.
-/
theorem standardizedTiltedRademacherPMF_toMeasure
    (u a : ι → ℝ) :
    (standardizedTiltedRademacherPMF u a).toMeasure =
      (biasedSignProductPMF u).toMeasure.map
        (standardizedTiltedRademacherSum u a) := by
  exact (PMF.toMeasure_map
    (p := biasedSignProductPMF u)
    (f := standardizedTiltedRademacherSum u a)
    (measurable_standardizedTiltedRademacherSum u a)).symm

/--
The explicit finite characteristic-function expectation is the Mathlib
characteristic function of the standardized tilted-sum law.
-/
theorem standardizedTiltedRademacherChar_eq_charFun
    (u a : ι → ℝ) (t : ℝ) :
    standardizedTiltedRademacherChar u a t =
      charFun (standardizedTiltedRademacherPMF u a).toMeasure t := by
  classical
  rw [charFun_apply_real, standardizedTiltedRademacherPMF_toMeasure]
  rw [integral_map_of_stronglyMeasurable
    (measurable_standardizedTiltedRademacherSum u a) (by fun_prop)]
  rw [finitePMF_integral_eq_sum]
  unfold standardizedTiltedRademacherChar
  rw [tsum_fintype]
  simp only [Complex.real_smul]
  apply Finset.sum_congr rfl
  intro bits _
  push_cast
  rfl

/--
The standardized tilted-sum characteristic function factors into its exact
one-coordinate characteristic functions.
-/
theorem standardizedTiltedRademacherChar_eq_prod
    (u a : ι → ℝ) (t : ℝ) :
    standardizedTiltedRademacherChar u a t =
      ∏ i, centeredBiasedSignChar
        (u i) (a i / tiltedRademacherStdDev u a) t := by
  classical
  unfold standardizedTiltedRademacherChar
  rw [tsum_fintype]
  simp_rw [biasedSignProductPMF_toReal_apply]
  have hexp (bits : ι → Bool) :
      Complex.exp
          (((t * standardizedTiltedRademacherSum u a bits : ℝ) : ℂ) *
            Complex.I) =
        ∏ i, Complex.exp
          ((((t * (a i / tiltedRademacherStdDev u a) *
              (biasedSignValue (bits i) - Real.tanh (u i)) : ℝ) : ℂ) *
            Complex.I)) := by
    rw [← Complex.exp_sum]
    congr 1
    unfold standardizedTiltedRademacherSum
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [hexp]
  let f : ι → Bool → ℂ := fun i b =>
    (biasedSignWeight (u i) b : ℂ) *
      Complex.exp
        ((((t * (a i / tiltedRademacherStdDev u a) *
            (biasedSignValue b - Real.tanh (u i)) : ℝ) : ℂ) * Complex.I))
  have hfactor (bits : ι → Bool) :
      ((∏ i, biasedSignWeight (u i) (bits i) : ℝ) : ℂ) *
          ∏ i, Complex.exp
            ((((t * (a i / tiltedRademacherStdDev u a) *
                (biasedSignValue (bits i) - Real.tanh (u i)) : ℝ) : ℂ) *
              Complex.I)) =
        ∏ i, f i (bits i) := by
    dsimp only [f]
    push_cast
    rw [← Finset.prod_mul_distrib]
  simp_rw [hfactor]
  calc
    (∑ bits : ι → Bool, ∏ i, f i (bits i)) =
        ∏ i, ∑ b : Bool, f i b :=
      (Fintype.prod_sum f).symm
    _ = ∏ i, centeredBiasedSignChar
          (u i) (a i / tiltedRademacherStdDev u a) t := by
      apply Finset.prod_congr rfl
      intro i _
      dsimp only [f]
      rfl

/--
The Mathlib characteristic function of the standardized tilted-sum law has
the exact finite-product formula used by the smoothing argument.
-/
theorem charFun_standardizedTiltedRademacherPMF_eq_prod
    (u a : ι → ℝ) (t : ℝ) :
    charFun (standardizedTiltedRademacherPMF u a).toMeasure t =
      ∏ i, centeredBiasedSignChar
        (u i) (a i / tiltedRademacherStdDev u a) t := by
  rw [← standardizedTiltedRademacherChar_eq_charFun]
  exact standardizedTiltedRademacherChar_eq_prod u a t

/-- The standardized tilted-sum characteristic function is measurable. -/
theorem measurable_standardizedTiltedRademacherChar
    (u a : ι → ℝ) :
    Measurable (standardizedTiltedRademacherChar u a) := by
  rw [funext fun t => standardizedTiltedRademacherChar_eq_charFun u a t]
  fun_prop

@[simp]
theorem centeredBiasedSignChar_zero (u a : ℝ) :
    centeredBiasedSignChar u a 0 = 1 := by
  rw [centeredBiasedSignChar_eq]
  simp

@[simp]
theorem standardizedTiltedRademacherChar_zero
    (u a : ι → ℝ) :
    standardizedTiltedRademacherChar u a 0 = 1 := by
  rw [standardizedTiltedRademacherChar_eq_prod]
  simp

theorem charFun_standardizedTiltedRademacherPMF_zero
    (u a : ι → ℝ) :
    charFun (standardizedTiltedRademacherPMF u a).toMeasure 0 = 1 := by
  rw [← standardizedTiltedRademacherChar_eq_charFun]
  exact standardizedTiltedRademacherChar_zero u a

end Product

end Probability
end CertifiedJL
