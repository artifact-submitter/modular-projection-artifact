/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.SmoothBounds.HyperbolicProfile

/-!
# Exponentially biased signs

This module records the elementary two-point law obtained by exponentially
tilting a Rademacher sign.  Its parameter is the tilt `u`; the positive and
negative signs have respective weights `(1 + tanh u) / 2` and
`(1 - tanh u) / 2`.

We use a real-valued finite-expectation API.  This is the form consumed by the
analytic one-row argument and avoids coercing elementary finite sums through
extended nonnegative reals.
-/

open scoped BigOperators

namespace CertifiedJL
namespace Probability

/-- The negative-sign weight of the Rademacher law tilted by `u`. -/
noncomputable def biasedSignNegWeight (u : ℝ) : ℝ :=
  (1 - Real.tanh u) / 2

/-- The positive-sign weight of the Rademacher law tilted by `u`. -/
noncomputable def biasedSignPosWeight (u : ℝ) : ℝ :=
  (1 + Real.tanh u) / 2

/-- A Boolean realization of a sign, with `false ↦ -1` and `true ↦ 1`. -/
def biasedSignValue : Bool → ℝ
  | false => -1
  | true => 1

/-- The two weights of the Rademacher law tilted by `u`. -/
noncomputable def biasedSignWeight (u : ℝ) : Bool → ℝ
  | false => biasedSignNegWeight u
  | true => biasedSignPosWeight u

/-- Finite expectation under the Rademacher law tilted by `u`. -/
noncomputable def biasedSignExpectation (u : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ b : Bool, biasedSignWeight u b * f (biasedSignValue b)

theorem biasedSignNegWeight_nonneg (u : ℝ) :
    0 ≤ biasedSignNegWeight u := by
  unfold biasedSignNegWeight
  exact div_nonneg (sub_nonneg.mpr (Real.tanh_lt_one u).le) (by norm_num)

theorem biasedSignPosWeight_nonneg (u : ℝ) :
    0 ≤ biasedSignPosWeight u := by
  unfold biasedSignPosWeight
  exact div_nonneg (by linarith [Real.neg_one_lt_tanh u]) (by norm_num)

@[simp]
theorem biasedSign_weights_sum (u : ℝ) :
    biasedSignNegWeight u + biasedSignPosWeight u = 1 := by
  simp [biasedSignNegWeight, biasedSignPosWeight]
  ring

@[simp]
theorem biasedSignExpectation_apply (u : ℝ) (f : ℝ → ℝ) :
    biasedSignExpectation u f =
      biasedSignNegWeight u * f (-1) +
        biasedSignPosWeight u * f 1 := by
  simp [biasedSignExpectation, biasedSignWeight, biasedSignValue,
    add_comm]

/-- The mean of the tilted sign is `tanh u`. -/
theorem biasedSign_mean (u : ℝ) :
    biasedSignExpectation u id = Real.tanh u := by
  rw [biasedSignExpectation_apply]
  simp only [id_eq]
  unfold biasedSignNegWeight biasedSignPosWeight
  ring

/-- The centered second moment of the tilted sign. -/
theorem biasedSign_centeredVariance (u : ℝ) :
    biasedSignExpectation u
        (fun x => (x - Real.tanh u) ^ 2) =
      1 - Real.tanh u ^ 2 := by
  rw [biasedSignExpectation_apply]
  unfold biasedSignNegWeight biasedSignPosWeight
  ring

/-- The centered variance, in the reciprocal-`cosh` form. -/
theorem biasedSign_centeredVariance_eq_inv_cosh_sq (u : ℝ) :
    biasedSignExpectation u
        (fun x => (x - Real.tanh u) ^ 2) =
      (Real.cosh u)⁻¹ ^ 2 := by
  rw [biasedSign_centeredVariance, one_sub_tanh_sq]

/-- The third absolute centered moment of the tilted sign. -/
theorem biasedSign_thirdAbsoluteCenteredMoment (u : ℝ) :
    biasedSignExpectation u
        (fun x => |x - Real.tanh u| ^ 3) =
      1 - Real.tanh u ^ 4 := by
  rw [biasedSignExpectation_apply]
  have hupper : Real.tanh u ≤ 1 := (Real.tanh_lt_one u).le
  have hlower : -1 ≤ Real.tanh u := (Real.neg_one_lt_tanh u).le
  rw [abs_of_nonpos (by linarith : -1 - Real.tanh u ≤ 0)]
  rw [abs_of_nonneg (by linarith : 0 ≤ 1 - Real.tanh u)]
  unfold biasedSignNegWeight biasedSignPosWeight
  ring

/-- The positive weight in exponential-tilt form. -/
theorem biasedSignPosWeight_eq_exp_div_cosh (u : ℝ) :
    biasedSignPosWeight u =
      Real.exp u / (2 * Real.cosh u) := by
  unfold biasedSignPosWeight
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  rw [Real.cosh_add_sinh]

/-- The negative weight in exponential-tilt form. -/
theorem biasedSignNegWeight_eq_exp_neg_div_cosh (u : ℝ) :
    biasedSignNegWeight u =
      Real.exp (-u) / (2 * Real.cosh u) := by
  unfold biasedSignNegWeight
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  rw [Real.cosh_sub_sinh]

end Probability
end CertifiedJL
