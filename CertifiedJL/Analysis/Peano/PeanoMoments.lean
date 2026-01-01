/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author.
-/

import CertifiedJL.Analysis.Peano.PeanoIdentity

/-!
# Moment cancellation for the noncompact Peano bridge

This module records the actual degree-zero-through-three moment boundary used
by the noncompact fourth-order P0.  The compact-support identity does not need
these hypotheses; the cutoff consumer does.  In particular, degree one is
represented by genuine `Integrable id` fields rather than by an informal
"centered" premise.
-/

open MeasureTheory

namespace CertifiedJL

/-- Two laws have equal moments through degree `n`, with all required moments
    explicitly Bochner-integrable on both sides. -/
structure EqualMomentsThrough (μ ν : Measure ℝ) (n : ℕ) : Prop where
  integrable_left : ∀ k ≤ n, Integrable (fun y : ℝ => y ^ k) μ
  integrable_right : ∀ k ≤ n, Integrable (fun y : ℝ => y ^ k) ν
  equal : ∀ k ≤ n,
    (∫ y, y ^ k ∂μ) = ∫ y, y ^ k ∂ν

namespace EqualMomentsThrough

lemma integrable_id_left {μ ν : Measure ℝ}
    (hm : EqualMomentsThrough μ ν 3) : Integrable id μ := by
  change Integrable (fun y : ℝ => y) μ
  simpa only [pow_one] using hm.integrable_left 1 (by norm_num)

lemma integrable_id_right {μ ν : Measure ℝ}
    (hm : EqualMomentsThrough μ ν 3) : Integrable id ν := by
  change Integrable (fun y : ℝ => y) ν
  simpa only [pow_one] using hm.integrable_right 1 (by norm_num)

lemma equal_mass {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : EqualMomentsThrough μ ν 3) : μ.real Set.univ = ν.real Set.univ := by
  have h := hm.equal 0 (by norm_num)
  simpa only [pow_zero, integral_const, smul_eq_mul, one_mul, mul_one] using h

lemma equal_first_moment {μ ν : Measure ℝ}
    (hm : EqualMomentsThrough μ ν 3) :
    (∫ y, y ∂μ) = ∫ y, y ∂ν := by
  simpa only [pow_one] using hm.equal 1 (by norm_num)

end EqualMomentsThrough

/-! ## The degree-three Taylor polynomial -/

/-- The Taylor polynomial through degree three, written with real scalar
    multiplication so the later consumer can use `E = ℂ` directly. -/
noncomputable def taylorPolynomial3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (x y : ℝ) : E :=
  (y ^ 0) • f x + (y ^ 1) • deriv f x +
    ((y ^ 2) / 2) • deriv (deriv f) x +
    ((y ^ 3) / 6) • deriv (deriv (deriv f)) x

theorem integrable_taylorPolynomial3_left
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    {μ ν : Measure ℝ} (hm : EqualMomentsThrough μ ν 3)
    (f : ℝ → E) (x : ℝ) :
    Integrable (fun y => taylorPolynomial3 f x y) μ := by
  have h0 := (hm.integrable_left 0 (by norm_num)).smul_const (f x)
  have h1 := (hm.integrable_left 1 (by norm_num)).smul_const (deriv f x)
  have h2 := (hm.integrable_left 2 (by norm_num)).div_const 2 |>.smul_const
    (deriv (deriv f) x)
  have h3 := (hm.integrable_left 3 (by norm_num)).div_const 6 |>.smul_const
    (deriv (deriv (deriv f)) x)
  refine (((h0.add h1).add h2).add h3).congr
    (Filter.Eventually.of_forall (fun y => ?_))
  simp [taylorPolynomial3]

theorem integrable_taylorPolynomial3_right
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    {μ ν : Measure ℝ} (hm : EqualMomentsThrough μ ν 3)
    (f : ℝ → E) (x : ℝ) :
    Integrable (fun y => taylorPolynomial3 f x y) ν := by
  have h0 := (hm.integrable_right 0 (by norm_num)).smul_const (f x)
  have h1 := (hm.integrable_right 1 (by norm_num)).smul_const (deriv f x)
  have h2 := (hm.integrable_right 2 (by norm_num)).div_const 2 |>.smul_const
    (deriv (deriv f) x)
  have h3 := (hm.integrable_right 3 (by norm_num)).div_const 6 |>.smul_const
    (deriv (deriv (deriv f)) x)
  refine (((h0.add h1).add h2).add h3).congr
    (Filter.Eventually.of_forall (fun y => ?_))
  simp [taylorPolynomial3]

theorem equalMomentsThrough_taylorPolynomial3
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    {μ ν : Measure ℝ} (hm : EqualMomentsThrough μ ν 3)
    (f : ℝ → E) (x : ℝ) :
    (∫ y, taylorPolynomial3 f x y ∂μ) =
      ∫ y, taylorPolynomial3 f x y ∂ν := by
  have h0μ : Integrable (fun y : ℝ => y ^ 0) μ :=
    hm.integrable_left 0 (by norm_num)
  have h1μ : Integrable (fun y : ℝ => y ^ 1) μ :=
    hm.integrable_left 1 (by norm_num)
  have h2μ : Integrable (fun y : ℝ => y ^ 2) μ :=
    hm.integrable_left 2 (by norm_num)
  have h3μ : Integrable (fun y : ℝ => y ^ 3) μ :=
    hm.integrable_left 3 (by norm_num)
  have h0ν : Integrable (fun y : ℝ => y ^ 0) ν :=
    hm.integrable_right 0 (by norm_num)
  have h1ν : Integrable (fun y : ℝ => y ^ 1) ν :=
    hm.integrable_right 1 (by norm_num)
  have h2ν : Integrable (fun y : ℝ => y ^ 2) ν :=
    hm.integrable_right 2 (by norm_num)
  have h3ν : Integrable (fun y : ℝ => y ^ 3) ν :=
    hm.integrable_right 3 (by norm_num)
  have h0 :
      (∫ y, (y ^ 0) • f x ∂μ) = ∫ y, (y ^ 0) • f x ∂ν := by
    rw [integral_smul_const, integral_smul_const, hm.equal 0 (by norm_num)]
  have h1 :
      (∫ y, (y ^ 1) • deriv f x ∂μ) =
        ∫ y, (y ^ 1) • deriv f x ∂ν := by
    rw [integral_smul_const, integral_smul_const, hm.equal 1 (by norm_num)]
  have h2 :
      (∫ y, ((y ^ 2) / 2) • deriv (deriv f) x ∂μ) =
        ∫ y, ((y ^ 2) / 2) • deriv (deriv f) x ∂ν := by
    rw [integral_smul_const, integral_smul_const, integral_div, integral_div,
      hm.equal 2 (by norm_num)]
  have h3 :
      (∫ y, ((y ^ 3) / 6) • deriv (deriv (deriv f)) x ∂μ) =
        ∫ y, ((y ^ 3) / 6) • deriv (deriv (deriv f)) x ∂ν := by
    rw [integral_smul_const, integral_smul_const, integral_div, integral_div,
      hm.equal 3 (by norm_num)]
  have hμ0 : Integrable (fun y : ℝ => (y ^ 0) • f x) μ :=
    h0μ.smul_const _
  have hμ1 : Integrable (fun y : ℝ => (y ^ 1) • deriv f x) μ :=
    h1μ.smul_const _
  have hμ2 : Integrable (fun y : ℝ => ((y ^ 2) / 2) • deriv (deriv f) x) μ :=
    (h2μ.div_const 2).smul_const _
  have hμ3 : Integrable
      (fun y : ℝ => ((y ^ 3) / 6) • deriv (deriv (deriv f)) x) μ :=
    (h3μ.div_const 6).smul_const _
  have hν0 : Integrable (fun y : ℝ => (y ^ 0) • f x) ν :=
    h0ν.smul_const _
  have hν1 : Integrable (fun y : ℝ => (y ^ 1) • deriv f x) ν :=
    h1ν.smul_const _
  have hν2 : Integrable (fun y : ℝ => ((y ^ 2) / 2) • deriv (deriv f) x) ν :=
    (h2ν.div_const 2).smul_const _
  have hν3 : Integrable
      (fun y : ℝ => ((y ^ 3) / 6) • deriv (deriv (deriv f)) x) ν :=
    (h3ν.div_const 6).smul_const _
  have hμ01 : Integrable
      (fun y : ℝ => (y ^ 0) • f x + (y ^ 1) • deriv f x) μ :=
    hμ0.add hμ1
  have hν01 : Integrable
      (fun y : ℝ => (y ^ 0) • f x + (y ^ 1) • deriv f x) ν :=
    hν0.add hν1
  have hμ012 : Integrable
      (fun y : ℝ => (y ^ 0) • f x + (y ^ 1) • deriv f x +
        ((y ^ 2) / 2) • deriv (deriv f) x) μ :=
    hμ01.add hμ2
  have hν012 : Integrable
      (fun y : ℝ => (y ^ 0) • f x + (y ^ 1) • deriv f x +
        ((y ^ 2) / 2) • deriv (deriv f) x) ν :=
    hν01.add hν2
  have hμexpand :
      (∫ y, taylorPolynomial3 f x y ∂μ) =
        ((∫ y, (y ^ 0) • f x ∂μ) +
          ∫ y, (y ^ 1) • deriv f x ∂μ) +
          ∫ y, ((y ^ 2) / 2) • deriv (deriv f) x ∂μ +
          ∫ y, ((y ^ 3) / 6) • deriv (deriv (deriv f)) x ∂μ := by
    calc
      (∫ y, taylorPolynomial3 f x y ∂μ) =
          ∫ y, ((y ^ 0) • f x + (y ^ 1) • deriv f x +
            ((y ^ 2) / 2) • deriv (deriv f) x) +
            ((y ^ 3) / 6) • deriv (deriv (deriv f)) x ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun y => rfl)
      _ = (∫ y, (y ^ 0) • f x + (y ^ 1) • deriv f x +
            ((y ^ 2) / 2) • deriv (deriv f) x ∂μ) +
            ∫ y, ((y ^ 3) / 6) • deriv (deriv (deriv f)) x ∂μ :=
        integral_add hμ012 hμ3
      _ = ((∫ y, (y ^ 0) • f x ∂μ) +
            ∫ y, (y ^ 1) • deriv f x ∂μ) +
            ∫ y, ((y ^ 2) / 2) • deriv (deriv f) x ∂μ +
            ∫ y, ((y ^ 3) / 6) • deriv (deriv (deriv f)) x ∂μ := by
        rw [integral_add hμ01 hμ2]
        rw [integral_add hμ0 hμ1]
  have hνexpand :
      (∫ y, taylorPolynomial3 f x y ∂ν) =
        ((∫ y, (y ^ 0) • f x ∂ν) +
          ∫ y, (y ^ 1) • deriv f x ∂ν) +
          ∫ y, ((y ^ 2) / 2) • deriv (deriv f) x ∂ν +
          ∫ y, ((y ^ 3) / 6) • deriv (deriv (deriv f)) x ∂ν := by
    calc
      (∫ y, taylorPolynomial3 f x y ∂ν) =
          ∫ y, ((y ^ 0) • f x + (y ^ 1) • deriv f x +
            ((y ^ 2) / 2) • deriv (deriv f) x) +
            ((y ^ 3) / 6) • deriv (deriv (deriv f)) x ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun y => rfl)
      _ = (∫ y, (y ^ 0) • f x + (y ^ 1) • deriv f x +
            ((y ^ 2) / 2) • deriv (deriv f) x ∂ν) +
            ∫ y, ((y ^ 3) / 6) • deriv (deriv (deriv f)) x ∂ν :=
        integral_add hν012 hν3
      _ = ((∫ y, (y ^ 0) • f x ∂ν) +
            ∫ y, (y ^ 1) • deriv f x ∂ν) +
            ∫ y, ((y ^ 2) / 2) • deriv (deriv f) x ∂ν +
            ∫ y, ((y ^ 3) / 6) • deriv (deriv (deriv f)) x ∂ν := by
        rw [integral_add hν01 hν2]
        rw [integral_add hν0 hν1]
  rw [hμexpand, hνexpand, h0, h1, h2, h3]

end CertifiedJL
