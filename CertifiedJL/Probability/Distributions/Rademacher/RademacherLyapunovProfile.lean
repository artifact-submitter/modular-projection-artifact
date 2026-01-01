/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Distributions.Rademacher.RademacherVarianceProfile

/-!
# The Rademacher Lyapunov profile

For a normalized coefficient profile `b`, exponential tilting at `x` gives
the variance

`∑ i, b i ^ 2 * cosh (x * b i)⁻¹ ^ 2`

and the sum of third absolute centered moments

`∑ i, |b i| ^ 3 * (1 - tanh (x * b i) ^ 4)`.

This module proves the exact profile estimate `(O5)` used by the sparse
one-row argument.  The public ratio is defined without a nonzero-denominator
hypothesis.  Normalization and the variance-profile inequality `(O4)` imply
that its denominator is in fact strictly positive.
-/

open scoped BigOperators

namespace CertifiedJL
namespace Probability

/-- The total variance of the exponentially tilted weighted signs. -/
noncomputable def rademacherTiltedVariance
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i, b i ^ 2 * (Real.cosh (x * b i))⁻¹ ^ 2

/-- The sum of third absolute centered moments of the tilted summands. -/
noncomputable def rademacherLyapunovNumerator
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i, |b i| ^ 3 * (1 - Real.tanh (x * b i) ^ 4)

/--
The Lyapunov ratio of the exponentially tilted weighted signs.

This is a total real-valued definition.  The denominator is proved positive
for every normalized coefficient profile below.
-/
noncomputable def rademacherLyapunovRatio
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ) : ℝ :=
  rademacherLyapunovNumerator b x /
    (√(rademacherTiltedVariance b x)) ^ 3

/--
Finite Cauchy--Schwarz in the exact form needed for `(O5)`.

If `∑ i, b i² = 1`, then `∑ i, |b i|³ ≤ √(∑ i, b i⁴)`.
-/
theorem sum_abs_cube_le_sqrt_sum_fourth
    {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1) :
    ∑ i, |b i| ^ 3 ≤ √(∑ i, b i ^ 4) := by
  have hcs :=
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun i => |b i|) (fun i => b i ^ 2)
  have habs (i : ι) : |b i| ^ 3 = |b i| * b i ^ 2 := by
    calc
      |b i| ^ 3 = |b i| * |b i| ^ 2 := by ring
      _ = |b i| * b i ^ 2 := by rw [sq_abs]
  calc
    ∑ i, |b i| ^ 3 = ∑ i, |b i| * b i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact habs i
    _ ≤ √(∑ i, |b i| ^ 2) * √(∑ i, (b i ^ 2) ^ 2) := by
      simpa only [Finset.sum_subtype, Finset.mem_univ, ↓reduceIte] using hcs
    _ = √(∑ i, b i ^ 2) * √(∑ i, b i ^ 4) := by
      congr 2
      · apply Finset.sum_congr rfl
        intro i _
        exact sq_abs (b i)
      · apply Finset.sum_congr rfl
        intro i _
        ring
    _ = √(∑ i, b i ^ 4) := by rw [hnorm, Real.sqrt_one, one_mul]

/-- Each tilted third-moment factor is nonnegative. -/
theorem one_sub_tanh_fourth_nonneg (u : ℝ) :
    0 ≤ 1 - Real.tanh u ^ 4 := by
  have hsq : Real.tanh u ^ 2 ≤ 1 :=
    (Real.tanh_sq_lt_one u).le
  nlinarith [sq_nonneg (Real.tanh u ^ 2)]

/-- The tilted third-moment factor is in fact strictly positive. -/
theorem one_sub_tanh_fourth_pos (u : ℝ) :
    0 < 1 - Real.tanh u ^ 4 := by
  have hsq : Real.tanh u ^ 2 < 1 :=
    Real.tanh_sq_lt_one u
  have hsq0 : 0 ≤ Real.tanh u ^ 2 := sq_nonneg _
  nlinarith [sq_nonneg (Real.tanh u ^ 2 - 1)]

/-- The tilted third-moment numerator is nonnegative. -/
theorem rademacherLyapunovNumerator_nonneg
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ) :
    0 ≤ rademacherLyapunovNumerator b x := by
  unfold rademacherLyapunovNumerator
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (by positivity) (one_sub_tanh_fourth_nonneg (x * b i))

/--
Normalization forces at least one nonzero coefficient, hence the tilted
third-moment numerator is strictly positive.
-/
theorem rademacherLyapunovNumerator_pos
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1) :
    0 < rademacherLyapunovNumerator b x := by
  have hexists : ∃ i, b i ≠ 0 := by
    by_contra h
    push Not at h
    have hb : b = 0 := funext h
    subst b
    simp at hnorm
  obtain ⟨i, hi⟩ := hexists
  unfold rademacherLyapunovNumerator
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (by positivity)
      (one_sub_tanh_fourth_nonneg (x * b j))
  · refine ⟨i, Finset.mem_univ i, mul_pos ?_ ?_⟩
    · exact pow_pos (abs_pos.mpr hi) 3
    · exact one_sub_tanh_fourth_pos (x * b i)

/--
Dropping the tilted fourth-power factors bounds the numerator by the
unweighted absolute third moment.
-/
theorem rademacherLyapunovNumerator_le_sum_abs_cube
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ) :
    rademacherLyapunovNumerator b x ≤ ∑ i, |b i| ^ 3 := by
  unfold rademacherLyapunovNumerator
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_of_le_one_right (by positivity)
    (sub_le_self 1 (by positivity : 0 ≤ Real.tanh (x * b i) ^ 4))

/-- The normalized tilted numerator is bounded by the fourth-moment profile. -/
theorem rademacherLyapunovNumerator_le_sqrt_sum_fourth
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1) :
    rademacherLyapunovNumerator b x ≤ √(∑ i, b i ^ 4) :=
  (rademacherLyapunovNumerator_le_sum_abs_cube b x).trans
    (sum_abs_cube_le_sqrt_sum_fourth b hnorm)

/-- `cosh (|x| b)` agrees with `cosh (x b)`. -/
private theorem cosh_abs_mul_left (x y : ℝ) :
    Real.cosh (|x| * y) = Real.cosh (x * y) := by
  rw [← Real.cosh_abs (|x| * y), ← Real.cosh_abs (x * y)]
  simp only [abs_mul, abs_abs]

/--
The variance-profile inequality `(O4)`, with no sign restriction on the
tilt.  The original convexity statement is applied at `|x|`.
-/
theorem inv_cosh_sq_sqrt_sum_fourth_le_tiltedVariance
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1) :
    (Real.cosh (x * √(∑ i, b i ^ 4)))⁻¹ ^ 2 ≤
      rademacherTiltedVariance b x := by
  have h :=
    inv_cosh_sq_sqrt_sum_fourth_le_sum b (abs_nonneg x) hnorm
  unfold rademacherTiltedVariance
  simpa only [cosh_abs_mul_left] using h

/--
The tilted variance is strictly positive for a normalized coefficient
profile.  No separate nonzero-coordinate or nonempty-index assumption is
needed.
-/
theorem rademacherTiltedVariance_pos
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1) :
    0 < rademacherTiltedVariance b x := by
  have hlower :=
    inv_cosh_sq_sqrt_sum_fourth_le_tiltedVariance b x hnorm
  exact lt_of_lt_of_le (sq_pos_of_pos (inv_pos.mpr (Real.cosh_pos _))) hlower

/-- The square-root denominator in the Lyapunov ratio is strictly positive. -/
theorem sqrt_rademacherTiltedVariance_pos
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1) :
    0 < √(rademacherTiltedVariance b x) :=
  Real.sqrt_pos.2 (rademacherTiltedVariance_pos b x hnorm)

/-- The tilted Lyapunov ratio is nonnegative for a normalized profile. -/
theorem rademacherLyapunovRatio_nonneg
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ) :
    0 ≤ rademacherLyapunovRatio b x := by
  unfold rademacherLyapunovRatio
  exact div_nonneg
    (rademacherLyapunovNumerator_nonneg b x)
    (pow_nonneg
      (Real.sqrt_nonneg (rademacherTiltedVariance b x)) 3)

/-- The tilted Lyapunov ratio is strictly positive for a normalized profile. -/
theorem rademacherLyapunovRatio_pos
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1) :
    0 < rademacherLyapunovRatio b x := by
  unfold rademacherLyapunovRatio
  exact div_pos
    (rademacherLyapunovNumerator_pos b x hnorm)
    (pow_pos (sqrt_rademacherTiltedVariance_pos b x hnorm) 3)

/--
The square root of the tilted variance is at least the reciprocal hyperbolic
cosine supplied by `(O4)`.
-/
theorem inv_cosh_sqrt_sum_fourth_le_sqrt_tiltedVariance
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1) :
    (Real.cosh (x * √(∑ i, b i ^ 4)))⁻¹ ≤
      √(rademacherTiltedVariance b x) := by
  have hvar :=
    inv_cosh_sq_sqrt_sum_fourth_le_tiltedVariance b x hnorm
  have hsqrt := Real.sqrt_le_sqrt hvar
  rw [Real.sqrt_sq_eq_abs,
    abs_of_pos (inv_pos.mpr (Real.cosh_pos _))] at hsqrt
  exact hsqrt

/--
The exact Lyapunov-profile estimate `(O5)`.

For every normalized finite coefficient profile and every real tilt,
`L ≤ √ρ cosh³(x√ρ)`, where `ρ = ∑ i, b i⁴`.  The theorem has no
denominator side condition: positivity follows internally from `(O4)`.
-/
theorem rademacherLyapunovRatio_le
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1) :
    rademacherLyapunovRatio b x ≤
      √(∑ i, b i ^ 4) *
        Real.cosh (x * √(∑ i, b i ^ 4)) ^ 3 := by
  let ρ : ℝ := ∑ i, b i ^ 4
  let c : ℝ := Real.cosh (x * √ρ)
  let s : ℝ := √(rademacherTiltedVariance b x)
  have hc : 0 < c := Real.cosh_pos _
  have hs : 0 < s := sqrt_rademacherTiltedVariance_pos b x hnorm
  have hn :
      rademacherLyapunovNumerator b x ≤ √ρ := by
    exact rademacherLyapunovNumerator_le_sqrt_sum_fourth b x hnorm
  have hroot : c⁻¹ ≤ s := by
    exact inv_cosh_sqrt_sum_fourth_le_sqrt_tiltedVariance b x hnorm
  have hcs : 1 ≤ c * s := by
    calc
      1 = c * c⁻¹ := by field_simp
      _ ≤ c * s := mul_le_mul_of_nonneg_left hroot hc.le
  have hcspow : 1 ≤ (c * s) ^ 3 :=
    one_le_pow₀ hcs
  have hρ : 0 ≤ √ρ := Real.sqrt_nonneg ρ
  have hscale : √ρ ≤ √ρ * c ^ 3 * s ^ 3 := by
    calc
      √ρ = √ρ * 1 := by ring
      _ ≤ √ρ * (c * s) ^ 3 :=
        mul_le_mul_of_nonneg_left hcspow hρ
      _ = √ρ * c ^ 3 * s ^ 3 := by ring
  unfold rademacherLyapunovRatio
  change rademacherLyapunovNumerator b x / s ^ 3 ≤ √ρ * c ^ 3
  rw [div_le_iff₀ (pow_pos hs 3)]
  exact hn.trans hscale

end Probability
end CertifiedJL
