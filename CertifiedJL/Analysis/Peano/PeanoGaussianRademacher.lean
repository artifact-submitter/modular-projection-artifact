/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import CertifiedJL.Analysis.Peano.PeanoCutoffConcrete
import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpIntegrability

/-!
# The concrete Gaussian--Rademacher moment boundary

This module fixes the two laws used by the noncompact fourth-order P0
consumer.  The moment equalities are proved for the explicit standard
Gaussian measure and the explicit two-point Rademacher measure; no centered
or probability-law premise is carried opaquely into the stop-loss bridge.
-/

open MeasureTheory
open ProbabilityTheory

namespace CertifiedJL

/-- Every finite standard-Gaussian power used by the cubic stop-loss bridge is
    Bochner-integrable. -/
theorem integrable_standardGaussian_pow (k : ℕ) :
    Integrable (fun y : ℝ => y ^ k) (gaussianReal 0 1) := by
  simpa only [id_eq] using
    (integrable_pow_of_mem_interior_integrableExpSet
      (X := id) (μ := gaussianReal 0 1) (by simp) k)

/-- Every finite power is integrable under the explicit two-point law. -/
theorem integrable_standardRademacher_pow (k : ℕ) :
    Integrable (fun y : ℝ => y ^ k) standardRademacherMeasure := by
  rw [standardRademacherMeasure]
  apply Integrable.add_measure
  · exact (integrable_dirac
      (f := fun y : ℝ => y ^ k) (a := (-1 : ℝ)) (by simp)).smul_measure
      (by norm_num)
  · exact (integrable_dirac
      (f := fun y : ℝ => y ^ k) (a := (1 : ℝ)) (by simp)).smul_measure
      (by norm_num)

/-- Integrals under the explicit law reduce to its two half-weight atoms. -/
theorem integral_standardRademacher_pow (k : ℕ) :
    (∫ y, y ^ k ∂standardRademacherMeasure) =
      (1 / 2 : ℝ) * (-1 : ℝ) ^ k + (1 / 2 : ℝ) * (1 : ℝ) ^ k := by
  rw [standardRademacherMeasure, integral_add_measure]
  · simp [integral_smul_measure]
  · exact (integrable_dirac
      (f := fun y : ℝ => y ^ k) (a := (-1 : ℝ)) (by simp)).smul_measure
      (by norm_num)
  · exact (integrable_dirac
      (f := fun y : ℝ => y ^ k) (a := (1 : ℝ)) (by simp)).smul_measure
      (by norm_num)

/-- The explicit Rademacher law has total mass one. -/
theorem standardRademacherMeasure_mass :
    standardRademacherMeasure Set.univ = 1 := by
  simp [standardRademacherMeasure, ENNReal.inv_two_add_inv_two]

/-- The explicit Rademacher law is centered. -/
theorem standardRademacherMeasure_first_moment :
    (∫ y, y ∂standardRademacherMeasure) = 0 := by
  have h := integral_standardRademacher_pow 1
  norm_num at h
  exact h

/-- The explicit Rademacher law has second moment one. -/
theorem standardRademacherMeasure_second_moment :
    (∫ y, y ^ 2 ∂standardRademacherMeasure) = 1 := by
  have h := integral_standardRademacher_pow 2
  norm_num at h
  exact h

private theorem integral_standardGaussian_pow_zero :
    (∫ y, y ^ 0 ∂(gaussianReal 0 1)) = (1 : ℝ) := by
  simp

private theorem integral_standardGaussian_pow_one :
    (∫ y, y ^ 1 ∂(gaussianReal 0 1)) = (0 : ℝ) := by
  simpa only [pow_one] using
    (integral_id_gaussianReal (μ := 0) (v := 1))

private theorem integral_standardGaussian_pow_two :
    (∫ y, y ^ 2 ∂(gaussianReal 0 1)) = (1 : ℝ) := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral
      (measurable_id' : Measurable (fun y : ℝ => y)).aemeasurable,
    integral_id_gaussianReal] at h
  simpa using h

private theorem integral_standardGaussian_pow_three :
    (∫ y, y ^ 3 ∂(gaussianReal 0 1)) = (0 : ℝ) := by
  have hpow := integrable_standardGaussian_pow 3
  have hmap :
      (gaussianReal 0 1).map (fun y : ℝ => -y) = gaussianReal 0 1 := by
    simpa using (gaussianReal_map_neg (μ := 0) (v := 1))
  have hpow_map : Integrable (fun y : ℝ => y ^ 3)
      ((gaussianReal 0 1).map (fun y : ℝ => -y)) := by
    rw [hmap]
    exact hpow
  have hsymm :
      (∫ y, y ^ 3 ∂(gaussianReal 0 1)) =
        ∫ y, (-y) ^ 3 ∂(gaussianReal 0 1) := by
    calc
      (∫ y, y ^ 3 ∂(gaussianReal 0 1)) =
          ∫ y, y ^ 3 ∂((gaussianReal 0 1).map (fun y : ℝ => -y)) := by
        rw [hmap]
      _ = ∫ y, (-y) ^ 3 ∂(gaussianReal 0 1) :=
        integral_map (μ := gaussianReal 0 1)
          (φ := fun y : ℝ => -y) (by fun_prop) hpow_map.aestronglyMeasurable
  rw [show (fun y : ℝ => (-y) ^ 3) = fun y => -(y ^ 3) by
      funext y; ring] at hsymm
  rw [integral_neg] at hsymm
  linarith

/-- The explicit standard Gaussian and Rademacher laws agree through degree 3. -/
theorem standardGaussianRademacher_equalMoments :
    EqualMomentsThrough (gaussianReal 0 1) standardRademacherMeasure 3 := by
  constructor
  · intro k hk
    exact integrable_standardGaussian_pow k
  · intro k hk
    exact integrable_standardRademacher_pow k
  · intro k hk
    interval_cases k
    · rw [integral_standardGaussian_pow_zero,
        integral_standardRademacher_pow]
      norm_num
    · rw [integral_standardGaussian_pow_one,
        integral_standardRademacher_pow]
      norm_num
    · rw [integral_standardGaussian_pow_two,
        integral_standardRademacher_pow]
      norm_num
    · rw [integral_standardGaussian_pow_three,
        integral_standardRademacher_pow]
      norm_num

private theorem integrable_cubic_stoploss_of_pows
    {μ : Measure ℝ} {t : ℝ}
    (h0 : Integrable (fun y : ℝ => y ^ 0) μ)
    (h1 : Integrable (fun y : ℝ => y ^ 1) μ)
    (h2 : Integrable (fun y : ℝ => y ^ 2) μ)
    (h3 : Integrable (fun y : ℝ => y ^ 3) μ) :
    Integrable (fun y : ℝ => (max (y - t) 0) ^ 3) μ := by
  have h1abs : Integrable (fun y : ℝ => |y| ^ 1) μ := by
    simpa [Real.norm_eq_abs, abs_pow] using h1.norm
  have h2abs : Integrable (fun y : ℝ => |y| ^ 2) μ := by
    simpa [Real.norm_eq_abs, abs_pow] using h2.norm
  have h3abs : Integrable (fun y : ℝ => |y| ^ 3) μ := by
    simpa [Real.norm_eq_abs, abs_pow] using h3.norm
  have hmajorant : Integrable (fun y : ℝ => (|y| + |t|) ^ 3) μ := by
    have hsum := h3abs.add ((h2abs.const_mul (3 * |t|)).add
      ((h1abs.const_mul (3 * |t| ^ 2)).add
        (h0.const_mul (|t| ^ 3))))
    refine hsum.congr (Filter.Eventually.of_forall (fun y => ?_))
    simp only [Pi.add_apply]
    ring
  refine hmajorant.mono' (by fun_prop) ?_
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_max_right _ _) 3)]
  have hyt : y - t ≤ |y| + |t| := by
    linarith [le_abs_self y, neg_le_abs t]
  have hmax : max (y - t) 0 ≤ |y| + |t| := max_le
    hyt
    (add_nonneg (abs_nonneg y) (abs_nonneg t))
  have hdiff : 0 ≤ (|y| + |t|) - max (y - t) 0 := sub_nonneg.mpr hmax
  have hfactor : 0 ≤ (|y| + |t|) ^ 2 +
      (|y| + |t|) * max (y - t) 0 + (max (y - t) 0) ^ 2 := by
    positivity
  have hprod := mul_nonneg hdiff hfactor
  nlinarith [hprod]

/- The explicit integrability instances used by both one-sided stop-loss
   identities.  Their proofs expand a cubic absolute-value envelope from
   the separately proved degree-0--3 moments. -/
/-- The Gaussian cubic stop-loss is integrable for every real endpoint. -/
theorem integrable_standardGaussian_cubicStopLoss (t : ℝ) :
    Integrable (fun y : ℝ => (max (y - t) 0) ^ 3)
      (gaussianReal 0 1) := by
  exact integrable_cubic_stoploss_of_pows
    (integrable_standardGaussian_pow 0)
    (integrable_standardGaussian_pow 1)
    (integrable_standardGaussian_pow 2)
    (integrable_standardGaussian_pow 3)

/-- The Rademacher cubic stop-loss is integrable for every real endpoint. -/
theorem integrable_standardRademacher_cubicStopLoss (t : ℝ) :
    Integrable (fun y : ℝ => (max (y - t) 0) ^ 3)
      standardRademacherMeasure := by
  exact integrable_cubic_stoploss_of_pows
    (integrable_standardRademacher_pow 0)
    (integrable_standardRademacher_pow 1)
    (integrable_standardRademacher_pow 2)
    (integrable_standardRademacher_pow 3)

/-- The Gaussian-minus-Rademacher cubic stop-loss difference is strongly
measurable as a function of the threshold. -/
theorem stronglyMeasurable_standardGaussianRademacher_cubicStopLossDifference :
    StronglyMeasurable (fun t : ℝ =>
      cubicStopLossDifference (gaussianReal 0 1)
        standardRademacherMeasure t) := by
  have hμ : StronglyMeasurable (fun t : ℝ =>
      ∫ y, (max (y - t) 0) ^ 3 ∂(gaussianReal 0 1)) := by
    have hjoint : StronglyMeasurable (Function.uncurry (fun t y : ℝ =>
        (max (y - t) 0) ^ 3)) := by
      fun_prop
    exact hjoint.integral_prod_right'
  have hν : StronglyMeasurable (fun t : ℝ =>
      ∫ y, (max (y - t) 0) ^ 3 ∂standardRademacherMeasure) := by
    have hjoint : StronglyMeasurable (Function.uncurry (fun t y : ℝ =>
        (max (y - t) 0) ^ 3)) := by
      fun_prop
    exact hjoint.integral_prod_right'
  change StronglyMeasurable (fun t : ℝ =>
    (∫ y, (max (y - t) 0) ^ 3 ∂(gaussianReal 0 1)) -
      ∫ y, (max (y - t) 0) ^ 3 ∂standardRademacherMeasure)
  exact hμ.sub hν

private theorem integral_cubic_stoploss_Ioi
    {μ : Measure ℝ} {t : ℝ} :
    (∫ y, (max (y - t) 0) ^ 3 ∂μ) =
      ∫ y in Set.Ioi t, (y - t) ^ 3 ∂μ := by
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y ∈ Set.Ioi t
  · have hy' : t < y := hy
    simp [hy, max_eq_left (sub_nonneg.mpr hy'.le)]
  · have hy' : y ≤ t := le_of_not_gt hy
    simp [hy, max_eq_right (sub_nonpos.mpr hy')]

private theorem integral_lower_cubic_stoploss_Iio
    {μ : Measure ℝ} {t : ℝ} :
    (∫ y, (max (t - y) 0) ^ 3 ∂μ) =
      ∫ y in Set.Iio t, (t - y) ^ 3 ∂μ := by
  rw [← integral_indicator measurableSet_Iio]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y ∈ Set.Iio t
  · have hy' : y < t := hy
    simp [hy, max_eq_left (sub_nonneg.mpr hy'.le)]
  · have hy' : t ≤ y := le_of_not_gt hy
    simp [hy, max_eq_right (sub_nonpos.mpr hy')]

private theorem cubic_stoploss_decompose (y t : ℝ) :
    (max (y - t) 0) ^ 3 =
      (y - t) ^ 3 + (max (t - y) 0) ^ 3 := by
  by_cases h : t ≤ y
  · rw [max_eq_left (sub_nonneg.mpr h),
      max_eq_right (sub_nonpos.mpr h)]
    ring
  · have h' : y ≤ t := le_of_lt (lt_of_not_ge h)
    rw [max_eq_right (sub_nonpos.mpr h'),
      max_eq_left (sub_nonneg.mpr h')]
    ring

private theorem taylorPolynomial3_cube (t y : ℝ) :
    taylorPolynomial3 (fun z : ℝ => z ^ 3) (-t) y = (y - t) ^ 3 := by
  have hderiv1 : deriv (fun z : ℝ => z ^ 3) =
      (fun z : ℝ => 3 * z ^ 2) := by
    funext z
    convert ((hasDerivAt_id z).pow 3).deriv using 1 <;>
      simp [id_eq]
  have hderiv2 : deriv (fun z : ℝ => 3 * z ^ 2) =
      (fun z : ℝ => 6 * z) := by
    funext z
    convert ((hasDerivAt_const z 3).mul ((hasDerivAt_id z).pow 2)).deriv
        using 1 <;> (simp [id_eq] <;> ring)
  have hderiv3 : deriv (fun z : ℝ => 6 * z) =
      (fun _ : ℝ => 6) := by
    funext z
    convert ((hasDerivAt_const z 6).mul (hasDerivAt_id z)).deriv
        using 1 <;> simp [id_eq]
  have h1val : deriv (fun z : ℝ => z ^ 3) (-t) =
      3 * (-t) ^ 2 := congrFun hderiv1 (-t)
  have h2val : deriv (deriv (fun z : ℝ => z ^ 3)) (-t) =
      6 * (-t) := by
    rw [hderiv1]
    exact congrFun hderiv2 (-t)
  have h3val : deriv (deriv (deriv (fun z : ℝ => z ^ 3))) (-t) =
      6 := by
    rw [hderiv1, hderiv2]
    exact congrFun hderiv3 (-t)
  simp only [taylorPolynomial3]
  rw [h1val, h2val, h3val]
  ring

private theorem integral_shifted_cube_standardGaussian_rademacher_eq (t : ℝ) :
    (∫ y, (y - t) ^ 3 ∂(gaussianReal 0 1)) =
      ∫ y, (y - t) ^ 3 ∂standardRademacherMeasure := by
  have h := equalMomentsThrough_taylorPolynomial3
    (hm := standardGaussianRademacher_equalMoments)
    (f := fun z : ℝ => z ^ 3) (-t)
  simpa only [taylorPolynomial3_cube] using h

private theorem integrable_shifted_cube_standardGaussian_rademacher (t : ℝ) :
    Integrable (fun y => (y - t) ^ 3) (gaussianReal 0 1) ∧
      Integrable (fun y => (y - t) ^ 3) standardRademacherMeasure := by
  constructor
  · have h := integrable_taylorPolynomial3_left
      (hm := standardGaussianRademacher_equalMoments)
      (f := fun z : ℝ => z ^ 3) (-t)
    simpa only [taylorPolynomial3_cube] using h
  · have h := integrable_taylorPolynomial3_right
      (hm := standardGaussianRademacher_equalMoments)
      (f := fun z : ℝ => z ^ 3) (-t)
    simpa only [taylorPolynomial3_cube] using h

/-- The lower-tail cubic stop-loss difference is the strict Gaussian lower
    tail once `t ≤ -1`; the Rademacher lower stop-loss vanishes at its two
    support points and the shifted cubic polynomial cancels through degree 3. -/
theorem cubicStopLossDifference_standardGaussian_rademacher_of_le_neg_one
    {t : ℝ} (ht : t ≤ -1) :
    cubicStopLossDifference (gaussianReal 0 1) standardRademacherMeasure t =
      ∫ y in Set.Iio t, (t - y) ^ 3 ∂(gaussianReal 0 1) := by
  have hGstop := integrable_standardGaussian_cubicStopLoss t
  have hRstop := integrable_standardRademacher_cubicStopLoss t
  have hpoly := integrable_shifted_cube_standardGaussian_rademacher t
  have hGlower : Integrable (fun y => (max (t - y) 0) ^ 3)
      (gaussianReal 0 1) := by
    have h := hGstop.sub hpoly.1
    exact h.congr (Filter.Eventually.of_forall (fun y => by
      change (max (y - t) 0) ^ 3 - (y - t) ^ 3 =
        (max (t - y) 0) ^ 3
      rw [cubic_stoploss_decompose]
      ring))
  have hRlower : Integrable (fun y => (max (t - y) 0) ^ 3)
      standardRademacherMeasure := by
    have h := hRstop.sub hpoly.2
    exact h.congr (Filter.Eventually.of_forall (fun y => by
      change (max (y - t) 0) ^ 3 - (y - t) ^ 3 =
        (max (t - y) 0) ^ 3
      rw [cubic_stoploss_decompose]
      ring))
  have hGdecomp :
      (∫ y, (max (y - t) 0) ^ 3 ∂(gaussianReal 0 1)) =
        (∫ y, (y - t) ^ 3 ∂(gaussianReal 0 1)) +
          ∫ y, (max (t - y) 0) ^ 3 ∂(gaussianReal 0 1) := by
    calc
      (∫ y, (max (y - t) 0) ^ 3 ∂(gaussianReal 0 1)) =
          ∫ y, (y - t) ^ 3 + (max (t - y) 0) ^ 3
            ∂(gaussianReal 0 1) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun y =>
          cubic_stoploss_decompose y t)
      _ = (∫ y, (y - t) ^ 3 ∂(gaussianReal 0 1)) +
          ∫ y, (max (t - y) 0) ^ 3 ∂(gaussianReal 0 1) :=
        integral_add hpoly.1 hGlower
  have hRdecomp :
      (∫ y, (max (y - t) 0) ^ 3 ∂standardRademacherMeasure) =
        (∫ y, (y - t) ^ 3 ∂standardRademacherMeasure) +
          ∫ y, (max (t - y) 0) ^ 3 ∂standardRademacherMeasure := by
    calc
      (∫ y, (max (y - t) 0) ^ 3 ∂standardRademacherMeasure) =
          ∫ y, (y - t) ^ 3 + (max (t - y) 0) ^ 3
            ∂standardRademacherMeasure := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun y =>
          cubic_stoploss_decompose y t)
      _ = (∫ y, (y - t) ^ 3 ∂standardRademacherMeasure) +
          ∫ y, (max (t - y) 0) ^ 3 ∂standardRademacherMeasure :=
        integral_add hpoly.2 hRlower
  have hRlower_zero :
      (∫ y, (max (t - y) 0) ^ 3 ∂standardRademacherMeasure) = 0 := by
    rw [standardRademacherMeasure, integral_add_measure]
    · simp only [integral_smul_measure, integral_dirac]
      rw [max_eq_right (by linarith : t - (-1 : ℝ) ≤ 0),
        max_eq_right (by linarith : t - (1 : ℝ) ≤ 0)]
      norm_num
    · exact (integrable_dirac
        (f := fun y : ℝ => (max (t - y) 0) ^ 3) (a := (-1 : ℝ))
        (by simp)).smul_measure (by norm_num)
    · exact (integrable_dirac
        (f := fun y : ℝ => (max (t - y) 0) ^ 3) (a := (1 : ℝ))
        (by simp)).smul_measure (by norm_num)
  unfold cubicStopLossDifference
  calc
    (∫ y, (max (y - t) 0) ^ 3 ∂(gaussianReal 0 1)) -
        ∫ y, (max (y - t) 0) ^ 3 ∂standardRademacherMeasure =
        ((∫ y, (y - t) ^ 3 ∂(gaussianReal 0 1)) +
          ∫ y, (max (t - y) 0) ^ 3 ∂(gaussianReal 0 1)) -
        ((∫ y, (y - t) ^ 3 ∂standardRademacherMeasure) +
          ∫ y, (max (t - y) 0) ^ 3 ∂standardRademacherMeasure) := by
      rw [hGdecomp, hRdecomp]
    _ = ∫ y, (max (t - y) 0) ^ 3 ∂(gaussianReal 0 1) := by
      rw [integral_shifted_cube_standardGaussian_rademacher_eq,
        hRlower_zero]
      ring
    _ = ∫ y in Set.Iio t, (t - y) ^ 3 ∂(gaussianReal 0 1) :=
      integral_lower_cubic_stoploss_Iio

/-- For `t ≥ 1`, the Gaussian-minus-Rademacher cubic stop-loss is the strict
    Gaussian upper-tail integral. -/
theorem cubicStopLossDifference_standardGaussian_rademacher_of_one_le
    {t : ℝ} (ht : 1 ≤ t) :
    cubicStopLossDifference (gaussianReal 0 1) standardRademacherMeasure t =
      ∫ y in Set.Ioi t, (y - t) ^ 3 ∂(gaussianReal 0 1) := by
  have hGset := integral_cubic_stoploss_Ioi
    (μ := gaussianReal 0 1) (t := t)
  have hRzero :
      (∫ y, (max (y - t) 0) ^ 3 ∂standardRademacherMeasure) = 0 := by
    rw [standardRademacherMeasure, integral_add_measure]
    · simp only [integral_smul_measure, integral_dirac]
      rw [max_eq_right (by linarith : -1 - t ≤ 0),
        max_eq_right (by linarith : 1 - t ≤ 0)]
      norm_num
    · exact (integrable_dirac
        (f := fun y : ℝ => (max (y - t) 0) ^ 3) (a := (-1 : ℝ))
        (by simp)).smul_measure (by norm_num)
    · exact (integrable_dirac
        (f := fun y : ℝ => (max (y - t) 0) ^ 3) (a := (1 : ℝ))
        (by simp)).smul_measure (by norm_num)
  unfold cubicStopLossDifference
  rw [hGset, hRzero]
  ring

/-! ### Global cubic stop-loss kernel

The next theorems join the two strict tail identities at the exact endpoints.
The law orientation remains Gaussian minus Rademacher throughout, matching
`cubicStopLossDifference` and the compact fourth-order Peano identity. -/

/-- The explicit Rademacher cubic stop-loss is the uniform positive-part
    formula for its two half-weight atoms. -/
theorem integral_standardRademacher_cubicStopLoss (t : ℝ) :
    (∫ y, (max (y - t) 0) ^ 3 ∂standardRademacherMeasure) =
      ((max ((1 : ℝ) - t) 0) ^ 3 +
        (max ((-1 : ℝ) - t) 0) ^ 3) / 2 := by
  rw [standardRademacherMeasure, integral_add_measure]
  · simp only [integral_smul_measure, integral_dirac]
    norm_num
    ring
  · exact (integrable_dirac
      (f := fun y : ℝ => (max (y - t) 0) ^ 3) (a := (-1 : ℝ))
      (by simp)).smul_measure (by norm_num)
  · exact (integrable_dirac
      (f := fun y : ℝ => (max (y - t) 0) ^ 3) (a := (1 : ℝ))
      (by simp)).smul_measure (by norm_num)

/-- On the open middle interval, the Rademacher atom at `-1` vanishes and
    the atom at `1` contributes exactly `(1-t)^3/2`. -/
theorem cubicStopLossDifference_standardGaussian_rademacher_of_mem_Ioo
    {t : ℝ} (hleft : -1 < t) (hright : t < 1) :
    cubicStopLossDifference (gaussianReal 0 1) standardRademacherMeasure t =
      (∫ y, (max (y - t) 0) ^ 3 ∂(gaussianReal 0 1)) -
        (1 / 2 : ℝ) * (1 - t) ^ 3 := by
  rw [cubicStopLossDifference, integral_standardRademacher_cubicStopLoss]
  rw [max_eq_left (by linarith : 0 ≤ (1 : ℝ) - t),
    max_eq_right (by linarith : (-1 : ℝ) - t ≤ 0)]
  ring

/-- The Gaussian-minus-Rademacher stop-loss has an exhaustive, disjoint
    three-branch form: `t ≤ -1`, `-1 < t ∧ t < 1`, and `1 ≤ t`. -/
theorem cubicStopLossDifference_standardGaussian_rademacher_piecewise (t : ℝ) :
    cubicStopLossDifference (gaussianReal 0 1) standardRademacherMeasure t =
      if t ≤ -1 then
        ∫ y in Set.Iio t, (t - y) ^ 3 ∂(gaussianReal 0 1)
      else if -1 < t ∧ t < 1 then
        (∫ y, (max (y - t) 0) ^ 3 ∂(gaussianReal 0 1)) -
          (1 / 2 : ℝ) * (1 - t) ^ 3
      else
        ∫ y in Set.Ioi t, (y - t) ^ 3 ∂(gaussianReal 0 1) := by
  by_cases hleft : t ≤ -1
  · rw [if_pos hleft]
    exact cubicStopLossDifference_standardGaussian_rademacher_of_le_neg_one hleft
  · have hleft' : -1 < t := lt_of_not_ge hleft
    by_cases hmid : -1 < t ∧ t < 1
    · rw [if_neg hleft, if_pos hmid]
      exact cubicStopLossDifference_standardGaussian_rademacher_of_mem_Ioo
        hmid.1 hmid.2
    · have hright : 1 ≤ t := by
        by_contra h
        have hlt : t < 1 := lt_of_not_ge h
        exact hmid ⟨hleft', hlt⟩
      rw [if_neg hleft, if_neg hmid]
      exact cubicStopLossDifference_standardGaussian_rademacher_of_one_le hright

/-- The compact-Peano prefactor and the normalized kernel agree pointwise:
    `K=2Δ₃` turns `1/6` into `1/12`. -/
theorem standardGaussianRademacher_cubicStopLossKernel_normalization (t : ℝ) :
    (1 / 12 : ℝ) *
        cubicStopLossKernel (gaussianReal 0 1) standardRademacherMeasure t =
      (1 / 6 : ℝ) *
        cubicStopLossDifference (gaussianReal 0 1) standardRademacherMeasure t := by
  simp only [cubicStopLossKernel]
  ring

/-- The genuinely scaled replacement kernel used by a later Peano consumer.
    The complex scaling parameter is part of the production definition, so
    the fourth power cannot be erased by an external arithmetic canary. -/
noncomputable def cubicStopLossKernelScaled
    (c : ℂ) (μ ν : Measure ℝ) (t : ℝ) : ℂ :=
  c ^ 4 * (cubicStopLossKernel μ ν t : ℂ)

/-- Scaling the k=4 kernel preserves the exact `1/12` versus `1/6` bridge. -/
theorem cubicStopLossKernelScaled_normalization
    (c : ℂ) (t : ℝ) :
    (1 / 12 : ℂ) *
        cubicStopLossKernelScaled c (gaussianReal 0 1)
          standardRademacherMeasure t =
      c ^ 4 * ((1 / 6 : ℝ) : ℂ) *
        (cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t : ℂ) := by
  simp only [cubicStopLossKernelScaled, cubicStopLossKernel,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  norm_num
  ring

/-- Cubic growth is integrable under any real measure whose first four raw
power functions are integrable. -/
theorem integrable_one_add_abs_cubic_of_pows
    {μ : Measure ℝ}
    (h0 : Integrable (fun y : ℝ => y ^ 0) μ)
    (h1 : Integrable (fun y : ℝ => y ^ 1) μ)
    (h2 : Integrable (fun y : ℝ => y ^ 2) μ)
    (h3 : Integrable (fun y : ℝ => y ^ 3) μ) :
    Integrable (fun y : ℝ => (1 + |y|) ^ 3) μ := by
  have h0' : Integrable (fun _ : ℝ => (1 : ℝ)) μ := by
    refine h0.congr (Filter.Eventually.of_forall (fun y => ?_))
    simp
  have h1' : Integrable (fun y : ℝ => |y|) μ := by
    simpa [Real.norm_eq_abs, abs_pow] using h1.norm
  have h2' : Integrable (fun y : ℝ => |y| ^ 2) μ := by
    simpa [Real.norm_eq_abs, abs_pow] using h2.norm
  have h3' : Integrable (fun y : ℝ => |y| ^ 3) μ := by
    simpa [Real.norm_eq_abs, abs_pow] using h3.norm
  have hsum := h0'.add ((h1'.const_mul 3).add
    ((h2'.const_mul 3).add h3'))
  refine hsum.congr (Filter.Eventually.of_forall (fun y => ?_))
  simp only [Pi.add_apply]
  ring

end CertifiedJL
