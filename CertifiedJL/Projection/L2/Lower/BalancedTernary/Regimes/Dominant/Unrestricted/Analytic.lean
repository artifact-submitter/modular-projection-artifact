/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Unrestricted.Scalar
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Unrestricted.Cell
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Shared.Scalar.LobeTail
import CertifiedJL.Model.Distributions.BalancedTernary.Duplication
import CertifiedJL.Probability.Distributions.Rademacher.BiasedSignProduct

set_option linter.style.longFile 2000

/-!
# Analytic dominant-row bounds

This module proves the coefficient-uniform inactive row bound, the exact
shifted-active estimate, and its literal shifted periodization through the
canonical active scalar cell bound. The public-threshold layer transports
these scalar bounds to its conditioned row distributions. The module contains no
certificate data or
checker assumptions.
-/

open scoped BigOperators ENNReal

open MeasureTheory

namespace CertifiedJL

open Probability

private theorem integral_comp_eq_of_pmf_map_eq_early
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ]
    (p : PMF α) (q : PMF β) (X : α → γ) (Y : β → γ) (f : γ → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hf : Measurable f)
    (hmap : p.map X = q.map Y) :
    ∫ x, f (X x) ∂p.toMeasure = ∫ y, f (Y y) ∂q.toMeasure := by
  calc
    ∫ x, f (X x) ∂p.toMeasure =
        ∫ z, f z ∂Measure.map X p.toMeasure := by
      exact (integral_map hX.aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ z, f z ∂(p.map X).toMeasure := by
      rw [PMF.toMeasure_map X p hX]
    _ = ∫ z, f z ∂(q.map Y).toMeasure := by rw [hmap]
    _ = ∫ z, f z ∂Measure.map Y q.toMeasure := by
      rw [PMF.toMeasure_map Y q hY]
    _ = ∫ y, f (Y y) ∂q.toMeasure := by
      exact integral_map hY.aemeasurable hf.aestronglyMeasurable

private theorem abs_tanh_le_abs (x : ℝ) : |Real.tanh x| ≤ |x| := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, abs_of_nonneg (tanh_nonneg hx)]
    exact tanh_le_self hx
  · have hnx : 0 ≤ -x := neg_nonneg.mpr hx
    have ht := tanh_le_self hnx
    rw [Real.tanh_neg] at ht
    have htx : Real.tanh x ≤ 0 := by
      rw [← neg_nonneg, ← Real.tanh_neg]
      exact tanh_nonneg hnx
    rw [abs_of_nonpos hx, abs_of_nonpos htx]
    linarith

private theorem mul_tanh_nonneg (x : ℝ) : 0 ≤ x * Real.tanh x := by
  rcases le_total 0 x with hx | hx
  · exact mul_nonneg hx (tanh_nonneg hx)
  · have hnx : 0 ≤ -x := neg_nonneg.mpr hx
    have ht : Real.tanh x ≤ 0 := by
      rw [← neg_nonneg, ← Real.tanh_neg]
      exact tanh_nonneg hnx
    exact mul_nonneg_of_nonpos_of_nonpos hx ht

private theorem exp_neg_le_one_sub_add_sq_half {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have hq : 0 < 1 + x + x ^ 2 / 2 := by positivity
  have hexp := Real.quadratic_le_exp_of_nonneg hx
  rw [Real.exp_neg]
  have hinv : (Real.exp x)⁻¹ ≤ (1 + x + x ^ 2 / 2)⁻¹ :=
    inv_anti₀ hq hexp
  calc
    (Real.exp x)⁻¹ ≤ (1 + x + x ^ 2 / 2)⁻¹ := hinv
    _ ≤ 1 - x + x ^ 2 / 2 := by
      rw [inv_le_iff_one_le_mul₀' hq]
      nlinarith [sq_nonneg (x ^ 2)]

private theorem add_fourth_le_eight (x y : ℝ) :
    (x + y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
  have htwo : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg (x - y)]
  have hsq := pow_le_pow_left₀ (sq_nonneg (x + y)) htwo 2
  calc
    (x + y) ^ 4 = ((x + y) ^ 2) ^ 2 := by ring
    _ ≤ (2 * (x ^ 2 + y ^ 2)) ^ 2 := hsq
    _ ≤ 8 * (x ^ 4 + y ^ 4) := by
      nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]

/-- Cubic control of the error in the tangent approximation to `tanh`. -/
private theorem self_sub_tanh_le_cube_third {x : ℝ} (hx : 0 ≤ x) :
    x - Real.tanh x ≤ x ^ 3 / 3 := by
  have hf : Differentiable ℝ
      (fun y : ℝ => y ^ 3 / 3 - y + Real.tanh y) := by
    exact (((differentiable_id.pow 3).div_const 3).sub
      differentiable_id).add differentiable_tanh
  have hderiv : ∀ y, 0 ≤ deriv
      (fun t : ℝ => t ^ 3 / 3 - t + Real.tanh t) y := by
    intro y
    have hpow : HasDerivAt (fun x : ℝ => x ^ 3 / 3) (3 * y ^ 2 / 3) y := by
      simpa only [Nat.cast_ofNat, Nat.reduceSub, one_mul] using
        (hasDerivAt_pow 3 y).div_const (3 : ℝ)
    have hsub : HasDerivAt (fun x : ℝ => x ^ 3 / 3 - x)
        (3 * y ^ 2 / 3 - 1) y :=
      hpow.fun_sub (hasDerivAt_id y)
    have hraw := hsub.fun_add (hasDerivAt_tanh y)
    rw [hraw.deriv, ← one_sub_tanh_sq]
    have habs := abs_tanh_le_abs y
    have hsq : Real.tanh y ^ 2 ≤ y ^ 2 := by
      have hpow := pow_le_pow_left₀ (abs_nonneg _) habs 2
      simpa [sq_abs] using hpow
    linarith
  have hmono : Monotone (fun y : ℝ => y ^ 3 / 3 - y + Real.tanh y) :=
    monotone_of_deriv_nonneg hf hderiv
  have := hmono hx
  norm_num at this
  linarith

private theorem abs_tanh_sub_self_le_cube_third (x : ℝ) :
    |Real.tanh x - x| ≤ |x| ^ 3 / 3 := by
  rcases le_total 0 x with hx | hx
  · have ht := tanh_le_self hx
    have hc := self_sub_tanh_le_cube_third hx
    rw [abs_of_nonneg hx, abs_of_nonpos (by linarith : Real.tanh x - x ≤ 0)]
    linarith
  · have hnx : 0 ≤ -x := neg_nonneg.mpr hx
    have hc := self_sub_tanh_le_cube_third hnx
    rw [Real.tanh_neg] at hc
    have ht : 0 ≤ Real.tanh x - x := by
      have := tanh_le_self hnx
      rw [Real.tanh_neg] at this
      linarith
    rw [abs_of_nonpos hx, abs_of_nonneg ht]
    nlinarith

/-- Weighted fourth-power Young inequality tuned to a one-fifth shift. -/
private theorem add_fourth_le_weighted (x y : ℝ) :
    (x + y) ^ 4 ≤ (216 / 125 : ℝ) * x ^ 4 + 216 * y ^ 4 := by
  have hquad : 0 ≤ 91 * x ^ 2 + 410 * x * y + 1075 * y ^ 2 := by
    nlinarith [sq_nonneg (182 * x + 410 * y), sq_nonneg y]
  have hprod : 0 ≤ (5 * y - x) ^ 2 *
      (91 * x ^ 2 + 410 * x * y + 1075 * y ^ 2) :=
    mul_nonneg (sq_nonneg _) hquad
  nlinarith [hprod]

/-- Fourth moment about the Gaussian Esscher center, retaining the cubic
`tanh` cancellation.  This is the sharpened active-row primitive needed at
the `49/50` threshold endpoint. -/
theorem biasedSignProduct_shiftedWeightedFourthMoment_le
    {ι : Type*} [Fintype ι] (coeff : ι → ℝ) (u lam : ℝ)
    (hu : 0 < u)
    (hmass : ∑ i, coeff i ^ 2 = u / 2)
    (hcoeff : ∀ i, 2 * |coeff i| ≤ Real.sqrt u) :
    ∫ bits, (rademacherSum coeff bits - lam * u / 2) ^ 4
        ∂(biasedSignProductPMF (fun i => lam * coeff i)).toMeasure ≤
      (216 / 125 : ℝ) * (3 * u ^ 2 / 4) +
        216 * (|lam| ^ 3 * u ^ 2 / 24) ^ 4 := by
  classical
  let tilt : ι → ℝ := fun i => lam * coeff i
  let X : (ι → Bool) → ℝ := rademacherSum coeff
  let mean : ℝ := ∑ i, coeff i * Real.tanh (tilt i)
  let Z : (ι → Bool) → ℝ := fun bits =>
    ∑ i, coeff i *
      (biasedSignValue (bits i) - Real.tanh (tilt i))
  let delta : ℝ := mean - lam * u / 2
  let mu : Measure (ι → Bool) := (biasedSignProductPMF tilt).toMeasure
  have hX_Z (bits : ι → Bool) : X bits = Z bits + mean := by
    dsimp [X, Z, mean, rademacherSum]
    simp_rw [biasedSignValue_eq_signBit]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hfourthZ : ∫ bits, Z bits ^ 4 ∂mu ≤ 3 * u ^ 2 / 4 := by
    have hfourth := biasedSignProduct_centeredWeightedFourthMoment_le
      tilt coeff Finset.univ
    change (∫ bits, Z bits ^ 4 ∂mu) ≤ _
    calc
      ∫ bits, Z bits ^ 4 ∂mu ≤ 3 * (∑ i, coeff i ^ 2) ^ 2 := by
        simpa [Z, mu] using hfourth
      _ = 3 * u ^ 2 / 4 := by rw [hmass]; ring
  have hdelta_sum : delta = ∑ i,
      coeff i * (Real.tanh (lam * coeff i) - lam * coeff i) := by
    dsimp [delta, mean, tilt]
    rw [show lam * u / 2 = lam * (∑ i, coeff i ^ 2) by rw [hmass]; ring]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hdelta_abs : |delta| ≤ |lam| ^ 3 * u ^ 2 / 24 := by
    rw [hdelta_sum]
    calc
      |∑ i, coeff i *
          (Real.tanh (lam * coeff i) - lam * coeff i)| ≤
          ∑ i, |coeff i *
            (Real.tanh (lam * coeff i) - lam * coeff i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |lam| ^ 3 * |coeff i| ^ 4 / 3 := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        have ht := abs_tanh_sub_self_le_cube_third (lam * coeff i)
        have hc : 0 ≤ |coeff i| := abs_nonneg _
        have hmul := mul_le_mul_of_nonneg_left ht hc
        calc
          |coeff i| * |Real.tanh (lam * coeff i) - lam * coeff i| ≤
              |coeff i| * (|lam * coeff i| ^ 3 / 3) := hmul
          _ = |lam| ^ 3 * |coeff i| ^ 4 / 3 := by
            rw [abs_mul]
            ring
      _ = |lam| ^ 3 / 3 * ∑ i, |coeff i| ^ 4 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ |lam| ^ 3 / 3 * (u ^ 2 / 8) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hsum : ∑ i, |coeff i| ^ 4 ≤ u / 4 * ∑ i, coeff i ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i hi
          have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * |coeff i|)
            (hcoeff i) 2
          have hci : |coeff i| ^ 2 ≤ u / 4 := by
            rw [show Real.sqrt u ^ 2 = u by exact Real.sq_sqrt hu.le] at hsquare
            nlinarith
          have hmul := mul_le_mul_of_nonneg_right hci (sq_nonneg (coeff i))
          calc
            |coeff i| ^ 4 = |coeff i| ^ 2 * coeff i ^ 2 := by
              rw [show |coeff i| ^ 4 = |coeff i| ^ 2 * |coeff i| ^ 2 by ring,
                sq_abs]
            _ ≤ u / 4 * coeff i ^ 2 := hmul
        rw [hmass] at hsum
        nlinarith
      _ = |lam| ^ 3 * u ^ 2 / 24 := by ring
  have hdelta_fourth : delta ^ 4 ≤ (|lam| ^ 3 * u ^ 2 / 24) ^ 4 := by
    have habs_pow := pow_le_pow_left₀ (abs_nonneg delta) hdelta_abs 4
    calc
      delta ^ 4 = |delta| ^ 4 := by
        calc
          delta ^ 4 = |delta ^ 4| := (abs_of_nonneg (by positivity)).symm
          _ = |delta| ^ 4 := abs_pow delta 4
      _ ≤ (|lam| ^ 3 * u ^ 2 / 24) ^ 4 := habs_pow
  have hpoint (bits : ι → Bool) :
      (X bits - lam * u / 2) ^ 4 ≤
        (216 / 125 : ℝ) * Z bits ^ 4 + 216 * delta ^ 4 := by
    rw [hX_Z]
    have hcenter : Z bits + mean - lam * u / 2 = Z bits + delta := by
      dsimp [delta]
      ring
    rw [hcenter]
    exact add_fourth_le_weighted (Z bits) delta
  change (∫ bits, (X bits - lam * u / 2) ^ 4 ∂mu) ≤ _
  calc
    ∫ bits, (X bits - lam * u / 2) ^ 4 ∂mu ≤
        ∫ bits, ((216 / 125 : ℝ) * Z bits ^ 4 +
          216 * delta ^ 4) ∂mu := by
      exact integral_mono_ae Integrable.of_finite Integrable.of_finite
        (Filter.Eventually.of_forall hpoint)
    _ = (216 / 125 : ℝ) * (∫ bits, Z bits ^ 4 ∂mu) +
        216 * delta ^ 4 := by
      rw [integral_add Integrable.of_finite Integrable.of_finite,
        integral_const_mul]
      simp
    _ ≤ (216 / 125 : ℝ) * (3 * u ^ 2 / 4) +
        216 * (|lam| ^ 3 * u ^ 2 / 24) ^ 4 := by
      gcongr

/--
The paper's shifted dominant-row estimate for a doubled-sign remainder
profile.  The squared coefficient mass is `u/2`, so the Rademacher sum has the
same variance as a sparse remainder of normalized squared mass `u`.
-/
theorem shiftedDominantRow
    {ι : Type*} [Fintype ι] (coeff : ι → ℝ) (u z : ℝ)
    (hu : 0 < u) (hz : 0 < z)
    (hmass : ∑ i, coeff i ^ 2 = u / 2)
    (hcoeff : ∀ i, 2 * |coeff i| ≤ Real.sqrt u) :
    let s := z * u
    let h := z * Real.sqrt u / (1 + s)
    ∫ bits, Real.exp
        (-z * (1 + rademacherSum coeff bits) ^ 2)
      ∂(rademacherPMF ι).toMeasure ≤
      Real.exp (-z / (1 + s)) *
        min 1
          (1 - s / 2 * (Real.cosh h)⁻¹ ^ 2 +
            3 * s ^ 2 + 4 * s ^ 2 * h ^ 4) := by
  classical
  dsimp only
  let s : ℝ := z * u
  let lam : ℝ := -2 * z / (1 + s)
  let r0 : ℝ := -s / (1 + s)
  let h : ℝ := z * Real.sqrt u / (1 + s)
  let tilt : ι → ℝ := fun i => lam * coeff i
  let X : (ι → Bool) → ℝ := rademacherSum coeff
  let mean : ℝ := ∑ i, coeff i * Real.tanh (tilt i)
  let Z : (ι → Bool) → ℝ := fun bits =>
    ∑ i, coeff i *
      (biasedSignValue (bits i) - Real.tanh (tilt i))
  let μ : Measure (ι → Bool) := (biasedSignProductPMF tilt).toMeasure
  change (∫ bits, Real.exp (-z * (1 + X bits) ^ 2)
      ∂(rademacherPMF ι).toMeasure) ≤
    Real.exp (-z / (1 + s)) *
      min 1 (1 - s / 2 * (Real.cosh h)⁻¹ ^ 2 +
        3 * s ^ 2 + 4 * s ^ 2 * h ^ 4)
  have hs : 0 < s := by dsimp [s]; positivity
  have hden : 0 < 1 + s := by linarith
  have hlam : lam < 0 := by
    dsimp [lam]
    exact div_neg_of_neg_of_pos (by linarith) hden
  have hsqrt : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu.le
  have hh_nonneg : 0 ≤ h := by dsimp [h]; positivity
  have htilt : tilt = fun i => lam * coeff i := rfl
  have hX_Z (bits : ι → Bool) : X bits = Z bits + mean := by
    dsimp [X, Z, mean, rademacherSum]
    simp_rw [biasedSignValue_eq_signBit]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hmean_integral : ∫ bits, Z bits ∂μ = 0 := by
    dsimp [Z, μ, tilt]
    rw [← biasedSignProductExpectation_eq_integral]
    rw [show biasedSignProductExpectation (fun i => lam * coeff i)
        (fun bits => ∑ i, coeff i *
          (biasedSignValue (bits i) - Real.tanh (lam * coeff i))) =
        ∑ i, biasedSignProductExpectation (fun j => lam * coeff j)
          (fun bits => coeff i *
            (biasedSignValue (bits i) - Real.tanh (lam * coeff i))) by
      unfold biasedSignProductExpectation
      simp only [tsum_fintype]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro bits hbits
      rw [Finset.mul_sum]]
    simp only [biasedSignProduct_centeredWeightedMean,
      Finset.sum_const_zero]
  have hmean_nonpos : mean ≤ 0 := by
    dsimp [mean, tilt]
    apply Finset.sum_nonpos
    intro i hi
    have hprod := mul_tanh_nonneg (lam * coeff i)
    have hlam_neg := hlam
    nlinarith
  have hmean_abs : |mean| ≤ -r0 := by
    calc
      |mean| = |∑ i, coeff i * Real.tanh (tilt i)| := rfl
      _ ≤ ∑ i, |coeff i * Real.tanh (tilt i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |lam| * coeff i ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        calc
          |coeff i| * |Real.tanh (tilt i)| ≤
              |coeff i| * |tilt i| :=
            mul_le_mul_of_nonneg_left (abs_tanh_le_abs _) (abs_nonneg _)
          _ = |lam| * coeff i ^ 2 := by
            dsimp [tilt]
            rw [abs_mul]
            rw [← sq_abs]
            ring
      _ = |lam| * (u / 2) := by rw [← Finset.mul_sum, hmass]
      _ = -r0 := by
        rw [abs_of_nonpos hlam.le]
        dsimp [lam, r0, s]
        field_simp [hden.ne']
  have hr0_nonpos : r0 ≤ 0 := by
    dsimp [r0]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) hden.le
  have hr0_le_mean : r0 ≤ mean := by
    have hmean_abs' := hmean_abs
    rw [abs_of_nonpos hmean_nonpos] at hmean_abs'
    linarith
  have hdist_nonneg : 0 ≤ mean - r0 := sub_nonneg.mpr hr0_le_mean
  have hdist : mean - r0 ≤ Real.sqrt u * h := by
    have hroot : Real.sqrt u * h = -r0 := by
      dsimp [h, r0, s]
      field_simp [hden.ne']
      rw [hsqrt]
    rw [hroot]
    linarith
  have harg (i : ι) : |tilt i| ≤ h := by
    calc
      |tilt i| = 2 * z * |coeff i| / (1 + s) := by
        dsimp [tilt, lam]
        rw [abs_mul, abs_div, abs_mul, abs_of_pos hz, abs_of_pos hden]
        norm_num
        ring
      _ ≤ z * Real.sqrt u / (1 + s) := by
        apply (div_le_div_iff₀ hden hden).2
        have := mul_le_mul_of_nonneg_left (hcoeff i) hz.le
        nlinarith
      _ = h := by rfl
  have hvariance :
      u / 2 * (Real.cosh h)⁻¹ ^ 2 ≤ ∫ bits, Z bits ^ 2 ∂μ := by
    have hexact := biasedSignProduct_centeredWeightedSumVariance tilt coeff
    change (∫ bits, Z bits ^ 2 ∂μ) =
      ∑ i, coeff i ^ 2 * (1 - Real.tanh (tilt i) ^ 2) at hexact
    rw [hexact]
    calc
      u / 2 * (Real.cosh h)⁻¹ ^ 2 =
          ∑ i, coeff i ^ 2 * (Real.cosh h)⁻¹ ^ 2 := by
        rw [← Finset.sum_mul, hmass]
      _ ≤ ∑ i, coeff i ^ 2 * (1 - Real.tanh (tilt i) ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        rw [one_sub_tanh_sq]
        have hcosh : Real.cosh (tilt i) ≤ Real.cosh h :=
          Real.cosh_le_cosh.mpr (by simpa [abs_of_nonneg hh_nonneg] using harg i)
        have hinv : (Real.cosh h)⁻¹ ≤ (Real.cosh (tilt i))⁻¹ :=
          inv_anti₀ (Real.cosh_pos _) hcosh
        exact pow_le_pow_left₀ (by positivity) hinv 2
  have hfourthZ : ∫ bits, Z bits ^ 4 ∂μ ≤ 3 * u ^ 2 / 4 := by
    have hfourth := biasedSignProduct_centeredWeightedFourthMoment_le
      tilt coeff Finset.univ
    change (∫ bits, Z bits ^ 4 ∂μ) ≤ _
    calc
      ∫ bits, Z bits ^ 4 ∂μ ≤
          3 * (∑ i, coeff i ^ 2) ^ 2 := by simpa [Z, μ] using hfourth
      _ = 3 * u ^ 2 / 4 := by rw [hmass]; ring
  have hfourthY :
      ∫ bits, (X bits - r0) ^ 4 ∂μ ≤
        (6 + 8 * h ^ 4) * u ^ 2 := by
    have hpoint (bits : ι → Bool) :
        (X bits - r0) ^ 4 ≤
          8 * (Z bits ^ 4 + (mean - r0) ^ 4) := by
      rw [hX_Z]
      convert add_fourth_le_eight (Z bits) (mean - r0) using 1
      all_goals ring
    calc
      ∫ bits, (X bits - r0) ^ 4 ∂μ ≤
          ∫ bits, 8 * (Z bits ^ 4 + (mean - r0) ^ 4) ∂μ := by
        exact integral_mono_ae Integrable.of_finite Integrable.of_finite
          (Filter.Eventually.of_forall hpoint)
      _ = 8 * (∫ bits, Z bits ^ 4 ∂μ + (mean - r0) ^ 4) := by
        rw [integral_const_mul]
        rw [integral_add Integrable.of_finite Integrable.of_finite]
        simp
      _ ≤ 8 * (3 * u ^ 2 / 4 + (Real.sqrt u * h) ^ 4) := by
        gcongr
      _ = (6 + 8 * h ^ 4) * u ^ 2 := by
        rw [mul_pow, show Real.sqrt u ^ 4 = u ^ 2 by
          calc Real.sqrt u ^ 4 = (Real.sqrt u ^ 2) ^ 2 := by ring
          _ = u ^ 2 := by rw [hsqrt]]
        ring
  have hsecondY :
      u / 2 * (Real.cosh h)⁻¹ ^ 2 ≤
        ∫ bits, (X bits - r0) ^ 2 ∂μ := by
    calc
      u / 2 * (Real.cosh h)⁻¹ ^ 2 ≤ ∫ bits, Z bits ^ 2 ∂μ := hvariance
      _ ≤ ∫ bits, (X bits - r0) ^ 2 ∂μ := by
        have heq :
            ∫ bits, (X bits - r0) ^ 2 ∂μ =
              ∫ bits, Z bits ^ 2 ∂μ + (mean - r0) ^ 2 := by
          rw [show (fun bits => (X bits - r0) ^ 2) =
              fun bits => Z bits ^ 2 +
                2 * (mean - r0) * Z bits + (mean - r0) ^ 2 by
            funext bits
            rw [hX_Z]
            ring]
          rw [integral_add Integrable.of_finite Integrable.of_finite,
            integral_add Integrable.of_finite Integrable.of_finite,
            integral_const_mul, hmean_integral]
          simp
        rw [heq]
        exact le_add_of_nonneg_right (sq_nonneg _)
  let B : ℝ := ∫ bits, Real.exp (-z * (X bits - r0) ^ 2) ∂μ
  let rho : ℝ :=
    1 - s / 2 * (Real.cosh h)⁻¹ ^ 2 +
      3 * s ^ 2 + 4 * s ^ 2 * h ^ 4
  have hB_nonneg : 0 ≤ B := by dsimp [B]; positivity
  have hB_one : B ≤ 1 := by
    dsimp [B]
    calc
      ∫ bits, Real.exp (-z * (X bits - r0) ^ 2) ∂μ ≤
          ∫ _bits, (1 : ℝ) ∂μ := by
        exact integral_mono_ae Integrable.of_finite Integrable.of_finite
          (Filter.Eventually.of_forall fun bits =>
            Real.exp_le_one_iff.mpr
              (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz.le)
                (sq_nonneg _)))
      _ = 1 := by simp
  have hB_rho : B ≤ rho := by
    have hpoint (bits : ι → Bool) :
        Real.exp (-z * (X bits - r0) ^ 2) ≤
          1 - z * (X bits - r0) ^ 2 +
            z ^ 2 * (X bits - r0) ^ 4 / 2 := by
      convert exp_neg_le_one_sub_add_sq_half
        (mul_nonneg hz.le (sq_nonneg (X bits - r0))) using 1 <;> ring
    have hint :
        B ≤ 1 - z * (∫ bits, (X bits - r0) ^ 2 ∂μ) +
          z ^ 2 / 2 * (∫ bits, (X bits - r0) ^ 4 ∂μ) := by
      dsimp [B]
      calc
        _ ≤ ∫ bits, (1 - z * (X bits - r0) ^ 2 +
              z ^ 2 * (X bits - r0) ^ 4 / 2) ∂μ := by
          exact integral_mono_ae Integrable.of_finite Integrable.of_finite
            (Filter.Eventually.of_forall hpoint)
        _ = _ := by
          rw [integral_add Integrable.of_finite Integrable.of_finite,
            integral_sub Integrable.of_finite Integrable.of_finite,
            integral_const, probReal_univ, integral_const_mul]
          rw [show (fun a : ι → Bool => z ^ 2 * (X a - r0) ^ 4 / 2) =
              fun a => (z ^ 2 / 2) * (X a - r0) ^ 4 by
            funext a
            ring,
            integral_const_mul]
          ring
    calc
      B ≤ _ := hint
      _ ≤ 1 - z * (u / 2 * (Real.cosh h)⁻¹ ^ 2) +
          z ^ 2 / 2 * ((6 + 8 * h ^ 4) * u ^ 2) := by
        nlinarith [hsecondY, hfourthY]
      _ = rho := by dsimp [rho, s]; ring
  have hB : B ≤ min 1 rho := le_min hB_one hB_rho
  let C : ℝ := Real.exp (-z * (1 + 2 * s) / (1 + s) ^ 2)
  have hrewrite (bits : ι → Bool) :
      Real.exp (-z * (1 + X bits) ^ 2) =
        C * (Real.exp (lam * X bits) *
          Real.exp (-z * (X bits - r0) ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [C, lam, r0]
    field_simp [hden.ne']
    ring
  have hesscher :
      ∫ bits, Real.exp (lam * X bits) *
          Real.exp (-z * (X bits - r0) ^ 2)
        ∂(rademacherPMF ι).toMeasure =
      (∏ i, Real.cosh (lam * coeff i)) * B := by
    simpa only [X, tilt, μ, B] using
      rademacherIntegral_exp_mul_eq_biasedSignProduct lam coeff
        (fun bits => Real.exp (-z * (X bits - r0) ^ 2))
  have hnormalizer :
      ∏ i, Real.cosh (lam * coeff i) ≤ Real.exp (u * lam ^ 2 / 4) := by
    calc
      _ ≤ Real.exp (lam ^ 2 * (∑ i, coeff i ^ 2) / 2) :=
        prod_cosh_le_exp_sum_sq lam coeff
      _ = Real.exp (u * lam ^ 2 / 4) := by
        rw [hmass]
        congr 1
        all_goals ring
  have hconstant : C * Real.exp (u * lam ^ 2 / 4) =
      Real.exp (-z / (1 + s)) := by
    dsimp [C, lam]
    rw [← Real.exp_add]
    congr 1
    field_simp [hden.ne']
    ring
  calc
    ∫ bits, Real.exp (-z * (1 + rademacherSum coeff bits) ^ 2)
        ∂(rademacherPMF ι).toMeasure =
        C * ∫ bits, Real.exp (lam * X bits) *
          Real.exp (-z * (X bits - r0) ^ 2)
            ∂(rademacherPMF ι).toMeasure := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with bits
      simpa [X] using hrewrite bits
    _ = C * ((∏ i, Real.cosh (lam * coeff i)) * B) := by rw [hesscher]
    _ ≤ C * (Real.exp (u * lam ^ 2 / 4) * B) := by
      gcongr
    _ = Real.exp (-z / (1 + s)) * B := by rw [← mul_assoc, hconstant]
    _ ≤ Real.exp (-z / (1 + s)) * min 1 rho := by gcongr
    _ = Real.exp (-z / (1 + s)) *
        min 1 (1 - s / 2 * (Real.cosh h)⁻¹ ^ 2 +
          3 * s ^ 2 + 4 * s ^ 2 * h ^ 4) := by rfl

/-- A sparse row is the doubled-sign profile consumed by
`shiftedDominantRow`. -/
theorem sparseRow_shiftedDominantRow
    {d : ℕ} (b : Fin d → ℝ) (u z : ℝ)
    (hu : 0 < u) (hz : 0 < z) (hmass : ∑ i, b i ^ 2 = u) :
    let s := z * u
    let h := z * Real.sqrt u / (1 + s)
    ∫ row, Real.exp (-z * (1 + realRowDot row b) ^ 2)
        ∂(sparseRademacherRow d).toMeasure ≤
      Real.exp (-z / (1 + s)) *
        min 1
          (1 - s / 2 * (Real.cosh h)⁻¹ ^ 2 +
            3 * s ^ 2 + 4 * s ^ 2 * h ^ 4) := by
  classical
  dsimp only
  let coeff : Fin d × Fin 2 → ℝ := fun p => b p.1 / 2
  have hcoeffMass : ∑ p, coeff p ^ 2 = u / 2 := by
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two, coeff]
    calc
      ∑ i, ((b i / 2) ^ 2 + (b i / 2) ^ 2) =
          (∑ i, b i ^ 2) / 2 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = u / 2 := by rw [hmass]
  have hcoeffBound (p : Fin d × Fin 2) :
      2 * |coeff p| ≤ Real.sqrt u := by
    have hsingle := Finset.single_le_sum
      (s := Finset.univ) (f := fun i => b i ^ 2)
      (fun i _ => sq_nonneg (b i)) (Finset.mem_univ p.1)
    rw [hmass] at hsingle
    have habs : |b p.1| ≤ Real.sqrt u := by
      apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).1
      rw [sq_abs, Real.sq_sqrt hu.le]
      exact hsingle
    calc
      2 * |coeff p| = |b p.1| := by
        dsimp [coeff]
        rw [abs_div]
        norm_num
        field_simp
      _ ≤ Real.sqrt u := habs
  have hseedDot (seed : SparseRowSeed d) :
      realRowDot (sparseRow seed) b =
        rademacherSum coeff (sparseRowSeedSigns seed) := by
    rw [realRowDot, rademacherSum, Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two, coeff, sparseRowSeedSigns]
    apply Finset.sum_congr rfl
    intro i hi
    have hs := sparseBit_eq_average (seed i)
    have hsReal := congrArg (fun x : ℤ => (x : ℝ)) hs
    norm_num only [Int.cast_mul, Int.cast_add, Int.cast_ofNat] at hsReal
    simp only [sparseRow]
    simp only [if_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
    linear_combination (b i / 2) * hsReal
  have hmap :
      (sparseRademacherRow d).map (fun row => realRowDot row b) =
        (rademacherPMF (Fin d × Fin 2)).map
          (rademacherSum coeff) := by
    rw [sparseRademacherRow_eq_map_uniformRowSeed, PMF.map_comp]
    calc
      (PMF.uniformOfFintype (SparseRowSeed d)).map
          ((fun row => realRowDot row b) ∘ sparseRow) =
          (PMF.uniformOfFintype (SparseRowSeed d)).map
            (rademacherSum coeff ∘ sparseRowSeedSigns) := by
        congr 1
        funext seed
        exact hseedDot seed
      _ = ((PMF.uniformOfFintype (SparseRowSeed d)).map
          sparseRowSeedSigns).map (rademacherSum coeff) := by
        rw [PMF.map_comp]
      _ = (PMF.uniformOfFintype (Fin d × Fin 2 → Bool)).map
          (rademacherSum coeff) := by rw [map_uniformSparseSeed_signs]
      _ = (rademacherPMF (Fin d × Fin 2)).map
          (rademacherSum coeff) := by
        unfold rademacherPMF
        rw [uniformPiPMF_eq_uniformOfFintype]
  have hintegral :
      ∫ row, Real.exp (-z * (1 + realRowDot row b) ^ 2)
          ∂(sparseRademacherRow d).toMeasure =
        ∫ bits, Real.exp (-z * (1 + rademacherSum coeff bits) ^ 2)
          ∂(rademacherPMF (Fin d × Fin 2)).toMeasure := by
    exact integral_comp_eq_of_pmf_map_eq_early
      (sparseRademacherRow d) (rademacherPMF (Fin d × Fin 2))
      (fun row => realRowDot row b) (rademacherSum coeff)
      (fun x => Real.exp (-z * (1 + x) ^ 2))
      (measurable_of_countable _) (measurable_of_finite _)
      (by fun_prop) hmap
  rw [hintegral]
  exact shiftedDominantRow coeff u z hu hz hcoeffMass hcoeffBound

private theorem dominantProfile_le_quarter
    {z x : ℝ} (hz : 0 < z) (hx : 0 ≤ x) :
    z ^ 2 * x / (1 + z * x) ^ 2 ≤ z / 4 := by
  have hden : 0 < 1 + z * x := by positivity
  apply (div_le_div_iff₀ (sq_pos_of_pos hden) (by positivity : (0 : ℝ) < 4)).2
  nlinarith [sq_nonneg (1 - z * x)]

private theorem dominantProfile_mono_before_one
    {z x y : ℝ} (hz : 0 < z) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : z * y ≤ 1) :
    z ^ 2 * x / (1 + z * x) ^ 2 ≤
      z ^ 2 * y / (1 + z * y) ^ 2 := by
  have hy_nonneg : 0 ≤ y := hx.trans hxy
  have hdenx : 0 < 1 + z * x := by positivity
  have hdeny : 0 < 1 + z * y := by positivity
  have hprod : 0 ≤ 1 - z ^ 2 * x * y := by
    have hzx : 0 ≤ z * x := mul_nonneg hz.le hx
    have hzy : 0 ≤ z * y := mul_nonneg hz.le hy_nonneg
    have haux := mul_nonneg hzx (sub_nonneg.mpr hy)
    nlinarith
  apply (div_le_div_iff₀ (sq_pos_of_pos hdenx) (sq_pos_of_pos hdeny)).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) hprod]

private theorem dominantProfile_antitone_after_one
    {z x y : ℝ} (hz : 0 < z) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hxone : 1 ≤ z * x) :
    z ^ 2 * y / (1 + z * y) ^ 2 ≤
      z ^ 2 * x / (1 + z * x) ^ 2 := by
  have hy_nonneg : 0 ≤ y := hx.trans hxy
  have hdenx : 0 < 1 + z * x := by positivity
  have hdeny : 0 < 1 + z * y := by positivity
  have hprod : 0 ≤ z ^ 2 * x * y - 1 := by
    have hzy : 1 ≤ z * y := hxone.trans (mul_le_mul_of_nonneg_left hxy hz.le)
    have haux := mul_nonneg (sub_nonneg.mpr hxone) (by positivity : 0 ≤ z * y)
    nlinarith
  apply (div_le_div_iff₀ (sq_pos_of_pos hdeny) (sq_pos_of_pos hdenx)).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) hprod]

/-- The literal endpoint/critical-point expression L15 bounds the actual
squared shifted-row tilt throughout a valid cell. -/
theorem dominantCellHsq_ge
    (lower upper z : ℚ) (u : ℝ)
    (hlower : 0 < (lower : ℝ))
    (hlower_u : (lower : ℝ) ≤ u) (hu_upper : u ≤ (upper : ℝ))
    (hz : 0 < (z : ℝ)) :
    ((z : ℝ) * Real.sqrt u / (1 + (z : ℝ) * u)) ^ 2 ≤
      dominantCellHsq lower upper z := by
  let zr : ℝ := (z : ℝ)
  let lr : ℝ := (lower : ℝ)
  let ur : ℝ := (upper : ℝ)
  have hu : 0 < u := lt_of_lt_of_le hlower hlower_u
  have hlr : 0 ≤ lr := hlower.le
  have hur : 0 ≤ ur := hlr.trans (hlower_u.trans hu_upper)
  have hsqrt : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu.le
  have hleft :
      ((z : ℝ) * Real.sqrt u / (1 + (z : ℝ) * u)) ^ 2 =
        zr ^ 2 * u / (1 + zr * u) ^ 2 := by
    dsimp [zr]
    rw [div_pow, mul_pow, hsqrt]
  rw [hleft]
  by_cases hbefore : zr * u ≤ 1
  · by_cases hupper_before : zr * ur ≤ 1
    · have hmono := dominantProfile_mono_before_one
        (z := zr) (x := u) (y := ur) hz hu.le hu_upper hupper_before
      exact hmono.trans (by
        unfold dominantCellHsq
        exact le_max_of_le_right (le_max_left _ _))
    · have hcrit : z * lower ≤ 1 ∧ 1 ≤ z * upper := by
        constructor
        · exact_mod_cast (mul_le_mul_of_nonneg_left hlower_u hz.le).trans hbefore
        · have hreal : (1 : ℝ) ≤ (z : ℝ) * (upper : ℝ) := by
            simpa [zr, ur] using le_of_not_ge hupper_before
          exact_mod_cast hreal
      have hquarter := dominantProfile_le_quarter hz hu.le
      exact hquarter.trans (by
        unfold dominantCellHsq
        simp only [hcrit]
        exact le_max_of_le_right (le_max_right _ _))
  · have hafter : 1 ≤ zr * u := le_of_not_ge hbefore
    by_cases hlower_after : 1 ≤ zr * lr
    · have hanti := dominantProfile_antitone_after_one
        (z := zr) (x := lr) (y := u) hz hlr hlower_u hlower_after
      exact hanti.trans (by
        unfold dominantCellHsq
        exact le_max_left _ _)
    · have hcrit : z * lower ≤ 1 ∧ 1 ≤ z * upper := by
        constructor
        · have hreal : (z : ℝ) * (lower : ℝ) ≤ 1 := by
            simpa [zr, lr] using le_of_not_ge hlower_after
          exact_mod_cast hreal
        · have hreal : (1 : ℝ) ≤ (z : ℝ) * (upper : ℝ) := by
            simpa [zr] using hafter.trans
              (mul_le_mul_of_nonneg_left hu_upper hz.le)
          exact_mod_cast hreal
      have hquarter := dominantProfile_le_quarter hz hu.le
      exact hquarter.trans (by
        unfold dominantCellHsq
        simp only [hcrit]
        exact le_max_of_le_right (le_max_right _ _))

/-- L15 enlarges the exact shifted-row correction at every endpoint in the
direction required for an upper bound. -/
theorem shiftedDominantRho_le_cell
    (lower upper z : ℚ) (u : ℝ)
    (hlower : 0 < (lower : ℝ))
    (hlower_u : (lower : ℝ) ≤ u) (hu_upper : u ≤ (upper : ℝ))
    (hz : 0 < (z : ℝ)) :
    let s := (z : ℝ) * u
    let h := (z : ℝ) * Real.sqrt u / (1 + s)
    min 1
        (1 - s / 2 * (Real.cosh h)⁻¹ ^ 2 +
          3 * s ^ 2 + 4 * s ^ 2 * h ^ 4) ≤
      dominantCellRho lower upper z := by
  dsimp only
  let s : ℝ := (z : ℝ) * u
  let sLower : ℝ := (z : ℝ) * (lower : ℝ)
  let sUpper : ℝ := (z : ℝ) * (upper : ℝ)
  let h : ℝ := (z : ℝ) * Real.sqrt u / (1 + s)
  let H2 : ℝ := dominantCellHsq lower upper z
  have hu : 0 < u := lt_of_lt_of_le hlower hlower_u
  have hsLower_nonneg : 0 ≤ sLower := by dsimp [sLower]; positivity
  have hsLower_s : sLower ≤ s := by
    dsimp [sLower, s]
    exact mul_le_mul_of_nonneg_left hlower_u hz.le
  have hs_sUpper : s ≤ sUpper := by
    dsimp [sUpper, s]
    exact mul_le_mul_of_nonneg_left hu_upper hz.le
  have hs_nonneg : 0 ≤ s := hsLower_nonneg.trans hsLower_s
  have hsUpper_nonneg : 0 ≤ sUpper := hs_nonneg.trans hs_sUpper
  have hh_nonneg : 0 ≤ h := by dsimp [h, s]; positivity
  have hh2 : h ^ 2 ≤ H2 := by
    dsimp [h, s, H2]
    exact dominantCellHsq_ge lower upper z u hlower hlower_u hu_upper hz
  have hH2_nonneg : 0 ≤ H2 := (sq_nonneg h).trans hh2
  have htanh : Real.tanh h ^ 2 ≤ h ^ 2 := by
    have ht := tanh_le_self hh_nonneg
    exact (sq_le_sq₀ (tanh_nonneg hh_nonneg) hh_nonneg).2 ht
  have hsech_lower :
      max 0 (1 - H2) ≤ (Real.cosh h)⁻¹ ^ 2 := by
    rw [← one_sub_tanh_sq]
    apply max_le
    · nlinarith [Real.tanh_sq_lt_one h]
    · nlinarith
  have hmax_nonneg : 0 ≤ max 0 (1 - H2) := le_max_left _ _
  have hsech_nonneg : 0 ≤ (Real.cosh h)⁻¹ ^ 2 := sq_nonneg _
  have hnegterm :
      -(s / 2 * (Real.cosh h)⁻¹ ^ 2) ≤
        -(sLower / 2 * max 0 (1 - H2)) := by
    have hsLower_half : sLower / 2 ≤ s / 2 := by linarith
    have hprod := mul_le_mul hsLower_half hsech_lower
      hmax_nonneg (by positivity : 0 ≤ s / 2)
    nlinarith
  have hs_sq : s ^ 2 ≤ sUpper ^ 2 :=
    (sq_le_sq₀ hs_nonneg hsUpper_nonneg).2 hs_sUpper
  have hh4 : h ^ 4 ≤ H2 ^ 2 := by
    calc
      h ^ 4 = (h ^ 2) ^ 2 := by ring
      _ ≤ H2 ^ 2 := (sq_le_sq₀ (sq_nonneg h) hH2_nonneg).2 hh2
  have hmix : s ^ 2 * h ^ 4 ≤ sUpper ^ 2 * H2 ^ 2 :=
    mul_le_mul hs_sq hh4 (by positivity) (sq_nonneg _)
  unfold dominantCellRho
  dsimp only
  apply min_le_min_left 1
  dsimp [s, sLower, sUpper, h, H2] at *
  nlinarith

private theorem exp_neg_div_one_sub_exp_neg_mono
    {a₀ a c₀ c : ℝ} (haa : a₀ ≤ a)
    (hc₀ : 0 < c₀) (hcc : c₀ ≤ c) :
    Real.exp (-a) / (1 - Real.exp (-c)) ≤
      Real.exp (-a₀) / (1 - Real.exp (-c₀)) := by
  have hnum : Real.exp (-a) ≤ Real.exp (-a₀) :=
    Real.exp_le_exp.mpr (neg_le_neg haa)
  have hc : 0 < c := hc₀.trans_le hcc
  have hden₀ : 0 < 1 - Real.exp (-c₀) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hc₀))
  have hden : 0 < 1 - Real.exp (-c) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hc))
  have hden_order : 1 - Real.exp (-c₀) ≤ 1 - Real.exp (-c) := by
    have := Real.exp_le_exp.mpr (neg_le_neg hcc)
    linarith
  exact div_le_div₀ (Real.exp_nonneg _) hnum hden₀ hden_order

/-- The actual two-oriented active wrap decreases to the literal L16 cell
endpoint expression when `alpha` is lowered and `B` is lowered. -/
theorem shiftedActiveWrap_le_cell
    (lower upper z : ℚ) (u B : ℝ)
    (hlower : 0 < (lower : ℝ))
    (hlower_u : (lower : ℝ) ≤ u) (hu_upper : u ≤ (upper : ℝ))
    (hz : 0 < (z : ℝ))
    (hB : 3 * Real.sqrt (1 + (lower : ℝ)) ≤ B) :
    let alpha : ℝ := (z : ℝ) / (1 + (z : ℝ) * u)
    Real.exp (-alpha * (B - 1) ^ 2) /
        (1 - Real.exp (-alpha * (3 * B ^ 2 - 2 * B))) +
      Real.exp (-alpha * (B + 1) ^ 2) /
        (1 - Real.exp (-alpha * (3 * B ^ 2 + 2 * B))) ≤
      dominantCellActiveWrap lower upper z := by
  dsimp only
  let B₀ : ℝ := 3 * Real.sqrt (1 + (lower : ℝ))
  let alpha₀ : ℝ := (z : ℝ) / (1 + (z : ℝ) * (upper : ℝ))
  let alpha : ℝ := (z : ℝ) / (1 + (z : ℝ) * u)
  have hu : 0 < u := lt_of_lt_of_le hlower hlower_u
  have hupper : 0 < (upper : ℝ) := hlower.trans_le (hlower_u.trans hu_upper)
  have hden : 0 < 1 + (z : ℝ) * u := by positivity
  have hden₀ : 0 < 1 + (z : ℝ) * (upper : ℝ) := by positivity
  have halpha : 0 < alpha := by dsimp [alpha]; positivity
  have halpha₀ : 0 < alpha₀ := by dsimp [alpha₀]; positivity
  have halpha_le : alpha₀ ≤ alpha := by
    have hden_le : 1 + (z : ℝ) * u ≤
        1 + (z : ℝ) * (upper : ℝ) := by
      simpa [add_comm] using
        add_le_add_left (mul_le_mul_of_nonneg_left hu_upper hz.le) 1
    apply (div_le_div_iff₀ hden₀ hden).2
    exact mul_le_mul_of_nonneg_left hden_le hz.le
  have hsqrt_one : 1 < Real.sqrt (1 + (lower : ℝ)) := by
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith
  have hB₀ : 1 < B₀ := by dsimp [B₀]; nlinarith
  have hB1 : 1 < B := hB₀.trans_le (by simpa [B₀] using hB)
  have hminus_sq : (B₀ - 1) ^ 2 ≤ (B - 1) ^ 2 := by
    exact (sq_le_sq₀ (by linarith) (by linarith)).2 (by simpa [B₀] using hB)
  have hplus_sq : (B₀ + 1) ^ 2 ≤ (B + 1) ^ 2 := by
    exact (sq_le_sq₀ (by linarith) (by linarith)).2 (by simpa [B₀] using hB)
  have hminus_rate : 3 * B₀ ^ 2 - 2 * B₀ ≤ 3 * B ^ 2 - 2 * B := by
    have hsum : 0 ≤ 3 * (B₀ + B) - 2 := by nlinarith
    have hdiff : 0 ≤ B - B₀ := by simpa [B₀] using hB
    nlinarith [mul_nonneg hdiff hsum]
  have hplus_rate : 3 * B₀ ^ 2 + 2 * B₀ ≤ 3 * B ^ 2 + 2 * B := by
    have hsum : 0 ≤ 3 * (B₀ + B) + 2 := by nlinarith
    have hdiff : 0 ≤ B - B₀ := by simpa [B₀] using hB
    nlinarith [mul_nonneg hdiff hsum]
  have hminus_rate_pos : 0 < 3 * B₀ ^ 2 - 2 * B₀ := by
    have : 0 < B₀ * (3 * B₀ - 2) := mul_pos (by linarith) (by linarith)
    nlinarith
  have hplus_rate_pos : 0 < 3 * B₀ ^ 2 + 2 * B₀ := by
    have : 0 < B₀ * (3 * B₀ + 2) := mul_pos (by linarith) (by linarith)
    nlinarith
  have hminus := exp_neg_div_one_sub_exp_neg_mono
    (mul_le_mul halpha_le hminus_sq (sq_nonneg _) halpha.le)
    (mul_pos halpha₀ hminus_rate_pos)
    (mul_le_mul halpha_le hminus_rate
      (by positivity) halpha.le)
  have hplus := exp_neg_div_one_sub_exp_neg_mono
    (mul_le_mul halpha_le hplus_sq (sq_nonneg _) halpha.le)
    (mul_pos halpha₀ hplus_rate_pos)
    (mul_le_mul halpha_le hplus_rate
      (by positivity) halpha.le)
  unfold dominantCellActiveWrap
  dsimp [B₀, alpha₀, alpha] at *
  simpa only [neg_mul] using add_le_add hminus hplus

private theorem integral_comp_eq_of_pmf_map_eq
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ]
    (p : PMF α) (q : PMF β) (X : α → γ) (Y : β → γ) (f : γ → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hf : Measurable f)
    (hmap : p.map X = q.map Y) :
    ∫ x, f (X x) ∂p.toMeasure = ∫ y, f (Y y) ∂q.toMeasure := by
  calc
    ∫ x, f (X x) ∂p.toMeasure =
        ∫ z, f z ∂Measure.map X p.toMeasure := by
      exact (integral_map hX.aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ z, f z ∂(p.map X).toMeasure := by
      rw [PMF.toMeasure_map X p hX]
    _ = ∫ z, f z ∂(q.map Y).toMeasure := by rw [hmap]
    _ = ∫ z, f z ∂Measure.map Y q.toMeasure := by
      rw [PMF.toMeasure_map Y q hY]
    _ = ∫ y, f (Y y) ∂q.toMeasure := by
      exact integral_map hY.aemeasurable hf.aestronglyMeasurable

private theorem integral_even_comp_eq_of_square_map_eq
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [Countable β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (p : PMF α) (q : PMF β) (X : α → ℤ) (Y : β → ℤ) (f : ℤ → ℝ)
    (heven : Function.Even f)
    (hmap : p.map (fun x => X x ^ 2) = q.map (fun y => Y y ^ 2)) :
    ∫ x, f (X x) ∂p.toMeasure = ∫ y, f (Y y) ∂q.toMeasure := by
  classical
  let g : ℤ → ℝ := fun t =>
    if h : ∃ x : ℤ, x ^ 2 = t then f h.choose else 0
  have hfactor (x : ℤ) : g (x ^ 2) = f x := by
    dsimp [g]
    let hexists : ∃ y : ℤ, y ^ 2 = x ^ 2 := ⟨x, rfl⟩
    rw [dif_pos hexists]
    let y := Classical.choose hexists
    change f y = f x
    have hsquare : y ^ 2 = x ^ 2 := Classical.choose_spec hexists
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with h | h
    · rw [h]
    · rw [h]
      exact heven x
  calc
    ∫ x, f (X x) ∂p.toMeasure =
        ∫ x, g (X x ^ 2) ∂p.toMeasure := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hfactor]
    _ = ∫ y, g (Y y ^ 2) ∂q.toMeasure :=
      integral_comp_eq_of_pmf_map_eq p q
        (fun x => X x ^ 2) (fun y => Y y ^ 2) g
        (measurable_of_countable _) (measurable_of_countable _)
        (measurable_of_countable _) hmap
    _ = ∫ y, f (Y y) ∂q.toMeasure := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hfactor]

private theorem centeredMod_neg {q : ℕ} (hq : Odd q) (x : ℤ) :
    centeredMod q (-x) = -centeredMod q x := by
  apply (centeredMod_eq_iff hq (-x) (-centeredMod q x)).2
  constructor
  · simp
  · have hx := centeredMod_mem_centeredInterval hq x
    simp only [centeredInterval, Set.mem_Icc] at hx ⊢
    omega

/-- The closed two-sided geometric tail decreases with its positive rate. -/
theorem twoSidedGeometricTail_antitone
    {c₀ c : ℝ} (hc₀ : 0 < c₀) (hcc : c₀ ≤ c) :
    2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) ≤
      2 * Real.exp (-c₀) / (1 - (Real.exp (-c₀)) ^ 3) := by
  have hr : Real.exp (-c) ≤ Real.exp (-c₀) := by
    exact Real.exp_le_exp.mpr (neg_le_neg hcc)
  have hr₀_lt : Real.exp (-c₀) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hc₀)
  have hr₀_pow : (Real.exp (-c₀)) ^ 3 < 1 := by
    simpa using pow_lt_pow_left₀ hr₀_lt (Real.exp_pos (-c₀)).le
      (by norm_num : (3 : ℕ) ≠ 0)
  have hden₀ : 0 < 1 - (Real.exp (-c₀)) ^ 3 := sub_pos.mpr hr₀_pow
  have hpow : (Real.exp (-c)) ^ 3 ≤ (Real.exp (-c₀)) ^ 3 := by
    exact pow_le_pow_left₀ (Real.exp_nonneg _) hr 3
  exact div_le_div₀ (by positivity) (by nlinarith) hden₀ (by nlinarith)

/--
The all-lobe scalar bound is monotone in the two endpoint parameters used by
the dominant cell.  The actual tilt remains in the square-root normalization,
while the lobe tail is enlarged at `sUpper` and at the smallest Holder
exponent `p = 2`.
-/
theorem sparseScalarF_lobe_le_dominantCentral
    {s sUpper p : ℝ} (hs : 0 < s) (hsUpper : s ≤ sUpper)
    (hp : 2 ≤ p) :
    sparseScalarF s p ≤
      1 / Real.sqrt (1 + s) *
        (1 + 2 * Real.exp (-Real.pi ^ 2 / (1 + sUpper)) /
          (1 - (Real.exp (-Real.pi ^ 2 / (1 + sUpper))) ^ 3)) := by
  have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hsUpper_pos : 0 < 1 + sUpper := by linarith
  let c : ℝ := Real.pi ^ 2 / (1 + sUpper)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hL6 := sparseScalarF_lobe_periodization hs hp_pos
  have hterm (k : ℤ) :
      Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + s))) ≤
        Real.exp (-c * (k : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hden : 0 < 1 + s := by linarith
    have hcoeff : c ≤ p * Real.pi ^ 2 / (2 * (1 + s)) := by
      dsimp [c]
      apply (div_le_div_iff₀ hsUpper_pos (by positivity : 0 < 2 * (1 + s))).2
      have hbase : 2 * (1 + s) ≤ p * (1 + sUpper) := by
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left hbase (sq_nonneg Real.pi)
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (k : ℝ))
    calc
      -(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + s)) =
          -(p * Real.pi ^ 2 / (2 * (1 + s)) * (k : ℝ) ^ 2) := by ring
      _ ≤ -(c * (k : ℝ) ^ 2) := by linarith
      _ = -c * (k : ℝ) ^ 2 := by ring
  have hsource : Summable (fun k : ℤ =>
      Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + s)))) := by
    have htarget : Summable (fun k : ℤ =>
        Real.exp (-c * (k : ℝ) ^ 2)) := by
      exact summable_real_integer_exp_neg_sq hc
    exact htarget.of_nonneg_of_le (fun _ => by positivity) hterm
  have hsum :
      (∑' k : ℤ,
        Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) / (2 * (1 + s)))) ≤
        1 + 2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) := by
    exact (hsource.tsum_le_tsum hterm
      (summable_real_integer_exp_neg_sq hc)).trans
        (scalarLobe_real_integer_exp_geometricTail hc)
  calc
    sparseScalarF s p ≤
        1 / Real.sqrt (1 + s) *
          ∑' k : ℤ,
            Real.exp (-(p * ((k : ℝ) * Real.pi) ^ 2) /
              (2 * (1 + s))) := hL6
    _ ≤ 1 / Real.sqrt (1 + s) *
        (1 + 2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3)) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 / Real.sqrt (1 + s) *
        (1 + 2 * Real.exp (-Real.pi ^ 2 / (1 + sUpper)) /
          (1 - (Real.exp (-Real.pi ^ 2 / (1 + sUpper))) ^ 3)) := by
      dsimp [c]
      congr 4 <;> ring

/--
The complete support-indexed Holder product is bounded by the paper's L17
inactive central factor at the two cell endpoints.
-/
theorem gaussianCosineProduct_le_dominantCentral
    {d : ℕ} (a : Fin d → ℝ) (S : Finset (Fin d))
    {sLower s sUpper : ℝ}
    (hS : ∀ j, j ∈ S ↔ a j ≠ 0)
    (ha : ∑ j, a j ^ 2 = 1)
    (hsLower : 0 ≤ sLower) (hsLower_le : sLower ≤ s)
    (hs : 0 < s) (hsUpper : s ≤ sUpper) :
    ∏ j ∈ S, gaussianCosineMoment s (2 / (a j ^ 2)) ^ (a j ^ 2) ≤
      ENNReal.ofReal
        ((1 / Real.sqrt (1 + sLower)) *
          (1 + 2 * Real.exp (-Real.pi ^ 2 / (1 + sUpper)) /
            (1 - (Real.exp (-Real.pi ^ 2 / (1 + sUpper))) ^ 3))) := by
  let C : ℝ :=
    1 + 2 * Real.exp (-Real.pi ^ 2 / (1 + sUpper)) /
      (1 - (Real.exp (-Real.pi ^ 2 / (1 + sUpper))) ^ 3)
  let B : ℝ := 1 / Real.sqrt (1 + sLower) * C
  have hsUpper_pos : 0 < 1 + sUpper := by linarith
  have htheta : Real.exp (-Real.pi ^ 2 / (1 + sUpper)) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos Real.pi_pos))
      hsUpper_pos
  have hden : 0 < 1 - (Real.exp
      (-Real.pi ^ 2 / (1 + sUpper))) ^ 3 := by
    have hpow := pow_lt_pow_left₀ htheta
      (Real.exp_pos (-Real.pi ^ 2 / (1 + sUpper))).le
      (by norm_num : (3 : ℕ) ≠ 0)
    simpa using sub_pos.mpr hpow
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hsumS : ∑ j ∈ S, a j ^ 2 = 1 := by
    calc
      ∑ j ∈ S, a j ^ 2 = ∑ j, a j ^ 2 := by
        apply Finset.sum_subset (by simp)
        intro j hj hnot
        have haj : a j = 0 := by
          by_contra hne
          exact hnot ((hS j).2 hne)
        simp [haj]
      _ = 1 := ha
  have hfactor (j : Fin d) (hj : j ∈ S) :
      gaussianCosineMoment s (2 / (a j ^ 2)) ≤ ENNReal.ofReal B := by
    have haj : a j ≠ 0 := (hS j).1 hj
    have haj_sq : 0 < a j ^ 2 := sq_pos_of_ne_zero haj
    have hp : 2 ≤ 2 / (a j ^ 2) := by
      apply (le_div_iff₀ haj_sq).2
      have haj_le : a j ^ 2 ≤ 1 := by
        have hsingle := Finset.single_le_sum
          (s := Finset.univ) (f := fun k => a k ^ 2)
          (fun k _ => sq_nonneg (a k)) (Finset.mem_univ j)
        rw [ha] at hsingle
        exact hsingle
      nlinarith
    have hp_pos : 0 < 2 / (a j ^ 2) := by positivity
    rw [gaussianCosineMoment_eq_ofReal_sparseScalarF hp_pos]
    apply ENNReal.ofReal_mono
    have hscalar := sparseScalarF_lobe_le_dominantCentral hs hsUpper hp
    have hsqrt :
        1 / Real.sqrt (1 + s) ≤ 1 / Real.sqrt (1 + sLower) := by
      have hsLower_one : 0 < 1 + sLower := by linarith
      have hsqrt_pos : 0 < Real.sqrt (1 + sLower) :=
        Real.sqrt_pos.2 hsLower_one
      have hsqrt_mono : Real.sqrt (1 + sLower) ≤ Real.sqrt (1 + s) :=
        Real.sqrt_le_sqrt (by linarith)
      exact one_div_le_one_div_of_le hsqrt_pos hsqrt_mono
    calc
      sparseScalarF s (2 / (a j ^ 2)) ≤
          1 / Real.sqrt (1 + s) * C := by
        simpa [C] using hscalar
      _ ≤ 1 / Real.sqrt (1 + sLower) * C :=
        mul_le_mul_of_nonneg_right hsqrt hC
      _ = B := by rfl
  have hcollapse (T : Finset (Fin d)) :
      (ENNReal.ofReal B) ^ (∑ j ∈ T, a j ^ 2) =
        ∏ j ∈ T, (ENNReal.ofReal B) ^ (a j ^ 2) := by
    induction T using Finset.induction with
    | empty => simp
    | @insert j T hj ih =>
        rw [Finset.sum_insert hj, Finset.prod_insert hj,
          ENNReal.rpow_add_of_nonneg _ _ (sq_nonneg (a j))
            (Finset.sum_nonneg fun k _ => sq_nonneg (a k)), ih]
  calc
    ∏ j ∈ S, gaussianCosineMoment s (2 / (a j ^ 2)) ^ (a j ^ 2) ≤
        ∏ j ∈ S, (ENNReal.ofReal B) ^ (a j ^ 2) := by
      apply Finset.prod_le_prod
      · intro j hj
        positivity
      · intro j hj
        exact ENNReal.rpow_le_rpow (hfactor j hj) (sq_nonneg (a j))
    _ = (ENNReal.ofReal B) ^ (∑ j ∈ S, a j ^ 2) := by
      exact (hcollapse S).symm
    _ = ENNReal.ofReal B := by rw [hsumS, ENNReal.rpow_one]
    _ = ENNReal.ofReal
        ((1 / Real.sqrt (1 + sLower)) *
          (1 + 2 * Real.exp (-Real.pi ^ 2 / (1 + sUpper)) /
            (1 - (Real.exp (-Real.pi ^ 2 / (1 + sUpper))) ^ 3))) := by
      rfl

/-- The canonically reindexed active remainder satisfies the complete L17
active row bound: shifted zero image plus the literal two-sided L16 wrap. -/
theorem dominantRemainderFin_active_le_cellRow
    {d : ℕ} (w : Fin d → ℤ) (i : Fin d) (q : ℕ)
    (lower upper z : ℚ)
    (hq : Odd q) (hi : w i ≠ 0)
    (hlower : 0 < (lower : ℝ))
    (hlower_u : (lower : ℝ) ≤ dominantResidualRatio w i)
    (hu_upper : dominantResidualRatio w i ≤ (upper : ℝ))
    (hz : 0 < (z : ℝ))
    (hmodulus : 3 * Real.sqrt (1 + (lower : ℝ)) ≤
      (q : ℝ) / (dominantAmplitude w i : ℝ)) :
    (∫ row, Real.exp
          (-(z : ℝ) * ((centeredMod q
            ((dominantAmplitude w i : ℤ) +
              ∑ j, row j * dominantRemainderFinWeights w i j : ℤ) : ℝ) /
                (dominantAmplitude w i : ℝ)) ^ 2)
          ∂(sparseRademacherRow
            (Fintype.card (DominantRemainderIndex i))).toMeasure) ≤
      dominantCellActiveRow lower upper z := by
  let A : ℕ := dominantAmplitude w i
  let V : ℝ := dominantRemainderSqNorm w i
  let u : ℝ := dominantResidualRatio w i
  let B : ℝ := (q : ℝ) / (A : ℝ)
  let alpha : ℝ := (z : ℝ) / (1 + (z : ℝ) * u)
  let rho : ℝ :=
    let s := (z : ℝ) * u
    let h := (z : ℝ) * Real.sqrt u / (1 + s)
    min 1 (1 - s / 2 * (Real.cosh h)⁻¹ ^ 2 +
      3 * s ^ 2 + 4 * s ^ 2 * h ^ 4)
  let central : ℝ := Real.exp (-(z : ℝ) / (1 + (z : ℝ) * u)) * rho
  let wrap : ℝ :=
    Real.exp (-alpha * (B - 1) ^ 2) /
        (1 - Real.exp (-alpha * (3 * B ^ 2 - 2 * B))) +
      Real.exp (-alpha * (B + 1) ^ 2) /
        (1 - Real.exp (-alpha * (3 * B ^ 2 + 2 * B)))
  have hA : 0 < A := by dsimp [A]; exact dominantAmplitude_pos hi
  have hu : 0 < u := lt_of_lt_of_le hlower hlower_u
  have hV : 0 < V := by
    dsimp [V, u, dominantResidualRatio] at hu ⊢
    rcases div_pos_iff.mp hu with h | h
    · exact h.1
    · exact False.elim ((not_lt_of_ge (by positivity)) h.1)
  have hnorm : ∑ j, (dominantRemainderFinWeights w i j : ℝ) ^ 2 = V := by
    dsimp [V]
    rw [← realCast_sqNorm, sqNorm_dominantRemainderFinWeights]
  have hmass :
      ∑ j, ((dominantRemainderFinWeights w i j : ℝ) / (A : ℝ)) ^ 2 = u := by
    simp_rw [div_pow]
    rw [← Finset.sum_div, hnorm]
    rfl
  have hB1 : 1 < B := by
    have hsqrt : 1 < Real.sqrt (1 + (lower : ℝ)) := by
      rw [Real.lt_sqrt (by norm_num)]
      nlinarith
    dsimp [B, A]
    nlinarith
  have hperiod := sparseRow_shiftedNormalizedPeriodization_nonzeroImageBound
    (dominantRemainderFinWeights w i) q A V (z : ℝ)
    hq hA hV hnorm hz hB1
  have hcore := sparseRow_shiftedDominantRow
    (fun j => (dominantRemainderFinWeights w i j : ℝ) / (A : ℝ))
    u (z : ℝ) hu hz hmass
  have hdot (row : Fin (Fintype.card (DominantRemainderIndex i)) → ℤ) :
      realRowDot row
          (fun j => (dominantRemainderFinWeights w i j : ℝ) / (A : ℝ)) =
        ((∑ j, row j * dominantRemainderFinWeights w i j : ℤ) : ℝ) /
          (A : ℝ) := by
    simp only [realRowDot, Int.cast_sum, Int.cast_mul]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hcentral :
      (∫ row, Real.exp (-(z : ℝ) * ((((A : ℤ) +
          ∑ j, row j * dominantRemainderFinWeights w i j : ℤ) : ℝ) /
            (A : ℝ)) ^ 2)
        ∂(sparseRademacherRow
          (Fintype.card (DominantRemainderIndex i))).toMeasure) ≤ central := by
    rw [show (∫ row, Real.exp (-(z : ℝ) * ((((A : ℤ) +
        ∑ j, row j * dominantRemainderFinWeights w i j : ℤ) : ℝ) /
          (A : ℝ)) ^ 2)
      ∂(sparseRademacherRow (Fintype.card (DominantRemainderIndex i))).toMeasure) =
      ∫ row, Real.exp (-(z : ℝ) * (1 + realRowDot row
        (fun j => (dominantRemainderFinWeights w i j : ℝ) / (A : ℝ))) ^ 2)
      ∂(sparseRademacherRow (Fintype.card (DominantRemainderIndex i))).toMeasure by
        apply integral_congr_ae
        filter_upwards [] with row
        congr 1
        rw [hdot]
        push_cast
        field_simp [show (A : ℝ) ≠ 0 by exact_mod_cast hA.ne']
        ]
    simpa only [central, rho] using hcore
  have hrho := shiftedDominantRho_le_cell
    lower upper z u hlower hlower_u hu_upper hz
  have hcentral_nonneg : 0 ≤ central :=
    (integral_nonneg fun _ => Real.exp_nonneg _).trans hcentral
  have hrho_nonneg : 0 ≤ rho := by
    dsimp [central] at hcentral_nonneg
    by_contra hneg
    have hrho_neg : rho < 0 := lt_of_not_ge hneg
    exact (not_lt_of_ge hcentral_nonneg)
      (mul_neg_of_pos_of_neg (Real.exp_pos _) hrho_neg)
  have hden_le : 1 + (z : ℝ) * u ≤
      1 + (z : ℝ) * (upper : ℝ) := by
    simpa [add_comm] using
      add_le_add_left (mul_le_mul_of_nonneg_left hu_upper hz.le) 1
  have hexp : Real.exp (-(z : ℝ) / (1 + (z : ℝ) * u)) ≤
      Real.exp (-(z : ℝ) / (1 + (z : ℝ) * (upper : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hdenu : 0 < 1 + (z : ℝ) * u := by positivity
    have hupper : 0 < (upper : ℝ) := hlower.trans_le (hlower_u.trans hu_upper)
    have hdenUpper : 0 < 1 + (z : ℝ) * (upper : ℝ) := by positivity
    have hdiv := (div_le_div_iff₀ hdenUpper hdenu).2
      (mul_le_mul_of_nonneg_left hden_le hz.le)
    simpa only [neg_div] using neg_le_neg hdiv
  have hcentral_cell : central ≤
      Real.exp (-(z : ℝ) / (1 + (z : ℝ) * (upper : ℝ))) *
        dominantCellRho lower upper z := by
    dsimp [central]
    calc
      _ ≤ Real.exp (-(z : ℝ) / (1 + (z : ℝ) * u)) *
          dominantCellRho lower upper z :=
        mul_le_mul_of_nonneg_left hrho (Real.exp_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right hexp (hrho_nonneg.trans hrho)
  have hwrap_cell : wrap ≤ dominantCellActiveWrap lower upper z := by
    simpa only [wrap, alpha, B, A, u] using
      shiftedActiveWrap_le_cell lower upper z u B
        hlower hlower_u hu_upper hz (by simpa [B, A] using hmodulus)
  have hcell_central_nonneg : 0 ≤
      Real.exp (-(z : ℝ) / (1 + (z : ℝ) * (upper : ℝ))) *
        dominantCellRho lower upper z :=
    mul_nonneg (Real.exp_nonneg _) (hrho_nonneg.trans hrho)
  have hcell_wrap_nonneg : 0 ≤ dominantCellActiveWrap lower upper z := by
    have hwrap_nonneg : 0 ≤ wrap := by
      have halpha : 0 < alpha := by dsimp [alpha]; positivity
      have hminus : 0 < alpha * (3 * B ^ 2 - 2 * B) := by
        have : 0 < B * (3 * B - 2) := mul_pos (by linarith) (by linarith)
        have : 0 < 3 * B ^ 2 - 2 * B := by nlinarith
        positivity
      have hplus : 0 < alpha * (3 * B ^ 2 + 2 * B) := by
        have : 0 < B * (3 * B + 2) := mul_pos (by linarith) (by linarith)
        have : 0 < 3 * B ^ 2 + 2 * B := by nlinarith
        positivity
      dsimp [wrap]
      have hdminus : 0 < 1 - Real.exp (-alpha * (3 * B ^ 2 - 2 * B)) :=
        sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
      have hdplus : 0 < 1 - Real.exp (-alpha * (3 * B ^ 2 + 2 * B)) :=
        sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
      positivity
    exact hwrap_nonneg.trans hwrap_cell
  have hENN : ENNReal.ofReal
        (∫ row, Real.exp
          (-(z : ℝ) * ((centeredMod q
            ((dominantAmplitude w i : ℤ) +
              ∑ j, row j * dominantRemainderFinWeights w i j : ℤ) : ℝ) /
                (dominantAmplitude w i : ℝ)) ^ 2)
          ∂(sparseRademacherRow
            (Fintype.card (DominantRemainderIndex i))).toMeasure) ≤
      ENNReal.ofReal (dominantCellActiveRow lower upper z) := by
    calc
      _ ≤ ENNReal.ofReal central + ENNReal.ofReal wrap := by
        simpa only [A, V, u, B, alpha, central, wrap,
          dominantResidualRatio] using hperiod.trans
          (add_le_add (ENNReal.ofReal_mono hcentral) le_rfl)
      _ ≤ ENNReal.ofReal
          (Real.exp (-(z : ℝ) / (1 + (z : ℝ) * (upper : ℝ))) *
            dominantCellRho lower upper z) +
          ENNReal.ofReal (dominantCellActiveWrap lower upper z) := by
        exact add_le_add (ENNReal.ofReal_mono hcentral_cell)
          (ENNReal.ofReal_mono hwrap_cell)
      _ = ENNReal.ofReal (dominantCellActiveRow lower upper z) := by
        rw [← ENNReal.ofReal_add hcell_central_nonneg hcell_wrap_nonneg]
        rfl
  have hintegral_nonneg : 0 ≤ ∫ row, Real.exp
      (-(z : ℝ) * ((centeredMod q
        ((dominantAmplitude w i : ℤ) +
          ∑ j, row j * dominantRemainderFinWeights w i j : ℤ) : ℝ) /
            (dominantAmplitude w i : ℝ)) ^ 2)
      ∂(sparseRademacherRow
        (Fintype.card (DominantRemainderIndex i))).toMeasure :=
    integral_nonneg fun _ => Real.exp_nonneg _
  have hactive_nonneg : 0 ≤ dominantCellActiveRow lower upper z := by
    unfold dominantCellActiveRow
    exact add_nonneg hcell_central_nonneg hcell_wrap_nonneg
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN
  rw [ENNReal.toReal_ofReal hintegral_nonneg,
    ENNReal.toReal_ofReal hactive_nonneg] at hreal
  exact hreal

/--
The canonically reindexed inactive remainder satisfies the exact paper L17
row factor, assuming the cell contains its residual ratio and the normalized
modulus is at least the cell's `D₀ = 3` endpoint.
-/
theorem dominantRemainderFin_inactive_le_cellRow
    {d : ℕ} (w : Fin d → ℤ) (i : Fin d) (q : ℕ)
    (lower upper z : ℚ)
    (hq : Odd q) (hi : w i ≠ 0)
    (hlower : 0 < (lower : ℝ))
    (hlower_u : (lower : ℝ) ≤ dominantResidualRatio w i)
    (hu_upper : dominantResidualRatio w i ≤ (upper : ℝ))
    (hz : 0 < (z : ℝ))
    (hmodulus :
      3 * Real.sqrt (1 + (lower : ℝ)) ≤
        (q : ℝ) / (dominantAmplitude w i : ℝ)) :
    ∫ row, Real.exp
        (-(z : ℝ) * dominantResidualRatio w i *
          ((centeredMod q
            (∑ j, row j * dominantRemainderFinWeights w i j : ℤ) : ℝ) /
              Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2)
        ∂(sparseRademacherRow
          (Fintype.card (DominantRemainderIndex i))).toMeasure ≤
      dominantCellInactiveRow lower upper z := by
  let u : ℝ := dominantResidualRatio w i
  let s : ℝ := (z : ℝ) * u
  let sLower : ℝ := (z : ℝ) * (lower : ℝ)
  let sUpper : ℝ := (z : ℝ) * (upper : ℝ)
  let central : ℝ :=
    (1 / Real.sqrt (1 + sLower)) *
      (1 + 2 * Real.exp (-Real.pi ^ 2 / (1 + sUpper)) /
        (1 - (Real.exp (-Real.pi ^ 2 / (1 + sUpper))) ^ 3))
  let wrap : ℝ := dominantCellInactiveWrap lower upper z
  have hA : 0 < (dominantAmplitude w i : ℝ) := by
    exact_mod_cast dominantAmplitude_pos hi
  have hu_pos : 0 < u := lt_of_lt_of_le hlower hlower_u
  have hU : 0 < dominantRemainderSqNorm w i := by
    have hUreal : 0 < (dominantRemainderSqNorm w i : ℝ) := by
      dsimp [u, dominantResidualRatio] at hu_pos
      rcases (div_pos_iff.mp hu_pos) with h | h
      · exact h.1
      · exact False.elim ((not_lt_of_ge (by positivity)) h.1)
    exact_mod_cast hUreal
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hsLower : 0 ≤ sLower := by
    dsimp [sLower]
    positivity
  have hsLower_le : sLower ≤ s := by
    dsimp [sLower, s]
    exact mul_le_mul_of_nonneg_left hlower_u hz.le
  have hsUpper : s ≤ sUpper := by
    dsimp [sUpper, s]
    exact mul_le_mul_of_nonneg_left hu_upper hz.le
  let a : Fin (Fintype.card (DominantRemainderIndex i)) → ℝ :=
    fun j => (dominantRemainderFinWeights w i j : ℝ) /
      Real.sqrt (dominantRemainderSqNorm w i : ℝ)
  let S := Finset.univ.filter fun j => a j ≠ 0
  have hS : ∀ j, j ∈ S ↔ a j ≠ 0 := by
    intro j
    simp [S]
  have hUreal : 0 < (dominantRemainderSqNorm w i : ℝ) := by
    exact_mod_cast hU
  have hsqrtU : Real.sqrt (dominantRemainderSqNorm w i : ℝ) ^ 2 =
      (dominantRemainderSqNorm w i : ℝ) := Real.sq_sqrt hUreal.le
  have hnorm :
      ∑ j, (dominantRemainderFinWeights w i j : ℝ) ^ 2 =
        (dominantRemainderSqNorm w i : ℝ) := by
    rw [← realCast_sqNorm, sqNorm_dominantRemainderFinWeights]
  have ha : ∑ j, a j ^ 2 = 1 := by
    calc
      ∑ j, a j ^ 2 =
          ∑ j, (dominantRemainderFinWeights w i j : ℝ) ^ 2 /
            (dominantRemainderSqNorm w i : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [a]
        rw [div_pow, hsqrtU]
      _ = (∑ j, (dominantRemainderFinWeights w i j : ℝ) ^ 2) /
          (dominantRemainderSqNorm w i : ℝ) := by
        rw [Finset.sum_div]
      _ = 1 := by rw [hnorm, div_self hUreal.ne']
  have hproduct :
      ∏ j ∈ S, gaussianCosineMoment s (2 / (a j ^ 2)) ^ (a j ^ 2) ≤
        ENNReal.ofReal central := by
    simpa [central] using gaussianCosineProduct_le_dominantCentral
      a S hS ha hsLower hsLower_le hs hsUpper
  have hperiod := dominantRemainderFin_modular_le_scalarProduct_add_wrap
    w i q s hq hU hs
  have hc₀ : 0 <
      ((z : ℝ) / (1 + (z : ℝ) * (upper : ℝ))) *
        (3 * Real.sqrt (1 + (lower : ℝ))) ^ 2 := by
    have hden : 0 < 1 + (z : ℝ) * (upper : ℝ) := by
      have hu_nonneg : 0 ≤ (upper : ℝ) :=
        (hlower.le.trans hlower_u).trans hu_upper
      positivity
    positivity
  have hc_compare :
      ((z : ℝ) / (1 + (z : ℝ) * (upper : ℝ))) *
          (3 * Real.sqrt (1 + (lower : ℝ))) ^ 2 ≤
        s * ((q : ℝ) /
          Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 / (1 + s) := by
    have hu_nonneg : 0 ≤ u := hu_pos.le
    have hupper_nonneg : 0 ≤ (upper : ℝ) := hu_nonneg.trans hu_upper
    have hden_u : 0 < 1 + (z : ℝ) * u := by positivity
    have hden_upper : 0 < 1 + (z : ℝ) * (upper : ℝ) := by positivity
    have halpha :
        (z : ℝ) / (1 + (z : ℝ) * (upper : ℝ)) ≤
          (z : ℝ) / (1 + (z : ℝ) * u) := by
      exact div_le_div_of_nonneg_left hz.le hden_u
        (by nlinarith [mul_le_mul_of_nonneg_left hu_upper hz.le])
    have hmod_sq :
        (3 * Real.sqrt (1 + (lower : ℝ))) ^ 2 ≤
          ((q : ℝ) / (dominantAmplitude w i : ℝ)) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).2 hmodulus
    have hboth := mul_le_mul halpha hmod_sq (sq_nonneg _)
      (by positivity : 0 ≤ (z : ℝ) /
        (1 + (z : ℝ) * u))
    calc
      _ ≤ ((z : ℝ) / (1 + (z : ℝ) * u)) *
          ((q : ℝ) / (dominantAmplitude w i : ℝ)) ^ 2 := hboth
      _ = s * ((q : ℝ) /
          Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 / (1 + s) := by
        dsimp [s, u, dominantResidualRatio]
        field_simp [hA.ne', hUreal.ne', (Real.sqrt_pos.2 hUreal).ne', hsqrtU]
        rw [hsqrtU]
        ring
  have hwrapReal :
      2 * Real.exp
          (-s * ((q : ℝ) /
            Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 / (1 + s)) /
          (1 - (Real.exp
            (-s * ((q : ℝ) /
              Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 /
                (1 + s))) ^ 3) ≤ wrap := by
    have hmono := twoSidedGeometricTail_antitone hc₀ hc_compare
    have hpoweq :
        (Real.exp (-((z : ℝ) / (1 + (z : ℝ) * (upper : ℝ)) *
          (3 * Real.sqrt (1 + (lower : ℝ))) ^ 2))) ^ 3 =
        Real.exp (-3 * ((z : ℝ) /
          (1 + (z : ℝ) * (upper : ℝ))) *
            (3 * Real.sqrt (1 + (lower : ℝ))) ^ 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    dsimp [wrap, dominantCellInactiveWrap]
    rw [← hpoweq]
    convert hmono using 1 <;> ring
  have hcentral_nonneg : 0 ≤ central := by
    dsimp [central]
    have hsUpper_pos : 0 < 1 + sUpper := by linarith
    have htheta : Real.exp (-Real.pi ^ 2 / (1 + sUpper)) < 1 := by
      rw [Real.exp_lt_one_iff]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos Real.pi_pos))
        hsUpper_pos
    have hpow := pow_lt_pow_left₀ htheta
      (Real.exp_pos (-Real.pi ^ 2 / (1 + sUpper))).le
      (by norm_num : (3 : ℕ) ≠ 0)
    have hden : 0 < 1 -
        (Real.exp (-Real.pi ^ 2 / (1 + sUpper))) ^ 3 := by
      exact sub_pos.mpr (by simpa using hpow)
    positivity
  have hwrap_nonneg : 0 ≤ wrap := by
    have hactual_nonneg : 0 ≤
        2 * Real.exp
          (-s * ((q : ℝ) /
            Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 / (1 + s)) /
          (1 - (Real.exp
            (-s * ((q : ℝ) /
              Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 /
                (1 + s))) ^ 3) := by
      have hrate : 0 < s * ((q : ℝ) /
          Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 / (1 + s) := by
        have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq.pos
        positivity
      have hexp : Real.exp (-s * ((q : ℝ) /
          Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 /
            (1 + s)) < 1 := by
        apply Real.exp_lt_one_iff.mpr
        convert neg_lt_zero.mpr hrate using 1
        all_goals ring
      have hpow := pow_lt_pow_left₀ hexp (Real.exp_pos _).le
        (by norm_num : (3 : ℕ) ≠ 0)
      have hden : 0 < 1 - (Real.exp
          (-s * ((q : ℝ) /
            Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 /
              (1 + s))) ^ 3 := sub_pos.mpr (by simpa using hpow)
      exact div_nonneg (by positivity) hden.le
    exact hactual_nonneg.trans hwrapReal
  have hENN : ENNReal.ofReal
      (∫ row, Real.exp
        (-s * ((centeredMod q
          (∑ j, row j * dominantRemainderFinWeights w i j : ℤ) : ℝ) /
            Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2)
        ∂(sparseRademacherRow
          (Fintype.card (DominantRemainderIndex i))).toMeasure) ≤
      ENNReal.ofReal (central + wrap) := by
    calc
      _ ≤ (∏ j ∈ S,
          gaussianCosineMoment s (2 / (a j ^ 2)) ^ (a j ^ 2)) +
          ENNReal.ofReal
            (2 * Real.exp
              (-s * ((q : ℝ) /
                Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 / (1 + s)) /
              (1 - (Real.exp
                (-s * ((q : ℝ) /
                  Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 /
                    (1 + s))) ^ 3)) := by
        simpa [a, S] using hperiod
      _ ≤ ENNReal.ofReal central + ENNReal.ofReal wrap :=
        add_le_add hproduct (ENNReal.ofReal_mono hwrapReal)
      _ = ENNReal.ofReal (central + wrap) := by
        rw [ENNReal.ofReal_add hcentral_nonneg hwrap_nonneg]
  have hreal := ENNReal.toReal_le_of_le_ofReal
    (add_nonneg hcentral_nonneg hwrap_nonneg) hENN
  rw [ENNReal.toReal_ofReal] at hreal
  · simpa [u, s, central, wrap, sLower, sUpper,
      dominantCellInactiveRow] using hreal
  · exact integral_nonneg fun _ => Real.exp_nonneg _

end CertifiedJL
