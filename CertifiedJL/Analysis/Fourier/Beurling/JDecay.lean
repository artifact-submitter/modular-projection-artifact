/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author

The two-integration-by-parts engine is adapted from
`MathExtras/NumberTheory/Analysis/VaalerJ227Decay.lean` in
`gersh/ternary-goldbach-lean`, commit
`89416190c037331d7ebc04cd62ddb974cfb4dfcf` (Apache-2.0),
copyright (c) 2026 Gershon Bialer.
-/

import CertifiedJL.Analysis.Fourier.Beurling.JFourier
import CertifiedJL.Analysis.Fourier.SincSmooth
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Quadratic decay and integrability of the Vaaler kernel

We avoid singular endpoint derivative formulas by covering `[0,1]` with
two smooth removable-singularity charts.  The chart near zero divides by
`sinc (πt)`; the chart near one divides by `sinc (π(1-t))`.  Reflecting
them gives four smooth pieces on `[-1,1]`.  Two integrations by parts on
each piece, followed by exact cancellation of adjacent boundary values,
gives `J(x) = O(x⁻²)` and hence `J ∈ L¹`.
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology intervalIntegral Set
open FourierTransform
open scoped ContDiff RealInnerProductSpace

namespace CertifiedJL
namespace Probability

/-- Smooth removable-singularity chart for `Ĵ` near frequency zero. -/
noncomputable def beurlingJHatZeroChart (t : ℝ) : ℝ :=
  (1 - t) * Real.cos (Real.pi * t) / Real.sinc (Real.pi * t) + t

/-- Smooth removable-singularity chart for `Ĵ` near frequency one. -/
noncomputable def beurlingJHatOneChart (t : ℝ) : ℝ :=
  t * Real.cos (Real.pi * t) /
      Real.sinc (Real.pi * (1 - t)) + t

private theorem sinc_pi_mul_ne_zero
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    Real.sinc (Real.pi * t) ≠ 0 := by
  rcases eq_or_ne t 0 with rfl | htne
  · simp
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htne)
    have harg : Real.pi * t ≠ 0 :=
      mul_ne_zero Real.pi_ne_zero htne
    rw [Real.sinc_of_ne_zero harg]
    exact div_ne_zero
      (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
        (mul_pos Real.pi_pos htpos)
        (by
          have htlt : t < 1 := by linarith
          have hmul := mul_lt_mul_of_pos_left htlt Real.pi_pos
          simpa using hmul)))
      harg

private theorem sinc_pi_one_sub_ne_zero
    {t : ℝ} (ht0 : 1 / 2 ≤ t) (ht1 : t ≤ 1) :
    Real.sinc (Real.pi * (1 - t)) ≠ 0 := by
  rcases eq_or_ne t 1 with rfl | htne
  · simp
  · have hpos : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne ht1 htne)
    have hle : 1 - t ≤ 1 / 2 := by linarith
    exact sinc_pi_mul_ne_zero hpos.le hle

private theorem contDiffAt_beurlingJHatZeroChart
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    ContDiffAt ℝ ∞ beurlingJHatZeroChart t := by
  have hden :
      ContDiffAt ℝ ∞ (fun s : ℝ => Real.sinc (Real.pi * s)) t :=
    contDiff_realSinc.contDiffAt.comp t (by fun_prop)
  have hnum :
      ContDiffAt ℝ ∞
        (fun s : ℝ => (1 - s) * Real.cos (Real.pi * s)) t := by
    fun_prop
  have hquot :=
    hnum.div hden (sinc_pi_mul_ne_zero ht0 ht1)
  exact hquot.add (by fun_prop)

private theorem contDiffAt_beurlingJHatOneChart
    {t : ℝ} (ht0 : 1 / 2 ≤ t) (ht1 : t ≤ 1) :
    ContDiffAt ℝ ∞ beurlingJHatOneChart t := by
  have hden :
      ContDiffAt ℝ ∞
        (fun s : ℝ => Real.sinc (Real.pi * (1 - s))) t :=
    contDiff_realSinc.contDiffAt.comp t (by fun_prop)
  have hnum :
      ContDiffAt ℝ ∞
        (fun s : ℝ => s * Real.cos (Real.pi * s)) t := by
    fun_prop
  have hquot :=
    hnum.div hden (sinc_pi_one_sub_ne_zero ht0 ht1)
  exact hquot.add (by fun_prop)

theorem beurlingJHat_eq_zeroChart
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    beurlingJHat t = beurlingJHatZeroChart t := by
  rcases eq_or_ne t 0 with rfl | htne
  · simp [beurlingJHatZeroChart]
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htne)
    have habs : |t| = t := abs_of_pos htpos
    have htlt : |t| < 1 := by rw [habs]; linarith
    have harg : Real.pi * t ≠ 0 :=
      mul_ne_zero Real.pi_ne_zero htne
    rw [beurlingJHat_of_ne_zero_of_abs_lt_one htne htlt,
      Real.cot_eq_cos_div_sin]
    unfold beurlingJHatZeroChart
    rw [Real.sinc_of_ne_zero harg]
    rw [habs]
    field_simp

theorem beurlingJHat_eq_oneChart
    {t : ℝ} (ht0 : 1 / 2 ≤ t) (ht1 : t ≤ 1) :
    beurlingJHat t = beurlingJHatOneChart t := by
  rcases eq_or_ne t 1 with rfl | htne
  · norm_num [beurlingJHatOneChart]
  · have htpos : 0 < t := by linarith
    have htlt : t < 1 := lt_of_le_of_ne ht1 htne
    have habs : |t| = t := abs_of_pos htpos
    have h1t : 0 < 1 - t := sub_pos.mpr htlt
    have hsin :
        Real.sin (Real.pi * t) =
          Real.sin (Real.pi * (1 - t)) := by
      have harg :
          Real.pi * (1 - t) =
            Real.pi - Real.pi * t := by ring
      rw [harg, Real.sin_pi_sub]
    have harg : Real.pi * (1 - t) ≠ 0 :=
      mul_ne_zero Real.pi_ne_zero h1t.ne'
    rw [beurlingJHat_of_ne_zero_of_abs_lt_one
      (by linarith) (by simpa [habs] using htlt),
      Real.cot_eq_cos_div_sin, hsin]
    unfold beurlingJHatOneChart
    rw [Real.sinc_of_ne_zero harg]
    rw [habs]
    field_simp

/-! ## The two-integration-by-parts engine -/

/-- Positive Fourier character in Mathlib's inverse-transform convention. -/
noncomputable def beurlingPositiveCharacter (t x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * t * x)

/-- Derivative frequency `2πix`. -/
noncomputable def beurlingAngularFrequency (x : ℝ) : ℂ :=
  2 * Real.pi * Complex.I * x

theorem norm_beurlingPositiveCharacter (t x : ℝ) :
    ‖beurlingPositiveCharacter t x‖ = 1 := by
  unfold beurlingPositiveCharacter
  rw [show
      (2 : ℂ) * Real.pi * Complex.I * t * x =
        ((2 * Real.pi * (t * x) : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem norm_beurlingAngularFrequency (x : ℝ) :
    ‖beurlingAngularFrequency x‖ = 2 * Real.pi * |x| := by
  unfold beurlingAngularFrequency
  rw [show
      (2 : ℂ) * Real.pi * Complex.I * x =
        ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2),
    abs_of_pos Real.pi_pos]

theorem beurlingAngularFrequency_ne_zero
    {x : ℝ} (hx : x ≠ 0) :
    beurlingAngularFrequency x ≠ 0 := by
  unfold beurlingAngularFrequency
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero)
    (by exact_mod_cast hx)

theorem beurlingPositiveCharacter_eq_exp_frequency
    (t x : ℝ) :
    beurlingPositiveCharacter t x =
      Complex.exp (beurlingAngularFrequency x * (t : ℂ)) := by
  unfold beurlingPositiveCharacter beurlingAngularFrequency
  congr 1
  ring

theorem hasDerivAt_beurlingPositiveCharacter
    (x t : ℝ) :
    HasDerivAt (fun s : ℝ => beurlingPositiveCharacter s x)
      (beurlingAngularFrequency x *
        beurlingPositiveCharacter t x) t := by
  have hof :
      HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have hlin :
      HasDerivAt
        (fun s : ℝ => beurlingAngularFrequency x * (s : ℂ))
        (beurlingAngularFrequency x) t := by
    simpa using hof.const_mul (beurlingAngularFrequency x)
  have hexp := hlin.cexp
  have hgoal :
      HasDerivAt
        (fun s : ℝ =>
          Complex.exp (beurlingAngularFrequency x * (s : ℂ)))
        (beurlingAngularFrequency x *
          beurlingPositiveCharacter t x) t := by
    rw [beurlingPositiveCharacter_eq_exp_frequency, mul_comm]
    exact hexp
  refine hgoal.congr_of_eventuallyEq ?_
  filter_upwards with s
  rw [beurlingPositiveCharacter_eq_exp_frequency]

theorem hasDerivAt_beurlingPositiveCharacter_antideriv
    {x : ℝ} (hx : x ≠ 0) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ =>
        (beurlingAngularFrequency x)⁻¹ *
          beurlingPositiveCharacter s x)
      (beurlingPositiveCharacter t x) t := by
  have h :=
    (hasDerivAt_beurlingPositiveCharacter x t).const_mul
      (beurlingAngularFrequency x)⁻¹
  have heq :
      (beurlingAngularFrequency x)⁻¹ *
          (beurlingAngularFrequency x *
            beurlingPositiveCharacter t x) =
        beurlingPositiveCharacter t x := by
    rw [← mul_assoc, inv_mul_cancel₀
      (beurlingAngularFrequency_ne_zero hx), one_mul]
  rwa [heq] at h

/--
First integration by parts on one smooth frequency piece.  Derivatives are
required only on the open interior, so the lemma applies to one-sided
smooth charts meeting at corners.
-/
theorem beurlingOneIBP
    {x : ℝ} (hx : x ≠ 0) {a b : ℝ} (hab : a ≤ b)
    {f f' : ℝ → ℂ}
    (hfc : ContinuousOn f (uIcc a b))
    (hf : ∀ t ∈ Ioo a b,
      HasDerivWithinAt f (f' t) (Ioi t) t)
    (hf' : IntervalIntegrable f' volume a b) :
    (∫ t in a..b, f t * beurlingPositiveCharacter t x) =
      (beurlingAngularFrequency x)⁻¹ *
          (f b * beurlingPositiveCharacter b x -
            f a * beurlingPositiveCharacter a x)
        - (beurlingAngularFrequency x)⁻¹ *
          ∫ t in a..b,
            f' t * beurlingPositiveCharacter t x := by
  let Φ : ℝ → ℂ := fun t =>
    (beurlingAngularFrequency x)⁻¹ *
      beurlingPositiveCharacter t x
  have hΦc : ContinuousOn Φ (uIcc a b) := by
    apply Continuous.continuousOn
    unfold Φ beurlingPositiveCharacter
    fun_prop
  have hΦd :
      ∀ t ∈ Ioo (min a b) (max a b),
        HasDerivWithinAt Φ (beurlingPositiveCharacter t x)
          (Ioi t) t := by
    intro t _
    exact
      (hasDerivAt_beurlingPositiveCharacter_antideriv hx t).hasDerivWithinAt
  have hfd :
      ∀ t ∈ Ioo (min a b) (max a b),
        HasDerivWithinAt f (f' t) (Ioi t) t := by
    simpa [min_eq_left hab, max_eq_right hab] using hf
  have hcharInt :
      IntervalIntegrable
        (fun t => beurlingPositiveCharacter t x) volume a b := by
    apply Continuous.intervalIntegrable
    unfold beurlingPositiveCharacter
    fun_prop
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
      (u := f) (v := Φ) (u' := f')
      (v' := fun t => beurlingPositiveCharacter t x)
      hfc hΦc hfd hΦd hf' hcharInt
  rw [hparts]
  simp only [Φ]
  rw [show
      ∀ t : ℝ,
        f t * ((beurlingAngularFrequency x)⁻¹ *
          beurlingPositiveCharacter t x) =
        (beurlingAngularFrequency x)⁻¹ *
          (f t * beurlingPositiveCharacter t x) from fun t => by ring]
  rw [show
      (∫ t in a..b,
        f' t * ((beurlingAngularFrequency x)⁻¹ *
          beurlingPositiveCharacter t x)) =
        (beurlingAngularFrequency x)⁻¹ *
          ∫ t in a..b,
            f' t * beurlingPositiveCharacter t x by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro t _
    ring]
  ring

/-- Two integrations by parts on one smooth frequency piece. -/
theorem beurlingTwoIBP
    {x : ℝ} (hx : x ≠ 0) {a b : ℝ} (hab : a ≤ b)
    {f f' f'' : ℝ → ℂ}
    (hfc : ContinuousOn f (uIcc a b))
    (hf : ∀ t ∈ Ioo a b,
      HasDerivWithinAt f (f' t) (Ioi t) t)
    (hf'c : ContinuousOn f' (uIcc a b))
    (hf'd : ∀ t ∈ Ioo a b,
      HasDerivWithinAt f' (f'' t) (Ioi t) t)
    (hf' : IntervalIntegrable f' volume a b)
    (hf'' : IntervalIntegrable f'' volume a b) :
    (∫ t in a..b, f t * beurlingPositiveCharacter t x) =
      (beurlingAngularFrequency x)⁻¹ *
          (f b * beurlingPositiveCharacter b x -
            f a * beurlingPositiveCharacter a x)
        - (beurlingAngularFrequency x)⁻¹ ^ 2 *
          (f' b * beurlingPositiveCharacter b x -
            f' a * beurlingPositiveCharacter a x)
        + (beurlingAngularFrequency x)⁻¹ ^ 2 *
          ∫ t in a..b,
            f'' t * beurlingPositiveCharacter t x := by
  rw [beurlingOneIBP hx hab hfc hf hf',
    beurlingOneIBP hx hab hf'c hf'd hf'']
  ring

/--
Regularity and integrability data required to integrate one Beurling-kernel
piece by parts twice.
-/
structure BeurlingTwoIBPPieceData
    (a b : ℝ) (f : ℝ → ℂ) : Prop where
  continuousOn : ContinuousOn f (uIcc a b)
  hasDerivWithinAt :
    ∀ t ∈ Ioo a b,
      HasDerivWithinAt f (deriv f t) (Ioi t) t
  continuousOnDeriv : ContinuousOn (deriv f) (uIcc a b)
  hasSecondDerivWithinAt :
    ∀ t ∈ Ioo a b,
      HasDerivWithinAt (deriv f) (deriv (deriv f) t) (Ioi t) t
  intervalIntegrableDeriv :
    IntervalIntegrable (deriv f) volume a b
  intervalIntegrableSecondDeriv :
    IntervalIntegrable (deriv (deriv f)) volume a b

private theorem twoIBPPieceData_of_contDiffAt
    {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℂ}
    (hf : ∀ t ∈ Icc a b, ContDiffAt ℝ ∞ f t) :
    BeurlingTwoIBPPieceData a b f := by
  have hcont : ContinuousOn f (uIcc a b) := by
    rw [uIcc_of_le hab]
    intro t ht
    exact (hf t ht).continuousAt.continuousWithinAt
  have hderivCont :
      ContinuousOn (deriv f) (uIcc a b) := by
    rw [uIcc_of_le hab]
    intro t ht
    have hd : ContDiffAt ℝ ∞ (deriv f) t :=
      (hf t ht).derivWithin (m := ∞) (by simp)
    exact hd.continuousAt.continuousWithinAt
  have hsecondCont :
      ContinuousOn (deriv (deriv f)) (uIcc a b) := by
    rw [uIcc_of_le hab]
    intro t ht
    have hd : ContDiffAt ℝ ∞ (deriv f) t :=
      (hf t ht).derivWithin (m := ∞) (by simp)
    have hdd : ContDiffAt ℝ ∞ (deriv (deriv f)) t :=
      hd.derivWithin (m := ∞) (by simp)
    exact hdd.continuousAt.continuousWithinAt
  refine
    { continuousOn := hcont
      hasDerivWithinAt := ?_
      continuousOnDeriv := hderivCont
      hasSecondDerivWithinAt := ?_
      intervalIntegrableDeriv :=
        hderivCont.intervalIntegrable
      intervalIntegrableSecondDeriv :=
        hsecondCont.intervalIntegrable }
  · intro t ht
    have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
    exact ((hf t ht').differentiableAt (by simp)).hasDerivAt.hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
    have hd : ContDiffAt ℝ ∞ (deriv f) t :=
      (hf t ht').derivWithin (m := ∞) (by simp)
    exact (hd.differentiableAt (by simp)).hasDerivAt.hasDerivWithinAt

/-- Complex zero-endpoint chart. -/
noncomputable def beurlingJHatZeroChartC (t : ℝ) : ℂ :=
  (beurlingJHatZeroChart t : ℂ)

/-- Complex one-endpoint chart. -/
noncomputable def beurlingJHatOneChartC (t : ℝ) : ℂ :=
  (beurlingJHatOneChart t : ℂ)

private theorem contDiffAt_beurlingJHatZeroChartC
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    ContDiffAt ℝ ∞ beurlingJHatZeroChartC t := by
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp t
    (contDiffAt_beurlingJHatZeroChart ht0 ht1)

private theorem contDiffAt_beurlingJHatOneChartC
    {t : ℝ} (ht0 : 1 / 2 ≤ t) (ht1 : t ≤ 1) :
    ContDiffAt ℝ ∞ beurlingJHatOneChartC t := by
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp t
    (contDiffAt_beurlingJHatOneChart ht0 ht1)

private theorem zeroChartPieceData :
    BeurlingTwoIBPPieceData 0 (1 / 2)
      beurlingJHatZeroChartC := by
  apply twoIBPPieceData_of_contDiffAt (by norm_num)
  intro t ht
  exact contDiffAt_beurlingJHatZeroChartC ht.1 ht.2

private theorem oneChartPieceData :
    BeurlingTwoIBPPieceData (1 / 2) 1
      beurlingJHatOneChartC := by
  apply twoIBPPieceData_of_contDiffAt (by norm_num)
  intro t ht
  exact contDiffAt_beurlingJHatOneChartC ht.1 ht.2

/-- Reflected zero chart for `[-1/2,0]`. -/
noncomputable def beurlingJHatNegZeroChartC (t : ℝ) : ℂ :=
  beurlingJHatZeroChartC (-t)

/-- Reflected one chart for `[-1,-1/2]`. -/
noncomputable def beurlingJHatNegOneChartC (t : ℝ) : ℂ :=
  beurlingJHatOneChartC (-t)

private theorem negZeroChartPieceData :
    BeurlingTwoIBPPieceData (-1 / 2) 0
      beurlingJHatNegZeroChartC := by
  apply twoIBPPieceData_of_contDiffAt (by norm_num)
  intro t ht
  have hpos : 0 ≤ -t := by linarith [ht.2]
  have hhalf : -t ≤ 1 / 2 := by linarith [ht.1]
  exact
    (contDiffAt_beurlingJHatZeroChartC hpos hhalf).comp t
      (by fun_prop)

private theorem negOneChartPieceData :
    BeurlingTwoIBPPieceData (-1) (-1 / 2)
      beurlingJHatNegOneChartC := by
  apply twoIBPPieceData_of_contDiffAt (by norm_num)
  intro t ht
  have hhalf : 1 / 2 ≤ -t := by linarith [ht.2]
  have hone : -t ≤ 1 := by linarith [ht.1]
  exact
    (contDiffAt_beurlingJHatOneChartC hhalf hone).comp t
      (by fun_prop)

private theorem beurlingJHatC_eq_zeroChartC
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    beurlingJHatC t = beurlingJHatZeroChartC t := by
  unfold beurlingJHatC beurlingJHatZeroChartC
  rw [beurlingJHat_eq_zeroChart ht0 ht1]

private theorem beurlingJHatC_eq_oneChartC
    {t : ℝ} (ht0 : 1 / 2 ≤ t) (ht1 : t ≤ 1) :
    beurlingJHatC t = beurlingJHatOneChartC t := by
  unfold beurlingJHatC beurlingJHatOneChartC
  rw [beurlingJHat_eq_oneChart ht0 ht1]

private theorem beurlingJHatC_eq_negZeroChartC
    {t : ℝ} (ht0 : -1 / 2 ≤ t) (ht1 : t ≤ 0) :
    beurlingJHatC t = beurlingJHatNegZeroChartC t := by
  change (beurlingJHat t : ℂ) =
    (beurlingJHatZeroChart (-t) : ℂ)
  rw [← beurlingJHat_neg t,
    beurlingJHat_eq_zeroChart (by linarith) (by linarith)]

private theorem beurlingJHatC_eq_negOneChartC
    {t : ℝ} (ht0 : -1 ≤ t) (ht1 : t ≤ -1 / 2) :
    beurlingJHatC t = beurlingJHatNegOneChartC t := by
  change (beurlingJHat t : ℂ) =
    (beurlingJHatOneChart (-t) : ℂ)
  rw [← beurlingJHat_neg t,
    beurlingJHat_eq_oneChart (by linarith) (by linarith)]

private theorem beurlingPositiveCharacter_eq_mathlibKernel
    (t x : ℝ) :
    beurlingPositiveCharacter t x =
      Complex.exp
        ((↑(2 * Real.pi * ⟪t, x⟫) : ℂ) * Complex.I) := by
  unfold beurlingPositiveCharacter
  congr 1
  simp
  ring

theorem beurlingJ_eq_intervalIntegral (x : ℝ) :
    beurlingJ x =
      ∫ t in (-1 : ℝ)..1,
        beurlingJHatC t * beurlingPositiveCharacter t x := by
  rw [beurlingJ, fourierInv_eq']
  have hkernel :
      (fun t : ℝ =>
        Complex.exp
            ((↑(2 * Real.pi * ⟪t, x⟫) : ℂ) * Complex.I) •
          beurlingJHatC t) =
        fun t : ℝ =>
          beurlingJHatC t * beurlingPositiveCharacter t x := by
    funext t
    rw [smul_eq_mul, beurlingPositiveCharacter_eq_mathlibKernel,
      mul_comm]
  rw [hkernel]
  let g : ℝ → ℂ := fun t =>
    beurlingJHatC t * beurlingPositiveCharacter t x
  have hfull :
      (∫ t : ℝ, g t) = ∫ t in Ioc (-1 : ℝ) 1, g t := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    rw [mem_Ioc, not_and_or] at ht
    have habs : 1 ≤ |t| := by
      rcases ht with hleft | hright
      · rw [le_abs]
        exact Or.inr (by linarith)
      · rw [le_abs]
        exact Or.inl (by linarith)
    change
      beurlingJHatC t * beurlingPositiveCharacter t x = 0
    rw [beurlingJHatC_eq_zero_of_one_le_abs habs, zero_mul]
  rw [hfull, intervalIntegral.integral_of_le (by norm_num)]

private theorem continuous_beurlingJFrequencyIntegrand (x : ℝ) :
    Continuous
      (fun t : ℝ =>
        beurlingJHatC t * beurlingPositiveCharacter t x) := by
  exact continuous_beurlingJHatC.mul (by
    unfold beurlingPositiveCharacter
    fun_prop)

/-- Exact four-chart decomposition of the inverse transform. -/
theorem beurlingJ_eq_four_chart_integrals (x : ℝ) :
    beurlingJ x =
        (∫ t in (-1 : ℝ)..(-1 / 2),
          beurlingJHatNegOneChartC t *
            beurlingPositiveCharacter t x)
      + (∫ t in (-1 / 2 : ℝ)..0,
          beurlingJHatNegZeroChartC t *
            beurlingPositiveCharacter t x)
      + (∫ t in (0 : ℝ)..(1 / 2),
          beurlingJHatZeroChartC t *
            beurlingPositiveCharacter t x)
      + (∫ t in (1 / 2 : ℝ)..1,
          beurlingJHatOneChartC t *
            beurlingPositiveCharacter t x) := by
  rw [beurlingJ_eq_intervalIntegral]
  let g : ℝ → ℂ := fun t =>
    beurlingJHatC t * beurlingPositiveCharacter t x
  have hg := continuous_beurlingJFrequencyIntegrand x
  have hsplit1 :=
    intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable (μ := volume)
        (-1 : ℝ) (-1 / 2 : ℝ))
      (hg.intervalIntegrable (μ := volume)
        (-1 / 2 : ℝ) (1 : ℝ))
  have hsplit2 :=
    intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable (μ := volume)
        (-1 / 2 : ℝ) (0 : ℝ))
      (hg.intervalIntegrable (μ := volume)
        (0 : ℝ) (1 : ℝ))
  have hsplit3 :=
    intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable (μ := volume)
        (0 : ℝ) (1 / 2 : ℝ))
      (hg.intervalIntegrable (μ := volume)
        (1 / 2 : ℝ) (1 : ℝ))
  rw [← hsplit1, ← hsplit2, ← hsplit3]
  have hchart1 :
      (∫ t in (-1 : ℝ)..(-1 / 2),
        beurlingJHatC t * beurlingPositiveCharacter t x) =
      ∫ t in (-1 : ℝ)..(-1 / 2),
        beurlingJHatNegOneChartC t *
          beurlingPositiveCharacter t x := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (-1 : ℝ) (-1 / 2) := by
      simpa [uIcc_of_le (by norm_num :
        (-1 : ℝ) ≤ -1 / 2)] using ht
    change
      beurlingJHatC t * beurlingPositiveCharacter t x =
        beurlingJHatNegOneChartC t *
          beurlingPositiveCharacter t x
    rw [beurlingJHatC_eq_negOneChartC ht'.1 ht'.2]
  have hchart2 :
      (∫ t in (-1 / 2 : ℝ)..0,
        beurlingJHatC t * beurlingPositiveCharacter t x) =
      ∫ t in (-1 / 2 : ℝ)..0,
        beurlingJHatNegZeroChartC t *
          beurlingPositiveCharacter t x := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (-1 / 2 : ℝ) 0 := by
      simpa [uIcc_of_le (by norm_num :
        (-1 / 2 : ℝ) ≤ 0)] using ht
    change
      beurlingJHatC t * beurlingPositiveCharacter t x =
        beurlingJHatNegZeroChartC t *
          beurlingPositiveCharacter t x
    rw [beurlingJHatC_eq_negZeroChartC ht'.1 ht'.2]
  have hchart3 :
      (∫ t in (0 : ℝ)..(1 / 2),
        beurlingJHatC t * beurlingPositiveCharacter t x) =
      ∫ t in (0 : ℝ)..(1 / 2),
        beurlingJHatZeroChartC t *
          beurlingPositiveCharacter t x := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) (1 / 2) := by
      simpa [uIcc_of_le (by norm_num :
        (0 : ℝ) ≤ 1 / 2)] using ht
    change
      beurlingJHatC t * beurlingPositiveCharacter t x =
        beurlingJHatZeroChartC t *
          beurlingPositiveCharacter t x
    rw [beurlingJHatC_eq_zeroChartC ht'.1 ht'.2]
  have hchart4 :
      (∫ t in (1 / 2 : ℝ)..1,
        beurlingJHatC t * beurlingPositiveCharacter t x) =
      ∫ t in (1 / 2 : ℝ)..1,
        beurlingJHatOneChartC t *
          beurlingPositiveCharacter t x := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (1 / 2 : ℝ) 1 := by
      rw [uIcc_of_le (by norm_num :
        (1 / 2 : ℝ) ≤ 1)] at ht
      exact ht
    change
      beurlingJHatC t * beurlingPositiveCharacter t x =
        beurlingJHatOneChartC t *
          beurlingPositiveCharacter t x
    rw [beurlingJHatC_eq_oneChartC ht'.1 ht'.2]
  rw [hchart1, hchart2, hchart3, hchart4]
  ring

/-- The bounded remainder left after all first-order boundary terms cancel. -/
noncomputable def beurlingJSecondOrderRemainder (x : ℝ) : ℂ :=
    (-(deriv beurlingJHatNegOneChartC (-1 / 2) *
          beurlingPositiveCharacter (-1 / 2) x -
        deriv beurlingJHatNegOneChartC (-1) *
          beurlingPositiveCharacter (-1) x)
      + ∫ t in (-1 : ℝ)..(-1 / 2),
          deriv (deriv beurlingJHatNegOneChartC) t *
            beurlingPositiveCharacter t x)
  + (-(deriv beurlingJHatNegZeroChartC 0 *
          beurlingPositiveCharacter 0 x -
        deriv beurlingJHatNegZeroChartC (-1 / 2) *
          beurlingPositiveCharacter (-1 / 2) x)
      + ∫ t in (-1 / 2 : ℝ)..0,
          deriv (deriv beurlingJHatNegZeroChartC) t *
            beurlingPositiveCharacter t x)
  + (-(deriv beurlingJHatZeroChartC (1 / 2) *
          beurlingPositiveCharacter (1 / 2) x -
        deriv beurlingJHatZeroChartC 0 *
          beurlingPositiveCharacter 0 x)
      + ∫ t in (0 : ℝ)..(1 / 2),
          deriv (deriv beurlingJHatZeroChartC) t *
            beurlingPositiveCharacter t x)
  + (-(deriv beurlingJHatOneChartC 1 *
          beurlingPositiveCharacter 1 x -
        deriv beurlingJHatOneChartC (1 / 2) *
          beurlingPositiveCharacter (1 / 2) x)
      + ∫ t in (1 / 2 : ℝ)..1,
          deriv (deriv beurlingJHatOneChartC) t *
            beurlingPositiveCharacter t x)

private theorem negOneChart_outer_zero :
    beurlingJHatNegOneChartC (-1) = 0 := by
  rw [← beurlingJHatC_eq_negOneChartC
    (by norm_num) (by norm_num)]
  change (beurlingJHat (-1) : ℂ) = 0
  rw [beurlingJHat_eq_zero_of_one_le_abs (by norm_num)]
  norm_num

private theorem oneChart_outer_zero :
    beurlingJHatOneChartC 1 = 0 := by
  rw [← beurlingJHatC_eq_oneChartC
    (by norm_num) (by norm_num)]
  simp [beurlingJHatC]

private theorem charts_match_neg_half :
    beurlingJHatNegOneChartC (-1 / 2) =
      beurlingJHatNegZeroChartC (-1 / 2) := by
  rw [← beurlingJHatC_eq_negOneChartC
      (by norm_num) (by norm_num),
    ← beurlingJHatC_eq_negZeroChartC
      (by norm_num) (by norm_num)]

private theorem charts_match_zero :
    beurlingJHatNegZeroChartC 0 =
      beurlingJHatZeroChartC 0 := by
  rw [← beurlingJHatC_eq_negZeroChartC
      (by norm_num) (by norm_num),
    ← beurlingJHatC_eq_zeroChartC
      (by norm_num) (by norm_num)]

private theorem charts_match_half :
    beurlingJHatZeroChartC (1 / 2) =
      beurlingJHatOneChartC (1 / 2) := by
  rw [← beurlingJHatC_eq_zeroChartC
      (by norm_num) (by norm_num),
    ← beurlingJHatC_eq_oneChartC
      (by norm_num) (by norm_num)]

theorem beurlingJ_eq_angular_inv_sq_mul_remainder
    {x : ℝ} (hx : x ≠ 0) :
    beurlingJ x =
      (beurlingAngularFrequency x)⁻¹ ^ 2 *
        beurlingJSecondOrderRemainder x := by
  have h1 := beurlingTwoIBP (x := x) hx
    (by norm_num : (-1 : ℝ) ≤ -1 / 2)
    negOneChartPieceData.continuousOn
    negOneChartPieceData.hasDerivWithinAt
    negOneChartPieceData.continuousOnDeriv
    negOneChartPieceData.hasSecondDerivWithinAt
    negOneChartPieceData.intervalIntegrableDeriv
    negOneChartPieceData.intervalIntegrableSecondDeriv
  have h2 := beurlingTwoIBP (x := x) hx
    (by norm_num : (-1 / 2 : ℝ) ≤ 0)
    negZeroChartPieceData.continuousOn
    negZeroChartPieceData.hasDerivWithinAt
    negZeroChartPieceData.continuousOnDeriv
    negZeroChartPieceData.hasSecondDerivWithinAt
    negZeroChartPieceData.intervalIntegrableDeriv
    negZeroChartPieceData.intervalIntegrableSecondDeriv
  have h3 := beurlingTwoIBP (x := x) hx
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    zeroChartPieceData.continuousOn
    zeroChartPieceData.hasDerivWithinAt
    zeroChartPieceData.continuousOnDeriv
    zeroChartPieceData.hasSecondDerivWithinAt
    zeroChartPieceData.intervalIntegrableDeriv
    zeroChartPieceData.intervalIntegrableSecondDeriv
  have h4 := beurlingTwoIBP (x := x) hx
    (by norm_num : (1 / 2 : ℝ) ≤ 1)
    oneChartPieceData.continuousOn
    oneChartPieceData.hasDerivWithinAt
    oneChartPieceData.continuousOnDeriv
    oneChartPieceData.hasSecondDerivWithinAt
    oneChartPieceData.intervalIntegrableDeriv
    oneChartPieceData.intervalIntegrableSecondDeriv
  rw [beurlingJ_eq_four_chart_integrals, h1, h2, h3, h4,
    negOneChart_outer_zero, oneChart_outer_zero,
    charts_match_neg_half, charts_match_zero, charts_match_half]
  unfold beurlingJSecondOrderRemainder
  ring

private theorem norm_beurlingSecondOrderPiece_le
    {a b x : ℝ} (hab : a ≤ b)
    (f' f'' : ℝ → ℂ) :
    ‖-(f' b * beurlingPositiveCharacter b x -
          f' a * beurlingPositiveCharacter a x)
        + ∫ t in a..b,
            f'' t * beurlingPositiveCharacter t x‖ ≤
      ‖f' a‖ + ‖f' b‖ + ∫ t in a..b, ‖f'' t‖ := by
  have hboundary :
      ‖-(f' b * beurlingPositiveCharacter b x -
          f' a * beurlingPositiveCharacter a x)‖ ≤
        ‖f' b‖ + ‖f' a‖ := by
    rw [norm_neg]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul,
      norm_beurlingPositiveCharacter,
      norm_beurlingPositiveCharacter]
    ring_nf
    exact le_rfl
  have hintegral :
      ‖∫ t in a..b,
          f'' t * beurlingPositiveCharacter t x‖ ≤
        ∫ t in a..b, ‖f'' t‖ := by
    refine
      (intervalIntegral.norm_integral_le_integral_norm hab).trans ?_
    apply le_of_eq
    refine intervalIntegral.integral_congr ?_
    intro t _
    change
      ‖f'' t * beurlingPositiveCharacter t x‖ = ‖f'' t‖
    rw [norm_mul, norm_beurlingPositiveCharacter, mul_one]
  calc
    ‖-(f' b * beurlingPositiveCharacter b x -
          f' a * beurlingPositiveCharacter a x)
        + ∫ t in a..b,
            f'' t * beurlingPositiveCharacter t x‖
        ≤ ‖-(f' b * beurlingPositiveCharacter b x -
              f' a * beurlingPositiveCharacter a x)‖
          + ‖∫ t in a..b,
              f'' t * beurlingPositiveCharacter t x‖ :=
            norm_add_le _ _
    _ ≤ (‖f' b‖ + ‖f' a‖) +
          ∫ t in a..b, ‖f'' t‖ :=
        add_le_add hboundary hintegral
    _ = ‖f' a‖ + ‖f' b‖ +
          ∫ t in a..b, ‖f'' t‖ := by ring

/-- Uniform norm budget for the four second-order chart remainders. -/
noncomputable def beurlingJDecayBudget : ℝ :=
    (‖deriv beurlingJHatNegOneChartC (-1)‖
      + ‖deriv beurlingJHatNegOneChartC (-1 / 2)‖
      + ∫ t in (-1 : ℝ)..(-1 / 2),
          ‖deriv (deriv beurlingJHatNegOneChartC) t‖)
  + (‖deriv beurlingJHatNegZeroChartC (-1 / 2)‖
      + ‖deriv beurlingJHatNegZeroChartC 0‖
      + ∫ t in (-1 / 2 : ℝ)..0,
          ‖deriv (deriv beurlingJHatNegZeroChartC) t‖)
  + (‖deriv beurlingJHatZeroChartC 0‖
      + ‖deriv beurlingJHatZeroChartC (1 / 2)‖
      + ∫ t in (0 : ℝ)..(1 / 2),
          ‖deriv (deriv beurlingJHatZeroChartC) t‖)
  + (‖deriv beurlingJHatOneChartC (1 / 2)‖
      + ‖deriv beurlingJHatOneChartC 1‖
      + ∫ t in (1 / 2 : ℝ)..1,
          ‖deriv (deriv beurlingJHatOneChartC) t‖)

theorem norm_beurlingJSecondOrderRemainder_le (x : ℝ) :
    ‖beurlingJSecondOrderRemainder x‖ ≤
      beurlingJDecayBudget := by
  have h1 := norm_beurlingSecondOrderPiece_le
    (x := x) (by norm_num : (-1 : ℝ) ≤ -1 / 2)
    (deriv beurlingJHatNegOneChartC)
    (deriv (deriv beurlingJHatNegOneChartC))
  have h2 := norm_beurlingSecondOrderPiece_le
    (x := x) (by norm_num : (-1 / 2 : ℝ) ≤ 0)
    (deriv beurlingJHatNegZeroChartC)
    (deriv (deriv beurlingJHatNegZeroChartC))
  have h3 := norm_beurlingSecondOrderPiece_le
    (x := x) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (deriv beurlingJHatZeroChartC)
    (deriv (deriv beurlingJHatZeroChartC))
  have h4 := norm_beurlingSecondOrderPiece_le
    (x := x) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (deriv beurlingJHatOneChartC)
    (deriv (deriv beurlingJHatOneChartC))
  unfold beurlingJSecondOrderRemainder beurlingJDecayBudget
  calc
    ‖_ + _ + _ + _‖
        ≤ (‖_‖ + ‖_‖) + ‖_‖ + ‖_‖ := by
          exact (norm_add_le _ _).trans
            (add_le_add
              ((norm_add_le _ _).trans
                (add_le_add (norm_add_le _ _) le_rfl))
              le_rfl)
    _ ≤ _ := by
      gcongr

theorem beurlingJDecayBudget_nonneg :
    0 ≤ beurlingJDecayBudget :=
  (norm_nonneg (beurlingJSecondOrderRemainder 0)).trans
    (norm_beurlingJSecondOrderRemainder_le 0)

theorem norm_angularFrequency_inv_sq (x : ℝ) :
    (‖beurlingAngularFrequency x‖⁻¹) ^ 2 =
      ((2 * Real.pi) ^ 2)⁻¹ * (x ^ 2)⁻¹ := by
  rw [norm_beurlingAngularFrequency, mul_inv, mul_pow,
    inv_pow, inv_pow, ← sq_abs x]

/-- The inverse-transform kernel has a uniform quadratic tail. -/
theorem norm_beurlingJ_le_quadratic
    {x : ℝ} (hx : x ≠ 0) :
    ‖beurlingJ x‖ ≤
      (((2 * Real.pi) ^ 2)⁻¹ * beurlingJDecayBudget) *
        (x ^ 2)⁻¹ := by
  rw [beurlingJ_eq_angular_inv_sq_mul_remainder hx,
    norm_mul, norm_pow, norm_inv]
  refine
    (mul_le_mul_of_nonneg_left
      (norm_beurlingJSecondOrderRemainder_le x)
      (sq_nonneg _)).trans_eq ?_
  rw [norm_angularFrequency_inv_sq]
  ring

/-- Frequency `L¹` norm controlling the spatial kernel near the origin. -/
noncomputable def beurlingJHatL1 : ℝ :=
  ∫ t in (-1 : ℝ)..1, ‖beurlingJHatC t‖

theorem beurlingJHatL1_nonneg :
    0 ≤ beurlingJHatL1 := by
  unfold beurlingJHatL1
  exact intervalIntegral.integral_nonneg (by norm_num)
    (fun t _ => norm_nonneg _)

theorem norm_beurlingJ_le_hatL1 (x : ℝ) :
    ‖beurlingJ x‖ ≤ beurlingJHatL1 := by
  rw [beurlingJ_eq_intervalIntegral]
  refine
    (intervalIntegral.norm_integral_le_integral_norm
      (by norm_num : (-1 : ℝ) ≤ 1)).trans ?_
  apply le_of_eq
  unfold beurlingJHatL1
  refine intervalIntegral.integral_congr ?_
  intro t _
  change
    ‖beurlingJHatC t * beurlingPositiveCharacter t x‖ =
      ‖beurlingJHatC t‖
  rw [norm_mul, norm_beurlingPositiveCharacter, mul_one]

/--
A constant bound plus a quadratic tail give an integrable
`(1+x²)⁻¹` envelope.
-/
private theorem norm_beurlingJ_le_inv_one_add_sq
    (x : ℝ) :
    ‖beurlingJ x‖ ≤
      (2 * max beurlingJHatL1
        (((2 * Real.pi) ^ 2)⁻¹ * beurlingJDecayBudget)) *
          (1 + x ^ 2)⁻¹ := by
  let C₂ : ℝ :=
    ((2 * Real.pi) ^ 2)⁻¹ * beurlingJDecayBudget
  have hC₂ : 0 ≤ C₂ := by
    dsimp [C₂]
    exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _))
      beurlingJDecayBudget_nonneg
  have hmax0 :
      beurlingJHatL1 ≤ max beurlingJHatL1 C₂ :=
    le_max_left _ _
  have hmax2 : C₂ ≤ max beurlingJHatL1 C₂ :=
    le_max_right _ _
  have hmaxNonneg : 0 ≤ max beurlingJHatL1 C₂ :=
    beurlingJHatL1_nonneg.trans hmax0
  have hden : 0 < 1 + x ^ 2 := by positivity
  by_cases hx : |x| ≤ 1
  · have hx2 : x ^ 2 ≤ 1 := by
      nlinarith [sq_abs x, abs_nonneg x]
    have hhalf : (1 : ℝ) ≤ 2 * (1 + x ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ hden]
      nlinarith [hx2]
    calc
      ‖beurlingJ x‖ ≤ beurlingJHatL1 :=
        norm_beurlingJ_le_hatL1 x
      _ = beurlingJHatL1 * 1 := by ring
      _ ≤ max beurlingJHatL1 C₂ *
          (2 * (1 + x ^ 2)⁻¹) :=
        mul_le_mul hmax0 hhalf (by norm_num) hmaxNonneg
      _ = 2 * max beurlingJHatL1 C₂ *
          (1 + x ^ 2)⁻¹ := by ring
  · have hxlt : 1 < |x| := lt_of_not_ge hx
    have hxne : x ≠ 0 := by
      intro h
      subst x
      norm_num at hxlt
    have hx2 : 1 ≤ x ^ 2 := by
      nlinarith [sq_abs x, abs_nonneg x]
    have hx2pos : 0 < x ^ 2 := by linarith
    have hkey :
        (x ^ 2)⁻¹ ≤ 2 * (1 + x ^ 2)⁻¹ := by
      rw [inv_le_iff_one_le_mul₀ hx2pos]
      rw [show
          (2 : ℝ) * (1 + x ^ 2)⁻¹ * x ^ 2 =
            2 * x ^ 2 * (1 + x ^ 2)⁻¹ by ring,
        le_mul_inv_iff₀ hden]
      nlinarith [hx2]
    calc
      ‖beurlingJ x‖ ≤ C₂ * (x ^ 2)⁻¹ := by
        dsimp [C₂]
        exact norm_beurlingJ_le_quadratic hxne
      _ ≤ max beurlingJHatL1 C₂ *
          (2 * (1 + x ^ 2)⁻¹) :=
        mul_le_mul hmax2 hkey (by positivity) hmaxNonneg
      _ = 2 * max beurlingJHatL1 C₂ *
          (1 + x ^ 2)⁻¹ := by ring

/-- The spatial Vaaler kernel is integrable, unconditionally. -/
theorem integrable_beurlingJ :
    Integrable beurlingJ := by
  let C : ℝ :=
    2 * max beurlingJHatL1
      (((2 * Real.pi) ^ 2)⁻¹ * beurlingJDecayBudget)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by norm_num)
      (beurlingJHatL1_nonneg.trans (le_max_left _ _))
  have hmajorant :
      Integrable (fun x : ℝ => C * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul C
  refine hmajorant.mono' continuous_beurlingJ.aestronglyMeasurable ?_
  filter_upwards with x
  exact norm_beurlingJ_le_inv_one_add_sq x

/-- Unconditional Fourier transform of the Vaaler kernel. -/
theorem fourier_beurlingJ (t : ℝ) :
    𝓕 beurlingJ t = beurlingJHatC t :=
  fourier_beurlingJ_eq_beurlingJHatC_of_integrable
    integrable_beurlingJ t

end Probability
end CertifiedJL
