/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The Prawitz smoothing kernel

We use the compactly supported version of the classical Prawitz kernel

`K(t) = (1 - |t|) / 2
  + I * ((1 - |t|) cot (πt) + sign(t) / π) / 2`

on `|t| < 1`, and set it to zero at and beyond the endpoints.  At zero,
Lean's totalized cotangent gives `K(0) = 1/2`; this value is immaterial to
Lebesgue integration.  The kernel itself has a principal-value `1/t`
singularity at zero and is not claimed to be integrable across zero.

The genuinely removable object is `t * K(t)`.  We package its continuous
extension separately using `Real.sinc`; its value at zero is `I / (2π)`.
-/

open Filter MeasureTheory Set
open scoped ComplexConjugate
open scoped Topology

namespace CertifiedJL
namespace Probability

/-- Real part of the compactly supported Prawitz kernel. -/
noncomputable def prawitzKernelReal (t : ℝ) : ℝ :=
  if |t| < 1 then (1 - |t|) / 2 else 0

/-- Imaginary part of the compactly supported Prawitz kernel. -/
noncomputable def prawitzKernelImag (t : ℝ) : ℝ :=
  if |t| < 1 then
    ((1 - |t|) * Real.cot (Real.pi * t) + Real.sign t / Real.pi) / 2
  else 0

/-- The compactly supported complex Prawitz kernel. -/
noncomputable def prawitzKernel (t : ℝ) : ℂ :=
  (prawitzKernelReal t : ℂ) + (prawitzKernelImag t : ℂ) * Complex.I

/--
The continuous extension of `t * cot (πt)` at zero.
-/
noncomputable def regularizedFrequencyCot (t : ℝ) : ℝ :=
  Real.cos (Real.pi * t) /
    (Real.pi * Real.sinc (Real.pi * t))

/--
The compactly supported continuous-at-zero extension of `t * K(t)`.

Only continuity at zero is asserted here; the strict support convention
introduces endpoint values separately.
-/
noncomputable def regularizedPrawitzFrequencyKernel (t : ℝ) : ℂ :=
  if |t| < 1 then
    ((t * (1 - |t|) / 2 : ℝ) : ℂ) +
      ((((1 - |t|) * regularizedFrequencyCot t +
          |t| / Real.pi) / 2 : ℝ) : ℂ) * Complex.I
  else 0

/--
The frequency-kernel remainder after subtracting its removable value at
zero.  This is the numerator that appears when regularizing the Prawitz
`1/t` term.
-/
noncomputable def prawitzFrequencyRemainder (t : ℝ) : ℂ :=
  regularizedPrawitzFrequencyKernel t -
    Complex.I / (2 * Real.pi)

@[simp]
theorem prawitzKernelReal_zero :
    prawitzKernelReal 0 = 1 / 2 := by
  simp [prawitzKernelReal]

@[simp]
theorem prawitzKernelImag_zero :
    prawitzKernelImag 0 = 0 := by
  rw [prawitzKernelImag]
  simp only [abs_zero, zero_lt_one, ↓reduceIte, sub_zero, mul_zero,
    Real.sign_zero, zero_div, add_zero, zero_div]
  rw [Real.cot_eq_cos_div_sin]
  simp

@[simp]
theorem prawitzKernel_zero :
    prawitzKernel 0 = (1 / 2 : ℝ) := by
  simp [prawitzKernel]

@[simp]
theorem prawitzKernelReal_one :
    prawitzKernelReal 1 = 0 := by
  simp [prawitzKernelReal]

@[simp]
theorem prawitzKernelImag_one :
    prawitzKernelImag 1 = 0 := by
  simp [prawitzKernelImag]

@[simp]
theorem prawitzKernel_one :
    prawitzKernel 1 = 0 := by
  simp [prawitzKernel]

@[simp]
theorem prawitzKernel_neg_one :
    prawitzKernel (-1) = 0 := by
  simp [prawitzKernel, prawitzKernelReal, prawitzKernelImag]

theorem prawitzKernelReal_of_abs_lt_one {t : ℝ} (ht : |t| < 1) :
    prawitzKernelReal t = (1 - |t|) / 2 := by
  simp [prawitzKernelReal, ht]

theorem prawitzKernelImag_of_abs_lt_one {t : ℝ} (ht : |t| < 1) :
    prawitzKernelImag t =
      ((1 - |t|) * Real.cot (Real.pi * t) +
        Real.sign t / Real.pi) / 2 := by
  simp [prawitzKernelImag, ht]

theorem prawitzKernel_eq_zero_of_one_le_abs {t : ℝ} (ht : 1 ≤ |t|) :
    prawitzKernel t = 0 := by
  simp [prawitzKernel, prawitzKernelReal, prawitzKernelImag,
    not_lt.mpr ht]

theorem prawitzKernel_ne_zero_imp_abs_lt_one {t : ℝ}
    (ht : prawitzKernel t ≠ 0) :
    |t| < 1 := by
  by_contra h
  exact ht (prawitzKernel_eq_zero_of_one_le_abs (not_lt.mp h))

private theorem real_cot_neg (t : ℝ) :
    Real.cot (-t) = -Real.cot t := by
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
  simp only [Real.cos_neg, Real.sin_neg]
  ring

theorem prawitzKernelReal_neg (t : ℝ) :
    prawitzKernelReal (-t) = prawitzKernelReal t := by
  simp [prawitzKernelReal]

theorem prawitzKernelImag_neg (t : ℝ) :
    prawitzKernelImag (-t) = -prawitzKernelImag t := by
  rw [prawitzKernelImag, prawitzKernelImag]
  simp only [abs_neg, Real.sign_neg, mul_neg, real_cot_neg]
  split_ifs
  · ring
  · simp

/-- The Prawitz kernel has Hermitian parity. -/
theorem prawitzKernel_neg (t : ℝ) :
    prawitzKernel (-t) = conj (prawitzKernel t) := by
  rw [prawitzKernel, prawitzKernel, prawitzKernelReal_neg,
    prawitzKernelImag_neg]
  simp

private theorem measurable_real_sign :
    Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite
    (measurableSet_lt measurable_id measurable_const)
    measurable_const
    (Measurable.ite
      (measurableSet_lt measurable_const measurable_id)
      measurable_const measurable_const)

private theorem measurable_real_cot_comp_pi_mul :
    Measurable (fun t : ℝ => Real.cot (Real.pi * t)) := by
  simp_rw [Real.cot_eq_cos_div_sin]
  exact (Real.continuous_cos.measurable.comp
      (measurable_const.mul measurable_id)).div
    (Real.continuous_sin.measurable.comp
      (measurable_const.mul measurable_id))

theorem measurable_prawitzKernelReal :
    Measurable prawitzKernelReal := by
  unfold prawitzKernelReal
  exact Measurable.ite
    (measurableSet_lt continuous_abs.measurable measurable_const)
    (by fun_prop) measurable_const

theorem measurable_prawitzKernelImag :
    Measurable prawitzKernelImag := by
  unfold prawitzKernelImag
  have habs : Measurable (fun t : ℝ => |t|) :=
    continuous_abs.measurable
  have honeSub : Measurable (fun t : ℝ => 1 - |t|) :=
    measurable_const.sub habs
  exact Measurable.ite
    (measurableSet_lt continuous_abs.measurable measurable_const)
    (((honeSub.mul measurable_real_cot_comp_pi_mul).add
      (measurable_real_sign.div measurable_const)).div measurable_const)
    measurable_const

theorem measurable_prawitzKernel :
    Measurable prawitzKernel := by
  unfold prawitzKernel
  exact ((Complex.continuous_ofReal.measurable.comp
      measurable_prawitzKernelReal).add
    ((Complex.continuous_ofReal.measurable.comp
      measurable_prawitzKernelImag).mul measurable_const))

theorem measurable_regularizedFrequencyCot :
    Measurable regularizedFrequencyCot := by
  unfold regularizedFrequencyCot
  fun_prop

theorem measurable_regularizedPrawitzFrequencyKernel :
    Measurable regularizedPrawitzFrequencyKernel := by
  unfold regularizedPrawitzFrequencyKernel
  have habs : Measurable (fun t : ℝ => |t|) :=
    continuous_abs.measurable
  have honeSub : Measurable (fun t : ℝ => 1 - |t|) :=
    measurable_const.sub habs
  have hre : Measurable (fun t : ℝ => t * (1 - |t|) / 2) :=
    (measurable_id.mul honeSub).div measurable_const
  have him : Measurable (fun t : ℝ =>
      ((1 - |t|) * regularizedFrequencyCot t +
        |t| / Real.pi) / 2) :=
    ((honeSub.mul measurable_regularizedFrequencyCot).add
      (habs.div measurable_const)).div measurable_const
  exact Measurable.ite
    (measurableSet_lt continuous_abs.measurable measurable_const)
    ((Complex.continuous_ofReal.measurable.comp hre).add
      ((Complex.continuous_ofReal.measurable.comp him).mul measurable_const))
    measurable_const

theorem measurable_prawitzFrequencyRemainder :
    Measurable prawitzFrequencyRemainder := by
  unfold prawitzFrequencyRemainder
  exact measurable_regularizedPrawitzFrequencyKernel.sub measurable_const

/-- The real part of the Prawitz kernel lies between zero and one half. -/
theorem prawitzKernelReal_mem_Icc (t : ℝ) :
    prawitzKernelReal t ∈ Icc 0 (1 / 2) := by
  unfold prawitzKernelReal
  split_ifs with ht
  · constructor
    · positivity
    · have habs : |t| ≥ 0 := abs_nonneg t
      linarith
  · norm_num

/-- Elementary componentwise norm bound for the complex kernel. -/
theorem norm_prawitzKernel_le (t : ℝ) :
    ‖prawitzKernel t‖ ≤
      |prawitzKernelReal t| + |prawitzKernelImag t| := by
  unfold prawitzKernel
  calc
    ‖(prawitzKernelReal t : ℂ) +
        (prawitzKernelImag t : ℂ) * Complex.I‖ ≤
        ‖(prawitzKernelReal t : ℂ)‖ +
          ‖(prawitzKernelImag t : ℂ) * Complex.I‖ :=
      norm_add_le _ _
    _ = |prawitzKernelReal t| + |prawitzKernelImag t| := by simp

@[simp]
theorem regularizedFrequencyCot_zero :
    regularizedFrequencyCot 0 = 1 / Real.pi := by
  simp [regularizedFrequencyCot]

@[simp]
theorem regularizedPrawitzFrequencyKernel_zero :
    regularizedPrawitzFrequencyKernel 0 =
      Complex.I / (2 * Real.pi) := by
  rw [regularizedPrawitzFrequencyKernel]
  simp [regularizedFrequencyCot]
  ring

@[simp]
theorem prawitzFrequencyRemainder_zero :
    prawitzFrequencyRemainder 0 = 0 := by
  simp [prawitzFrequencyRemainder]

private theorem real_mul_sign_eq_abs (t : ℝ) :
    t * Real.sign t = |t| := by
  obtain ht | rfl | ht := lt_trichotomy t 0
  · rw [Real.sign_of_neg ht, abs_of_neg ht]
    ring
  · simp
  · rw [Real.sign_of_pos ht, abs_of_pos ht]
    ring

private theorem sin_pi_mul_ne_zero_of_abs_lt_one_of_ne_zero
    {t : ℝ} (ht : |t| < 1) (hzero : t ≠ 0) :
    Real.sin (Real.pi * t) ≠ 0 := by
  have ht' := abs_lt.mp ht
  have hlower : -Real.pi < Real.pi * t := by
    nlinarith [Real.pi_pos]
  have hupper : Real.pi * t < Real.pi := by
    nlinarith [Real.pi_pos]
  rw [ne_eq, Real.sin_eq_zero_iff_of_lt_of_lt hlower hupper]
  exact mul_ne_zero Real.pi_ne_zero hzero

/-- Away from zero, the sinc formula is exactly `t * cot (πt)`. -/
theorem regularizedFrequencyCot_eq_mul_cot
    {t : ℝ} (ht : |t| < 1) (hzero : t ≠ 0) :
    regularizedFrequencyCot t =
      t * Real.cot (Real.pi * t) := by
  have hpit : Real.pi * t ≠ 0 :=
    mul_ne_zero Real.pi_ne_zero hzero
  have hsin :=
    sin_pi_mul_ne_zero_of_abs_lt_one_of_ne_zero ht hzero
  rw [regularizedFrequencyCot, Real.sinc_of_ne_zero hpit,
    Real.cot_eq_cos_div_sin]
  field_simp

/--
Away from zero, the regularized frequency kernel agrees exactly with
frequency times the classical Prawitz kernel.
-/
theorem regularizedPrawitzFrequencyKernel_eq_mul
    {t : ℝ} (ht : |t| < 1) (hzero : t ≠ 0) :
    regularizedPrawitzFrequencyKernel t =
      (t : ℂ) * prawitzKernel t := by
  rw [regularizedPrawitzFrequencyKernel, if_pos ht]
  rw [prawitzKernel, prawitzKernelReal_of_abs_lt_one ht,
    prawitzKernelImag_of_abs_lt_one ht]
  rw [regularizedFrequencyCot_eq_mul_cot ht hzero]
  rw [← real_mul_sign_eq_abs t]
  push_cast
  ring

/-- The regularized cotangent factor is continuous at zero. -/
@[fun_prop]
theorem continuousAt_regularizedFrequencyCot_zero :
    ContinuousAt regularizedFrequencyCot 0 := by
  unfold regularizedFrequencyCot
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · simp

/--
The singularity of `t * K(t)` at zero is removable, with limiting value
`I / (2π)`.
-/
theorem continuousAt_regularizedPrawitzFrequencyKernel_zero :
    ContinuousAt regularizedPrawitzFrequencyKernel 0 := by
  have hinner : ContinuousAt (fun t : ℝ =>
      ((t * (1 - |t|) / 2 : ℝ) : ℂ) +
        ((((1 - |t|) * regularizedFrequencyCot t +
            |t| / Real.pi) / 2 : ℝ) : ℂ) * Complex.I) 0 := by
    fun_prop
  apply hinner.congr_of_eventuallyEq
  have hopen : IsOpen {t : ℝ | |t| < 1} :=
    isOpen_lt continuous_abs continuous_const
  have hzero : (0 : ℝ) ∈ {t : ℝ | |t| < 1} := by simp
  filter_upwards [hopen.mem_nhds hzero] with t ht
  simp [regularizedPrawitzFrequencyKernel, ht]

/-- The regularized Prawitz frequency remainder vanishes continuously at zero. -/
theorem continuousAt_prawitzFrequencyRemainder_zero :
    ContinuousAt prawitzFrequencyRemainder 0 := by
  unfold prawitzFrequencyRemainder
  exact continuousAt_regularizedPrawitzFrequencyKernel_zero.sub
    continuousAt_const

theorem tendsto_mul_prawitzKernel_zero :
    Tendsto (fun t : ℝ => regularizedPrawitzFrequencyKernel t)
      (𝓝 0) (𝓝 (Complex.I / (2 * Real.pi))) := by
  rw [← regularizedPrawitzFrequencyKernel_zero]
  exact continuousAt_regularizedPrawitzFrequencyKernel_zero

private theorem sinc_pi_mul_ne_zero_of_abs_lt_one
    {t : ℝ} (ht : |t| < 1) :
    Real.sinc (Real.pi * t) ≠ 0 := by
  by_cases hzero : t = 0
  · subst t
    simp
  · have hpit : Real.pi * t ≠ 0 :=
      mul_ne_zero Real.pi_ne_zero hzero
    rw [Real.sinc_of_ne_zero hpit]
    exact div_ne_zero
      (sin_pi_mul_ne_zero_of_abs_lt_one_of_ne_zero ht hzero)
      hpit

theorem continuousAt_regularizedFrequencyCot_of_abs_lt_one
    {t : ℝ} (ht : |t| < 1) :
    ContinuousAt regularizedFrequencyCot t := by
  unfold regularizedFrequencyCot
  exact (by fun_prop : ContinuousAt
      (fun s : ℝ => Real.cos (Real.pi * s)) t).div
    (by fun_prop : ContinuousAt
      (fun s : ℝ => Real.pi * Real.sinc (Real.pi * s)) t)
    (mul_ne_zero Real.pi_ne_zero
      (sinc_pi_mul_ne_zero_of_abs_lt_one ht))

/-- The regularized frequency kernel is continuous throughout its interior. -/
theorem continuousAt_regularizedPrawitzFrequencyKernel_of_abs_lt_one
    {t : ℝ} (ht : |t| < 1) :
    ContinuousAt regularizedPrawitzFrequencyKernel t := by
  have habs : ContinuousAt (fun s : ℝ => |s|) t :=
    continuous_abs.continuousAt
  have honeSub : ContinuousAt (fun s : ℝ => 1 - |s|) t :=
    continuousAt_const.sub habs
  have hcot := continuousAt_regularizedFrequencyCot_of_abs_lt_one ht
  have hre : ContinuousAt (fun s : ℝ => s * (1 - |s|) / 2) t :=
    (continuousAt_id.mul honeSub).div_const _
  have him : ContinuousAt (fun s : ℝ =>
      ((1 - |s|) * regularizedFrequencyCot s +
        |s| / Real.pi) / 2) t :=
    ((honeSub.mul hcot).add (habs.div_const _)).div_const _
  have hinner : ContinuousAt (fun s : ℝ =>
      ((s * (1 - |s|) / 2 : ℝ) : ℂ) +
        ((((1 - |s|) * regularizedFrequencyCot s +
            |s| / Real.pi) / 2 : ℝ) : ℂ) * Complex.I) t :=
    (Complex.continuous_ofReal.continuousAt.comp hre).add
      ((Complex.continuous_ofReal.continuousAt.comp him).mul
        continuousAt_const)
  apply hinner.congr_of_eventuallyEq
  have hopen : IsOpen {s : ℝ | |s| < 1} :=
    isOpen_lt continuous_abs continuous_const
  filter_upwards [hopen.mem_nhds ht] with s hs
  simp [regularizedPrawitzFrequencyKernel, hs]

theorem continuousAt_prawitzFrequencyRemainder_of_abs_lt_one
    {t : ℝ} (ht : |t| < 1) :
    ContinuousAt prawitzFrequencyRemainder t := by
  unfold prawitzFrequencyRemainder
  exact (continuousAt_regularizedPrawitzFrequencyKernel_of_abs_lt_one ht).sub
    continuousAt_const

/--
The regularized frequency kernel is integrable on every closed interval
strictly inside the support.
-/
theorem integrableOn_regularizedPrawitzFrequencyKernel_Icc
    {r : ℝ} (hr : r < 1) :
    IntegrableOn regularizedPrawitzFrequencyKernel (Icc (-r) r) volume := by
  apply ContinuousOn.integrableOn_Icc (μ := volume)
  intro t ht
  apply (continuousAt_regularizedPrawitzFrequencyKernel_of_abs_lt_one ?_).continuousWithinAt
  rw [abs_lt]
  constructor <;> linarith [ht.1, ht.2]

theorem integrableOn_prawitzFrequencyRemainder_Icc
    {r : ℝ} (hr : r < 1) :
    IntegrableOn prawitzFrequencyRemainder (Icc (-r) r) volume := by
  apply ContinuousOn.integrableOn_Icc (μ := volume)
  intro t ht
  apply (continuousAt_prawitzFrequencyRemainder_of_abs_lt_one ?_).continuousWithinAt
  rw [abs_lt]
  constructor <;> linarith [ht.1, ht.2]

/--
The norm singularity of the raw kernel is exactly isolated by the
regularized frequency kernel.
-/
theorem norm_regularizedPrawitzFrequencyKernel_eq
    {t : ℝ} (ht : |t| < 1) (hzero : t ≠ 0) :
    ‖regularizedPrawitzFrequencyKernel t‖ =
      |t| * ‖prawitzKernel t‖ := by
  rw [regularizedPrawitzFrequencyKernel_eq_mul ht hzero, norm_mul]
  simp

theorem norm_prawitzKernel_eq_div
    {t : ℝ} (ht : |t| < 1) (hzero : t ≠ 0) :
    ‖prawitzKernel t‖ =
      ‖regularizedPrawitzFrequencyKernel t‖ / |t| := by
  rw [norm_regularizedPrawitzFrequencyKernel_eq ht hzero]
  exact (mul_div_cancel_left₀ _ (abs_ne_zero.mpr hzero)).symm

private theorem continuousAt_real_cot_pi_mul
    {t : ℝ} (ht : |t| < 1) (hzero : t ≠ 0) :
    ContinuousAt (fun s : ℝ => Real.cot (Real.pi * s)) t := by
  simp_rw [Real.cot_eq_cos_div_sin]
  exact (by fun_prop : ContinuousAt
      (fun s : ℝ => Real.cos (Real.pi * s)) t).div
    (by fun_prop : ContinuousAt
      (fun s : ℝ => Real.sin (Real.pi * s)) t)
    (sin_pi_mul_ne_zero_of_abs_lt_one_of_ne_zero ht hzero)

private theorem continuousAt_real_sign_of_ne_zero
    {t : ℝ} (hzero : t ≠ 0) :
    ContinuousAt Real.sign t := by
  obtain ht | ht := lt_or_gt_of_ne hzero
  · have hconst : ContinuousAt (fun _ : ℝ => (-1 : ℝ)) t :=
      continuousAt_const
    apply hconst.congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
    simp [Real.sign_of_neg hs]
  · have hconst : ContinuousAt (fun _ : ℝ => (1 : ℝ)) t :=
      continuousAt_const
    apply hconst.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    simp [Real.sign_of_pos hs]

/-- The Prawitz kernel is continuous at every nonzero interior point. -/
theorem continuousAt_prawitzKernel_of_abs_lt_one_of_ne_zero
    {t : ℝ} (ht : |t| < 1) (hzero : t ≠ 0) :
    ContinuousAt prawitzKernel t := by
  have habs : ContinuousAt (fun s : ℝ => |s|) t :=
    continuous_abs.continuousAt
  have honeSub : ContinuousAt (fun s : ℝ => 1 - |s|) t :=
    continuousAt_const.sub habs
  have hcot := continuousAt_real_cot_pi_mul ht hzero
  have hsign : ContinuousAt Real.sign t :=
    continuousAt_real_sign_of_ne_zero hzero
  have hre : ContinuousAt (fun s : ℝ => (1 - |s|) / 2) t :=
    honeSub.div_const _
  have him : ContinuousAt (fun s : ℝ =>
      ((1 - |s|) * Real.cot (Real.pi * s) +
        Real.sign s / Real.pi) / 2) t :=
    ((honeSub.mul hcot).add (hsign.div_const _)).div_const _
  have hinner : ContinuousAt (fun s : ℝ =>
      (((1 - |s|) / 2 : ℝ) : ℂ) +
        ((((1 - |s|) * Real.cot (Real.pi * s) +
            Real.sign s / Real.pi) / 2 : ℝ) : ℂ) * Complex.I) t :=
    (Complex.continuous_ofReal.continuousAt.comp hre).add
      ((Complex.continuous_ofReal.continuousAt.comp him).mul
        continuousAt_const)
  apply hinner.congr_of_eventuallyEq
  have hopen : IsOpen {s : ℝ | |s| < 1} :=
    isOpen_lt continuous_abs continuous_const
  filter_upwards [hopen.mem_nhds ht] with s hs
  simp [prawitzKernel, prawitzKernelReal, prawitzKernelImag, hs]

theorem integrableOn_prawitzKernel_Icc_of_pos_of_lt_one
    {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    IntegrableOn prawitzKernel (Icc a b) volume := by
  apply ContinuousOn.integrableOn_Icc (μ := volume)
  intro t ht
  have htpos : 0 < t := ha.trans_le ht.1
  have htlt : t < 1 := ht.2.trans_lt hb
  exact (continuousAt_prawitzKernel_of_abs_lt_one_of_ne_zero
    (by simpa [abs_of_pos htpos] using htlt) htpos.ne').continuousWithinAt

theorem integrableOn_prawitzKernel_Icc_of_neg_of_neg_one_lt
    {a b : ℝ} (ha : -1 < a) (hb : b < 0) :
    IntegrableOn prawitzKernel (Icc a b) volume := by
  apply ContinuousOn.integrableOn_Icc (μ := volume)
  intro t ht
  have htneg : t < 0 := ht.2.trans_lt hb
  have hnegone : -1 < t := ha.trans_le ht.1
  exact (continuousAt_prawitzKernel_of_abs_lt_one_of_ne_zero
    (by
      rw [abs_of_neg htneg]
      linarith)
    htneg.ne).continuousWithinAt

end Probability
end CertifiedJL
