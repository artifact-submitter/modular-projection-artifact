/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Fourier.FourierCDFInversion
import CertifiedJL.Analysis.Fourier.Beurling.Majorant
import CertifiedJL.Analysis.Fourier.Beurling.Frequency
import CertifiedJL.Analysis.Fourier.Prawitz.Kernel
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# The four-term Prawitz smoothing decomposition

This file develops the algebraic and measure-theoretic layer immediately
below the Prawitz inversion inequality.  It fixes the closed-`Iic` CDF and
atom convention, defines the scaled compactly supported kernel and the
principal Fourier reference term, and proves the exact four-term domination
used in the quantitative smoothing argument.

The final passage from the Fourier comparison integral to Kolmogorov
distance is deliberately not postulated here.  It requires a genuine
Prawitz inversion theorem; all declarations below are proved without a
theorem-shaped assumption.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ComplexConjugate ENNReal Topology

namespace CertifiedJL
namespace Probability

/-- The Prawitz kernel at bandwidth `U`, including the `1/U` scaling. -/
noncomputable def scaledPrawitzKernel (U u : ℝ) : ℂ :=
  ((1 / U : ℝ) : ℂ) * prawitzKernel (u / U)

/--
Exact Vaaler-multiplier decomposition of the scaled Prawitz kernel away from
the removable frequency zero.

The real part carries the triangle multiplier with the `1/U` scaling.  The
imaginary part carries `Ĵ(u/U)/(2πu)`; the bandwidth cancels from its
denominator.  This identity fixes the normalization used by the later
Beurling-center Fourier formula.
-/
theorem scaledPrawitzKernel_eq_multipliers
    {U u : ℝ} (hU : U ≠ 0) (hu : u ≠ 0) :
    scaledPrawitzKernel U u =
      ((beurlingKHat (u / U) / (2 * U) : ℝ) : ℂ) +
        (((beurlingJHat (u / U) /
          (2 * Real.pi * u) : ℝ) : ℂ) * Complex.I) := by
  have hratio : u / U ≠ 0 := div_ne_zero hu hU
  rw [scaledPrawitzKernel,
    prawitzKernel_eq_multipliers hratio]
  push_cast
  field_simp [hU, hu, Real.pi_ne_zero]

/--
The compactly supported Prawitz transform integrand for a characteristic
function.  The closed support convention includes the endpoints, where the
kernel itself is zero.
-/
noncomputable def truncatedPrawitzIntegrand
    (μ : Measure ℝ) (U u : ℝ) : ℂ :=
  if |u| ≤ U then
    scaledPrawitzKernel U u * charFun μ u
  else 0

/--
Norm of the difference between the truncated Prawitz transform of `μ` and
the principal Fourier transform of `ν`.
-/
noncomputable def prawitzFourierComparison
    (μ ν : Measure ℝ) (U u : ℝ) : ℝ :=
  ‖truncatedPrawitzIntegrand μ U u -
    principalCDFKernel u * charFun ν u‖

/-- Core characteristic-function discrepancy term. -/
noncomputable def prawitzCoreDiscrepancyTerm
    (μ ν : Measure ℝ) (U₀ U u : ℝ) : ℝ :=
  if |u| ≤ U₀ then
    ‖scaledPrawitzKernel U u‖ * ‖charFun μ u - charFun ν u‖
  else 0

/-- Outer part of the truncated characteristic function. -/
noncomputable def prawitzOuterKernelTerm
    (μ : Measure ℝ) (U₀ U u : ℝ) : ℝ :=
  if U₀ < |u| ∧ |u| ≤ U then
    ‖scaledPrawitzKernel U u‖ * ‖charFun μ u‖
  else 0

/-- Core correction from the scaled Prawitz kernel to `I/(2πu)`. -/
noncomputable def prawitzCoreCorrectionTerm
    (ν : Measure ℝ) (U₀ U u : ℝ) : ℝ :=
  if |u| ≤ U₀ then
    ‖scaledPrawitzKernel U u - principalCDFKernel u‖ *
      ‖charFun ν u‖
  else 0

/-- Principal-reference tail beyond the core cutoff. -/
noncomputable def prawitzReferenceTailTerm
    (ν : Measure ℝ) (U₀ u : ℝ) : ℝ :=
  if U₀ < |u| then
    ‖principalCDFKernel u‖ * ‖charFun ν u‖
  else 0

theorem scaledPrawitzKernel_eq_zero_of_abs_ge
    {U u : ℝ} (hU : 0 < U) (hu : U ≤ |u|) :
    scaledPrawitzKernel U u = 0 := by
  unfold scaledPrawitzKernel
  rw [prawitzKernel_eq_zero_of_one_le_abs]
  · simp
  · rw [abs_div, abs_of_pos hU]
    exact (le_div_iff₀ hU).2 (by simpa [mul_comm] using hu)

theorem scaledPrawitzKernel_neg (U u : ℝ) :
    scaledPrawitzKernel U (-u) =
      conj (scaledPrawitzKernel U u) := by
  unfold scaledPrawitzKernel
  rw [neg_div, prawitzKernel_neg]
  simp

theorem prawitzCoreDiscrepancyTerm_nonneg
    (μ ν : Measure ℝ) (U₀ U u : ℝ) :
    0 ≤ prawitzCoreDiscrepancyTerm μ ν U₀ U u := by
  unfold prawitzCoreDiscrepancyTerm
  split_ifs <;> positivity

theorem prawitzOuterKernelTerm_nonneg
    (μ : Measure ℝ) (U₀ U u : ℝ) :
    0 ≤ prawitzOuterKernelTerm μ U₀ U u := by
  unfold prawitzOuterKernelTerm
  split_ifs <;> positivity

theorem prawitzCoreCorrectionTerm_nonneg
    (ν : Measure ℝ) (U₀ U u : ℝ) :
    0 ≤ prawitzCoreCorrectionTerm ν U₀ U u := by
  unfold prawitzCoreCorrectionTerm
  split_ifs <;> positivity

theorem prawitzReferenceTailTerm_nonneg
    (ν : Measure ℝ) (U₀ u : ℝ) :
    0 ≤ prawitzReferenceTailTerm ν U₀ u := by
  unfold prawitzReferenceTailTerm
  split_ifs <;> positivity

theorem measurable_scaledPrawitzKernel (U : ℝ) :
    Measurable (scaledPrawitzKernel U) := by
  unfold scaledPrawitzKernel
  exact measurable_const.mul
    (measurable_prawitzKernel.comp
      (measurable_id.div measurable_const))

theorem measurable_truncatedPrawitzIntegrand
    (μ : Measure ℝ) [IsFiniteMeasure μ] (U : ℝ) :
    Measurable (truncatedPrawitzIntegrand μ U) := by
  unfold truncatedPrawitzIntegrand
  exact Measurable.ite
    (measurableSet_le continuous_abs.measurable measurable_const)
    ((measurable_scaledPrawitzKernel U).mul measurable_charFun)
    measurable_const

theorem measurable_prawitzFourierComparison
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (U : ℝ) :
    Measurable (prawitzFourierComparison μ ν U) := by
  unfold prawitzFourierComparison
  exact ((measurable_truncatedPrawitzIntegrand μ U).sub
    (measurable_principalCDFKernel.mul measurable_charFun)).norm

theorem measurable_prawitzCoreDiscrepancyTerm
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (U₀ U : ℝ) :
    Measurable (prawitzCoreDiscrepancyTerm μ ν U₀ U) := by
  unfold prawitzCoreDiscrepancyTerm
  exact Measurable.ite
    (measurableSet_le continuous_abs.measurable measurable_const)
    ((measurable_scaledPrawitzKernel U).norm.mul
      (measurable_charFun.sub measurable_charFun).norm)
    measurable_const

theorem measurable_prawitzOuterKernelTerm
    (μ : Measure ℝ) [IsFiniteMeasure μ] (U₀ U : ℝ) :
    Measurable (prawitzOuterKernelTerm μ U₀ U) := by
  unfold prawitzOuterKernelTerm
  exact Measurable.ite
    ((measurableSet_lt measurable_const continuous_abs.measurable).inter
      (measurableSet_le continuous_abs.measurable measurable_const))
    ((measurable_scaledPrawitzKernel U).norm.mul
      measurable_charFun.norm)
    measurable_const

theorem measurable_prawitzCoreCorrectionTerm
    (ν : Measure ℝ) [IsFiniteMeasure ν] (U₀ U : ℝ) :
    Measurable (prawitzCoreCorrectionTerm ν U₀ U) := by
  unfold prawitzCoreCorrectionTerm
  exact Measurable.ite
    (measurableSet_le continuous_abs.measurable measurable_const)
    (((measurable_scaledPrawitzKernel U).sub
      measurable_principalCDFKernel).norm.mul measurable_charFun.norm)
    measurable_const

theorem measurable_prawitzReferenceTailTerm
    (ν : Measure ℝ) [IsFiniteMeasure ν] (U₀ : ℝ) :
    Measurable (prawitzReferenceTailTerm ν U₀) := by
  unfold prawitzReferenceTailTerm
  exact Measurable.ite
    (measurableSet_lt measurable_const continuous_abs.measurable)
    (measurable_principalCDFKernel.norm.mul measurable_charFun.norm)
    measurable_const

/-- Sum of the four nonnegative Prawitz comparison terms. -/
noncomputable def prawitzFourTermMajorant
    (μ ν : Measure ℝ) (U₀ U u : ℝ) : ℝ :=
  prawitzCoreDiscrepancyTerm μ ν U₀ U u +
    prawitzOuterKernelTerm μ U₀ U u +
    prawitzCoreCorrectionTerm ν U₀ U u +
    prawitzReferenceTailTerm ν U₀ u

theorem prawitzFourTermMajorant_nonneg
    (μ ν : Measure ℝ) (U₀ U u : ℝ) :
    0 ≤ prawitzFourTermMajorant μ ν U₀ U u := by
  unfold prawitzFourTermMajorant
  exact add_nonneg
    (add_nonneg
      (add_nonneg
        (prawitzCoreDiscrepancyTerm_nonneg μ ν U₀ U u)
        (prawitzOuterKernelTerm_nonneg μ U₀ U u))
      (prawitzCoreCorrectionTerm_nonneg ν U₀ U u))
    (prawitzReferenceTailTerm_nonneg ν U₀ u)

theorem measurable_prawitzFourTermMajorant
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (U₀ U : ℝ) :
    Measurable (prawitzFourTermMajorant μ ν U₀ U) := by
  unfold prawitzFourTermMajorant
  exact (((measurable_prawitzCoreDiscrepancyTerm μ ν U₀ U).add
    (measurable_prawitzOuterKernelTerm μ U₀ U)).add
    (measurable_prawitzCoreCorrectionTerm ν U₀ U)).add
    (measurable_prawitzReferenceTailTerm ν U₀)

/--
Exact pointwise four-term domination behind the Prawitz smoothing bound.

The core uses the decomposition
`K_U f - P g = K_U (f-g) + (K_U-P)g`; the outer region uses the
triangle inequality, and beyond the kernel support only the principal
reference tail remains.
-/
theorem prawitzFourierComparison_le_four_terms
    (μ ν : Measure ℝ) {U₀ U u : ℝ}
    (hcut : U₀ ≤ U) :
    prawitzFourierComparison μ ν U u ≤
      prawitzCoreDiscrepancyTerm μ ν U₀ U u +
      prawitzOuterKernelTerm μ U₀ U u +
      prawitzCoreCorrectionTerm ν U₀ U u +
      prawitzReferenceTailTerm ν U₀ u := by
  by_cases hcore : |u| ≤ U₀
  · have hsupport : |u| ≤ U := hcore.trans hcut
    have hnotOuter : ¬U₀ < |u| := not_lt.mpr hcore
    simp only [prawitzFourierComparison, truncatedPrawitzIntegrand,
      prawitzCoreDiscrepancyTerm, prawitzOuterKernelTerm,
      prawitzCoreCorrectionTerm, prawitzReferenceTailTerm,
      if_pos hcore, if_pos hsupport, hnotOuter, false_and, if_false,
      add_zero]
    let K : ℂ := scaledPrawitzKernel U u
    let P : ℂ := principalCDFKernel u
    let f : ℂ := charFun μ u
    let g : ℂ := charFun ν u
    have hdecomp : K * f - P * g =
        K * (f - g) + (K - P) * g := by ring
    rw [show scaledPrawitzKernel U u * charFun μ u -
          principalCDFKernel u * charFun ν u =
        K * f - P * g by rfl]
    rw [hdecomp]
    calc
      ‖K * (f - g) + (K - P) * g‖ ≤
          ‖K * (f - g)‖ + ‖(K - P) * g‖ :=
        norm_add_le _ _
      _ = ‖K‖ * ‖f - g‖ + ‖K - P‖ * ‖g‖ := by
        rw [norm_mul, norm_mul]
  · have houter : U₀ < |u| := lt_of_not_ge hcore
    by_cases hsupport : |u| ≤ U
    · simp only [prawitzFourierComparison, truncatedPrawitzIntegrand,
        prawitzCoreDiscrepancyTerm, prawitzOuterKernelTerm,
        prawitzCoreCorrectionTerm, prawitzReferenceTailTerm,
        hcore, houter, hsupport, and_self, if_true, if_false,
        zero_add, add_zero]
      calc
        ‖scaledPrawitzKernel U u * charFun μ u -
            principalCDFKernel u * charFun ν u‖ ≤
            ‖scaledPrawitzKernel U u * charFun μ u‖ +
              ‖principalCDFKernel u * charFun ν u‖ :=
          norm_sub_le _ _
        _ = ‖scaledPrawitzKernel U u‖ * ‖charFun μ u‖ +
              ‖principalCDFKernel u‖ * ‖charFun ν u‖ := by
          rw [norm_mul, norm_mul]
    · simp only [prawitzFourierComparison, truncatedPrawitzIntegrand,
        prawitzCoreDiscrepancyTerm, prawitzOuterKernelTerm,
        prawitzCoreCorrectionTerm, prawitzReferenceTailTerm,
        hcore, houter, hsupport, and_false, if_true, if_false,
        zero_sub, norm_neg, zero_add, add_zero, norm_mul]
      exact le_rfl

/--
The pointwise four-term decomposition integrates without any finiteness
assumption by using nonnegative Lebesgue integrals.
-/
theorem lintegral_prawitzFourierComparison_le_fourTermMajorant
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {U₀ U : ℝ} (hcut : U₀ ≤ U) :
    ∫⁻ u, ENNReal.ofReal (prawitzFourierComparison μ ν U u) ∂volume ≤
      ∫⁻ u, ENNReal.ofReal
        (prawitzFourTermMajorant μ ν U₀ U u) ∂volume := by
  apply lintegral_mono
  intro u
  exact ENNReal.ofReal_le_ofReal
    (prawitzFourierComparison_le_four_terms μ ν hcut)

/--
Four-integral form of the Prawitz Fourier comparison bound.
-/
theorem lintegral_prawitzFourierComparison_le_four_integrals
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {U₀ U : ℝ} (hcut : U₀ ≤ U) :
    ∫⁻ u, ENNReal.ofReal (prawitzFourierComparison μ ν U u) ∂volume ≤
      (∫⁻ u, ENNReal.ofReal
          (prawitzCoreDiscrepancyTerm μ ν U₀ U u) ∂volume) +
      (∫⁻ u, ENNReal.ofReal
          (prawitzOuterKernelTerm μ U₀ U u) ∂volume) +
      (∫⁻ u, ENNReal.ofReal
          (prawitzCoreCorrectionTerm ν U₀ U u) ∂volume) +
      (∫⁻ u, ENNReal.ofReal
          (prawitzReferenceTailTerm ν U₀ u) ∂volume) := by
  calc
    (∫⁻ u, ENNReal.ofReal
        (prawitzFourierComparison μ ν U u) ∂volume) ≤
        ∫⁻ u, ENNReal.ofReal
          (prawitzFourTermMajorant μ ν U₀ U u) ∂volume :=
      lintegral_prawitzFourierComparison_le_fourTermMajorant
        μ ν hcut
    _ = ∫⁻ u,
        ENNReal.ofReal (prawitzCoreDiscrepancyTerm μ ν U₀ U u) +
        ENNReal.ofReal (prawitzOuterKernelTerm μ U₀ U u) +
        ENNReal.ofReal (prawitzCoreCorrectionTerm ν U₀ U u) +
        ENNReal.ofReal (prawitzReferenceTailTerm ν U₀ u) ∂volume := by
      apply lintegral_congr
      intro u
      unfold prawitzFourTermMajorant
      rw [ENNReal.ofReal_add
          (add_nonneg
            (add_nonneg
              (prawitzCoreDiscrepancyTerm_nonneg μ ν U₀ U u)
              (prawitzOuterKernelTerm_nonneg μ U₀ U u))
            (prawitzCoreCorrectionTerm_nonneg ν U₀ U u))
          (prawitzReferenceTailTerm_nonneg ν U₀ u)]
      rw [ENNReal.ofReal_add
          (add_nonneg
            (prawitzCoreDiscrepancyTerm_nonneg μ ν U₀ U u)
            (prawitzOuterKernelTerm_nonneg μ U₀ U u))
          (prawitzCoreCorrectionTerm_nonneg ν U₀ U u)]
      rw [ENNReal.ofReal_add
          (prawitzCoreDiscrepancyTerm_nonneg μ ν U₀ U u)
          (prawitzOuterKernelTerm_nonneg μ U₀ U u)]
    _ = _ := by
      rw [lintegral_add_left,
        lintegral_add_left, lintegral_add_left]
      · exact (measurable_prawitzCoreDiscrepancyTerm μ ν U₀ U).ennreal_ofReal
      · exact ((measurable_prawitzCoreDiscrepancyTerm μ ν U₀ U).ennreal_ofReal.add
          (measurable_prawitzOuterKernelTerm μ U₀ U).ennreal_ofReal)
      · exact (((measurable_prawitzCoreDiscrepancyTerm μ ν U₀ U).ennreal_ofReal.add
          (measurable_prawitzOuterKernelTerm μ U₀ U).ennreal_ofReal).add
          (measurable_prawitzCoreCorrectionTerm ν U₀ U).ennreal_ofReal)

/-! ## Deterministic finite-band Beurling bounds -/

theorem beurlingK_le_one (x : ℝ) :
    beurlingK x ≤ 1 := by
  unfold beurlingK
  rw [← sq_abs]
  have h := Real.abs_sinc_le_one (Real.pi * x)
  nlinarith [abs_nonneg (Real.sinc (Real.pi * x))]

theorem scaledBeurlingK_nonneg (T x : ℝ) :
    0 ≤ scaledBeurlingK T x :=
  beurlingK_nonneg (T * x)

theorem scaledBeurlingK_le_one (T x : ℝ) :
    scaledBeurlingK T x ≤ 1 :=
  beurlingK_le_one (T * x)

private theorem neg_one_le_sign (x : ℝ) :
    -1 ≤ Real.sign x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · simp [Real.sign_of_neg hx]
  · simp
  · simp [Real.sign_of_pos hx]

private theorem sign_le_one (x : ℝ) :
    Real.sign x ≤ 1 := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · simp [Real.sign_of_neg hx]
  · simp
  · simp [Real.sign_of_pos hx]

theorem abs_scaledBeurlingH_le_two
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    |scaledBeurlingH T x| ≤ 2 := by
  rw [abs_le]
  constructor
  · have hlow :=
      sign_sub_scaledBeurlingK_le_scaledBeurlingH hT x
    linarith [neg_one_le_sign x,
      scaledBeurlingK_le_one T x]
  · have hupp :=
      scaledBeurlingH_le_sign_add_scaledBeurlingK hT x
    linarith [sign_le_one x,
      scaledBeurlingK_le_one T x]

theorem integrable_scaledBeurlingH
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    Integrable (fun y => scaledBeurlingH T (x - y)) μ := by
  refine Integrable.mono'
    (integrable_const (2 : ℝ))
    (((measurable_scaledBeurlingH T).comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable)
    (ae_of_all μ fun y => ?_)
  rw [Real.norm_eq_abs]
  exact abs_scaledBeurlingH_le_two hT (x - y)

theorem integrable_scaledBeurlingK
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (T x : ℝ) :
    Integrable (fun y => scaledBeurlingK T (x - y)) μ := by
  refine Integrable.mono'
    (integrable_const (1 : ℝ))
    (((continuous_scaledBeurlingK T).measurable.comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable)
    (ae_of_all μ fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg
    (scaledBeurlingK_nonneg T (x - y))]
  exact scaledBeurlingK_le_one T (x - y)

theorem integral_sign_sub
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    ∫ y, Real.sign (x - y) ∂μ =
      2 * (midpointCDF μ x - 1 / 2) := by
  have hfun :
      cdfJumpKernel x =
        fun y => (1 / 2 : ℝ) * Real.sign (x - y) := by
    funext y
    rcases lt_trichotomy y x with hy | rfl | hy
    · simp [cdfJumpKernel, hy, Real.sign_of_pos (sub_pos.mpr hy)]
    · simp [cdfJumpKernel]
    · simp [cdfJumpKernel, hy, not_lt.mpr hy.le,
        Real.sign_of_neg (sub_neg.mpr hy)]
  have hjump := integral_cdfJumpKernel μ x
  rw [hfun, MeasureTheory.integral_const_mul] at hjump
  linarith

/-- Center of the finite-band Beurling approximation to a CDF. -/
noncomputable def beurlingCDFCenter
    (μ : Measure ℝ) (T x : ℝ) : ℝ :=
  1 / 2 + (1 / 2) *
    ∫ y, scaledBeurlingH T (x - y) ∂μ

/-- Nonnegative correction in the finite-band Beurling CDF bounds. -/
noncomputable def beurlingCDFCorrection
    (μ : Measure ℝ) (T x : ℝ) : ℝ :=
  (1 / 2) * ∫ y, scaledBeurlingK T (x - y) ∂μ

theorem beurlingCDFCorrection_nonneg
    (μ : Measure ℝ) (T x : ℝ) :
    0 ≤ beurlingCDFCorrection μ T x := by
  unfold beurlingCDFCorrection
  exact mul_nonneg (by norm_num) <|
    integral_nonneg fun y => scaledBeurlingK_nonneg T (x - y)

/--
The exact deterministic finite-band Beurling enclosure of the midpoint CDF.

This is the measure-integrated form of Vaaler's pointwise
majorant/minorant; it is logically independent of principal-value
inversion.
-/
theorem midpointCDF_mem_beurling_band
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    midpointCDF μ x - beurlingCDFCorrection μ T x ≤
        beurlingCDFCenter μ T x ∧
      beurlingCDFCenter μ T x ≤
        midpointCDF μ x + beurlingCDFCorrection μ T x := by
  have hsign : Integrable (fun y => Real.sign (x - y)) μ := by
    refine Integrable.mono'
      (integrable_const (1 : ℝ))
      ((Measurable.ite
        (measurableSet_lt
          (measurable_const.sub measurable_id) measurable_const)
        measurable_const
        (Measurable.ite
          (measurableSet_lt measurable_const
            (measurable_const.sub measurable_id))
          measurable_const measurable_const)).aestronglyMeasurable)
      (ae_of_all μ fun y => ?_)
    rw [Real.norm_eq_abs]
    rcases lt_trichotomy (x - y) 0 with h | h | h
    · simp [Real.sign_of_neg h]
    · simp [h]
    · simp [Real.sign_of_pos h]
  have hK := integrable_scaledBeurlingK μ T x
  have hH := integrable_scaledBeurlingH μ hT x
  have hlower :
      (∫ y, Real.sign (x - y) -
          scaledBeurlingK T (x - y) ∂μ) ≤
        ∫ y, scaledBeurlingH T (x - y) ∂μ := by
    exact integral_mono_ae (hsign.sub hK) hH
      (ae_of_all μ fun y =>
        sign_sub_scaledBeurlingK_le_scaledBeurlingH hT (x - y))
  have hupper :
      (∫ y, scaledBeurlingH T (x - y) ∂μ) ≤
        ∫ y, Real.sign (x - y) +
          scaledBeurlingK T (x - y) ∂μ := by
    exact integral_mono_ae hH (hsign.add hK)
      (ae_of_all μ fun y =>
        scaledBeurlingH_le_sign_add_scaledBeurlingK hT (x - y))
  rw [MeasureTheory.integral_sub hsign hK,
    integral_sign_sub] at hlower
  rw [MeasureTheory.integral_add hsign hK,
    integral_sign_sub] at hupper
  unfold beurlingCDFCenter beurlingCDFCorrection
  constructor <;> linarith

/-- Closed-`Iic` form, with the half-atom correction kept explicit. -/
theorem cdf_mem_beurling_band
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    cdf μ x - μ.real {x} / 2 -
        beurlingCDFCorrection μ T x ≤
        beurlingCDFCenter μ T x ∧
      beurlingCDFCenter μ T x ≤
        cdf μ x - μ.real {x} / 2 +
          beurlingCDFCorrection μ T x := by
  simpa only [midpointCDF_eq_cdf_sub_half_atom] using
    midpointCDF_mem_beurling_band μ hT x

theorem half_atom_le_beurlingCDFCorrection
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (T x : ℝ) :
    μ.real {x} / 2 ≤ beurlingCDFCorrection μ T x := by
  have hind : Integrable
      (({x} : Set ℝ).indicator (fun _ : ℝ => (1 : ℝ))) μ :=
    Integrable.indicator
      ((integrable_const (1 : ℝ)) :
        Integrable (fun _ : ℝ => (1 : ℝ)) μ)
      (measurableSet_singleton x)
  have hK := integrable_scaledBeurlingK μ T x
  have hmono :
      (∫ y, ({x} : Set ℝ).indicator
          (fun _ : ℝ => (1 : ℝ)) y ∂μ) ≤
        ∫ y, scaledBeurlingK T (x - y) ∂μ := by
    exact integral_mono hind hK fun y => by
      by_cases hy : y = x
      · subst y
        simp [scaledBeurlingK, beurlingK_zero]
      · rw [Set.indicator_of_notMem]
        · exact scaledBeurlingK_nonneg T (x - y)
        · simpa using hy
  have hmass :
      (∫ y, ({x} : Set ℝ).indicator
          (fun _ : ℝ => (1 : ℝ)) y ∂μ) = μ.real {x} := by
    rw [integral_indicator_const (μ := μ) (1 : ℝ)
      (measurableSet_singleton x)]
    simp
  rw [hmass] at hmono
  unfold beurlingCDFCorrection
  linarith

/--
Closed-CDF finite-band enclosure with no separate atom remainder.

The squared-sinc correction already contains half the endpoint atom because
`scaledBeurlingK T 0 = 1`.
-/
theorem cdf_mem_beurling_band_absorbing_atom
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    cdf μ x - beurlingCDFCorrection μ T x ≤
        beurlingCDFCenter μ T x ∧
      beurlingCDFCenter μ T x ≤
        cdf μ x + beurlingCDFCorrection μ T x := by
  let ind : ℝ → ℝ :=
    fun y => (Iic x).indicator (fun _ : ℝ => (1 : ℝ)) y
  let lower : ℝ → ℝ :=
    fun y => 1 / 2 + (1 / 2) * scaledBeurlingH T (x - y) -
      (1 / 2) * scaledBeurlingK T (x - y)
  let upper : ℝ → ℝ :=
    fun y => 1 / 2 + (1 / 2) * scaledBeurlingH T (x - y) +
      (1 / 2) * scaledBeurlingK T (x - y)
  have hind : Integrable ind μ := by
    exact Integrable.indicator
      ((integrable_const (1 : ℝ)) :
        Integrable (fun _ : ℝ => (1 : ℝ)) μ)
      measurableSet_Iic
  have hH := integrable_scaledBeurlingH μ hT x
  have hK := integrable_scaledBeurlingK μ T x
  have hlowerInt : Integrable lower μ := by
    exact ((integrable_const (1 / 2 : ℝ)).add
      (hH.const_mul (1 / 2))).sub (hK.const_mul (1 / 2))
  have hupperInt : Integrable upper μ := by
    exact ((integrable_const (1 / 2 : ℝ)).add
      (hH.const_mul (1 / 2))).add (hK.const_mul (1 / 2))
  have hlowerPoint : ∀ y, lower y ≤ ind y := by
    intro y
    rcases lt_trichotomy y x with hy | rfl | hy
    · have hmin :=
        scaledBeurlingH_le_sign_add_scaledBeurlingK hT (x - y)
      simp only [lower, ind, Set.indicator_of_mem (mem_Iic.mpr hy.le)]
      rw [Real.sign_of_pos (sub_pos.mpr hy)] at hmin
      linarith
    · simp [lower, ind, scaledBeurlingH, scaledBeurlingK,
        beurlingH_zero, beurlingK_zero]
    · have hmaj :=
        scaledBeurlingH_le_sign_add_scaledBeurlingK hT (x - y)
      have hindZero : ind y = 0 := by
        simp [ind, not_le.mpr hy]
      rw [hindZero]
      simp only [lower]
      rw [Real.sign_of_neg (sub_neg.mpr hy)] at hmaj
      linarith
  have hupperPoint : ∀ y, ind y ≤ upper y := by
    intro y
    rcases lt_trichotomy y x with hy | rfl | hy
    · have hmin :=
        sign_sub_scaledBeurlingK_le_scaledBeurlingH hT (x - y)
      simp only [upper, ind, Set.indicator_of_mem (mem_Iic.mpr hy.le)]
      rw [Real.sign_of_pos (sub_pos.mpr hy)] at hmin
      linarith
    · norm_num [upper, ind, scaledBeurlingH, scaledBeurlingK,
        beurlingH_zero, beurlingK_zero]
    · have hmin :=
        sign_sub_scaledBeurlingK_le_scaledBeurlingH hT (x - y)
      have hindZero : ind y = 0 := by
        simp [ind, not_le.mpr hy]
      rw [hindZero]
      simp only [upper]
      rw [Real.sign_of_neg (sub_neg.mpr hy)] at hmin
      linarith
  have hlower :
      (∫ y, lower y ∂μ) ≤ ∫ y, ind y ∂μ :=
    integral_mono hlowerInt hind hlowerPoint
  have hupper :
      (∫ y, ind y ∂μ) ≤ ∫ y, upper y ∂μ :=
    integral_mono hind hupperInt hupperPoint
  have hindValue : (∫ y, ind y ∂μ) = cdf μ x := by
    rw [show ind = (Iic x).indicator
        (fun _ : ℝ => (1 : ℝ)) by rfl,
      integral_indicator_const (μ := μ) (1 : ℝ) measurableSet_Iic,
      ProbabilityTheory.cdf_eq_real]
    simp
  have hlowerValue :
      (∫ y, lower y ∂μ) =
        beurlingCDFCenter μ T x -
          beurlingCDFCorrection μ T x := by
    change (∫ y, (1 / 2 : ℝ) +
        (1 / 2) * scaledBeurlingH T (x - y) -
        (1 / 2) * scaledBeurlingK T (x - y) ∂μ) = _
    calc
      _ = (∫ y, (1 / 2 : ℝ) +
              (1 / 2) * scaledBeurlingH T (x - y) ∂μ) -
            ∫ y, (1 / 2) * scaledBeurlingK T (x - y) ∂μ :=
        MeasureTheory.integral_sub
          ((integrable_const (1 / 2 : ℝ)).add
            (hH.const_mul (1 / 2)))
          (hK.const_mul (1 / 2))
      _ = beurlingCDFCenter μ T x -
          beurlingCDFCorrection μ T x := by
        rw [MeasureTheory.integral_add
            (integrable_const (1 / 2 : ℝ))
            (hH.const_mul (1 / 2)),
          MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul,
          integral_const]
        simp [beurlingCDFCenter, beurlingCDFCorrection]
  have hupperValue :
      (∫ y, upper y ∂μ) =
        beurlingCDFCenter μ T x +
          beurlingCDFCorrection μ T x := by
    change (∫ y, (1 / 2 : ℝ) +
        (1 / 2) * scaledBeurlingH T (x - y) +
        (1 / 2) * scaledBeurlingK T (x - y) ∂μ) = _
    calc
      _ = (∫ y, (1 / 2 : ℝ) +
              (1 / 2) * scaledBeurlingH T (x - y) ∂μ) +
            ∫ y, (1 / 2) * scaledBeurlingK T (x - y) ∂μ :=
        MeasureTheory.integral_add
          ((integrable_const (1 / 2 : ℝ)).add
            (hH.const_mul (1 / 2)))
          (hK.const_mul (1 / 2))
      _ = beurlingCDFCenter μ T x +
          beurlingCDFCorrection μ T x := by
        rw [MeasureTheory.integral_add
            (integrable_const (1 / 2 : ℝ))
            (hH.const_mul (1 / 2)),
          MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul,
          integral_const]
        simp [beurlingCDFCenter, beurlingCDFCorrection]
  rw [hlowerValue, hindValue] at hlower
  rw [hindValue, hupperValue] at hupper
  constructor <;> linarith

/--
Two-law deterministic Beurling smoothing inequality in spatial form.
-/
theorem abs_cdfDiscrepancy_sub_beurlingCenters_le
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    |cdfDiscrepancy μ ν x -
        (beurlingCDFCenter μ T x -
          beurlingCDFCenter ν T x)| ≤
      beurlingCDFCorrection μ T x +
        beurlingCDFCorrection ν T x := by
  obtain ⟨hμl, hμu⟩ :=
    cdf_mem_beurling_band_absorbing_atom μ hT x
  obtain ⟨hνl, hνu⟩ :=
    cdf_mem_beurling_band_absorbing_atom ν hT x
  rw [abs_le]
  unfold cdfDiscrepancy
  constructor <;> linarith

end Probability
end CertifiedJL
