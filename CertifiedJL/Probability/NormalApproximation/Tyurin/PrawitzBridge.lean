/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Fourier.Prawitz.Inversion
import CertifiedJL.Probability.NormalApproximation.Tyurin.DStarCertificate
import CertifiedJL.Probability.NormalApproximation.Tyurin.CoreEnvelope

/-!
# From asymmetric Prawitz inversion to Tyurin's D-star functional

This file is the analytic bridge between the exact two-sided inversion
theorem and the scalar `D*` certificate.  Its public hypotheses are the two
characteristic-function envelopes proved by the deleted-product argument:

* the core discrepancy is bounded by `min delta₁ delta₂`;
* the outer characteristic function is bounded by Tyurin's product envelope.

All support, parity, compact-interval integrability, Gaussian-reference
terms, and `ℝ≥0∞` finiteness conversions are discharged here.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CertifiedJL
namespace Probability

/-- Symmetric core integrand occurring in Tyurin's `D*` numerator. -/
noncomputable def tyurinCoreFourierEnvelope
    (L U₀ U u : ℝ) : ℝ :=
  if |u| ≤ U₀ then
    ‖scaledPrawitzKernel U u‖ *
      min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)
  else 0

/-- Symmetric outer-band integrand occurring in Tyurin's `D*` numerator. -/
noncomputable def tyurinOuterFourierEnvelope
    (L U₀ U u : ℝ) : ℝ :=
  if U₀ ≤ |u| ∧ |u| ≤ U then
    ‖scaledPrawitzKernel U u‖ * tyurinProductEnvelope L u
  else 0

theorem tyurinCoreBase_neg (L U u : ℝ) :
    ‖scaledPrawitzKernel U (-u)‖ *
        min (tyurinDeltaOne L (-u)) (tyurinDeltaTwo L (-u)) =
      ‖scaledPrawitzKernel U u‖ *
        min (tyurinDeltaOne L u) (tyurinDeltaTwo L u) := by
  rw [scaledPrawitzKernel_neg, Complex.norm_conj,
    tyurinDeltaOne_neg, tyurinDeltaTwo_neg]

theorem tyurinOuterBase_neg (L U u : ℝ) :
    ‖scaledPrawitzKernel U (-u)‖ *
        tyurinProductEnvelope L (-u) =
      ‖scaledPrawitzKernel U u‖ *
        tyurinProductEnvelope L u := by
  rw [scaledPrawitzKernel_neg, Complex.norm_conj,
    tyurinProductEnvelope_neg]

theorem tyurinCoreFourierEnvelope_neg (L U₀ U u : ℝ) :
    tyurinCoreFourierEnvelope L U₀ U (-u) =
      tyurinCoreFourierEnvelope L U₀ U u := by
  simp only [tyurinCoreFourierEnvelope, abs_neg]
  split_ifs
  · exact tyurinCoreBase_neg L U u
  · rfl

theorem tyurinOuterFourierEnvelope_neg (L U₀ U u : ℝ) :
    tyurinOuterFourierEnvelope L U₀ U (-u) =
      tyurinOuterFourierEnvelope L U₀ U u := by
  simp only [tyurinOuterFourierEnvelope, abs_neg]
  split_ifs
  · exact tyurinOuterBase_neg L U u
  · rfl

theorem measurable_tyurinCoreFourierEnvelope
    (L U₀ U : ℝ) :
    Measurable (tyurinCoreFourierEnvelope L U₀ U) := by
  unfold tyurinCoreFourierEnvelope
  exact Measurable.ite
    (measurableSet_le continuous_abs.measurable measurable_const)
    (measurable_tyurinCoreIntegrand L U)
    measurable_const

theorem measurable_tyurinOuterFourierEnvelope
    (L U₀ U : ℝ) :
    Measurable (tyurinOuterFourierEnvelope L U₀ U) := by
  unfold tyurinOuterFourierEnvelope
  exact Measurable.ite
    ((measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_le continuous_abs.measurable measurable_const))
    (measurable_tyurinOuterIntegrand L U)
    measurable_const

theorem tyurinCoreFourierEnvelope_nonneg
    {L U₀ U : ℝ} (hL : 0 < L) (u : ℝ) :
    0 ≤ tyurinCoreFourierEnvelope L U₀ U u := by
  unfold tyurinCoreFourierEnvelope
  split_ifs
  · exact mul_nonneg (norm_nonneg _)
      (le_min (tyurinDeltaOne_nonneg hL.le)
        (tyurinDeltaTwo_nonneg hL))
  · exact le_rfl

theorem tyurinOuterFourierEnvelope_nonneg
    (L U₀ U u : ℝ) :
    0 ≤ tyurinOuterFourierEnvelope L U₀ U u := by
  unfold tyurinOuterFourierEnvelope
  split_ifs
  · exact mul_nonneg (norm_nonneg _)
      (tyurinProductEnvelope_nonneg L u)
  · exact le_rfl

private theorem intervalIntegral_tyurinCoreBase_neg_eq
    (L U₀ U : ℝ) :
    (∫ u : ℝ in (-U₀)..0,
        ‖scaledPrawitzKernel U u‖ *
          min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)) =
      ∫ u : ℝ in 0..U₀,
        ‖scaledPrawitzKernel U u‖ *
          min (tyurinDeltaOne L u) (tyurinDeltaTwo L u) := by
  let f : ℝ → ℝ := fun u =>
    ‖scaledPrawitzKernel U u‖ *
      min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)
  calc
    (∫ u : ℝ in (-U₀)..0, f u) =
        ∫ u : ℝ in 0..U₀, f (-u) := by
      simpa only [neg_zero] using
        (intervalIntegral.integral_comp_neg
          (f := f) (a := 0) (b := U₀)).symm
    _ = ∫ u : ℝ in 0..U₀, f u := by
      apply intervalIntegral.integral_congr
      intro u _
      exact tyurinCoreBase_neg L U u

private theorem intervalIntegral_tyurinOuterBase_neg_eq
    (L U₀ U : ℝ) :
    (∫ u : ℝ in (-U)..(-U₀),
        ‖scaledPrawitzKernel U u‖ *
          tyurinProductEnvelope L u) =
      ∫ u : ℝ in U₀..U,
        ‖scaledPrawitzKernel U u‖ *
          tyurinProductEnvelope L u := by
  let f : ℝ → ℝ := fun u =>
    ‖scaledPrawitzKernel U u‖ *
      tyurinProductEnvelope L u
  calc
    (∫ u : ℝ in (-U)..(-U₀), f u) =
        ∫ u : ℝ in U₀..U, f (-u) := by
      rw [intervalIntegral.integral_comp_neg]
    _ = ∫ u : ℝ in U₀..U, f u := by
      apply intervalIntegral.integral_congr
      intro u _
      exact tyurinOuterBase_neg L U u

theorem integrable_tyurinCoreFourierEnvelope
    {L U₀ U : ℝ} (hL : 0 < L) (hU₀ : 0 < U₀)
    (hU : 0 < U) (hcut : U₀ ≤ U) :
    Integrable (tyurinCoreFourierEnvelope L U₀ U) := by
  let f : ℝ → ℝ := fun u =>
    ‖scaledPrawitzKernel U u‖ *
      min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)
  have hpos : IntervalIntegrable f volume 0 U₀ :=
    intervalIntegrable_tyurinCoreIntegrand
      (n := 1) (by norm_num) hL hU₀ hU hcut
  have hneg : IntervalIntegrable f volume (-U₀) 0 := by
    rw [IntervalIntegrable.iff_comp_neg]
    convert hpos.symm using 1
    · funext u
      exact tyurinCoreBase_neg L U u
    all_goals simp
  have hsym : IntervalIntegrable f volume (-U₀) U₀ :=
    hneg.trans hpos
  have hOn : IntegrableOn f (Icc (-U₀) U₀) volume := by
    rwa [← intervalIntegrable_iff_integrableOn_Icc_of_le
      (by linarith : -U₀ ≤ U₀)]
  have hind :
      Integrable ((Icc (-U₀) U₀).indicator f) :=
    (integrable_indicator_iff measurableSet_Icc).2 hOn
  refine hind.congr (ae_of_all volume fun u => ?_)
  unfold tyurinCoreFourierEnvelope
  by_cases hu : |u| ≤ U₀
  · simp [hu, abs_le.mp hu]
    rfl
  · rw [if_neg hu, Set.indicator_of_notMem]
    simpa [abs_le] using hu

theorem integral_tyurinCoreFourierEnvelope
    {L U₀ U : ℝ} (hL : 0 < L) (hU₀ : 0 < U₀)
    (hU : 0 < U) (hcut : U₀ ≤ U) :
    (∫ u : ℝ, tyurinCoreFourierEnvelope L U₀ U u) =
      2 * (∫ u : ℝ in 0..U₀,
        ‖scaledPrawitzKernel U u‖ *
          min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)) := by
  let f : ℝ → ℝ := fun u =>
    ‖scaledPrawitzKernel U u‖ *
      min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)
  have hpos : IntervalIntegrable f volume 0 U₀ :=
    intervalIntegrable_tyurinCoreIntegrand
      (n := 1) (by norm_num) hL hU₀ hU hcut
  have hneg : IntervalIntegrable f volume (-U₀) 0 := by
    rw [IntervalIntegrable.iff_comp_neg]
    convert hpos.symm using 1
    · funext u
      exact tyurinCoreBase_neg L U u
    all_goals simp
  calc
    (∫ u : ℝ, tyurinCoreFourierEnvelope L U₀ U u) =
        ∫ u in Icc (-U₀) U₀, f u := by
      rw [← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards with u
      unfold tyurinCoreFourierEnvelope
      by_cases hu : |u| ≤ U₀
      · simp [hu, abs_le.mp hu]
        rfl
      · rw [if_neg hu, Set.indicator_of_notMem]
        simpa [abs_le] using hu
    _ = ∫ u : ℝ in (-U₀)..U₀, f u := by
      rw [intervalIntegral.integral_of_le
        (by linarith : -U₀ ≤ U₀),
        ← integral_Icc_eq_integral_Ioc]
    _ = (∫ u : ℝ in (-U₀)..0, f u) +
        ∫ u : ℝ in 0..U₀, f u :=
      (intervalIntegral.integral_add_adjacent_intervals hneg hpos).symm
    _ = 2 * (∫ u : ℝ in 0..U₀, f u) := by
      rw [intervalIntegral_tyurinCoreBase_neg_eq L U₀ U]
      ring

theorem integrable_tyurinOuterFourierEnvelope
    {L U₀ U : ℝ} (hL : 0 < L) (hU₀ : 0 < U₀)
    (hU : 0 < U) (hcut : U₀ ≤ U) :
    Integrable (tyurinOuterFourierEnvelope L U₀ U) := by
  let f : ℝ → ℝ := fun u =>
    ‖scaledPrawitzKernel U u‖ * tyurinProductEnvelope L u
  let S : Set ℝ := Icc (-U) (-U₀) ∪ Icc U₀ U
  have hpos : IntegrableOn f (Icc U₀ U) volume := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hcut).mp
      (intervalIntegrable_tyurinOuterIntegrand hL hU₀ hU hcut)
  have hnegI : IntervalIntegrable f volume (-U) (-U₀) := by
    rw [IntervalIntegrable.iff_comp_neg]
    convert
      (intervalIntegrable_tyurinOuterIntegrand hL hU₀ hU hcut).symm
      using 1
    · funext u
      exact tyurinOuterBase_neg L U u
    all_goals simp
  have hneg : IntegrableOn f (Icc (-U) (-U₀)) volume := by
    rwa [← intervalIntegrable_iff_integrableOn_Icc_of_le
      (by linarith : -U ≤ -U₀)]
  have hdisj : Disjoint (Icc (-U) (-U₀)) (Icc U₀ U) := by
    rw [Set.disjoint_left]
    intro u huNeg huPos
    rcases huNeg with ⟨_, huNeg⟩
    rcases huPos with ⟨huPos, _⟩
    linarith
  have hOn : IntegrableOn f S volume :=
    hneg.union hpos
  have hind : Integrable (S.indicator f) :=
    (integrable_indicator_iff
      (measurableSet_Icc.union measurableSet_Icc)).2 hOn
  refine hind.congr (ae_of_all volume fun u => ?_)
  unfold tyurinOuterFourierEnvelope
  by_cases hu : U₀ ≤ |u| ∧ |u| ≤ U
  · rw [if_pos hu, Set.indicator_of_mem]
    rcases le_total u 0 with hu0 | hu0
    · left
      rw [abs_of_nonpos hu0] at hu
      exact ⟨by linarith, by linarith⟩
    · right
      rw [abs_of_nonneg hu0] at hu
      exact hu
  · rw [if_neg hu, Set.indicator_of_notMem]
    intro hmem
    rcases hmem with hmem | hmem
    · apply hu
      have hu0 : u ≤ 0 := by linarith [hmem.2, hU₀]
      rw [abs_of_nonpos hu0]
      exact ⟨by linarith [hmem.2], by linarith [hmem.1]⟩
    · apply hu
      have hu0 : 0 ≤ u := hU₀.le.trans hmem.1
      rw [abs_of_nonneg hu0]
      exact hmem

theorem integral_tyurinOuterFourierEnvelope
    {L U₀ U : ℝ} (hL : 0 < L) (hU₀ : 0 < U₀)
    (hU : 0 < U) (hcut : U₀ ≤ U) :
    (∫ u : ℝ, tyurinOuterFourierEnvelope L U₀ U u) =
      2 * (∫ u : ℝ in U₀..U,
        ‖scaledPrawitzKernel U u‖ *
          tyurinProductEnvelope L u) := by
  let f : ℝ → ℝ := fun u =>
    ‖scaledPrawitzKernel U u‖ * tyurinProductEnvelope L u
  let S : Set ℝ := Icc (-U) (-U₀) ∪ Icc U₀ U
  have hpos : IntegrableOn f (Icc U₀ U) volume := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hcut).mp
      (intervalIntegrable_tyurinOuterIntegrand hL hU₀ hU hcut)
  have hnegI : IntervalIntegrable f volume (-U) (-U₀) := by
    rw [IntervalIntegrable.iff_comp_neg]
    convert
      (intervalIntegrable_tyurinOuterIntegrand hL hU₀ hU hcut).symm
      using 1
    · funext u
      exact tyurinOuterBase_neg L U u
    all_goals simp
  have hneg : IntegrableOn f (Icc (-U) (-U₀)) volume := by
    rwa [← intervalIntegrable_iff_integrableOn_Icc_of_le
      (by linarith : -U ≤ -U₀)]
  have hdisj : Disjoint (Icc (-U) (-U₀)) (Icc U₀ U) := by
    rw [Set.disjoint_left]
    intro u huNeg huPos
    rcases huNeg with ⟨_, huNeg⟩
    rcases huPos with ⟨huPos, _⟩
    linarith
  calc
    (∫ u : ℝ, tyurinOuterFourierEnvelope L U₀ U u) =
        ∫ u in S, f u := by
      rw [← integral_indicator
        (measurableSet_Icc.union measurableSet_Icc)]
      apply integral_congr_ae
      filter_upwards with u
      unfold tyurinOuterFourierEnvelope
      by_cases hu : U₀ ≤ |u| ∧ |u| ≤ U
      · rw [if_pos hu, Set.indicator_of_mem]
        rcases le_total u 0 with hu0 | hu0
        · left
          rw [abs_of_nonpos hu0] at hu
          exact ⟨by linarith, by linarith⟩
        · right
          rw [abs_of_nonneg hu0] at hu
          exact hu
      · rw [if_neg hu, Set.indicator_of_notMem]
        intro hmem
        rcases hmem with hmem | hmem
        · apply hu
          have hu0 : u ≤ 0 := by linarith [hmem.2, hU₀]
          rw [abs_of_nonpos hu0]
          exact ⟨by linarith [hmem.2], by linarith [hmem.1]⟩
        · apply hu
          have hu0 : 0 ≤ u := hU₀.le.trans hmem.1
          rw [abs_of_nonneg hu0]
          exact hmem
    _ = (∫ u in Icc (-U) (-U₀), f u) +
        ∫ u in Icc U₀ U, f u :=
      setIntegral_union hdisj measurableSet_Icc hneg hpos
    _ = (∫ u : ℝ in (-U)..(-U₀), f u) +
        ∫ u : ℝ in U₀..U, f u := by
      rw [intervalIntegral.integral_of_le
          (by linarith : -U ≤ -U₀),
        intervalIntegral.integral_of_le hcut,
        ← integral_Icc_eq_integral_Ioc,
        ← integral_Icc_eq_integral_Ioc]
    _ = 2 * (∫ u : ℝ in U₀..U, f u) := by
      rw [intervalIntegral_tyurinOuterBase_neg_eq L U₀ U]
      ring

theorem prawitzCoreDiscrepancyTerm_le_tyurinCoreFourierEnvelope
    (μ : Measure ℝ) {L U₀ U : ℝ}
    (hcore : ∀ u : ℝ,
      ‖charFun μ u - charFun (gaussianReal 0 1) u‖ ≤
        min (tyurinDeltaOne L u) (tyurinDeltaTwo L u))
    (u : ℝ) :
    prawitzCoreDiscrepancyTerm
        μ (gaussianReal 0 1) U₀ U u ≤
      tyurinCoreFourierEnvelope L U₀ U u := by
  unfold prawitzCoreDiscrepancyTerm tyurinCoreFourierEnvelope
  by_cases hu : |u| ≤ U₀
  · rw [if_pos hu, if_pos hu]
    exact mul_le_mul_of_nonneg_left (hcore u) (norm_nonneg _)
  · rw [if_neg hu, if_neg hu]

theorem prawitzOuterKernelTerm_le_tyurinOuterFourierEnvelope
    (μ : Measure ℝ) {L U₀ U : ℝ}
    (houter : ∀ u : ℝ,
      ‖charFun μ u‖ ≤ tyurinProductEnvelope L u)
    (u : ℝ) :
    prawitzOuterKernelTerm μ U₀ U u ≤
      tyurinOuterFourierEnvelope L U₀ U u := by
  unfold prawitzOuterKernelTerm tyurinOuterFourierEnvelope
  by_cases hu : U₀ < |u| ∧ |u| ≤ U
  · rw [if_pos hu, if_pos ⟨hu.1.le, hu.2⟩]
    exact mul_le_mul_of_nonneg_left (houter u) (norm_nonneg _)
  · rw [if_neg hu]
    split_ifs
    · exact mul_nonneg (norm_nonneg _)
        (tyurinProductEnvelope_nonneg L u)
    · exact le_rfl

theorem lintegral_prawitzCoreDiscrepancyTerm_le_tyurinCore
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {L U₀ U : ℝ} (hL : 0 < L) (hU₀ : 0 < U₀)
    (hU : 0 < U) (hcut : U₀ ≤ U)
    (hcore : ∀ u : ℝ,
      ‖charFun μ u - charFun (gaussianReal 0 1) u‖ ≤
        min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)) :
    (∫⁻ u, ENNReal.ofReal
        (prawitzCoreDiscrepancyTerm
          μ (gaussianReal 0 1) U₀ U u) ∂volume) ≤
      ENNReal.ofReal
        (2 * (∫ u : ℝ in 0..U₀,
          ‖scaledPrawitzKernel U u‖ *
            min (tyurinDeltaOne L u) (tyurinDeltaTwo L u))) := by
  calc
    (∫⁻ u, ENNReal.ofReal
        (prawitzCoreDiscrepancyTerm
          μ (gaussianReal 0 1) U₀ U u) ∂volume) ≤
        ∫⁻ u, ENNReal.ofReal
          (tyurinCoreFourierEnvelope L U₀ U u) ∂volume := by
      apply lintegral_mono
      intro u
      exact ENNReal.ofReal_le_ofReal
        (prawitzCoreDiscrepancyTerm_le_tyurinCoreFourierEnvelope
          μ hcore u)
    _ = ENNReal.ofReal
        (∫ u, tyurinCoreFourierEnvelope L U₀ U u) := by
      rw [ofReal_integral_eq_lintegral_ofReal
        (integrable_tyurinCoreFourierEnvelope hL hU₀ hU hcut)
        (ae_of_all volume
          (tyurinCoreFourierEnvelope_nonneg hL))]
    _ = _ := by
      rw [integral_tyurinCoreFourierEnvelope hL hU₀ hU hcut]

theorem lintegral_prawitzOuterKernelTerm_le_tyurinOuter
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {L U₀ U : ℝ} (hL : 0 < L) (hU₀ : 0 < U₀)
    (hU : 0 < U) (hcut : U₀ ≤ U)
    (houter : ∀ u : ℝ,
      ‖charFun μ u‖ ≤ tyurinProductEnvelope L u) :
    (∫⁻ u, ENNReal.ofReal
        (prawitzOuterKernelTerm μ U₀ U u) ∂volume) ≤
      ENNReal.ofReal
        (2 * (∫ u : ℝ in U₀..U,
          ‖scaledPrawitzKernel U u‖ *
            tyurinProductEnvelope L u)) := by
  calc
    (∫⁻ u, ENNReal.ofReal
        (prawitzOuterKernelTerm μ U₀ U u) ∂volume) ≤
        ∫⁻ u, ENNReal.ofReal
          (tyurinOuterFourierEnvelope L U₀ U u) ∂volume := by
      apply lintegral_mono
      intro u
      exact ENNReal.ofReal_le_ofReal
        (prawitzOuterKernelTerm_le_tyurinOuterFourierEnvelope
          μ houter u)
    _ = ENNReal.ofReal
        (∫ u, tyurinOuterFourierEnvelope L U₀ U u) := by
      rw [ofReal_integral_eq_lintegral_ofReal
        (integrable_tyurinOuterFourierEnvelope hL hU₀ hU hcut)
        (ae_of_all volume
          (tyurinOuterFourierEnvelope_nonneg L U₀ U))]
    _ = _ := by
      rw [integral_tyurinOuterFourierEnvelope hL hU₀ hU hcut]

theorem prawitzGaussianSharpClosedBudget_nonneg
    {U₀ U : ℝ} (hU₀ : 0 < U₀) (hU : 0 < U)
    (hcut : U₀ ≤ U) :
    0 ≤ prawitzGaussianSharpClosedBudget U₀ U := by
  have hcore :
      0 ≤ prawitzGaussianSharpCoreBudget U₀ U := by
    exact (integral_nonneg
      (gaussianSharpCoreEnvelope_nonneg hU₀.le hU hcut)).trans
      (integral_gaussianSharpCoreEnvelope_le_budget hU₀.le hU)
  unfold prawitzGaussianSharpClosedBudget
  positivity

/--
The exact four-integral Prawitz budget is bounded by the numerator of
Tyurin's rational `D*` functional.
-/
theorem prawitzFourIntegralBudget_standardGaussian_le_tyurinNumerator
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {L U₀ U : ℝ} (hL : 0 < L) (hU₀ : 0 < U₀)
    (hU : 0 < U) (hcut : U₀ ≤ U)
    (hcore : ∀ u : ℝ,
      ‖charFun μ u - charFun (gaussianReal 0 1) u‖ ≤
        min (tyurinDeltaOne L u) (tyurinDeltaTwo L u))
    (houter : ∀ u : ℝ,
      ‖charFun μ u‖ ≤ tyurinProductEnvelope L u) :
    prawitzFourIntegralBudget μ (gaussianReal 0 1) U₀ U ≤
      ENNReal.ofReal (L * tyurinRationalDStar L U₀ U) := by
  have hcoreInt :=
    lintegral_prawitzCoreDiscrepancyTerm_le_tyurinCore
      μ hL hU₀ hU hcut hcore
  have houterInt :=
    lintegral_prawitzOuterKernelTerm_le_tyurinOuter
      μ hL hU₀ hU hcut houter
  have hgaussian :=
    lintegral_prawitzGaussianTerms_standardGaussian_le_sharpBudget
      hU₀ hU hcut
  let C : ℝ := 2 * (∫ u : ℝ in 0..U₀,
    ‖scaledPrawitzKernel U u‖ *
      min (tyurinDeltaOne L u) (tyurinDeltaTwo L u))
  let O : ℝ := 2 * (∫ u : ℝ in U₀..U,
    ‖scaledPrawitzKernel U u‖ * tyurinProductEnvelope L u)
  let G : ℝ := prawitzGaussianSharpClosedBudget U₀ U
  have hC : 0 ≤ C := by
    dsimp only [C]
    apply mul_nonneg (by norm_num)
    apply intervalIntegral.integral_nonneg hU₀.le
    intro u _
    exact mul_nonneg (norm_nonneg _)
      (le_min (tyurinDeltaOne_nonneg hL.le)
        (tyurinDeltaTwo_nonneg hL))
  have hO : 0 ≤ O := by
    dsimp only [O]
    apply mul_nonneg (by norm_num)
    apply intervalIntegral.integral_nonneg hcut
    intro u _
    exact mul_nonneg (norm_nonneg _)
      (tyurinProductEnvelope_nonneg L u)
  have hG : 0 ≤ G :=
    prawitzGaussianSharpClosedBudget_nonneg hU₀ hU hcut
  unfold prawitzFourIntegralBudget
  calc
    _ = ((∫⁻ u, ENNReal.ofReal
          (prawitzCoreDiscrepancyTerm
            μ (gaussianReal 0 1) U₀ U u) ∂volume) +
        (∫⁻ u, ENNReal.ofReal
          (prawitzOuterKernelTerm μ U₀ U u) ∂volume)) +
        ((∫⁻ u, ENNReal.ofReal
          (prawitzCoreCorrectionTerm
            (gaussianReal 0 1) U₀ U u) ∂volume) +
        (∫⁻ u, ENNReal.ofReal
          (prawitzReferenceTailTerm
            (gaussianReal 0 1) U₀ u) ∂volume)) := by
      ac_rfl
    _ ≤ ENNReal.ofReal C + ENNReal.ofReal O + ENNReal.ofReal G := by
      exact add_le_add (add_le_add hcoreInt houterInt) hgaussian
    _ = ENNReal.ofReal (C + O) + ENNReal.ofReal G := by
      rw [ENNReal.ofReal_add hC hO]
    _ = ENNReal.ofReal (C + O + G) := by
      rw [ENNReal.ofReal_add (add_nonneg hC hO) hG]
    _ = ENNReal.ofReal (L * tyurinRationalDStar L U₀ U) := by
      congr 1
      unfold tyurinRationalDStar
      dsimp only [C, O, G]
      field_simp [hL.ne']

private theorem integrable_id_standardGaussian :
    Integrable (fun y : ℝ => y) (gaussianReal 0 1) := by
  exact integrable_of_mem_interior_integrableExpSet (by simp)

/--
Generic Tyurin-to-Kolmogorov bridge.  Its only analytic inputs are precisely
the deleted-product core envelope and the global product envelope.
-/
theorem kolmogorovDistance_le_mul_tyurinRationalDStar
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : Integrable (fun y : ℝ => y) μ)
    {L U₀ U : ℝ} (hL : 0 < L) (hU₀ : 0 < U₀)
    (hU : 0 < U) (hcut : U₀ ≤ U)
    (hcore : ∀ u : ℝ,
      ‖charFun μ u - charFun (gaussianReal 0 1) u‖ ≤
        min (tyurinDeltaOne L u) (tyurinDeltaTwo L u))
    (houter : ∀ u : ℝ,
      ‖charFun μ u‖ ≤ tyurinProductEnvelope L u) :
    kolmogorovDistance μ (gaussianReal 0 1) ≤
      L * tyurinRationalDStar L U₀ U := by
  let : NullSingletonClass (gaussianReal 0 1) :=
    noAtoms_gaussianReal (by norm_num)
  have hinversion :=
    ofReal_kolmogorovDistance_le_prawitzFourIntegralBudget
      μ (gaussianReal 0 1) hmoment
      integrable_id_standardGaussian hU hcut
  have hbudget :=
    prawitzFourIntegralBudget_standardGaussian_le_tyurinNumerator
      μ hL hU₀ hU hcut hcore houter
  have hENN := hinversion.trans hbudget
  have hrhs : 0 ≤ L * tyurinRationalDStar L U₀ U := by
    unfold tyurinRationalDStar
    rw [mul_div_cancel₀ _ hL.ne']
    exact add_nonneg
      (add_nonneg
        (by
          apply mul_nonneg (by norm_num)
          apply intervalIntegral.integral_nonneg hU₀.le
          intro u _
          exact mul_nonneg (norm_nonneg _)
            (le_min (tyurinDeltaOne_nonneg hL.le)
              (tyurinDeltaTwo_nonneg hL)))
        (by
          apply mul_nonneg (by norm_num)
          apply intervalIntegral.integral_nonneg hcut
          intro u _
          exact mul_nonneg (norm_nonneg _)
            (tyurinProductEnvelope_nonneg L u)))
      (prawitzGaussianSharpClosedBudget_nonneg hU₀ hU hcut)
  exact (ENNReal.ofReal_le_ofReal_iff hrhs).mp hENN

theorem kolmogorovDistance_div_le_tyurinRationalDStar
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : Integrable (fun y : ℝ => y) μ)
    {L U₀ U : ℝ} (hL : 0 < L) (hU₀ : 0 < U₀)
    (hU : 0 < U) (hcut : U₀ ≤ U)
    (hcore : ∀ u : ℝ,
      ‖charFun μ u - charFun (gaussianReal 0 1) u‖ ≤
        min (tyurinDeltaOne L u) (tyurinDeltaTwo L u))
    (houter : ∀ u : ℝ,
      ‖charFun μ u‖ ≤ tyurinProductEnvelope L u) :
    kolmogorovDistance μ (gaussianReal 0 1) / L ≤
      tyurinRationalDStar L U₀ U := by
  rw [div_le_iff₀ hL]
  simpa [mul_comm] using
    kolmogorovDistance_le_mul_tyurinRationalDStar
      μ hmoment hL hU₀ hU hcut hcore houter

/--
Every real-valued function on a finite measurable space is integrable
against a finite measure.  This is the only finite-support fact needed to
feed the tilted-Rademacher law into Prawitz inversion.
-/
private theorem integrable_finite_domain
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Finite α] (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) :
    Integrable f μ := by
  obtain ⟨C, hC⟩ := Finite.exists_le (fun a => ‖f a‖)
  exact Integrable.of_bound
    (measurable_of_finite f).aestronglyMeasurable C
    (ae_of_all μ hC)

/--
The standardized tilted-Rademacher law has a finite first moment, because
it is the image of a probability mass function on the finite sign cube.
-/
theorem integrable_id_rademacherTiltedStandardizedLaw
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ) :
    Integrable (fun y : ℝ => y)
      (rademacherTiltedStandardizedLaw b x) := by
  unfold rademacherTiltedStandardizedLaw rademacherTiltedSumLaw
  rw [integrable_map_measure (by fun_prop) (by fun_prop)]
  rw [integrable_map_measure (by fun_prop)
    ((measurable_of_finite (rademacherSum b)).aemeasurable)]
  exact integrable_finite_domain _ _

/--
Unnormalized Tyurin bound for the actual standardized tilted-Rademacher
law.  No characteristic-function or moment premise remains: the only
probabilistic input is unit variance of the original coefficient vector.
-/
theorem
    kolmogorovDistance_rademacherTiltedStandardizedLaw_le_mul_tyurinRationalDStar
    {ι : Type*} [Fintype ι]
    (b : ι → ℝ) (x : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1)
    {U₀ U : ℝ} (hU₀ : 0 < U₀) (hcut : U₀ ≤ U) :
    kolmogorovDistance
        (rademacherTiltedStandardizedLaw b x)
        (gaussianReal 0 1) ≤
      rademacherLyapunovRatio b x *
        tyurinRationalDStar
          (rademacherLyapunovRatio b x) U₀ U := by
  have hU : 0 < U := hU₀.trans_le hcut
  apply kolmogorovDistance_le_mul_tyurinRationalDStar
    (rademacherTiltedStandardizedLaw b x)
    (integrable_id_rademacherTiltedStandardizedLaw b x)
    (rademacherLyapunovRatio_pos b x hnorm)
    hU₀ hU hcut
  · exact fun u =>
      norm_rademacherTiltedCharFun_sub_standardGaussian_le_tyurinCore
        b x u hnorm
  · exact fun u =>
      norm_rademacherTiltedCharFun_le_tyurinProductEnvelope
        b x u hnorm

/--
Normalized Tyurin `D*` bound for the actual standardized tilted-Rademacher
law.  This is the assumption-free analytic consumer theorem used by the
numerical certificate layer.
-/
theorem
    kolmogorovDistance_rademacherTiltedStandardizedLaw_div_le_tyurinRationalDStar
    {ι : Type*} [Fintype ι]
    (b : ι → ℝ) (x : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1)
    {U₀ U : ℝ} (hU₀ : 0 < U₀) (hcut : U₀ ≤ U) :
    kolmogorovDistance
        (rademacherTiltedStandardizedLaw b x)
        (gaussianReal 0 1) /
          rademacherLyapunovRatio b x ≤
      tyurinRationalDStar
        (rademacherLyapunovRatio b x) U₀ U := by
  have hU : 0 < U := hU₀.trans_le hcut
  apply kolmogorovDistance_div_le_tyurinRationalDStar
    (rademacherTiltedStandardizedLaw b x)
    (integrable_id_rademacherTiltedStandardizedLaw b x)
    (rademacherLyapunovRatio_pos b x hnorm)
    hU₀ hU hcut
  · exact fun u =>
      norm_rademacherTiltedCharFun_sub_standardGaussian_le_tyurinCore
        b x u hnorm
  · exact fun u =>
      norm_rademacherTiltedCharFun_le_tyurinProductEnvelope
        b x u hnorm

/--
Certificate-ready form of the normalized tilted-Rademacher Tyurin bound.
All analytic estimates have been discharged; callers provide only the
finite trapezoid mesh and scalar inequalities checked by the certificate.
-/
theorem
    kolmogorovDistance_rademacherTiltedStandardizedLaw_div_le_tyurinCertificate
    {ι : Type*} [Fintype ι]
    (b : ι → ℝ) (x : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1)
    {n : ℕ} {U₀ U e : ℝ}
    (hn : 0 < n) (hU₀ : 0 < U₀) (hcut : U₀ ≤ U)
    (he0 : 0 ≤ e)
    (hexp : Real.exp (-(U₀ ^ 2) / 2) ≤ e) :
    kolmogorovDistance
        (rademacherTiltedStandardizedLaw b x)
        (gaussianReal 0 1) /
          rademacherLyapunovRatio b x ≤
      tyurinCertificateDStarUpper n
        (rademacherLyapunovRatio b x) U₀ U e := by
  have hU : 0 < U := hU₀.trans_le hcut
  exact
    (kolmogorovDistance_rademacherTiltedStandardizedLaw_div_le_tyurinRationalDStar
      b x hnorm hU₀ hcut).trans
      (tyurinRationalDStar_le_certificateUpper
        hn (rademacherLyapunovRatio_pos b x hnorm)
        hU₀ hU hcut he0 hexp)

end Probability
end CertifiedJL
