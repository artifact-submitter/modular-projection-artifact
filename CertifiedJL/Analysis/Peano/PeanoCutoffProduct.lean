/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Peano.PeanoCutoffSecond
import CertifiedJL.Analysis.SmoothBounds.ScaledSmoothCutoff
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Translated cutoff products for second-order Peano replacement

The U3b replacement applies the second-order Peano identity to a fourth
derivative.  This module supplies the generic compact approximation used at
that boundary: a translated widening cutoff multiplied directly by the
target function.  It proves compactness, law-side dominated convergence, the
exact three-term second-derivative Leibniz formula, and pointwise convergence
of those second derivatives.  Law-specific kernel domination remains with
the noncompact U3b consumer.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace CertifiedJL

/-- A widening cutoff, translated to the expansion point, times the target
function. -/
noncomputable def upperCutoffProduct
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (f : ℝ → E) (x z : ℝ) : E :=
  upperCutoff n (z - x) • f z

theorem upperCutoffProduct_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (f : ℝ → E) (x y : ℝ) :
    upperCutoffProduct n f x (x + y) = upperCutoff n y • f (x + y) := by
  simp only [upperCutoffProduct, add_sub_cancel_left]

theorem upperCutoffProduct_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ 2 f) (n : ℕ) (x : ℝ) :
    ContDiff ℝ 2 (upperCutoffProduct n f x) := by
  have hshift : ContDiff ℝ 2 (fun z : ℝ => z - x) := by
    fun_prop
  have hcut : ContDiff ℝ 2 (fun z : ℝ => upperCutoff n (z - x)) :=
    ((upperCutoff_contDiff n).of_le (by norm_num)).comp hshift
  exact hcut.smul hf

theorem upperCutoffProduct_hasCompactSupport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (f : ℝ → E) (x : ℝ) :
    HasCompactSupport (upperCutoffProduct n f x) := by
  apply exists_compact_iff_hasCompactSupport.mp
  refine ⟨Icc (x - 2 * upperCutoffRadius n) (x + 2 * upperCutoffRadius n),
    isCompact_Icc, ?_⟩
  intro z hz
  rw [mem_Icc] at hz
  have hz' : z < x - 2 * upperCutoffRadius n ∨
      x + 2 * upperCutoffRadius n < z := by
    by_cases hleft : z < x - 2 * upperCutoffRadius n
    · exact Or.inl hleft
    · right
      by_contra hright
      exact hz ⟨le_of_not_gt hleft, le_of_not_gt hright⟩
  rcases hz' with hz' | hz'
  · have hnonpos : z - x ≤ 0 := by
      linarith [upperCutoffRadius_pos n]
    have habs : 2 * upperCutoffRadius n ≤ |z - x| := by
      rw [abs_of_nonpos hnonpos]
      linarith
    rw [upperCutoffProduct, upperCutoff_eq_zero habs, zero_smul]
  · have hnonneg : 0 ≤ z - x := by
      linarith [upperCutoffRadius_pos n]
    have habs : 2 * upperCutoffRadius n ≤ |z - x| := by
      rw [abs_of_nonneg hnonneg]
      linarith
    rw [upperCutoffProduct, upperCutoff_eq_zero habs, zero_smul]

/-- The translated cutoff products converge in Bochner integral whenever the
uncut translated function is integrable under the law. -/
theorem upperCutoffProduct_integral_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {μ : Measure ℝ} {f : ℝ → E}
    (hf : ContDiff ℝ 2 f) (x : ℝ)
    (hInt : Integrable (fun y : ℝ => f (x + y)) μ) :
    Tendsto
      (fun n => ∫ y, upperCutoffProduct n f x (x + y) ∂μ) atTop
      (𝓝 (∫ y, f (x + y) ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence
    (fun y : ℝ => ‖f (x + y)‖) ?_ hInt.norm ?_ ?_
  · intro n
    exact ((upperCutoffProduct_contDiff hf n x).comp (by fun_prop))
      |>.continuous |>.aestronglyMeasurable
  · intro n
    filter_upwards [] with y
    rw [upperCutoffProduct_apply, norm_smul]
    calc
      ‖(upperCutoff n y : ℝ)‖ * ‖f (x + y)‖ =
          upperCutoff n y * ‖f (x + y)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (upperCutoff_nonneg n y)]
      _ ≤ 1 * ‖f (x + y)‖ := by
        exact mul_le_mul_of_nonneg_right (upperCutoff_le_one n y) (norm_nonneg _)
      _ = ‖f (x + y)‖ := one_mul _
  · filter_upwards [] with y
    simpa [upperCutoffProduct_apply, one_smul] using
      (upperCutoff_pointwise_tendsto y).smul
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => f (x + y)) atTop (𝓝 (f (x + y))))

/-- The exact three-term Leibniz expansion for the second derivative of the
translated cutoff product. -/
theorem upperCutoffProduct_iteratedDeriv_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ 2 f) (n : ℕ) (x z : ℝ) :
    iteratedDeriv 2 (upperCutoffProduct n f x) z =
      ∑ i ∈ Finset.range (2 + 1),
        Nat.choose 2 i •
          iteratedDeriv i (fun w : ℝ => upperCutoff n (w - x)) z •
          iteratedDeriv (2 - i) f z := by
  have hshift : ContDiff ℝ 2 (fun w : ℝ => w - x) := by
    fun_prop
  have hcut : ContDiff ℝ 2 (fun w : ℝ => upperCutoff n (w - x)) :=
    ((upperCutoff_contDiff n).of_le (by norm_num)).comp hshift
  change iteratedDeriv 2
      ((fun w : ℝ => upperCutoff n (w - x)) • f) z = _
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_smul (Set.mem_univ z) uniqueDiffOn_univ
      hcut.contDiffWithinAt hf.contDiffWithinAt

private theorem upperCutoff_iteratedDeriv_one_tendsto_zero (t : ℝ) :
    Tendsto (fun n => iteratedDeriv 1 (upperCutoff n) t) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := upperCutoff_iteratedDeriv_bound 1
  have hinv : Tendsto (fun n : ℕ => (upperCutoffRadius n)⁻¹) atTop (𝓝 0) := by
    simpa only [upperCutoffRadius, inv_eq_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine squeeze_zero_norm
    (a := fun n => C * (upperCutoffRadius n)⁻¹ ^ 1) (fun n => hC n t) ?_
  simpa using (tendsto_const_nhds.mul hinv)

private theorem upperCutoff_iteratedDeriv_two_tendsto_zero (t : ℝ) :
    Tendsto (fun n => iteratedDeriv 2 (upperCutoff n) t) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := upperCutoff_iteratedDeriv_bound 2
  have hinv : Tendsto (fun n : ℕ => (upperCutoffRadius n)⁻¹) atTop (𝓝 0) := by
    simpa only [upperCutoffRadius, inv_eq_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine squeeze_zero_norm
    (a := fun n => C * (upperCutoffRadius n)⁻¹ ^ 2) (fun n => hC n t) ?_
  simpa using (tendsto_const_nhds.mul (hinv.pow 2))

/-- At every fixed translated point, the second derivatives of the cutoff
products converge to the uncut second derivative. -/
theorem upperCutoffProduct_iteratedDeriv_two_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ 2 f) (x t : ℝ) :
    Tendsto
      (fun n => iteratedDeriv 2 (upperCutoffProduct n f x) (x + t))
      atTop (𝓝 (iteratedDeriv 2 f (x + t))) := by
  have hshift (i n : ℕ) :
      iteratedDeriv i (fun w : ℝ => upperCutoff n (w - x)) (x + t) =
        iteratedDeriv i (upperCutoff n) t := by
    have h := congrFun (iteratedDeriv_comp_sub_const i (upperCutoff n) x) (x + t)
    simpa only [add_sub_cancel_left] using h
  have h0 : Tendsto
      (fun n => upperCutoff n t • iteratedDeriv 2 f (x + t)) atTop
      (𝓝 (iteratedDeriv 2 f (x + t))) := by
    simpa using (upperCutoff_pointwise_tendsto t).smul
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => iteratedDeriv 2 f (x + t)) atTop
        (𝓝 (iteratedDeriv 2 f (x + t))))
  have h1 : Tendsto
      (fun n => (2 : ℕ) • iteratedDeriv 1 (upperCutoff n) t •
        iteratedDeriv 1 f (x + t)) atTop (𝓝 0) := by
    simpa using
      ((upperCutoff_iteratedDeriv_one_tendsto_zero t).smul
        (tendsto_const_nhds : Tendsto
          (fun _ : ℕ => iteratedDeriv 1 f (x + t)) atTop
          (𝓝 (iteratedDeriv 1 f (x + t))))).nsmul 2
  have h2 : Tendsto
      (fun n => iteratedDeriv 2 (upperCutoff n) t • f (x + t))
      atTop (𝓝 0) := by
    simpa using (upperCutoff_iteratedDeriv_two_tendsto_zero t).smul
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => f (x + t)) atTop (𝓝 (f (x + t))))
  have hsum : Tendsto
      (fun n => upperCutoff n t • iteratedDeriv 2 f (x + t) +
        (2 : ℕ) • iteratedDeriv 1 (upperCutoff n) t •
          iteratedDeriv 1 f (x + t) +
        iteratedDeriv 2 (upperCutoff n) t • f (x + t))
      atTop (𝓝 (iteratedDeriv 2 f (x + t))) := by
    simpa using (h0.add h1).add h2
  apply hsum.congr'
  filter_upwards [] with n
  rw [upperCutoffProduct_iteratedDeriv_two hf n x (x + t)]
  simp [Finset.sum_range_succ, iteratedDeriv_zero, hshift, add_assoc]

/-- A noncompact second-order Peano identity obtained from the translated
cutoff products and one explicit cutoff-index-independent RHS majorant.

The theorem discharges both law-side limits and the weighted derivative limit.
The four compact Fubini/RHS obligations remain explicit because they are
law-specific, as are strong measurability of the stop-loss difference and the
actual dominating function. -/
theorem peanoIdentity2_of_upperCutoffProduct
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]
    {f : ℝ → E} (hf : ContDiff ℝ 2 f) (x : ℝ)
    (hμf : Integrable (fun y => f (x + y)) μ)
    (hνf : Integrable (fun y => f (x + y)) ν)
    (hμKernel : ∀ n, Integrable
      (Function.uncurry (fun t y =>
        max (y - t) 0 •
          iteratedDeriv 2 (upperCutoffProduct n f x) (x + t)))
        (volume.prod μ))
    (hνKernel : ∀ n, Integrable
      (Function.uncurry (fun t y =>
        max (y - t) 0 •
          iteratedDeriv 2 (upperCutoffProduct n f x) (x + t)))
        (volume.prod ν))
    (hμRhs : ∀ n, Integrable (fun t =>
      (∫ y, max (y - t) 0 ∂μ) •
        iteratedDeriv 2 (upperCutoffProduct n f x) (x + t)))
    (hνRhs : ∀ n, Integrable (fun t =>
      (∫ y, max (y - t) 0 ∂ν) •
        iteratedDeriv 2 (upperCutoffProduct n f x) (x + t)))
    (hΔ : StronglyMeasurable (firstStopLossDifference μ ν))
    (bound : ℝ → ℝ) (hboundInt : Integrable bound)
    (hbound : ∀ n t,
      ‖firstStopLossDifference μ ν t •
          iteratedDeriv 2 (upperCutoffProduct n f x) (x + t)‖ ≤ bound t) :
    (∫ y, f (x + y) ∂μ) - ∫ y, f (x + y) ∂ν =
      ∫ t, firstStopLossDifference μ ν t •
        iteratedDeriv 2 f (x + t) := by
  have hRhsLimit : Tendsto
      (fun n => ∫ t, firstStopLossDifference μ ν t •
        iteratedDeriv 2 (upperCutoffProduct n f x) (x + t)) atTop
      (𝓝 (∫ t, firstStopLossDifference μ ν t •
        iteratedDeriv 2 f (x + t))) := by
    refine tendsto_integral_of_dominated_convergence bound ?_ hboundInt ?_ ?_
    · intro n
      have hsecond : StronglyMeasurable (fun t : ℝ =>
          iteratedDeriv 2 (upperCutoffProduct n f x) (x + t)) :=
        ((upperCutoffProduct_contDiff hf n x).continuous_iteratedDeriv' 2
          |>.comp (continuous_const.add continuous_id)).stronglyMeasurable
      exact hΔ.smul hsecond |>.aestronglyMeasurable
    · intro n
      exact Eventually.of_forall (hbound n)
    · filter_upwards [] with t
      exact tendsto_const_nhds.smul
        (upperCutoffProduct_iteratedDeriv_two_tendsto hf x t)
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
    (peanoIdentity2_of_compact_approximants x
    (fun n => upperCutoffProduct n f x)
    (fun n => upperCutoffProduct_contDiff hf n x)
    (fun n => upperCutoffProduct_hasCompactSupport n f x)
    (fun n => by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hμKernel n)
    (fun n => by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hνKernel n)
    (fun n => by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hμRhs n)
    (fun n => by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hνRhs n)
    (upperCutoffProduct_integral_tendsto hf x hμf)
    (upperCutoffProduct_integral_tendsto hf x hνf)
    (by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hRhsLimit))

end CertifiedJL
