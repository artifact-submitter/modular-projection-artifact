/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Distributions.BalancedTernary.MGF
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Shifted Gaussian envelope

This is the analytic envelope used for nonzero modular images.  It is stated
for an arbitrary finite probability measure and consumes an explicit MGF
bound; the finite certificate layer is not involved.
-/

open scoped BigOperators

open MeasureTheory

namespace CertifiedJL

/--
An MGF sub-Gaussian bound controls every shifted quadratic Gaussian kernel.

The optimizer is kept in the proof rather than hidden behind a numerical
lemma. This makes the variance normalization and the shift sign visible at
the interface consumed by periodization.
-/
theorem shiftedGaussianEnvelope
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (σ α a : ℝ)
    (hX_meas : Measurable X)
    (hX_int : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ)
    (hmgf : ∀ t : ℝ,
      ∫ ω, Real.exp (t * X ω) ∂μ ≤
        Real.exp (σ ^ 2 * t ^ 2 / 2))
    (hα : 0 < α) :
    ∫ ω, Real.exp (-α * (X ω - a) ^ 2) ∂μ ≤
      Real.exp (-α * a ^ 2 / (1 + 2 * α * σ ^ 2)) := by
  let den : ℝ := 1 + 2 * α * σ ^ 2
  let lam : ℝ := 2 * α * a / den
  let b : ℝ := lam ^ 2 / (4 * α) - lam * a
  have hden : 0 < den := by
    dsimp [den]
    positivity
  have hden_ne : den ≠ 0 := hden.ne'
  have hquad (x : ℝ) :
      -α * (x - a) ^ 2 ≤ lam * x + b := by
    calc
      -α * (x - a) ^ 2 ≤
          -α * (x - a) ^ 2 +
            α * (x - a + lam / (2 * α)) ^ 2 := by
        exact le_add_of_nonneg_right
          (mul_nonneg hα.le (sq_nonneg _))
      _ = lam * x + b := by
        dsimp [b]
        field_simp [hα.ne']
        ring
  have h_lower_meas :
      Measurable (fun ω => Real.exp (-α * (X ω - a) ^ 2)) := by
    fun_prop
  have h_upper_meas :
      Measurable (fun ω => Real.exp (lam * X ω + b)) := by
    fun_prop
  have h_upper_int :
      Integrable (fun ω => Real.exp (lam * X ω + b)) μ := by
    simpa only [Real.exp_add, mul_comm] using
      (hX_int lam).const_mul (Real.exp b)
  have h_lower_int :
      Integrable (fun ω => Real.exp (-α * (X ω - a) ^ 2)) μ := by
    apply h_upper_int.mono_nonneg h_lower_meas.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le)
    · filter_upwards [] with ω
      exact (Real.exp_le_exp.mpr (hquad (X ω)))
  have h_pointwise :
      ∀ᵐ ω ∂μ,
        Real.exp (-α * (X ω - a) ^ 2) ≤
          Real.exp (lam * X ω + b) := by
    filter_upwards [] with ω
    exact Real.exp_le_exp.mpr (hquad (X ω))
  have h_mono :
      (∫ ω, Real.exp (-α * (X ω - a) ^ 2) ∂μ) ≤
        ∫ ω, Real.exp (lam * X ω + b) ∂μ :=
    integral_mono_ae h_lower_int h_upper_int h_pointwise
  have h_upper_integral :
      (∫ ω, Real.exp (lam * X ω + b) ∂μ) =
        Real.exp b * ∫ ω, Real.exp (lam * X ω) ∂μ := by
    simp_rw [Real.exp_add]
    rw [integral_mul_const]
    ring
  have h_mgf :
      Real.exp b * ∫ ω, Real.exp (lam * X ω) ∂μ ≤
        Real.exp b * Real.exp (σ ^ 2 * lam ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left (hmgf lam) (Real.exp_pos _).le
  have h_opt :
        Real.exp b * Real.exp (σ ^ 2 * lam ^ 2 / 2) =
        Real.exp (-α * a ^ 2 / den) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [lam, b]
    field_simp [hα.ne', hden_ne]
    ring
  calc
    (∫ ω, Real.exp (-α * (X ω - a) ^ 2) ∂μ) ≤
        ∫ ω, Real.exp (lam * X ω + b) ∂μ := h_mono
    _ = Real.exp b * ∫ ω, Real.exp (lam * X ω) ∂μ := h_upper_integral
    _ ≤ Real.exp b * Real.exp (σ ^ 2 * lam ^ 2 / 2) := h_mgf
    _ = Real.exp (-α * a ^ 2 / den) := h_opt
    _ = Real.exp (-α * a ^ 2 / (1 + 2 * α * σ ^ 2)) := by rfl

/--
The exact sparse-row MGF implies the variance-normalized sub-Gaussian bound
used by the lower-tail trunk.  The identity
`(1 + cosh x) / 2 = cosh (x / 2)^2` keeps the sparse normalization explicit.
-/
theorem sparseRowMGF_subGaussian
    {d : ℕ} (a : Fin d → ℝ)
    (h_norm : ∑ i, a i ^ 2 = 1) (t : ℝ) :
    ∫ row, Real.exp (t * realRowDot row a) ∂(sparseRademacherRow d).toMeasure ≤
      Real.exp (t ^ 2 / 4) := by
  calc
    (∫ row, Real.exp (t * realRowDot row a) ∂(sparseRademacherRow d).toMeasure) =
        ∫ row, Real.exp (realRowDot row (fun i => t * a i))
          ∂(sparseRademacherRow d).toMeasure := by
      apply integral_congr_ae
      filter_upwards [] with row
      congr 1
      simp only [realRowDot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∏ i, (1 + Real.cosh (t * a i)) / 2 := by
      simp only [sparseRowMGF]
    _ = ∏ i, Real.cosh (t * a i / 2) ^ 2 := by
      apply Finset.prod_congr rfl
      intro i hi
      have harg : t * a i = 2 * (t * a i / 2) := by ring
      conv_lhs => rw [harg]
      rw [Real.cosh_two_mul, Real.cosh_sq]
      ring
    _ ≤ ∏ i, Real.exp ((t * a i) ^ 2 / 4) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        have hcosh := Real.cosh_le_exp_half_sq (t * a i / 2)
        have hsq := pow_le_pow_left₀ (Real.cosh_pos _).le hcosh 2
        calc
          Real.cosh (t * a i / 2) ^ 2 ≤
              Real.exp ((t * a i / 2) ^ 2 / 2) ^ 2 := hsq
          _ = Real.exp ((t * a i) ^ 2 / 4) := by
            rw [← Real.exp_nat_mul]
            congr 1
            ring
    _ = Real.exp (t ^ 2 / 4) := by
      rw [← Real.exp_sum]
      congr 1
      calc
        ∑ i, (t * a i) ^ 2 / 4 =
            (t ^ 2 / 4) * ∑ i, a i ^ 2 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = t ^ 2 / 4 := by rw [h_norm, mul_one]

end CertifiedJL
