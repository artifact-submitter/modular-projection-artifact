/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Fourier.Periodization
import CertifiedJL.Analysis.Gaussian.IntegerGaussianTail
import CertifiedJL.Probability.Distributions.Gaussian.ShiftedGaussian
import CertifiedJL.Model.Vectors.SquaredNorm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Quantitative lower-tail periodization

This module supplies the quantitative part of the paper's periodization
lemma.  The pointwise and Tonelli bridges live in `Periodization`; here the
shifted sub-Gaussian estimate and the geometric tail are proved separately.
No certificate data is imported.
-/

open scoped BigOperators ENNReal

open MeasureTheory

namespace CertifiedJL

/--
The shifted Gaussian envelope specialized to the sparse-row variance
normalization `σ² = 1/2`.  Keeping this specialization explicit avoids hiding
the factor `1 + s` that is used by the modular-image bound.
-/
theorem shiftedSubGaussianImage
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (s a : ℝ)
    (hX_meas : Measurable X)
    (hX_int : ∀ t : ℝ,
      Integrable (fun ω => Real.exp (t * X ω)) μ)
    (hmgf : ∀ t : ℝ,
      ∫ ω, Real.exp (t * X ω) ∂μ ≤ Real.exp (t ^ 2 / 4))
    (hs : 0 < s) :
    ∫ ω, Real.exp (-s * (X ω - a) ^ 2) ∂μ ≤
      Real.exp (-s * a ^ 2 / (1 + s)) := by
  have hsigma : (Real.sqrt (1 / 2 : ℝ)) ^ 2 = (1 / 2 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  have hmgf' : ∀ t : ℝ,
      ∫ ω, Real.exp (t * X ω) ∂μ ≤
        Real.exp ((Real.sqrt (1 / 2 : ℝ)) ^ 2 * t ^ 2 / 2) := by
    intro t
    convert hmgf t using 1
    rw [hsigma]
    ring_nf
  have h := shiftedGaussianEnvelope X (Real.sqrt (1 / 2 : ℝ)) s a
    hX_meas hX_int hmgf' hs
  convert h using 1
  rw [hsigma]
  congr 1
  ring

/--
The normalized integer image used by the modular proof is an instance of the
preceding bound.  This wrapper records the exact `q / √V` shift without
silently replacing the integer-valued row statistic by a real surrogate.
-/
theorem normalizedIntegerImageBound
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (T : Ω → ℤ) (q : ℕ) (V s : ℝ) (n : ℤ)
    (hX_meas : Measurable (fun ω => (T ω : ℝ) / Real.sqrt V))
    (hX_int : ∀ t : ℝ,
      Integrable
        (fun ω => Real.exp (t * ((T ω : ℝ) / Real.sqrt V))) μ)
    (hmgf : ∀ t : ℝ,
      ∫ ω, Real.exp (t * ((T ω : ℝ) / Real.sqrt V)) ∂μ ≤
        Real.exp (t ^ 2 / 4))
    (hs : 0 < s) :
    ∫ ω,
        Real.exp
          (-s * (((T ω : ℝ) / Real.sqrt V) -
            (n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2) ∂μ ≤
      Real.exp
        (-s * ((n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) := by
  exact shiftedSubGaussianImage
    (fun ω => (T ω : ℝ) / Real.sqrt V)
    s ((n : ℝ) * (q : ℝ) / Real.sqrt V)
    hX_meas hX_int hmgf hs

/-! ## Sparse-row normalization -/

/--
The shifted image estimate specialized to an integer sparse-row dot product.
The hypothesis h_norm is the real cast of the squared coefficient mass;
keeping it explicit prevents the analytic layer from silently identifying a
natural-number norm with a real one.
-/
theorem sparseRow_normalizedIntegerImageBound
    {d : ℕ} (w : Fin d → ℤ) (q : ℕ) (V s : ℝ) (n : ℤ)
    (hV : 0 < V)
    (h_norm : ∑ i, (w i : ℝ) ^ 2 = V)
    (hs : 0 < s) :
    ∫ row, Real.exp
        (-s * (((∑ i, row i * w i : ℤ) : ℝ) / Real.sqrt V -
          (n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2)
        ∂(sparseRademacherRow d).toMeasure ≤
      Real.exp
        (-s * ((n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) := by
  let T : (Fin d → ℤ) → ℤ := fun row => ∑ i, row i * w i
  have hX_meas :
      Measurable (fun row : Fin d → ℤ => (T row : ℝ) / Real.sqrt V) := by
    exact measurable_of_countable _
  have hX_int : ∀ t : ℝ,
      Integrable
        (fun row : Fin d → ℤ =>
          Real.exp (t * ((T row : ℝ) / Real.sqrt V)))
        (sparseRademacherRow d).toMeasure := by
    intro t
    rw [sparseRademacherRow_eq_map_uniformRowSeed]
    rw [← PMF.toMeasure_map
      (p := PMF.uniformOfFintype (SparseRowSeed d))
      (f := sparseRow) (measurable_of_finite sparseRow)]
    apply (integrable_map_measure
      (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_finite sparseRow).aemeasurable).2
    exact Integrable.of_finite
  have h_norm' :
      ∑ i, ((w i : ℝ) / Real.sqrt V) ^ 2 = 1 := by
    have hsqrt : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hV.le
    have hsqrt_ne : Real.sqrt V ≠ 0 := (Real.sqrt_pos.2 hV).ne'
    calc
      ∑ i, ((w i : ℝ) / Real.sqrt V) ^ 2 =
          (1 / V) * ∑ i, (w i : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        field_simp [hsqrt_ne, hsqrt]
        rw [hsqrt]
      _ = 1 := by rw [h_norm]; field_simp
  have hmgf : ∀ t : ℝ,
      ∫ row, Real.exp (t * ((T row : ℝ) / Real.sqrt V))
          ∂(sparseRademacherRow d).toMeasure ≤
        Real.exp (t ^ 2 / 4) := by
    intro t
    have h := sparseRowMGF_subGaussian
      (fun i => (w i : ℝ) / Real.sqrt V) h_norm' t
    convert h using 1
    apply integral_congr_ae
    filter_upwards [] with row
    congr 1
    simp only [T, realRowDot]
    push_cast
    simp only [div_eq_mul_inv]
    calc
      t * ((∑ x, (row x : ℝ) * (w x : ℝ)) * (Real.sqrt V)⁻¹) =
          t * (∑ x, ((row x : ℝ) * (w x : ℝ)) * (Real.sqrt V)⁻¹) := by
        rw [Finset.sum_mul]
      _ = t * ∑ x, (row x : ℝ) * ((w x : ℝ) * (Real.sqrt V)⁻¹) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have h := normalizedIntegerImageBound
    (μ := (sparseRademacherRow d).toMeasure) T q V s n
    hX_meas hX_int hmgf hs
  simpa only [T] using h

/-- One active dominant image after normalization by a positive integer
amplitude.  The offset is literal: image `n` is centered at `n q / A - 1`. -/
theorem sparseRow_shiftedNormalizedIntegerImageBound
    {d : ℕ} (w : Fin d → ℤ) (q A : ℕ) (V z : ℝ) (n : ℤ)
    (hA : 0 < A) (hV : 0 < V)
    (h_norm : ∑ i, (w i : ℝ) ^ 2 = V) (hz : 0 < z) :
    let u : ℝ := V / (A : ℝ) ^ 2
    let B : ℝ := (q : ℝ) / (A : ℝ)
    let alpha : ℝ := z / (1 + z * u)
    ∫ row, Real.exp
        (-z * ((((A : ℤ) + ∑ i, row i * w i : ℤ) : ℝ) / (A : ℝ) -
          (n : ℝ) * B) ^ 2) ∂(sparseRademacherRow d).toMeasure ≤
      Real.exp (-alpha * ((n : ℝ) * B - 1) ^ 2) := by
  dsimp only
  let u : ℝ := V / (A : ℝ) ^ 2
  let s : ℝ := z * u
  let k : ℤ := n * (q : ℤ) - (A : ℤ)
  have hAr : 0 < (A : ℝ) := by exact_mod_cast hA
  have hsqrt : Real.sqrt V ^ 2 = V := Real.sq_sqrt hV.le
  have hsqrt_ne : Real.sqrt V ≠ 0 := (Real.sqrt_pos.2 hV).ne'
  have hs : 0 < s := by dsimp [s, u]; positivity
  have hbase := sparseRow_normalizedIntegerImageBound
    w 1 V s k hV h_norm hs
  convert hbase using 1
  · apply integral_congr_ae
    filter_upwards [] with row
    congr 1
    dsimp [s, u, k]
    push_cast
    field_simp [hAr.ne', hsqrt_ne, hsqrt]
    rw [hsqrt]
    ring
  · congr 1
    dsimp [s, u, k]
    push_cast
    field_simp [hAr.ne', hsqrt_ne, hsqrt]
    rw [hsqrt]
    ring

/-- Literal active periodization: the zero image remains the shifted row
kernel, while positive and negative nonzero images retain their distinct
geometric orientations. -/
theorem sparseRow_shiftedNormalizedPeriodization_nonzeroImageBound
    {d : ℕ} (w : Fin d → ℤ) (q A : ℕ) (V z : ℝ)
    (hq : Odd q) (hA : 0 < A) (hV : 0 < V)
    (h_norm : ∑ i, (w i : ℝ) ^ 2 = V) (hz : 0 < z)
    (hB : 1 < (q : ℝ) / (A : ℝ)) :
    let u : ℝ := V / (A : ℝ) ^ 2
    let B : ℝ := (q : ℝ) / (A : ℝ)
    let alpha : ℝ := z / (1 + z * u)
    ENNReal.ofReal
        (∫ row, Real.exp
          (-z * ((centeredMod q
            ((A : ℤ) + ∑ i, row i * w i : ℤ) : ℝ) / (A : ℝ)) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) ≤
      ENNReal.ofReal
        (∫ row, Real.exp
          (-z * ((((A : ℤ) + ∑ i, row i * w i : ℤ) : ℝ) /
            (A : ℝ)) ^ 2) ∂(sparseRademacherRow d).toMeasure) +
      ENNReal.ofReal
        (Real.exp (-alpha * (B - 1) ^ 2) /
            (1 - Real.exp (-alpha * (3 * B ^ 2 - 2 * B))) +
          Real.exp (-alpha * (B + 1) ^ 2) /
            (1 - Real.exp (-alpha * (3 * B ^ 2 + 2 * B)))) := by
  dsimp only
  let μ : Measure (Fin d → ℤ) := (sparseRademacherRow d).toMeasure
  let T : (Fin d → ℤ) → ℤ := fun row =>
    (A : ℤ) + ∑ i, row i * w i
  let u : ℝ := V / (A : ℝ) ^ 2
  let B : ℝ := (q : ℝ) / (A : ℝ)
  let alpha : ℝ := z / (1 + z * u)
  let s : ℝ := z / (A : ℝ) ^ 2
  let g : ℤ → ℝ≥0∞ := fun n => ENNReal.ofReal
    (Real.exp (-alpha * ((n : ℝ) * B - 1) ^ 2))
  have hAr : 0 < (A : ℝ) := by exact_mod_cast hA
  have hs : 0 < s := by dsimp [s]; positivity
  have hfinite (f : (Fin d → ℤ) → ℝ) : Integrable f μ := by
    dsimp [μ]
    rw [sparseRademacherRow_eq_map_uniformRowSeed]
    rw [← PMF.toMeasure_map
      (p := PMF.uniformOfFintype (SparseRowSeed d))
      (f := sparseRow) (measurable_of_finite sparseRow)]
    apply (integrable_map_measure
      (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_finite sparseRow).aemeasurable).2
    exact Integrable.of_finite
  have himage (n : ℤ) (hn : n ≠ 0) :
      ∫⁻ row, ENNReal.ofReal
          (Real.exp (-s * ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) ∂μ ≤
        g n := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (hfinite (fun row => Real.exp
        (-s * ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)))
      (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _))]
    apply ENNReal.ofReal_mono
    have hb := sparseRow_shiftedNormalizedIntegerImageBound
      w q A V z n hA hV h_norm hz
    have heq :
        (∫ row, Real.exp
          (-s * ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2) ∂μ) =
        ∫ row, Real.exp
          (-z * ((((A : ℤ) + ∑ i, row i * w i : ℤ) : ℝ) / (A : ℝ) -
            (n : ℝ) * B) ^ 2) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with row
      congr 1
      dsimp [s, T, B]
      push_cast
      field_simp [hAr.ne']
    rw [heq]
    simpa only [g, alpha, B, u, μ] using hb
  have hperiod := centeredPeriodization_tonelli_nonzero
    (sparseRademacherRow d) hq T (measurable_of_countable _) s hs g himage
  have hcenter :
      ENNReal.ofReal
          (∫ row, Real.exp
            (-z * ((centeredMod q (T row) : ℝ) / (A : ℝ)) ^ 2) ∂μ) =
        ∫⁻ row, ENNReal.ofReal
          (Real.exp (-s * (centeredMod q (T row) : ℝ) ^ 2)) ∂μ := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (hfinite (fun row => Real.exp
        (-s * (centeredMod q (T row) : ℝ) ^ 2)))
      (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _))]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with row
    congr 1
    dsimp [s]
    field_simp [hAr.ne']
  have hzero :
      (∫⁻ row, ENNReal.ofReal
          (Real.exp (-s * (T row : ℝ) ^ 2)) ∂μ) =
        ENNReal.ofReal
          (∫ row, Real.exp
            (-z * (((T row : ℝ) / (A : ℝ)) ^ 2)) ∂μ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (hfinite (fun row => Real.exp (-s * (T row : ℝ) ^ 2)))
      (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _))]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with row
    congr 1
    dsimp [s]
    field_simp [hAr.ne']
  have htail := integerShiftedGaussian_exp_nonzero_geometricTail
    alpha B (by dsimp [alpha, u]; positivity) (by simpa [B] using hB)
  calc
    ENNReal.ofReal
        (∫ row, Real.exp
          (-z * ((centeredMod q
            ((A : ℤ) + ∑ i, row i * w i : ℤ) : ℝ) / (A : ℝ)) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) =
        ∫⁻ row, ENNReal.ofReal
          (Real.exp (-s * (centeredMod q (T row) : ℝ) ^ 2)) ∂μ := by
      simpa [μ, T] using hcenter
    _ ≤ (∫⁻ row, ENNReal.ofReal
          (Real.exp (-s * (T row : ℝ) ^ 2)) ∂μ) +
        ∑' n : ℤ, if n = 0 then 0 else g n := hperiod
    _ = ENNReal.ofReal
          (∫ row, Real.exp
            (-z * (((T row : ℝ) / (A : ℝ)) ^ 2)) ∂μ) +
        ∑' n : ℤ, if n = 0 then 0 else g n := by rw [hzero]
    _ ≤ ENNReal.ofReal
          (∫ row, Real.exp
            (-z * (((T row : ℝ) / (A : ℝ)) ^ 2)) ∂μ) +
        ENNReal.ofReal
          (Real.exp (-alpha * (B - 1) ^ 2) /
              (1 - Real.exp (-alpha * (3 * B ^ 2 - 2 * B))) +
            Real.exp (-alpha * (B + 1) ^ 2) /
              (1 - Real.exp (-alpha * (3 * B ^ 2 + 2 * B)))) := by
      exact add_le_add le_rfl (by simpa [g] using htail)
    _ = _ := by simp [μ, T, alpha, B, u]

/-! ## Normalized Tonelli assembly -/

/-
The preceding row estimate is an estimate for one integer translate.  This
theorem keeps the complete two-sided image sum visible and only then applies
that estimate.  In particular, no nearest-representative or "zero image"
shortcut is hidden in the analytic interface.
-/
theorem sparseRow_normalizedPeriodization_imageBound
    {d : ℕ} (w : Fin d → ℤ) (q : ℕ) (V s : ℝ)
    (hq : Odd q) (hV : 0 < V)
    (h_norm : ∑ i, (w i : ℝ) ^ 2 = V)
    (hs : 0 < s) :
    ENNReal.ofReal
        (∫ row, Real.exp
          (-s * ((centeredMod q (∑ i, row i * w i : ℤ) : ℝ) /
            Real.sqrt V) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) ≤
      ∑' n : ℤ, ENNReal.ofReal
        (Real.exp
          (-s * ((n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))) := by
  let μ : Measure (Fin d → ℤ) := (sparseRademacherRow d).toMeasure
  let T : (Fin d → ℤ) → ℤ := fun row => ∑ i, row i * w i
  have hsqrt : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hV.le
  have hsqrt_ne : Real.sqrt V ≠ 0 := (Real.sqrt_pos.2 hV).ne'
  have hcenter_exp (row : Fin d → ℤ) :
      -s * (((centeredMod q (T row) : ℝ) / Real.sqrt V) ^ 2) =
        -(s / V) * (centeredMod q (T row) : ℝ) ^ 2 := by
    field_simp [hsqrt_ne, hsqrt]
    rw [hsqrt]
  have himage_exp (n : ℤ) (row : Fin d → ℤ) :
      -s * (((T row : ℝ) / Real.sqrt V -
        (n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2) =
        -(s / V) * ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2 := by
    field_simp [hsqrt_ne, hsqrt]
    rw [hsqrt]
    ring
  have hfinite_integrable (f : (Fin d → ℤ) → ℝ) :
      Integrable f μ := by
    dsimp [μ]
    rw [sparseRademacherRow_eq_map_uniformRowSeed]
    rw [← PMF.toMeasure_map
      (p := PMF.uniformOfFintype (SparseRowSeed d))
      (f := sparseRow) (measurable_of_finite sparseRow)]
    apply (integrable_map_measure
      (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_finite sparseRow).aemeasurable).2
    exact Integrable.of_finite
  have hcenter_lintegral :
      ENNReal.ofReal
          (∫ row, Real.exp
            (-s * (((centeredMod q (T row) : ℝ) / Real.sqrt V) ^ 2)) ∂μ) =
        ∫⁻ row, ENNReal.ofReal
          (Real.exp (-(s / V) * (centeredMod q (T row) : ℝ) ^ 2)) ∂μ := by
    calc
      ENNReal.ofReal
          (∫ row, Real.exp
            (-s * (((centeredMod q (T row) : ℝ) / Real.sqrt V) ^ 2)) ∂μ) =
          ENNReal.ofReal
            (∫ row, Real.exp
              (-(s / V) * (centeredMod q (T row) : ℝ) ^ 2) ∂μ) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with row
        rw [hcenter_exp]
      _ = ∫⁻ row, ENNReal.ofReal
          (Real.exp (-(s / V) * (centeredMod q (T row) : ℝ) ^ 2)) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal
          (hfinite_integrable (fun row => Real.exp
            (-(s / V) * (centeredMod q (T row) : ℝ) ^ 2)))
          (Filter.Eventually.of_forall (fun row => Real.exp_nonneg _))
  have hperiod := centeredPeriodization_tonelli
    (p := sparseRademacherRow d) hq T (measurable_of_countable _)
      (s / V) (div_pos hs hV)
  have himage_lintegral (n : ℤ) :
      ∫⁻ row, ENNReal.ofReal
          (Real.exp (-(s / V) *
            ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) ∂μ =
        ENNReal.ofReal
          (∫ row, Real.exp
            (-s * (((T row : ℝ) / Real.sqrt V -
              (n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2)) ∂μ) := by
    calc
      ∫⁻ row, ENNReal.ofReal
          (Real.exp (-(s / V) *
            ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) ∂μ =
          ∫⁻ row, ENNReal.ofReal
            (Real.exp (-s * (((T row : ℝ) / Real.sqrt V -
              (n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2))) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [] with row
        rw [himage_exp]
      _ = ENNReal.ofReal
          (∫ row, Real.exp
            (-s * (((T row : ℝ) / Real.sqrt V -
              (n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2)) ∂μ) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal
          (hfinite_integrable (fun row => Real.exp
            (-s * (((T row : ℝ) / Real.sqrt V -
              (n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2))))
          (Filter.Eventually.of_forall (fun row => Real.exp_nonneg _))
  calc
    ENNReal.ofReal
        (∫ row, Real.exp
          (-s * (((centeredMod q (∑ i, row i * w i : ℤ) : ℝ) /
            Real.sqrt V) ^ 2)) ∂μ) =
      ENNReal.ofReal
        (∫ row, Real.exp
          (-s * (((centeredMod q (T row) : ℝ) / Real.sqrt V) ^ 2)) ∂μ) := by
        congr 1
    _ = ∫⁻ row, ENNReal.ofReal
          (Real.exp (-(s / V) * (centeredMod q (T row) : ℝ) ^ 2)) ∂μ :=
      hcenter_lintegral
    _ ≤ ∑' n : ℤ, ∫⁻ row, ENNReal.ofReal
          (Real.exp (-(s / V) *
            ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) ∂μ := hperiod
    _ = ∑' n : ℤ, ENNReal.ofReal
          (∫ row, Real.exp
            (-s * (((T row : ℝ) / Real.sqrt V -
              (n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2)) ∂μ) := by
      apply tsum_congr
      intro n
      exact himage_lintegral n
    _ ≤ ∑' n : ℤ, ENNReal.ofReal
          (Real.exp
            (-s * ((n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))) := by
      apply ENNReal.tsum_le_tsum
      intro n
      apply ENNReal.ofReal_mono
      simpa [μ, T] using
        sparseRow_normalizedIntegerImageBound w q V s n hV h_norm hs

/--
The periodization interface in the headline's natural squared-norm
notation.  The nonzero-vector hypothesis supplies the positive denominator,
while `realCast_sqNorm` supplies the exact real normalization.
-/
theorem sparseRow_sqNorm_normalizedPeriodization_imageBound
    {d : ℕ} (w : Fin d → ℤ) (q : ℕ) (s : ℝ)
    (hq : Odd q) (hw : w ≠ 0) (hs : 0 < s) :
    ENNReal.ofReal
        (∫ row, Real.exp
          (-s * ((centeredMod q (∑ i, row i * w i : ℤ) : ℝ) /
            Real.sqrt (sqNorm w : ℝ)) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) ≤
      ∑' n : ℤ, ENNReal.ofReal
        (Real.exp
          (-s * ((n : ℝ) * (q : ℝ) / Real.sqrt (sqNorm w : ℝ)) ^ 2 /
            (1 + s))) := by
  have hsq_pos_nat : 0 < sqNorm w := (sqNorm_pos_iff w).2 hw
  have hsq_pos : 0 < (sqNorm w : ℝ) := by
    exact_mod_cast hsq_pos_nat
  simpa using sparseRow_normalizedPeriodization_imageBound
    w q (sqNorm w : ℝ) s hq hsq_pos (realCast_sqNorm w).symm hs

/--
The complete-image compatibility estimate. It deliberately includes the
zero image in the `1 + ...` budget and must not be used where the scalar
Fourier/Hölder bound consumes the zero image separately; use
`sparseRow_normalizedPeriodization_nonzeroImageBound` for that boundary.
-/
theorem sparseRow_normalizedPeriodization_geometricBound
    {d : ℕ} (w : Fin d → ℤ) (q : ℕ) (V s : ℝ)
    (hq : Odd q) (hV : 0 < V)
    (h_norm : ∑ i, (w i : ℝ) ^ 2 = V)
    (hs : 0 < s) :
    ENNReal.ofReal
        (∫ row, Real.exp
          (-s * ((centeredMod q (∑ i, row i * w i : ℤ) : ℝ) /
            Real.sqrt V) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) ≤
      ENNReal.ofReal
        (1 + 2 * Real.exp
          (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) /
          (1 - (Real.exp
            (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))) ^ 3)) := by
  let c : ℝ := s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)
  have hq_pos_nat : 0 < q := hq.pos
  have hq_pos : 0 < (q : ℝ) := by
    exact_mod_cast hq_pos_nat
  have hsqrt_pos : 0 < Real.sqrt V := Real.sqrt_pos.2 hV
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have himage := sparseRow_normalizedPeriodization_imageBound
    w q V s hq hV h_norm hs
  have hsum := integerGaussian_exp_geometricTail c hc
  have hterm (n : ℤ) :
      -s * (((n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2) / (1 + s) =
        -c * (n : ℝ) ^ 2 := by
    dsimp [c]
    ring
  calc
    ENNReal.ofReal
        (∫ row, Real.exp
          (-s * ((centeredMod q (∑ i, row i * w i : ℤ) : ℝ) /
            Real.sqrt V) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) ≤
        ∑' n : ℤ, ENNReal.ofReal
          (Real.exp
            (-s * ((n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))) := himage
    _ = ∑' n : ℤ, ENNReal.ofReal
        (Real.exp (-c * (n : ℝ) ^ 2)) := by
      apply tsum_congr
      intro n
      congr 1
      rw [hterm]
    _ ≤ ENNReal.ofReal (1 + 2 * Real.exp (-c) /
        (1 - (Real.exp (-c)) ^ 3)) := hsum
    _ = ENNReal.ofReal
        (1 + 2 * Real.exp
          (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) /
          (1 - (Real.exp
            (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))) ^ 3)) := by
      dsimp [c]
      have harg :
          -(s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) =
            -(s * ((q : ℝ) / Real.sqrt V) ^ 2) / (1 + s) := by
        ring
      rw [harg]
      congr 1
      ring_nf

/--
The zero image is not part of the geometric error budget. This explicit tail
theorem is the quantitative form consumed by the lower-tail proof: the
unmodulated row kernel remains available as a separate first term.
-/
theorem sparseRow_normalizedPeriodization_nonzeroImageBound
    {d : ℕ} (w : Fin d → ℤ) (q : ℕ) (V s : ℝ)
    (hq : Odd q) (hV : 0 < V)
    (h_norm : ∑ i, (w i : ℝ) ^ 2 = V)
    (hs : 0 < s) :
    ENNReal.ofReal
        (∫ row, Real.exp
          (-s * ((centeredMod q (∑ i, row i * w i : ℤ) : ℝ) /
            Real.sqrt V) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) ≤
      ENNReal.ofReal
        (∫ row, Real.exp
          (-s * (((∑ i, row i * w i : ℤ) : ℝ) /
            Real.sqrt V) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) +
      ENNReal.ofReal
        (2 * Real.exp
          (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) /
          (1 - (Real.exp
            (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))) ^ 3)) := by
  let μ : Measure (Fin d → ℤ) := (sparseRademacherRow d).toMeasure
  let T : (Fin d → ℤ) → ℤ := fun row => ∑ i, row i * w i
  have hsqrt : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hV.le
  have hsqrt_ne : Real.sqrt V ≠ 0 := (Real.sqrt_pos.2 hV).ne'
  have hcenter_exp (row : Fin d → ℤ) :
      -s * (((centeredMod q (T row) : ℝ) / Real.sqrt V) ^ 2) =
        -(s / V) * (centeredMod q (T row) : ℝ) ^ 2 := by
    field_simp [hsqrt_ne, hsqrt]
    rw [hsqrt]
  have hzero_exp (row : Fin d → ℤ) :
      -s * (((T row : ℝ) / Real.sqrt V) ^ 2) =
        -(s / V) * (T row : ℝ) ^ 2 := by
    field_simp [hsqrt_ne, hsqrt]
    rw [hsqrt]
  have himage_exp (n : ℤ) (row : Fin d → ℤ) :
      -s * (((T row : ℝ) / Real.sqrt V -
        (n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2) =
        -(s / V) * ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2 := by
    field_simp [hsqrt_ne, hsqrt]
    rw [hsqrt]
    ring
  have hfinite_integrable (f : (Fin d → ℤ) → ℝ) :
      Integrable f μ := by
    dsimp [μ]
    rw [sparseRademacherRow_eq_map_uniformRowSeed]
    rw [← PMF.toMeasure_map
      (p := PMF.uniformOfFintype (SparseRowSeed d))
      (f := sparseRow) (measurable_of_finite sparseRow)]
    apply (integrable_map_measure
      (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_finite sparseRow).aemeasurable).2
    exact Integrable.of_finite
  have hcenter_lintegral :
      ENNReal.ofReal
          (∫ row, Real.exp
            (-s * (((centeredMod q (T row) : ℝ) / Real.sqrt V) ^ 2)) ∂μ) =
        ∫⁻ row, ENNReal.ofReal
          (Real.exp (-(s / V) * (centeredMod q (T row) : ℝ) ^ 2)) ∂μ := by
    calc
      ENNReal.ofReal
          (∫ row, Real.exp
            (-s * (((centeredMod q (T row) : ℝ) / Real.sqrt V) ^ 2)) ∂μ) =
          ENNReal.ofReal
            (∫ row, Real.exp
              (-(s / V) * (centeredMod q (T row) : ℝ) ^ 2) ∂μ) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with row
        rw [hcenter_exp]
      _ = ∫⁻ row, ENNReal.ofReal
          (Real.exp (-(s / V) * (centeredMod q (T row) : ℝ) ^ 2)) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal
          (hfinite_integrable (fun row => Real.exp
            (-(s / V) * (centeredMod q (T row) : ℝ) ^ 2)))
          (Filter.Eventually.of_forall (fun row => Real.exp_nonneg _))
  have hnonmod_lintegral :
      ENNReal.ofReal
          (∫ row, Real.exp
            (-s * (((T row : ℝ) / Real.sqrt V) ^ 2)) ∂μ) =
        ∫⁻ row, ENNReal.ofReal
          (Real.exp (-(s / V) * (T row : ℝ) ^ 2)) ∂μ := by
    calc
      ENNReal.ofReal
          (∫ row, Real.exp
            (-s * (((T row : ℝ) / Real.sqrt V) ^ 2)) ∂μ) =
          ENNReal.ofReal
            (∫ row, Real.exp
              (-(s / V) * (T row : ℝ) ^ 2) ∂μ) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with row
        rw [hzero_exp]
      _ = ∫⁻ row, ENNReal.ofReal
          (Real.exp (-(s / V) * (T row : ℝ) ^ 2)) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal
          (hfinite_integrable (fun row => Real.exp
            (-(s / V) * (T row : ℝ) ^ 2)))
          (Filter.Eventually.of_forall (fun row => Real.exp_nonneg _))
  have hperiod := centeredPeriodization_tonelli
    (p := sparseRademacherRow d) hq T (measurable_of_countable _)
      (s / V) (div_pos hs hV)
  have himage_lintegral (n : ℤ) :
      ∫⁻ row, ENNReal.ofReal
          (Real.exp (-(s / V) *
            ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) ∂μ =
        ENNReal.ofReal
          (∫ row, Real.exp
            (-s * (((T row : ℝ) / Real.sqrt V -
              (n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2)) ∂μ) := by
    calc
      ∫⁻ row, ENNReal.ofReal
          (Real.exp (-(s / V) *
            ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) ∂μ =
          ∫⁻ row, ENNReal.ofReal
            (Real.exp (-s * (((T row : ℝ) / Real.sqrt V -
              (n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2))) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [] with row
        rw [himage_exp]
      _ = ENNReal.ofReal
          (∫ row, Real.exp
            (-s * (((T row : ℝ) / Real.sqrt V -
              (n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2)) ∂μ) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal
          (hfinite_integrable (fun row => Real.exp
            (-s * (((T row : ℝ) / Real.sqrt V -
              (n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2))))
          (Filter.Eventually.of_forall (fun row => Real.exp_nonneg _))
  have hzero_image :
      ∫⁻ row, ENNReal.ofReal
          (Real.exp (-(s / V) *
            ((T row : ℝ) - (0 : ℤ) * (q : ℝ)) ^ 2)) ∂μ =
        ENNReal.ofReal
          (∫ row, Real.exp
            (-s * (((T row : ℝ) / Real.sqrt V) ^ 2)) ∂μ) := by
    rw [himage_lintegral 0]
    simp only [Int.cast_zero, zero_mul, zero_div, sub_zero]
  have hnonzero (n : ℤ) (hn : n ≠ 0) :
      ∫⁻ row, ENNReal.ofReal
          (Real.exp (-(s / V) *
            ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) ∂μ ≤
        ENNReal.ofReal
          (Real.exp
            (-s * ((n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))) := by
    rw [himage_lintegral n]
    apply ENNReal.ofReal_mono
    simpa [μ, T] using
      sparseRow_normalizedIntegerImageBound w q V s n hV h_norm hs
  have htail_image :
      (∑' n : ℤ,
        (if n = 0 then (0 : ℝ≥0∞) else
          (∫⁻ row, ENNReal.ofReal
            (Real.exp (-(s / V) *
              ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) ∂μ))) ≤
      (∑' n : ℤ,
        (if n = 0 then (0 : ℝ≥0∞) else
          ENNReal.ofReal
            (Real.exp
              (-s * ((n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))))) := by
    apply ENNReal.tsum_le_tsum
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · simp only [if_neg hn]
      exact hnonzero n hn
  let c : ℝ := s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)
  have hq_pos_nat : 0 < q := hq.pos
  have hq_pos : 0 < (q : ℝ) := by exact_mod_cast hq_pos_nat
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hsqrt_pos : 0 < Real.sqrt V := Real.sqrt_pos.2 hV
  have hterm (n : ℤ) :
      -s * ((n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2 / (1 + s) =
        -c * (n : ℝ) ^ 2 := by
    dsimp [c]
    ring
  have htail_scalar :
      (∑' n : ℤ,
        (if n = 0 then (0 : ℝ≥0∞) else
          ENNReal.ofReal
            (Real.exp
              (-s * ((n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))))) ≤
      ENNReal.ofReal
        (2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3)) := by
    calc
      (∑' n : ℤ,
        (if n = 0 then (0 : ℝ≥0∞) else
          ENNReal.ofReal
            (Real.exp
              (-s * ((n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))))) =
          ∑' n : ℤ,
            (if n = 0 then (0 : ℝ≥0∞) else
              ENNReal.ofReal (Real.exp (-c * (n : ℝ) ^ 2))) := by
        apply tsum_congr
        intro n
        by_cases hn : n = 0
        · simp [hn]
        · simp only [if_neg hn]
          congr 1
          rw [hterm]
      _ ≤ ENNReal.ofReal
          (2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3)) :=
        integerGaussian_exp_nonzero_geometricTail c hc
  have hfirst :
      ENNReal.ofReal
          (∫ row, Real.exp
            (-s * (((T row : ℝ) / Real.sqrt V) ^ 2)) ∂μ) =
        ENNReal.ofReal
          (∫ row, Real.exp
            (-s * (((∑ i, row i * w i : ℤ) : ℝ) /
              Real.sqrt V) ^ 2)
            ∂(sparseRademacherRow d).toMeasure) := by
    simp [μ, T]
  calc
    ENNReal.ofReal
        (∫ row, Real.exp
          (-s * ((centeredMod q (∑ i, row i * w i : ℤ) : ℝ) /
            Real.sqrt V) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) =
      ∫⁻ row, ENNReal.ofReal
          (Real.exp (-(s / V) * (centeredMod q (T row) : ℝ) ^ 2)) ∂μ := by
      simpa [μ, T] using hcenter_lintegral
    _ ≤ ∑' n : ℤ, ∫⁻ row, ENNReal.ofReal
          (Real.exp (-(s / V) *
            ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) ∂μ := by
      simpa using hperiod
    _ = ENNReal.ofReal
          (∫ row, Real.exp
            (-s * (((T row : ℝ) / Real.sqrt V) ^ 2)) ∂μ) +
        (∑' n : ℤ,
          (if n = 0 then (0 : ℝ≥0∞) else
            (∫⁻ row, ENNReal.ofReal
              (Real.exp (-(s / V) *
                ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) ∂μ))) := by
      rw [ENNReal.tsum_eq_add_tsum_ite (f := fun n : ℤ =>
        ∫⁻ row, ENNReal.ofReal
          (Real.exp (-(s / V) *
            ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) ∂μ) 0]
      rw [hzero_image]
      congr 1
      apply tsum_congr
      intro n
      split_ifs <;> rfl
    _ ≤ ENNReal.ofReal
          (∫ row, Real.exp
            (-s * (((T row : ℝ) / Real.sqrt V) ^ 2)) ∂μ) +
        (∑' n : ℤ,
          (if n = 0 then (0 : ℝ≥0∞) else
            ENNReal.ofReal
              (Real.exp
                (-s * ((n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))))) :=
      by
        exact add_le_add_right htail_image _
      _ ≤ ENNReal.ofReal
          (∫ row, Real.exp
            (-s * (((T row : ℝ) / Real.sqrt V) ^ 2)) ∂μ) +
        ENNReal.ofReal
          (2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3)) :=
      by
        exact add_le_add_right htail_scalar _
    _ = ENNReal.ofReal
          (∫ row, Real.exp
            (-s * (((∑ i, row i * w i : ℤ) : ℝ) /
              Real.sqrt V) ^ 2)
            ∂(sparseRademacherRow d).toMeasure) +
        ENNReal.ofReal
          (2 * Real.exp
            (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)) /
            (1 - (Real.exp
              (-s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))) ^ 3)) := by
      rw [hfirst]
      congr 1
      dsimp [c]
      ring_nf

/-- The nonzero-image bound in the headline's natural `sqNorm` notation. -/
theorem sparseRow_sqNorm_normalizedPeriodization_nonzeroImageBound
    {d : ℕ} (w : Fin d → ℤ) (q : ℕ) (s : ℝ)
    (hq : Odd q) (hw : w ≠ 0) (hs : 0 < s) :
    ENNReal.ofReal
        (∫ row, Real.exp
          (-s * ((centeredMod q (∑ i, row i * w i : ℤ) : ℝ) /
            Real.sqrt (sqNorm w : ℝ)) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) ≤
      ENNReal.ofReal
        (∫ row, Real.exp
          (-s * (((∑ i, row i * w i : ℤ) : ℝ) /
            Real.sqrt (sqNorm w : ℝ)) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) +
      ENNReal.ofReal
        (2 * Real.exp
          (-s * ((q : ℝ) / Real.sqrt (sqNorm w : ℝ)) ^ 2 / (1 + s)) /
          (1 - (Real.exp
            (-s * ((q : ℝ) / Real.sqrt (sqNorm w : ℝ)) ^ 2 /
              (1 + s))) ^ 3)) := by
  have hsq_pos_nat : 0 < sqNorm w := (sqNorm_pos_iff w).2 hw
  have hsq_pos : 0 < (sqNorm w : ℝ) := by
    exact_mod_cast hsq_pos_nat
  simpa using sparseRow_normalizedPeriodization_nonzeroImageBound
    w q (sqNorm w : ℝ) s hq hsq_pos (realCast_sqNorm w).symm hs

theorem sparseRow_sqNorm_normalizedPeriodization_geometricBound
    {d : ℕ} (w : Fin d → ℤ) (q : ℕ) (s : ℝ)
    (hq : Odd q) (hw : w ≠ 0) (hs : 0 < s) :
    ENNReal.ofReal
        (∫ row, Real.exp
          (-s * ((centeredMod q (∑ i, row i * w i : ℤ) : ℝ) /
            Real.sqrt (sqNorm w : ℝ)) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) ≤
      ENNReal.ofReal
        (1 + 2 * Real.exp
          (-s * ((q : ℝ) / Real.sqrt (sqNorm w : ℝ)) ^ 2 / (1 + s)) /
          (1 - (Real.exp
            (-s * ((q : ℝ) / Real.sqrt (sqNorm w : ℝ)) ^ 2 /
              (1 + s))) ^ 3)) := by
  have hsq_pos_nat : 0 < sqNorm w := (sqNorm_pos_iff w).2 hw
  have hsq_pos : 0 < (sqNorm w : ℝ) := by
    exact_mod_cast hsq_pos_nat
  simpa using sparseRow_normalizedPeriodization_geometricBound
    w q (sqNorm w : ℝ) s hq hsq_pos (realCast_sqNorm w).symm hs

end CertifiedJL
