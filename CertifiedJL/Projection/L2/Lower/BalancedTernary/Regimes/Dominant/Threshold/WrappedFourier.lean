/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.Fourier
import CertifiedJL.Projection.L2.Lower.BalancedTernary.WrappedFourier

/-!
# Shifted wrapped-Gaussian deletion for a dominant coordinate

The positive Poisson coefficients survive a fixed dominant shift with one
cosine phase.  Negative phases may be discarded, while nonnegative phases
retain coordinate-deletion monotonicity.
-/

open scoped BigOperators

open MeasureTheory

namespace CertifiedJL

/-- An integer Fourier mode with a fixed shift, after discarding a negative
phase. -/
noncomputable def nonnegativeShiftedSparseCyclicCosineModeInt
    (q : ℕ) (shift : ℤ) {d : ℕ} (w : Fin d → ℤ) (k : ℤ) : ℝ :=
  max 0 (Real.cos
      ((2 * Real.pi * (k : ℝ) / (q : ℝ)) * (shift : ℝ))) *
    sparseCyclicCosineModeInt q w k

/-- Exact shifted cosine transform for an integer cyclic mode. -/
theorem sparseRow_shiftedCosineTransform_int
    (q d : ℕ) (shift : ℤ) (w : Fin d → ℤ) (k : ℤ) :
    ∫ row, Real.cos
        ((2 * Real.pi * (k : ℝ) / (q : ℝ)) *
          ((shift + ∑ i, row i * w i : ℤ) : ℝ))
        ∂(sparseRademacherRow d).toMeasure =
      Real.cos
          ((2 * Real.pi * (k : ℝ) / (q : ℝ)) * (shift : ℝ)) *
        sparseCyclicCosineModeInt q w k := by
  have h := sparseRow_shiftedCosineTransform d
    (2 * Real.pi * (k : ℝ) / (q : ℝ)) (shift : ℝ)
    (fun i => (w i : ℝ))
  unfold sparseCyclicCosineModeInt
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with row
  congr 1
  simp only [realRowDot, Int.cast_add, Int.cast_sum, Int.cast_mul]

/-- A shifted mode is bounded by a coordinate-restricted mode after its
negative phase has been discarded. -/
theorem shiftedSparseCyclicCosineModeInt_le_nonnegative_restrict
    (q : ℕ) (shift : ℤ) {d : ℕ} (w : Fin d → ℤ)
    (support : Finset (Fin d)) (k : ℤ) :
    Real.cos
          ((2 * Real.pi * (k : ℝ) / (q : ℝ)) * (shift : ℝ)) *
        sparseCyclicCosineModeInt q w k ≤
      nonnegativeShiftedSparseCyclicCosineModeInt q shift
        (fun i => if i ∈ support then w i else 0) k := by
  let phase := Real.cos
    ((2 * Real.pi * (k : ℝ) / (q : ℝ)) * (shift : ℝ))
  by_cases hphase : 0 ≤ phase
  · rw [nonnegativeShiftedSparseCyclicCosineModeInt, max_eq_right hphase]
    exact mul_le_mul_of_nonneg_left
      (sparseCyclicCosineModeInt_le_restrict q w support k) hphase
  · rw [nonnegativeShiftedSparseCyclicCosineModeInt,
      max_eq_left (le_of_not_ge hphase), zero_mul]
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hphase)
      (sparseCyclicCosineModeInt_nonneg q w k)

set_option maxHeartbeats 800000 in
-- Interchanging the integer Fourier series with the finite row integral is intensive.
/-- Exact positive-Fourier evaluation of a shifted wrapped sparse row. -/
theorem sparseRow_shiftedWrappedGaussianKernel_integral_eq
    {q d : ℕ} (shift : ℤ) (w : Fin d → ℤ) {s : ℝ}
    (hq : 0 < q) (hs : 0 < s) :
    ∫ row, wrappedGaussianKernel q s
        (shift + ∑ i, row i * w i)
        ∂(sparseRademacherRow d).toMeasure =
      1 / Real.sqrt (s * (q : ℝ) ^ 2 / Real.pi) *
        ∑' k : ℤ,
          Real.exp
              (-Real.pi / (s * (q : ℝ) ^ 2 / Real.pi) * (k : ℝ) ^ 2) *
            (Real.cos
                ((2 * Real.pi * (k : ℝ) / (q : ℝ)) * (shift : ℝ)) *
              sparseCyclicCosineModeInt q w k) := by
  let a : ℝ := s * (q : ℝ) ^ 2 / Real.pi
  let weight : ℤ → ℝ := fun k =>
    Real.exp (-Real.pi / a * (k : ℝ) ^ 2)
  let F : ℤ → (Fin d → ℤ) → ℝ := fun k row =>
    weight k * Real.cos
      ((2 * Real.pi * (k : ℝ) / (q : ℝ)) *
        ((shift + ∑ i, row i * w i : ℤ) : ℝ))
  have hqReal : 0 < (q : ℝ) := by exact_mod_cast hq
  have ha : 0 < a := by dsimp [a]; positivity
  have hweight : Summable weight := by
    dsimp [weight]
    simpa only [neg_div] using
      summable_real_integer_exp_neg_sq (div_pos Real.pi_pos ha)
  have hFint (k : ℤ) : Integrable (F k) (sparseRademacherRow d).toMeasure := by
    refine (integrable_const (weight k)).mono'
      (measurable_of_countable _).aestronglyMeasurable ?_
    filter_upwards [] with row
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le
      (Real.abs_cos_le_one _)
  have hFnorm (k : ℤ) :
      ∫ row, ‖F k row‖ ∂(sparseRademacherRow d).toMeasure ≤ weight k := by
    calc
      ∫ row, ‖F k row‖ ∂(sparseRademacherRow d).toMeasure ≤
          ∫ _row, weight k ∂(sparseRademacherRow d).toMeasure := by
        apply integral_mono (hFint k).norm (integrable_const _)
        intro row
        change ‖F k row‖ ≤ weight k
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_of_le_one_right (Real.exp_pos _).le
          (Real.abs_cos_le_one _)
      _ = weight k := by simp
  have hFsum : Summable (fun k : ℤ =>
      ∫ row, ‖F k row‖ ∂(sparseRademacherRow d).toMeasure) := by
    apply hweight.of_nonneg_of_le
    · intro k
      exact integral_nonneg fun _ => norm_nonneg _
    · exact hFnorm
  have hswap := integral_tsum_of_summable_integral_norm hFint hFsum
  have hpointwise (row : Fin d → ℤ) :
      wrappedGaussianKernel q s (shift + ∑ i, row i * w i) =
        1 / Real.sqrt a * ∑' k : ℤ, F k row := by
    have hp := wrappedGaussianKernel_eq_positiveFourier
      hq hs (shift + ∑ i, row i * w i)
    dsimp [a, F, weight]
    convert hp using 1
    congr 1
    apply tsum_congr
    intro k
    congr 2
    push_cast
    field_simp [hqReal.ne']
  calc
    ∫ row, wrappedGaussianKernel q s (shift + ∑ i, row i * w i)
        ∂(sparseRademacherRow d).toMeasure =
        ∫ row, (1 / Real.sqrt a) * ∑' k : ℤ, F k row
          ∂(sparseRademacherRow d).toMeasure := by
      apply integral_congr_ae
      filter_upwards [] with row
      exact hpointwise row
    _ = (1 / Real.sqrt a) *
        ∫ row, ∑' k : ℤ, F k row
          ∂(sparseRademacherRow d).toMeasure := by
      rw [integral_const_mul]
    _ = (1 / Real.sqrt a) * ∑' k : ℤ,
        ∫ row, F k row ∂(sparseRademacherRow d).toMeasure := by
      rw [← hswap]
    _ = (1 / Real.sqrt a) * ∑' k : ℤ,
        weight k *
          (Real.cos
              ((2 * Real.pi * (k : ℝ) / (q : ℝ)) * (shift : ℝ)) *
            sparseCyclicCosineModeInt q w k) := by
      congr 1
      apply tsum_congr
      intro k
      dsimp [F]
      rw [integral_const_mul, sparseRow_shiftedCosineTransform_int]
    _ = _ := by rfl

/-- Shifted positive-Fourier deletion with all negative dominant phases
discarded. -/
theorem sparseRow_shiftedWrappedGaussianKernel_le_nonnegative_restrict
    {q d : ℕ} (shift : ℤ) (w : Fin d → ℤ)
    (support : Finset (Fin d)) {s : ℝ}
    (hq : 0 < q) (hs : 0 < s) :
    ∫ row, wrappedGaussianKernel q s
        (shift + ∑ i, row i * w i)
        ∂(sparseRademacherRow d).toMeasure ≤
      1 / Real.sqrt (s * (q : ℝ) ^ 2 / Real.pi) *
        ∑' k : ℤ,
          Real.exp
              (-Real.pi / (s * (q : ℝ) ^ 2 / Real.pi) * (k : ℝ) ^ 2) *
            nonnegativeShiftedSparseCyclicCosineModeInt q shift
              (fun i => if i ∈ support then w i else 0) k := by
  rw [sparseRow_shiftedWrappedGaussianKernel_integral_eq shift w hq hs]
  apply mul_le_mul_of_nonneg_left
  · apply Summable.tsum_le_tsum
    · intro k
      exact mul_le_mul_of_nonneg_left
        (shiftedSparseCyclicCosineModeInt_le_nonnegative_restrict
          q shift w support k) (Real.exp_nonneg _)
    · have hbase : Summable (fun k : ℤ =>
          Real.exp (-Real.pi /
            (s * (q : ℝ) ^ 2 / Real.pi) * (k : ℝ) ^ 2)) := by
        simpa only [neg_div] using summable_real_integer_exp_neg_sq
          (show 0 < Real.pi /
            (s * (q : ℝ) ^ 2 / Real.pi) by positivity)
      apply hbase.of_norm_bounded
      intro k
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_mul]
      rw [abs_of_nonneg (sparseCyclicCosineModeInt_nonneg q w k)]
      apply mul_le_of_le_one_right (Real.exp_pos _).le
      calc
        |Real.cos ((2 * Real.pi * (k : ℝ) / (q : ℝ)) * (shift : ℝ))| *
              sparseCyclicCosineModeInt q w k ≤
            1 * sparseCyclicCosineModeInt q w k :=
          mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _)
            (sparseCyclicCosineModeInt_nonneg q w k)
        _ ≤ 1 := by simpa using sparseCyclicCosineModeInt_le_one q w k
    · have hbase : Summable (fun k : ℤ =>
          Real.exp (-Real.pi /
            (s * (q : ℝ) ^ 2 / Real.pi) * (k : ℝ) ^ 2)) := by
        simpa only [neg_div] using summable_real_integer_exp_neg_sq
          (show 0 < Real.pi /
            (s * (q : ℝ) ^ 2 / Real.pi) by positivity)
      apply hbase.of_norm_bounded
      intro k
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_nonneg]
      · apply mul_le_of_le_one_right (Real.exp_pos _).le
        calc
          max 0 (Real.cos
                ((2 * Real.pi * (k : ℝ) / (q : ℝ)) * (shift : ℝ))) *
              sparseCyclicCosineModeInt q
                (fun i => if i ∈ support then w i else 0) k ≤
            1 * sparseCyclicCosineModeInt q
                (fun i => if i ∈ support then w i else 0) k :=
              mul_le_mul_of_nonneg_right
                (max_le (by norm_num) (Real.cos_le_one _))
                (sparseCyclicCosineModeInt_nonneg q
                  (fun i => if i ∈ support then w i else 0) k)
          _ ≤ 1 := by
            simpa using (sparseCyclicCosineModeInt_le_one q
              (fun i => if i ∈ support then w i else 0) k)
      · unfold nonnegativeShiftedSparseCyclicCosineModeInt
        exact mul_nonneg (le_max_left _ _)
          (sparseCyclicCosineModeInt_nonneg q
            (fun i => if i ∈ support then w i else 0) k)
  · have hqReal : 0 < (q : ℝ) := by exact_mod_cast hq
    exact div_nonneg (by norm_num) (Real.sqrt_nonneg _)

end CertifiedJL
