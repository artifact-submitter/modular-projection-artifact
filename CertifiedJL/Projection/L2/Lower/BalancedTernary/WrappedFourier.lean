/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Fourier
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Shared.Scalar.LobeTail
import CertifiedJL.Analysis.Fourier.LowerPeriodization
import CertifiedJL.Analysis.Fourier.Periodization
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Positive Fourier transport for wrapped threshold Gaussians

The centered modular Gaussian is first dominated by its complete integer-image
periodization.  Poisson summation writes that wrapped Gaussian as an absolutely
convergent Fourier series with nonnegative Gaussian coefficients.  Sparse-row
characteristic factors lie in `[0,1]`, so deleting coordinates can only increase
the wrapped expectation.  This is the analytic transport from an arbitrary
input to the compact greedy subprofile used by the public-threshold proof.
-/

open scoped BigOperators ENNReal FourierTransform Real

open MeasureTheory

namespace CertifiedJL

/-- Shifted Poisson summation for a real Gaussian, kept in complex form until
the conjugate frequencies are paired. -/
theorem complex_tsum_exp_neg_sq_sub_poisson
    {a x : ℝ} (ha : 0 < a) :
    (∑' n : ℤ, Complex.exp
        (-(Real.pi : ℂ) * (a : ℂ) * ((n : ℂ) - (x : ℂ)) ^ 2)) =
      1 / (a : ℂ) ^ (1 / 2 : ℂ) *
        ∑' n : ℤ,
          Complex.exp
              (-(Real.pi : ℂ) / (a : ℂ) * (n : ℂ) ^ 2) *
            Complex.exp
              (-(2 * Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ)) := by
  have h := Complex.tsum_exp_neg_quadratic
    (a := (a : ℂ)) (by simpa using ha) ((a * x : ℝ) : ℂ)
  let c : ℂ := Complex.exp (-(Real.pi : ℂ) * (a : ℂ) * (x : ℂ) ^ 2)
  have hc := congrArg (fun y : ℂ ↦ c * y) h
  rw [mul_assoc] at hc
  calc
    (∑' n : ℤ, Complex.exp
        (-(Real.pi : ℂ) * (a : ℂ) * ((n : ℂ) - (x : ℂ)) ^ 2)) =
        c * ∑' n : ℤ, Complex.exp
          (-(Real.pi : ℂ) * (a : ℂ) * (n : ℂ) ^ 2 +
            2 * (Real.pi : ℂ) * ((a * x : ℝ) : ℂ) * (n : ℂ)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      dsimp [c]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = c * (1 / (a : ℂ) ^ (1 / 2 : ℂ) *
        ∑' n : ℤ, Complex.exp
          (-(Real.pi : ℂ) / (a : ℂ) *
            ((n : ℂ) + Complex.I * ((a * x : ℝ) : ℂ)) ^ 2)) := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hc
    _ = 1 / (a : ℂ) ^ (1 / 2 : ℂ) *
        ∑' n : ℤ,
          Complex.exp
              (-(Real.pi : ℂ) / (a : ℂ) * (n : ℂ) ^ 2) *
            Complex.exp
              (-(2 * Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ)) := by
      rw [show c * (1 / (a : ℂ) ^ (1 / 2 : ℂ) *
          ∑' n : ℤ, Complex.exp
            (-(Real.pi : ℂ) / (a : ℂ) *
              ((n : ℂ) + Complex.I * ((a * x : ℝ) : ℂ)) ^ 2)) =
          1 / (a : ℂ) ^ (1 / 2 : ℂ) *
            (c * ∑' n : ℤ, Complex.exp
              (-(Real.pi : ℂ) / (a : ℂ) *
                ((n : ℂ) + Complex.I * ((a * x : ℝ) : ℂ)) ^ 2)) by ring]
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      dsimp [c]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
      field_simp [ha0]
      push_cast
      ring_nf
      simp only [Complex.I_sq]
      ring

/-- Real cosine-series form of shifted Gaussian Poisson summation.  Every
Fourier weight on the right is nonnegative. -/
theorem tsum_exp_neg_sq_sub_poisson
    {a x : ℝ} (ha : 0 < a) :
    (∑' n : ℤ, Real.exp
        (-Real.pi * a * ((n : ℝ) - x) ^ 2)) =
      1 / Real.sqrt a *
        ∑' n : ℤ,
          Real.exp (-Real.pi / a * (n : ℝ) ^ 2) *
            Real.cos (2 * Real.pi * (n : ℝ) * x) := by
  let term : ℤ → ℂ := fun n =>
    Complex.exp (-(Real.pi : ℂ) / (a : ℂ) * (n : ℂ) ^ 2) *
      Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ))
  have hweight : Summable (fun n : ℤ =>
      Real.exp (-(Real.pi / a) * (n : ℝ) ^ 2)) :=
    summable_real_integer_exp_neg_sq (div_pos Real.pi_pos ha)
  have htermNorm (n : ℤ) :
      ‖term n‖ = Real.exp (-(Real.pi / a) * (n : ℝ) ^ 2) := by
    dsimp [term]
    have hfirst :
        Complex.exp (-(Real.pi : ℂ) / (a : ℂ) * (n : ℂ) ^ 2) =
          (Real.exp (-(Real.pi / a) * (n : ℝ) ^ 2) : ℝ) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    have hsecond :
        -(2 * Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ) =
          ((-(2 * Real.pi * (n : ℝ) * x) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hfirst, hsecond, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Complex.norm_exp_ofReal_mul_I, mul_one]
  have hterm : Summable term := by
    apply Summable.of_norm
    simpa only [htermNorm] using hweight
  have hcomplex := complex_tsum_exp_neg_sq_sub_poisson (x := x) ha
  have hre := congrArg Complex.re hcomplex
  change _ = (1 / (a : ℂ) ^ (1 / 2 : ℂ) * ∑' n : ℤ, term n).re at hre
  have hpow : (a : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt a : ℝ) := by
    simpa [Real.sqrt_eq_rpow] using
      (Complex.ofReal_cpow ha.le (1 / 2 : ℝ)).symm
  have hfactor :
      (1 / (a : ℂ) ^ (1 / 2 : ℂ)).re = 1 / Real.sqrt a := by
    rw [hpow]
    simp
  have hleft :
      (∑' n : ℤ, Complex.exp
        (-(Real.pi : ℂ) * (a : ℂ) * ((n : ℂ) - (x : ℂ)) ^ 2)).re =
        ∑' n : ℤ, Real.exp
          (-Real.pi * a * ((n : ℝ) - x) ^ 2) := by
    have hsumEq :
        (∑' n : ℤ, Complex.exp
          (-(Real.pi : ℂ) * (a : ℂ) * ((n : ℂ) - (x : ℂ)) ^ 2)) =
          ((∑' n : ℤ, Real.exp
            (-Real.pi * a * ((n : ℝ) - x) ^ 2) : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]
      apply tsum_congr
      intro n
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      rfl
    rw [hsumEq]
    simp
  have htermRe (n : ℤ) :
      (term n).re =
        Real.exp (-Real.pi / a * (n : ℝ) ^ 2) *
          Real.cos (2 * Real.pi * (n : ℝ) * x) := by
    dsimp [term]
    rw [Complex.mul_re]
    have hfirst :
        Complex.exp (-(Real.pi : ℂ) / (a : ℂ) * (n : ℂ) ^ 2) =
          (Real.exp (-Real.pi / a * (n : ℝ) ^ 2) : ℝ) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      rfl
    rw [hfirst]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [show -(2 * Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ) =
        ((-(2 * Real.pi * (n : ℝ) * x) : ℝ) : ℂ) * Complex.I by
      push_cast
      ring]
    rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  rw [hleft] at hre
  have hfactorIm : (1 / (a : ℂ) ^ (1 / 2 : ℂ)).im = 0 := by
    rw [hpow]
    simp
  rw [Complex.mul_re, hfactor, hfactorIm, zero_mul, sub_zero,
    Complex.re_tsum hterm] at hre
  simpa only [htermRe] using hre

/-- A translated real Gaussian is summable over the integers. -/
theorem summable_exp_neg_mul_int_sub_sq
    {c x : ℝ} (hc : 0 < c) :
    Summable (fun n : ℤ => Real.exp (-c * ((n : ℝ) - x) ^ 2)) := by
  have hbase := summable_real_integer_exp_neg_sq (show 0 < c / 2 by positivity)
  have hdom : Summable (fun n : ℤ =>
      Real.exp (c * x ^ 2) * Real.exp (-(c / 2) * (n : ℝ) ^ 2)) :=
    hbase.mul_left _
  apply hdom.of_nonneg_of_le
  · intro n
    positivity
  · intro n
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsq : 0 ≤ (((n : ℝ) - 2 * x) ^ 2) := sq_nonneg _
    nlinarith [mul_nonneg hc.le hsq]

/-- The complete integer-image periodization of a Gaussian kernel. -/
noncomputable def wrappedGaussianKernel (q : ℕ) (s : ℝ) (z : ℤ) : ℝ :=
  ∑' n : ℤ, Real.exp (-s * ((z : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)

/-- The complete wrapped Gaussian is even.  Negating the input simply
reindexes every integer image by `n ↦ -n`. -/
theorem wrappedGaussianKernel_neg (q : ℕ) (s : ℝ) (z : ℤ) :
    wrappedGaussianKernel q s (-z) = wrappedGaussianKernel q s z := by
  unfold wrappedGaussianKernel
  calc
    (∑' n : ℤ, Real.exp
        (-s * (((-z : ℤ) : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) =
      ∑' n : ℤ, Real.exp
        (-s * (((-z : ℤ) : ℝ) - ((-n : ℤ) : ℝ) * (q : ℝ)) ^ 2) := by
      exact (Equiv.tsum_eq (Equiv.neg ℤ) (fun n : ℤ => Real.exp
        (-s * (((-z : ℤ) : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2))).symm
    _ = ∑' n : ℤ, Real.exp
        (-s * ((z : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2) := by
      apply tsum_congr
      intro n
      congr 2
      push_cast
      ring

/-- Function-level evenness form used by conditioned-row reindexing. -/
theorem wrappedGaussianKernel_even (q : ℕ) (s : ℝ) :
    Function.Even (wrappedGaussianKernel q s) := by
  intro z
  exact wrappedGaussianKernel_neg q s z

theorem summable_wrappedGaussianKernel
    {q : ℕ} {s : ℝ} (hq : 0 < q) (hs : 0 < s) (z : ℤ) :
    Summable (fun n : ℤ =>
      Real.exp (-s * ((z : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) := by
  have hqReal : 0 < (q : ℝ) := by exact_mod_cast hq
  have hbase := summable_exp_neg_mul_int_sub_sq
    (c := s * (q : ℝ) ^ 2) (x := (z : ℝ) / (q : ℝ)) (by positivity)
  convert hbase using 1
  funext n
  congr 1
  field_simp [hqReal.ne']
  ring

/-- Poisson representation of the wrapped Gaussian.  The coefficients of
every cosine mode are manifestly nonnegative. -/
theorem wrappedGaussianKernel_eq_positiveFourier
    {q : ℕ} {s : ℝ} (hq : 0 < q) (hs : 0 < s) (z : ℤ) :
    wrappedGaussianKernel q s z =
      1 / Real.sqrt (s * (q : ℝ) ^ 2 / Real.pi) *
        ∑' k : ℤ,
          Real.exp
              (-Real.pi / (s * (q : ℝ) ^ 2 / Real.pi) * (k : ℝ) ^ 2) *
            Real.cos (2 * Real.pi * (k : ℝ) * ((z : ℝ) / (q : ℝ))) := by
  have hqReal : 0 < (q : ℝ) := by exact_mod_cast hq
  let a : ℝ := s * (q : ℝ) ^ 2 / Real.pi
  have ha : 0 < a := by dsimp [a]; positivity
  have hpoisson := tsum_exp_neg_sq_sub_poisson
    (a := a) (x := (z : ℝ) / (q : ℝ)) ha
  rw [wrappedGaussianKernel]
  convert hpoisson using 1
  · apply tsum_congr
    intro n
    congr 1
    dsimp [a]
    field_simp [hqReal.ne', Real.pi_ne_zero]
    ring

/-- The centered modular Gaussian is bounded pointwise by its wrapped
periodization. -/
theorem centeredGaussian_le_wrappedGaussianKernel
    {q : ℕ} (hq : Odd q) {s : ℝ} (hs : 0 < s) (z : ℤ) :
    Real.exp (-s * (centeredMod q z : ℝ) ^ 2) ≤
      wrappedGaussianKernel q s z := by
  have hq0 : 0 < q := hq.pos
  have hsum := summable_wrappedGaussianKernel hq0 hs z
  have hqne : q ≠ 0 := Nat.ne_of_gt hq0
  let : NeZero q := ⟨hqne⟩
  have hcong : (centeredMod q z : ZMod q) = (z : ZMod q) :=
    centeredMod_intCast q z
  have hdiv : (q : ℤ) ∣ z - centeredMod q z :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (centeredMod q z) z q).mp hcong
  rcases hdiv with ⟨n, hn⟩
  have hterm :
      (z : ℝ) - (n : ℝ) * (q : ℝ) = (centeredMod q z : ℝ) := by
    have hn' : (z : ℝ) - (centeredMod q z : ℝ) =
        (q : ℝ) * (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [wrappedGaussianKernel, ← hterm]
  rw [hsum.tsum_eq_add_tsum_ite n]
  exact le_add_of_nonneg_right (tsum_nonneg fun _ => by split <;> positivity)

/-- Tonelli form of the wrapped sparse-row expectation. This exposes the
literal zero image and every nonzero modular image to scalar lobe bounds while
keeping the real-valued wrapped kernel as the deletion theorem's interface. -/
theorem sparseRow_wrappedGaussianKernel_integral_eq_image_tsum
    {q d : ℕ} (w : Fin d → ℤ) {s : ℝ}
    (hq : 0 < q) (hs : 0 < s) :
    ENNReal.ofReal
        (∫ row, wrappedGaussianKernel q s (∑ i, row i * w i)
          ∂(sparseRademacherRow d).toMeasure) =
      ∑' n : ℤ, ENNReal.ofReal
        (∫ row, Real.exp
          (-s * (((∑ i, row i * w i : ℤ) : ℝ) -
            (n : ℝ) * (q : ℝ)) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) := by
  let μ : Measure (Fin d → ℤ) := (sparseRademacherRow d).toMeasure
  let T : (Fin d → ℤ) → ℤ := fun row => ∑ i, row i * w i
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
  have hwrapped_nonneg (row : Fin d → ℤ) :
      0 ≤ wrappedGaussianKernel q s (T row) := by
    rw [wrappedGaussianKernel]
    exact tsum_nonneg fun _ => Real.exp_nonneg _
  have hwrapped_lintegral :
      ENNReal.ofReal
          (∫ row, wrappedGaussianKernel q s (T row) ∂μ) =
        ∫⁻ row, ENNReal.ofReal (wrappedGaussianKernel q s (T row)) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal
      (hfinite_integrable fun row => wrappedGaussianKernel q s (T row))
      (Filter.Eventually.of_forall hwrapped_nonneg)
  calc
    ENNReal.ofReal
        (∫ row, wrappedGaussianKernel q s (∑ i, row i * w i)
          ∂(sparseRademacherRow d).toMeasure) =
        ∫⁻ row, ENNReal.ofReal (wrappedGaussianKernel q s (T row)) ∂μ := by
      simpa only [μ, T] using hwrapped_lintegral
    _ = ∫⁻ row, ∑' n : ℤ, ENNReal.ofReal
          (Real.exp (-s * ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [] with row
      rw [wrappedGaussianKernel,
        ENNReal.ofReal_tsum_of_nonneg
          (fun _ => Real.exp_nonneg _)
          (summable_wrappedGaussianKernel hq hs (T row))]
    _ = ∑' n : ℤ, ∫⁻ row, ENNReal.ofReal
          (Real.exp (-s * ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) ∂μ := by
      apply lintegral_tsum
      intro n
      exact (measurable_of_countable _).aemeasurable
    _ = ∑' n : ℤ, ENNReal.ofReal
        (∫ row, Real.exp
          (-s * (((∑ i, row i * w i : ℤ) : ℝ) -
            (n : ℝ) * (q : ℝ)) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) := by
      apply tsum_congr
      intro n
      have hconvert := ofReal_integral_eq_lintegral_ofReal
        (hfinite_integrable fun row =>
          Real.exp (-s * ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2))
        (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)
      simpa only [μ, T] using hconvert.symm

/-- Tonelli expansion for a wrapped sparse-row expectation with an integer
shift.  The active retained-coordinate branch is the special case in which
`shift` is its positive amplitude. -/
theorem sparseRow_shifted_wrappedGaussianKernel_integral_eq_image_tsum
    {q d : ℕ} (w : Fin d → ℤ) (shift : ℤ) {s : ℝ}
    (hq : 0 < q) (hs : 0 < s) :
    ENNReal.ofReal
        (∫ row, wrappedGaussianKernel q s
          (shift + ∑ i, row i * w i)
          ∂(sparseRademacherRow d).toMeasure) =
      ∑' n : ℤ, ENNReal.ofReal
        (∫ row, Real.exp
          (-s * (((shift + ∑ i, row i * w i : ℤ) : ℝ) -
            (n : ℝ) * (q : ℝ)) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) := by
  let μ : Measure (Fin d → ℤ) := (sparseRademacherRow d).toMeasure
  let T : (Fin d → ℤ) → ℤ := fun row => shift + ∑ i, row i * w i
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
  have hwrapped_nonneg (row : Fin d → ℤ) :
      0 ≤ wrappedGaussianKernel q s (T row) := by
    rw [wrappedGaussianKernel]
    exact tsum_nonneg fun _ => Real.exp_nonneg _
  have hwrapped_lintegral :
      ENNReal.ofReal
          (∫ row, wrappedGaussianKernel q s (T row) ∂μ) =
        ∫⁻ row, ENNReal.ofReal (wrappedGaussianKernel q s (T row)) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal
      (hfinite_integrable fun row => wrappedGaussianKernel q s (T row))
      (Filter.Eventually.of_forall hwrapped_nonneg)
  calc
    ENNReal.ofReal
        (∫ row, wrappedGaussianKernel q s
          (shift + ∑ i, row i * w i)
          ∂(sparseRademacherRow d).toMeasure) =
        ∫⁻ row, ENNReal.ofReal (wrappedGaussianKernel q s (T row)) ∂μ := by
      simpa only [μ, T] using hwrapped_lintegral
    _ = ∫⁻ row, ∑' n : ℤ, ENNReal.ofReal
          (Real.exp (-s * ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [] with row
      rw [wrappedGaussianKernel,
        ENNReal.ofReal_tsum_of_nonneg
          (fun _ => Real.exp_nonneg _)
          (summable_wrappedGaussianKernel hq hs (T row))]
    _ = ∑' n : ℤ, ∫⁻ row, ENNReal.ofReal
          (Real.exp (-s * ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) ∂μ := by
      apply lintegral_tsum
      intro n
      exact (measurable_of_countable _).aemeasurable
    _ = ∑' n : ℤ, ENNReal.ofReal
        (∫ row, Real.exp
          (-s * (((shift + ∑ i, row i * w i : ℤ) : ℝ) -
            (n : ℝ) * (q : ℝ)) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) := by
      apply tsum_congr
      intro n
      have hconvert := ofReal_integral_eq_lintegral_ofReal
        (hfinite_integrable fun row =>
          Real.exp (-s * ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2))
        (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)
      simpa only [μ, T] using hconvert.symm

/-- The shifted wrapped expectation admits the same asymmetric complete-image
tail as the active centered-periodization estimate.  Unlike that estimate,
this theorem bounds the wrapped kernel itself and can therefore be consumed
after positive-Fourier coordinate deletion. -/
theorem sparseRow_shifted_wrappedGaussianKernel_normalized_nonzeroImageBound
    {d : ℕ} (w : Fin d → ℤ) (q A : ℕ) (V z : ℝ)
    (hq : 0 < q) (hA : 0 < A) (hV : 0 < V)
    (h_norm : ∑ i, (w i : ℝ) ^ 2 = V) (hz : 0 < z)
    (hB : 1 < (q : ℝ) / (A : ℝ)) :
    let u : ℝ := V / (A : ℝ) ^ 2
    let B : ℝ := (q : ℝ) / (A : ℝ)
    let alpha : ℝ := z / (1 + z * u)
    ENNReal.ofReal
        (∫ row, wrappedGaussianKernel q (z / (A : ℝ) ^ 2)
          ((A : ℤ) + ∑ i, row i * w i)
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
  have himage (n : ℤ) (hn : n ≠ 0) :
      ENNReal.ofReal
          (∫ row, Real.exp
            (-s * ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2) ∂μ) ≤
        g n := by
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
  have htail_image :
      (∑' n : ℤ, if n = 0 then (0 : ℝ≥0∞) else
        ENNReal.ofReal
          (∫ row, Real.exp
            (-s * ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2) ∂μ)) ≤
      ∑' n : ℤ, if n = 0 then (0 : ℝ≥0∞) else g n := by
    apply ENNReal.tsum_le_tsum
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · simpa only [if_neg hn] using himage n hn
  have htail := integerShiftedGaussian_exp_nonzero_geometricTail
    alpha B (by dsimp [alpha, u]; positivity) (by simpa [B] using hB)
  have hzero :
      ENNReal.ofReal
          (∫ row, Real.exp
            (-s * ((T row : ℝ) - ((0 : ℤ) : ℝ) * (q : ℝ)) ^ 2) ∂μ) =
        ENNReal.ofReal
          (∫ row, Real.exp
            (-z * (((T row : ℝ) / (A : ℝ)) ^ 2)) ∂μ) := by
    congr 1
    apply integral_congr_ae
    filter_upwards [] with row
    congr 1
    dsimp [s]
    simp only [Int.cast_zero, zero_mul, sub_zero]
    field_simp [hAr.ne']
  have hperiod :=
    sparseRow_shifted_wrappedGaussianKernel_integral_eq_image_tsum
      w (A : ℤ) (s := s) hq hs
  calc
    ENNReal.ofReal
        (∫ row, wrappedGaussianKernel q (z / (A : ℝ) ^ 2)
          ((A : ℤ) + ∑ i, row i * w i)
          ∂(sparseRademacherRow d).toMeasure) =
        ∑' n : ℤ, ENNReal.ofReal
          (∫ row, Real.exp
            (-s * (((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2)) ∂μ) := by
      simpa only [s, μ, T] using hperiod
    _ = ENNReal.ofReal
          (∫ row, Real.exp (-z * (((T row : ℝ) / (A : ℝ)) ^ 2)) ∂μ) +
        (∑' n : ℤ, if n = 0 then (0 : ℝ≥0∞) else
          ENNReal.ofReal
            (∫ row, Real.exp
              (-s * ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2) ∂μ)) := by
      rw [ENNReal.tsum_eq_add_tsum_ite (f := fun n : ℤ =>
        ENNReal.ofReal
          (∫ row, Real.exp
            (-s * ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2) ∂μ)) 0]
      rw [hzero]
      congr 1
      apply tsum_congr
      intro n
      split_ifs <;> rfl
    _ ≤ ENNReal.ofReal
          (∫ row, Real.exp (-z * (((T row : ℝ) / (A : ℝ)) ^ 2)) ∂μ) +
        ∑' n : ℤ, if n = 0 then (0 : ℝ≥0∞) else g n :=
      add_le_add_right htail_image _
    _ ≤ ENNReal.ofReal
          (∫ row, Real.exp (-z * (((T row : ℝ) / (A : ℝ)) ^ 2)) ∂μ) +
        ENNReal.ofReal
          (Real.exp (-alpha * (B - 1) ^ 2) /
              (1 - Real.exp (-alpha * (3 * B ^ 2 - 2 * B))) +
            Real.exp (-alpha * (B + 1) ^ 2) /
              (1 - Real.exp (-alpha * (3 * B ^ 2 + 2 * B)))) :=
      add_le_add_right (by simpa only [g] using htail) _
    _ = _ := by simp only [μ, T, alpha, B, u]

/-- The wrapped expectation itself, not merely the centered modular kernel it
dominates, admits the standard zero-image plus complete geometric image-tail
bound. This is the quantitative consumer required after Fourier deletion. -/
theorem sparseRow_wrappedGaussianKernel_normalized_nonzeroImageBound
    {d : ℕ} (w : Fin d → ℤ) (q : ℕ) (V s : ℝ)
    (hq : 0 < q) (hV : 0 < V)
    (h_norm : ∑ i, (w i : ℝ) ^ 2 = V)
    (hs : 0 < s) :
    ENNReal.ofReal
        (∫ row, wrappedGaussianKernel q (s / V) (∑ i, row i * w i)
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
  have himage_exp (n : ℤ) (row : Fin d → ℤ) :
      -(s / V) * ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2 =
        -s * (((T row : ℝ) / Real.sqrt V -
          (n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2) := by
    field_simp [hsqrt_ne, hsqrt]
    rw [hsqrt]
    ring
  have himage_eq (n : ℤ) :
      ENNReal.ofReal
          (∫ row, Real.exp
            (-(s / V) * ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2) ∂μ) =
        ENNReal.ofReal
          (∫ row, Real.exp
            (-s * (((T row : ℝ) / Real.sqrt V -
              (n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2)) ∂μ) := by
    congr 1
    apply integral_congr_ae
    filter_upwards [] with row
    rw [himage_exp]
  have hperiod := sparseRow_wrappedGaussianKernel_integral_eq_image_tsum
    w (s := s / V) hq (div_pos hs hV)
  have hnonzero (n : ℤ) (hn : n ≠ 0) :
      ENNReal.ofReal
          (∫ row, Real.exp
            (-(s / V) * ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2) ∂μ) ≤
        ENNReal.ofReal
          (Real.exp
            (-s * ((n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))) := by
    rw [himage_eq n]
    apply ENNReal.ofReal_mono
    simpa only [μ, T] using
      sparseRow_normalizedIntegerImageBound w q V s n hV h_norm hs
  have htail_image :
      (∑' n : ℤ, if n = 0 then (0 : ℝ≥0∞) else
        ENNReal.ofReal
          (∫ row, Real.exp
            (-(s / V) * ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2) ∂μ)) ≤
      ∑' n : ℤ, if n = 0 then (0 : ℝ≥0∞) else
        ENNReal.ofReal
          (Real.exp
            (-s * ((n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))) := by
    apply ENNReal.tsum_le_tsum
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · simpa only [if_neg hn] using hnonzero n hn
  let c : ℝ := s * ((q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hterm (n : ℤ) :
      -s * ((n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2 / (1 + s) =
        -c * (n : ℝ) ^ 2 := by
    dsimp [c]
    ring
  have htail_scalar :
      (∑' n : ℤ, if n = 0 then (0 : ℝ≥0∞) else
        ENNReal.ofReal
          (Real.exp
            (-s * ((n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2 / (1 + s)))) ≤
      ENNReal.ofReal
        (2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3)) := by
    calc
      _ = ∑' n : ℤ, if n = 0 then (0 : ℝ≥0∞) else
          ENNReal.ofReal (Real.exp (-c * (n : ℝ) ^ 2)) := by
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
  have hzero :
      ENNReal.ofReal
          (∫ row, Real.exp
            (-(s / V) * ((T row : ℝ) - ((0 : ℤ) : ℝ) * (q : ℝ)) ^ 2) ∂μ) =
        ENNReal.ofReal
          (∫ row, Real.exp
            (-s * ((T row : ℝ) / Real.sqrt V) ^ 2) ∂μ) := by
    simpa only [Int.cast_zero, zero_mul, zero_div, sub_zero] using
      himage_eq (0 : ℤ)
  calc
    ENNReal.ofReal
        (∫ row, wrappedGaussianKernel q (s / V) (∑ i, row i * w i)
          ∂(sparseRademacherRow d).toMeasure) =
        ∑' n : ℤ, ENNReal.ofReal
          (∫ row, Real.exp
            (-(s / V) * (((∑ i, row i * w i : ℤ) : ℝ) -
              (n : ℝ) * (q : ℝ)) ^ 2)
            ∂(sparseRademacherRow d).toMeasure) := hperiod
    _ = ENNReal.ofReal
          (∫ row, Real.exp (-s * ((T row : ℝ) / Real.sqrt V) ^ 2) ∂μ) +
        (∑' n : ℤ, if n = 0 then (0 : ℝ≥0∞) else
          ENNReal.ofReal
            (∫ row, Real.exp
              (-(s / V) * ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2) ∂μ)) := by
      rw [ENNReal.tsum_eq_add_tsum_ite (f := fun n : ℤ =>
        ENNReal.ofReal
          (∫ row, Real.exp
            (-(s / V) * ((T row : ℝ) - (n : ℝ) * (q : ℝ)) ^ 2) ∂μ)) 0]
      rw [hzero]
      congr 1
      apply tsum_congr
      intro n
      split_ifs <;> rfl
    _ ≤ ENNReal.ofReal
          (∫ row, Real.exp (-s * ((T row : ℝ) / Real.sqrt V) ^ 2) ∂μ) +
        ∑' n : ℤ, if n = 0 then (0 : ℝ≥0∞) else
          ENNReal.ofReal
            (Real.exp
              (-s * ((n : ℝ) * (q : ℝ) / Real.sqrt V) ^ 2 / (1 + s))) :=
      add_le_add_right htail_image _
    _ ≤ ENNReal.ofReal
          (∫ row, Real.exp (-s * ((T row : ℝ) / Real.sqrt V) ^ 2) ∂μ) +
        ENNReal.ofReal
          (2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3)) :=
      add_le_add_right htail_scalar _
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
      simp only [μ, T]
      congr 1
      dsimp [c]
      ring_nf

/-- Sparse cyclic cosine mode indexed by all integer frequencies. -/
noncomputable def sparseCyclicCosineModeInt
    (q : ℕ) {d : ℕ} (w : Fin d → ℤ) (k : ℤ) : ℝ :=
  ∏ i, (1 + Real.cos
    ((2 * Real.pi * (k : ℝ) / (q : ℝ)) * (w i : ℝ))) / 2

theorem sparseCyclicCosineModeInt_nonneg
    (q : ℕ) {d : ℕ} (w : Fin d → ℤ) (k : ℤ) :
    0 ≤ sparseCyclicCosineModeInt q w k := by
  unfold sparseCyclicCosineModeInt
  apply Finset.prod_nonneg
  intro i _
  linarith [Real.neg_one_le_cos
    ((2 * Real.pi * (k : ℝ) / (q : ℝ)) * (w i : ℝ))]

theorem sparseCyclicCosineModeInt_le_one
    (q : ℕ) {d : ℕ} (w : Fin d → ℤ) (k : ℤ) :
    sparseCyclicCosineModeInt q w k ≤ 1 := by
  unfold sparseCyclicCosineModeInt
  apply Finset.prod_le_one
  · intro i _
    linarith [Real.neg_one_le_cos
      ((2 * Real.pi * (k : ℝ) / (q : ℝ)) * (w i : ℝ))]
  · intro i _
    linarith [Real.cos_le_one
      ((2 * Real.pi * (k : ℝ) / (q : ℝ)) * (w i : ℝ))]

/-- Removing coordinates can only increase an integer-frequency sparse
cosine mode. -/
theorem sparseCyclicCosineModeInt_le_restrict
    (q : ℕ) {d : ℕ} (w : Fin d → ℤ) (support : Finset (Fin d)) (k : ℤ) :
    sparseCyclicCosineModeInt q w k ≤
      sparseCyclicCosineModeInt q
        (fun i => if i ∈ support then w i else 0) k := by
  unfold sparseCyclicCosineModeInt
  apply Finset.prod_le_prod
  · intro i _
    linarith [Real.neg_one_le_cos
      ((2 * Real.pi * (k : ℝ) / (q : ℝ)) * (w i : ℝ))]
  · intro i _
    by_cases hi : i ∈ support
    · simp [hi]
    · simp [hi]
      linarith [Real.cos_le_one
        ((2 * Real.pi * (k : ℝ) / (q : ℝ)) * (w i : ℝ))]

/-- Exact sparse-row cosine expectation at an integer cyclic frequency. -/
theorem sparseRow_cosineTransform_int
    (q d : ℕ) (w : Fin d → ℤ) (k : ℤ) :
    ∫ row, Real.cos
        ((2 * Real.pi * (k : ℝ) / (q : ℝ)) *
          (∑ i, row i * w i : ℤ))
        ∂(sparseRademacherRow d).toMeasure =
      sparseCyclicCosineModeInt q w k := by
  have h := sparseRow_cosineTransform d
    (2 * Real.pi * (k : ℝ) / (q : ℝ)) (fun i => (w i : ℝ))
  unfold sparseCyclicCosineModeInt
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with row
  congr 1
  simp only [realRowDot, Int.cast_sum, Int.cast_mul]

set_option maxHeartbeats 800000 in
-- Exchanging the finite row expectation with the infinite Fourier series is
-- elaboration-intensive even though every analytic series is already summable.
/-- The wrapped sparse-row expectation is its positive Gaussian-weighted
cosine-mode series. -/
theorem sparseRow_wrappedGaussianKernel_integral_eq
    {q d : ℕ} (w : Fin d → ℤ) {s : ℝ}
    (hq : 0 < q) (hs : 0 < s) :
    ∫ row, wrappedGaussianKernel q s (∑ i, row i * w i)
        ∂(sparseRademacherRow d).toMeasure =
      1 / Real.sqrt (s * (q : ℝ) ^ 2 / Real.pi) *
        ∑' k : ℤ,
          Real.exp
              (-Real.pi / (s * (q : ℝ) ^ 2 / Real.pi) * (k : ℝ) ^ 2) *
            sparseCyclicCosineModeInt q w k := by
  let a : ℝ := s * (q : ℝ) ^ 2 / Real.pi
  let weight : ℤ → ℝ := fun k => Real.exp (-Real.pi / a * (k : ℝ) ^ 2)
  let F : ℤ → (Fin d → ℤ) → ℝ := fun k row =>
    weight k * Real.cos
      ((2 * Real.pi * (k : ℝ) / (q : ℝ)) *
        (∑ i, row i * w i : ℤ))
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
      wrappedGaussianKernel q s (∑ i, row i * w i) =
        1 / Real.sqrt a * ∑' k : ℤ, F k row := by
    have hp := wrappedGaussianKernel_eq_positiveFourier
      hq hs (∑ i, row i * w i)
    dsimp [a, F, weight]
    convert hp using 1
    congr 1
    apply tsum_congr
    intro k
    congr 2
    push_cast
    field_simp [hqReal.ne']
  calc
    ∫ row, wrappedGaussianKernel q s (∑ i, row i * w i)
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
        weight k * sparseCyclicCosineModeInt q w k := by
      congr 1
      apply tsum_congr
      intro k
      dsimp [F]
      rw [integral_const_mul, sparseRow_cosineTransform_int]
    _ = _ := by rfl

/-- Positive wrapped Fourier coefficients make the row expectation monotone
under coordinate deletion. -/
theorem sparseRow_wrappedGaussianKernel_le_restrict
    {q d : ℕ} (w : Fin d → ℤ) (support : Finset (Fin d)) {s : ℝ}
    (hq : 0 < q) (hs : 0 < s) :
    ∫ row, wrappedGaussianKernel q s (∑ i, row i * w i)
        ∂(sparseRademacherRow d).toMeasure ≤
      ∫ row, wrappedGaussianKernel q s
          (∑ i, row i * (if i ∈ support then w i else 0))
        ∂(sparseRademacherRow d).toMeasure := by
  rw [sparseRow_wrappedGaussianKernel_integral_eq w hq hs,
    sparseRow_wrappedGaussianKernel_integral_eq
      (fun i => if i ∈ support then w i else 0) hq hs]
  apply mul_le_mul_of_nonneg_left
  · apply Summable.tsum_le_tsum
    · intro k
      exact mul_le_mul_of_nonneg_left
        (sparseCyclicCosineModeInt_le_restrict q w support k)
        (Real.exp_nonneg _)
    · have hbase : Summable (fun k : ℤ =>
          Real.exp (-Real.pi / (s * (q : ℝ) ^ 2 / Real.pi) * (k : ℝ) ^ 2)) := by
        simpa only [neg_div] using summable_real_integer_exp_neg_sq
          (show 0 < Real.pi /
            (s * (q : ℝ) ^ 2 / Real.pi) by positivity)
      apply hbase.of_norm_bounded
      intro k
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_nonneg (sparseCyclicCosineModeInt_nonneg q w k)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le
        (sparseCyclicCosineModeInt_le_one q w k)
    · have hbase : Summable (fun k : ℤ =>
          Real.exp (-Real.pi / (s * (q : ℝ) ^ 2 / Real.pi) * (k : ℝ) ^ 2)) := by
        simpa only [neg_div] using summable_real_integer_exp_neg_sq
          (show 0 < Real.pi /
            (s * (q : ℝ) ^ 2 / Real.pi) by positivity)
      apply hbase.of_norm_bounded
      intro k
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_nonneg (sparseCyclicCosineModeInt_nonneg q
          (fun i => if i ∈ support then w i else 0) k)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le
        (sparseCyclicCosineModeInt_le_one q
          (fun i => if i ∈ support then w i else 0) k)
  · positivity

private theorem integrable_sparseRow_finite
    {d : ℕ} (f : (Fin d → ℤ) → ℝ) :
    Integrable f (sparseRademacherRow d).toMeasure := by
  rw [sparseRademacherRow_eq_map_uniformRowSeed]
  rw [← PMF.toMeasure_map
    (p := PMF.uniformOfFintype (SparseRowSeed d))
    (f := sparseRow) (measurable_of_finite sparseRow)]
  apply (integrable_map_measure
    (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_finite sparseRow).aemeasurable).2
  exact Integrable.of_finite

/-- Complete scalable transport: the exact centered modular row transform of
an arbitrary profile is bounded by the wrapped-Gaussian expectation of any
coordinate subprofile. -/
theorem sparseRow_centeredGaussian_le_wrappedGaussianKernel_restrict
    {q d : ℕ} (w : Fin d → ℤ) (support : Finset (Fin d)) {s : ℝ}
    (hq : Odd q) (hs : 0 < s) :
    ∫ row, Real.exp (-s * sparseLowerRowKernel q w row)
        ∂(sparseRademacherRow d).toMeasure ≤
      ∫ row, wrappedGaussianKernel q s
          (∑ i, row i * (if i ∈ support then w i else 0))
        ∂(sparseRademacherRow d).toMeasure := by
  calc
    ∫ row, Real.exp (-s * sparseLowerRowKernel q w row)
        ∂(sparseRademacherRow d).toMeasure ≤
        ∫ row, wrappedGaussianKernel q s (∑ i, row i * w i)
          ∂(sparseRademacherRow d).toMeasure := by
      apply integral_mono (integrable_sparseRow_finite _)
        (integrable_sparseRow_finite _)
      intro row
      simpa only [sparseLowerRowKernel_apply] using
        centeredGaussian_le_wrappedGaussianKernel hq hs
          (∑ i, row i * w i)
    _ ≤ ∫ row, wrappedGaussianKernel q s
          (∑ i, row i * (if i ∈ support then w i else 0))
        ∂(sparseRademacherRow d).toMeasure :=
      sparseRow_wrappedGaussianKernel_le_restrict w support hq.pos hs

end CertifiedJL
