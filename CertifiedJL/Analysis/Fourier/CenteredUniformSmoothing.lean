/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Gaussian.ShiftedGaussianInversion
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Centered-uniform averaging of a contour smoother

This file isolates the semantic primitive used by the compact sparse-upper
experiment.  A centered interval average multiplies a vertical-line contour
weight by `sinh (h s) / (h s)` while preserving absolute convergence.
-/

open MeasureTheory ProbabilityTheory

namespace CertifiedJL

/-- Average a real function over one centered uniform interval. -/
noncomputable def centeredUniformAverage (h : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / (2 * h)) * ∫ v : ℝ in -h..h, f (x + v)

/-- Reflection law characterizing a centered step smoother normalized to one
at `threshold`. -/
def CenteredReflection (threshold : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ y : ℝ, f (threshold + y) + f (threshold - y) = 2

/-- Centered averaging preserves pointwise nonnegativity. -/
theorem centeredUniformAverage_nonneg
    {h : ℝ} (hh : 0 < h) {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (x : ℝ) :
    0 ≤ centeredUniformAverage h f x := by
  unfold CertifiedJL.centeredUniformAverage
  apply mul_nonneg (by positivity)
  exact intervalIntegral.integral_nonneg_of_forall (by linarith)
    (fun v => hf (x + v))

/-- Centered averaging preserves monotonicity. -/
theorem Monotone.centeredUniformAverage
    {h : ℝ} (hh : 0 < h) {f : ℝ → ℝ} (hf : Monotone f) :
    Monotone (centeredUniformAverage h f) := by
  intro x y hxy
  unfold CertifiedJL.centeredUniformAverage
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hmonoX : Monotone (fun v : ℝ => f (x + v)) :=
    fun _ _ huv => hf (by linarith)
  have hmonoY : Monotone (fun v : ℝ => f (y + v)) :=
    fun _ _ huv => hf (by linarith)
  exact intervalIntegral.integral_mono_on (by linarith)
    hmonoX.intervalIntegrable hmonoY.intervalIntegrable
    (fun v _ => hf (by linarith))

/-- Centered averaging preserves the reflection law of a monotone smoother. -/
theorem CenteredReflection.centeredUniformAverage
    {h threshold : ℝ} (hh : 0 < h) {f : ℝ → ℝ}
    (hreflection : CenteredReflection threshold f) (hf : Monotone f) :
    CenteredReflection threshold (centeredUniformAverage h f) := by
  intro z
  unfold CertifiedJL.centeredUniformAverage
  have hfirst : IntervalIntegrable
      (fun v : ℝ => f (threshold + z + v)) volume (-h) h := by
    apply Monotone.intervalIntegrable
    intro a b hab
    exact hf (by linarith)
  have hsecond : IntervalIntegrable
      (fun v : ℝ => f (threshold - z - v)) volume (-h) h := by
    apply Antitone.intervalIntegrable
    intro a b hab
    exact hf (sub_le_sub_left hab (threshold - z))
  have hreflectIntegral :
      (∫ v : ℝ in -h..h, f (threshold - z + v)) =
        ∫ v : ℝ in -h..h, f (threshold - z - v) := by
    have hcomp := intervalIntegral.integral_comp_neg
      (a := -h) (b := h) (f := fun v : ℝ => f (threshold - z + v))
    simpa [sub_eq_add_neg, add_assoc] using hcomp.symm
  rw [hreflectIntegral, ← mul_add,
    ← intervalIntegral.integral_add hfirst hsecond]
  have hintegrand :
      (fun v : ℝ =>
          f (threshold + z + v) + f (threshold - z - v)) =
        fun _ : ℝ => 2 := by
    funext v
    convert hreflection (z + v) using 1 <;> ring_nf
  rw [hintegrand, intervalIntegral.integral_const]
  field_simp
  ring

/-- The Laplace transform of one centered uniform interval, written in the
form used by the contour checker. -/
noncomputable def centeredUniformLaplace
    (h lambda frequency : ℝ) : ℂ :=
  Complex.sinh ((h : ℂ) * (lambda + frequency * Complex.I)) /
    ((h : ℂ) * (lambda + frequency * Complex.I))

/-- Exact squared modulus of the complex hyperbolic sine on a vertical
line.  This is the analytic identity consumed by the compact certificate. -/
theorem normSq_sinh_vertical (a b : ℝ) :
    Complex.normSq (Complex.sinh ((a : ℂ) + b * Complex.I)) =
      Real.sinh a ^ 2 + Real.sin b ^ 2 := by
  rw [Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I]
  simp only [← Complex.ofReal_sinh, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sin, ← Complex.ofReal_cos]
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one]
  nlinarith [Real.cosh_sq_sub_sinh_sq a, Real.sin_sq_add_cos_sq b]

/-- Exact squared modulus of one centered-uniform Laplace factor. -/
theorem norm_centeredUniformLaplace_sq
    (h lambda frequency : ℝ) :
    ‖centeredUniformLaplace h lambda frequency‖ ^ 2 =
      (Real.sinh (h * lambda) ^ 2 + Real.sin (h * frequency) ^ 2) /
        (h ^ 2 * (lambda ^ 2 + frequency ^ 2)) := by
  unfold centeredUniformLaplace
  rw [norm_div, div_pow, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq]
  have hargument :
      (h : ℂ) * ((lambda : ℂ) + frequency * Complex.I) =
        ((h * lambda : ℝ) : ℂ) +
          ((h * frequency : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hargument, normSq_sinh_vertical]
  simp [Complex.normSq_mul, Complex.normSq_apply]
  ring

/-- The centered-uniform Laplace factor has even modulus along every
vertical contour line. -/
theorem norm_centeredUniformLaplace_neg
    (h lambda frequency : ℝ) :
    ‖centeredUniformLaplace h lambda (-frequency)‖ =
      ‖centeredUniformLaplace h lambda frequency‖ := by
  have hneg := norm_centeredUniformLaplace_sq h lambda (-frequency)
  have hpos := norm_centeredUniformLaplace_sq h lambda frequency
  have hsquares :
      ‖centeredUniformLaplace h lambda (-frequency)‖ ^ 2 =
        ‖centeredUniformLaplace h lambda frequency‖ ^ 2 := by
    rw [hneg, hpos]
    congr 2
    · rw [show h * -frequency = -(h * frequency) by ring, Real.sin_neg]
      ring
    · ring
  nlinarith [norm_nonneg (centeredUniformLaplace h lambda (-frequency)),
    norm_nonneg (centeredUniformLaplace h lambda frequency)]

/-- Elementary no-trigonometry envelope for the sine square. -/
theorem sin_sq_le_min_one_sq (x : ℝ) :
    Real.sin x ^ 2 ≤ min 1 (x ^ 2) := by
  exact le_min (Real.sin_sq_le_one x) Real.sin_sq_le_sq

/-- The rational shape used by the compact certificate is antitone in the
squared frequency once its constant numerator part dominates the squared
vertical displacement. -/
theorem compactRatio_le_of_le
    {A p qLeft q : ℝ} (hp : 0 < p) (hpA : p ≤ A)
    (hqLeft : 0 ≤ qLeft) (hfrequency : qLeft ≤ q) :
    (A + min 1 q) / (p + q) ≤
      (A + min 1 qLeft) / (p + qLeft) := by
  have hq : 0 ≤ q := hqLeft.trans hfrequency
  have hpLeft : 0 < p + qLeft := by positivity
  have hpq : 0 < p + q := by positivity
  by_cases hleftOne : 1 ≤ qLeft
  · have hqOne : 1 ≤ q := hleftOne.trans hfrequency
    rw [min_eq_left hleftOne, min_eq_left hqOne]
    apply (div_le_div_iff₀ hpq hpLeft).2
    nlinarith
  · have hqLeftOne : qLeft ≤ 1 := le_of_not_ge hleftOne
    rw [min_eq_right hqLeftOne]
    by_cases hqOne : q ≤ 1
    · rw [min_eq_right hqOne]
      apply (div_le_div_iff₀ hpq hpLeft).2
      nlinarith
    · have honeq : 1 ≤ q := le_of_not_ge hqOne
      rw [min_eq_left honeq]
      have hpOne : 0 < p + 1 := by positivity
      calc
        (A + 1) / (p + q) ≤ (A + 1) / (p + 1) := by
          apply div_le_div_of_nonneg_left (by nlinarith) hpOne
          linarith
        _ ≤ (A + qLeft) / (p + qLeft) := by
          apply (div_le_div_iff₀ hpOne hpLeft).2
          nlinarith

/-- Cellwise compact envelope for one centered-uniform transform.  The bound
uses only a scalar upper bound on `sinh (h*lambda)` and the cell's left
frequency endpoint. -/
theorem norm_centeredUniformLaplace_le_compactEnvelope
    {h lambda frequencyLeft frequency S : ℝ}
    (hh : 0 < h) (hlambda : 0 < lambda)
    (hfrequencyLeft : 0 ≤ frequencyLeft)
    (hfrequency : frequencyLeft ≤ frequency)
    (hS : Real.sinh (h * lambda) ≤ S) :
    ‖centeredUniformLaplace h lambda frequency‖ ≤
      Real.sqrt
        ((S ^ 2 + min 1 ((h * frequencyLeft) ^ 2)) /
          (h ^ 2 * (lambda ^ 2 + frequencyLeft ^ 2))) := by
  have hhlambda : 0 < h * lambda := mul_pos hh hlambda
  have hsinhNonneg : 0 ≤ Real.sinh (h * lambda) :=
    (Real.sinh_nonneg_iff).2 hhlambda.le
  have hSNonneg : 0 ≤ S := hsinhNonneg.trans hS
  have hsinhSq : Real.sinh (h * lambda) ^ 2 ≤ S ^ 2 := by
    nlinarith
  have hfrequencyNonneg : 0 ≤ frequency :=
    hfrequencyLeft.trans hfrequency
  have hq : (h * frequencyLeft) ^ 2 ≤ (h * frequency) ^ 2 := by
    exact pow_le_pow_left₀ (mul_nonneg hh.le hfrequencyLeft)
      (mul_le_mul_of_nonneg_left hfrequency hh.le) 2
  have hpA : (h * lambda) ^ 2 ≤ S ^ 2 := by
    have hsinhLinear : h * lambda ≤ Real.sinh (h * lambda) :=
      (Real.self_le_sinh_iff).2 hhlambda.le
    nlinarith
  have hratio := compactRatio_le_of_le
    (A := S ^ 2) (p := (h * lambda) ^ 2)
    (qLeft := (h * frequencyLeft) ^ 2)
    (q := (h * frequency) ^ 2) (sq_pos_of_pos hhlambda) hpA
    (sq_nonneg _) hq
  have hpointwise :
      (Real.sinh (h * lambda) ^ 2 +
          Real.sin (h * frequency) ^ 2) /
          (h ^ 2 * (lambda ^ 2 + frequency ^ 2)) ≤
        (S ^ 2 + min 1 ((h * frequencyLeft) ^ 2)) /
          (h ^ 2 * (lambda ^ 2 + frequencyLeft ^ 2)) := by
    have hnumerator :
        Real.sinh (h * lambda) ^ 2 + Real.sin (h * frequency) ^ 2 ≤
          S ^ 2 + min 1 ((h * frequency) ^ 2) :=
      add_le_add hsinhSq (sin_sq_le_min_one_sq (h * frequency))
    have hdenom : 0 < h ^ 2 * (lambda ^ 2 + frequency ^ 2) := by positivity
    calc
      _ ≤ (S ^ 2 + min 1 ((h * frequency) ^ 2)) /
          (h ^ 2 * (lambda ^ 2 + frequency ^ 2)) :=
        div_le_div_of_nonneg_right hnumerator hdenom.le
      _ = (S ^ 2 + min 1 ((h * frequency) ^ 2)) /
          ((h * lambda) ^ 2 + (h * frequency) ^ 2) := by
        congr 2 <;> ring
      _ ≤ (S ^ 2 + min 1 ((h * frequencyLeft) ^ 2)) /
          ((h * lambda) ^ 2 + (h * frequencyLeft) ^ 2) := hratio
      _ = _ := by congr 2 <;> ring
  rw [← norm_centeredUniformLaplace_sq] at hpointwise
  have henvelope :
      0 ≤ (S ^ 2 + min 1 ((h * frequencyLeft) ^ 2)) /
        (h ^ 2 * (lambda ^ 2 + frequencyLeft ^ 2)) := by positivity
  apply (Real.le_sqrt (norm_nonneg _) henvelope).2
  exact hpointwise

private theorem vertical_ne_zero {lambda frequency : ℝ} (hlambda : 0 < lambda) :
    (lambda : ℂ) + frequency * Complex.I ≠ 0 := by
  apply Complex.ne_zero_of_re_pos
  simpa using hlambda

/-- Exact normalized interval exponential integral. -/
theorem centeredUniformLaplace_eq_intervalIntegral
    {h lambda : ℝ} (hh : 0 < h) (hlambda : 0 < lambda)
    (frequency : ℝ) :
    centeredUniformLaplace h lambda frequency =
      (1 / (2 * h) : ℝ) *
        ∫ v : ℝ in -h..h,
          Complex.exp ((lambda + frequency * Complex.I) * v) := by
  let s : ℂ := (lambda : ℂ) + frequency * Complex.I
  have hs : s ≠ 0 := vertical_ne_zero hlambda
  have hhs : (h : ℂ) * s ≠ 0 := mul_ne_zero (by exact_mod_cast hh.ne') hs
  rw [integral_exp_mul_complex hs]
  unfold centeredUniformLaplace
  dsimp only [s]
  rw [Complex.sinh]
  push_cast
  field_simp [hs, hhs]

/-- The centered-uniform transform is bounded uniformly on a positive
vertical line.  The deliberately loose `exp (lambda*h)` constant is enough to
preserve Gaussian integrability under finite iteration. -/
theorem norm_centeredUniformLaplace_le
    {h lambda : ℝ} (hh : 0 < h) (hlambda : 0 < lambda)
    (frequency : ℝ) :
    ‖centeredUniformLaplace h lambda frequency‖ ≤ Real.exp (lambda * h) := by
  rw [centeredUniformLaplace_eq_intervalIntegral hh hlambda]
  have hcoeff : 0 ≤ (1 / (2 * h) : ℝ) := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoeff]
  calc
    (1 / (2 * h) : ℝ) *
          ‖∫ v : ℝ in -h..h,
            Complex.exp (((lambda : ℂ) + frequency * Complex.I) * v)‖ ≤
        (1 / (2 * h) : ℝ) *
          ∫ v : ℝ in -h..h,
            ‖Complex.exp (((lambda : ℂ) + frequency * Complex.I) * v)‖ := by
      gcongr
      exact intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ = (1 / (2 * h) : ℝ) *
          ∫ v : ℝ in -h..h, Real.exp (lambda * v) := by
      congr 2
      funext v
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.add_re, Complex.mul_im, Complex.add_im]
    _ ≤ (1 / (2 * h) : ℝ) *
          ∫ _v : ℝ in -h..h, Real.exp (lambda * h) := by
      gcongr
      apply intervalIntegral.integral_mono_on (by linarith)
        ((by fun_prop : Continuous fun v : ℝ => Real.exp (lambda * v)).intervalIntegrable (-h) h)
        (continuous_const.intervalIntegrable (-h) h)
      intro v hv
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hv.2 hlambda.le
    _ = Real.exp (lambda * h) := by
      rw [intervalIntegral.integral_const]
      field_simp
      ring

/-- Multiplication by one centered-uniform transform preserves integrability
of a contour weight. -/
theorem integrable_mul_centeredUniformLaplace
    {h lambda : ℝ} (hh : 0 < h) (hlambda : 0 < lambda)
    {W : ℝ → ℂ} (hW : Integrable W) :
    Integrable (fun u => W u * centeredUniformLaplace h lambda u) := by
  refine hW.norm.const_mul (Real.exp (lambda * h)) |>.mono' ?_ ?_
  · apply hW.aestronglyMeasurable.mul
    apply Continuous.aestronglyMeasurable
    unfold centeredUniformLaplace
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro u
      exact mul_ne_zero (by exact_mod_cast hh.ne')
        (vertical_ne_zero hlambda)
  filter_upwards [] with u
  rw [norm_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left
    (norm_centeredUniformLaplace_le hh hlambda u) (norm_nonneg (W u))

/-- One centered-uniform average multiplies a valid contour weight by the
uniform Laplace factor.  Absolute product integrability is proved here, so
downstream users do not assume a Fubini interchange. -/
theorem centeredUniformAverage_contourRepresentation
    {H : ℝ → ℝ} {W : ℝ → ℂ} {h lambda : ℝ}
    (hh : 0 < h) (hlambda : 0 < lambda) (hW : Integrable W)
    (hRepresentation : ∀ x : ℝ,
      (H x : ℂ) = ∫ u : ℝ, W u *
        Complex.exp ((lambda + u * Complex.I) * x))
    (x : ℝ) :
    (centeredUniformAverage h H x : ℂ) =
      ∫ u : ℝ,
        (W u * centeredUniformLaplace h lambda u) *
          Complex.exp ((lambda + u * Complex.I) * x) := by
  let F : ℝ → ℝ → ℂ := fun v u =>
    W u * Complex.exp ((lambda + u * Complex.I) * (x + v))
  have hv : IntegrableOn
      (fun v : ℝ => Real.exp (lambda * (x + |v|))) (Set.uIoc (-h) h) := by
    exact (((by fun_prop : Continuous fun v : ℝ =>
      Real.exp (lambda * (x + |v|))).continuousOn.integrableOn_compact
        isCompact_uIcc).mono_set Set.uIoc_subset_uIcc)
  have hmajorant := hv.mul_prod hW.norm
  have hF : Integrable (Function.uncurry F)
      ((volume.restrict (Set.uIoc (-h) h)).prod volume) := by
    refine hmajorant.mono' ?_ ?_
    · apply AEStronglyMeasurable.mul
      · exact hW.aestronglyMeasurable.comp_snd
      · exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
          Complex.exp (((lambda : ℂ) + (p.2 : ℂ) * Complex.I) *
            ((x : ℂ) + (p.1 : ℂ)))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun p => by
        change ‖W p.2 * Complex.exp
          (((lambda : ℂ) + (p.2 : ℂ) * Complex.I) *
            ((x : ℂ) + (p.1 : ℂ)))‖ ≤
          Real.exp (lambda * (x + |p.1|)) * ‖W p.2‖
        rw [norm_mul, Complex.norm_exp]
        have hre :
            (((lambda : ℂ) + (p.2 : ℂ) * Complex.I) *
              ((x : ℂ) + (p.1 : ℂ))).re = lambda * (x + p.1) := by
          simp [Complex.mul_re, Complex.add_re, Complex.mul_im,
            Complex.add_im]
        rw [hre]
        rw [mul_comm (Real.exp (lambda * (x + |p.1|))) ‖W p.2‖]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply Real.exp_le_exp.mpr
        gcongr
        exact le_abs_self p.1
  have hswap := intervalIntegral_integral_swap hF
  unfold centeredUniformAverage
  push_cast
  rw [← intervalIntegral.integral_ofReal]
  calc
    (1 / (2 * h) : ℂ) *
          ∫ v : ℝ in -h..h, (H (x + v) : ℂ) =
        (1 / (2 * h) : ℂ) *
          ∫ v : ℝ in -h..h, ∫ u : ℝ, F v u := by
      congr 1
      apply intervalIntegral.integral_congr
      intro v _
      change (H (x + v) : ℂ) = ∫ u : ℝ, W u *
        Complex.exp (((lambda : ℂ) + u * Complex.I) *
          ((x : ℂ) + v))
      convert hRepresentation (x + v) using 1 <;> (push_cast; rfl)
    _ = (1 / (2 * h) : ℂ) *
          ∫ u : ℝ, ∫ v : ℝ in -h..h, F v u := by rw [hswap]
    _ = ∫ u : ℝ,
          (W u * centeredUniformLaplace h lambda u) *
            Complex.exp ((lambda + u * Complex.I) * x) := by
      rw [← MeasureTheory.integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      rw [centeredUniformLaplace_eq_intervalIntegral hh hlambda]
      push_cast
      dsimp only [F]
      rw [← intervalIntegral.integral_const_mul]
      calc
        (∫ v : ℝ in -h..h,
            (1 / (2 * h) : ℂ) *
              (W u * Complex.exp
                (((lambda : ℂ) + u * Complex.I) * ((x : ℂ) + v)))) =
            ∫ v : ℝ in -h..h,
              (W u * (1 / (2 * h) : ℂ) *
                Complex.exp (((lambda : ℂ) + u * Complex.I) * x)) *
                  Complex.exp (((lambda : ℂ) + u * Complex.I) * v) := by
          apply intervalIntegral.integral_congr
          intro v _
          dsimp only
          rw [show (((lambda : ℂ) + u * Complex.I) * ((x : ℂ) + v)) =
              ((lambda : ℂ) + u * Complex.I) * x +
                ((lambda : ℂ) + u * Complex.I) * v by ring,
            Complex.exp_add]
          ring
        _ = (W u * (1 / (2 * h) : ℂ) *
              Complex.exp (((lambda : ℂ) + u * Complex.I) * x)) *
            ∫ v : ℝ in -h..h,
              Complex.exp (((lambda : ℂ) + u * Complex.I) * v) := by
          rw [intervalIntegral.integral_const_mul]
        _ = W u * ((1 / (2 * h) : ℂ) *
              ∫ v : ℝ in -h..h,
                Complex.exp (((lambda : ℂ) + u * Complex.I) * v)) *
            Complex.exp (((lambda : ℂ) + u * Complex.I) * x) := by ring

/-- Iterate centered-uniform averaging a finite number of times. -/
noncomputable def centeredUniformAverageN
    (count : ℕ) (h : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  Nat.iterate (centeredUniformAverage h) count f

/-- Finite centered averaging preserves pointwise nonnegativity. -/
theorem centeredUniformAverageN_nonneg
    {h : ℝ} (hh : 0 < h) {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x)
    (count : ℕ) (x : ℝ) :
    0 ≤ centeredUniformAverageN count h f x := by
  induction count generalizing x with
  | zero => simpa [centeredUniformAverageN] using hf x
  | succ count ih =>
      rw [centeredUniformAverageN, Function.iterate_succ_apply']
      exact centeredUniformAverage_nonneg hh (fun y => ih y) x

/-- Finite centered averaging jointly preserves monotonicity and the centered
reflection law. -/
theorem centeredUniformAverageN_monotone_reflection
    {h threshold : ℝ} (hh : 0 < h) {f : ℝ → ℝ}
    (hf : Monotone f) (hreflection : CenteredReflection threshold f)
    (count : ℕ) :
    Monotone (centeredUniformAverageN count h f) ∧
      CenteredReflection threshold (centeredUniformAverageN count h f) := by
  induction count with
  | zero => simpa [centeredUniformAverageN] using And.intro hf hreflection
  | succ count ih =>
      rw [centeredUniformAverageN, Function.iterate_succ_apply']
      exact And.intro (Monotone.centeredUniformAverage hh ih.1)
        (CenteredReflection.centeredUniformAverage hh ih.2 ih.1)

/-- A centered reflected smoother takes the value one at its threshold. -/
theorem CenteredReflection.eq_one_at_threshold
    {threshold : ℝ} {f : ℝ → ℝ}
    (hreflection : CenteredReflection threshold f) : f threshold = 1 := by
  have h := hreflection 0
  norm_num at h
  linarith

/-- The recursively factorized contour weight after finitely many averages. -/
noncomputable def centeredUniformContourWeightN
    (count : ℕ) (h lambda : ℝ) (W : ℝ → ℂ) : ℝ → ℂ :=
  Nat.iterate
    (fun V u => V u * centeredUniformLaplace h lambda u) count W

/-- The recursive contour weight is exactly the original weight multiplied by
the `count`th power of the centered-uniform transform. -/
theorem centeredUniformContourWeightN_apply
    (count : ℕ) (h lambda : ℝ) (W : ℝ → ℂ) (u : ℝ) :
    centeredUniformContourWeightN count h lambda W u =
      W u * centeredUniformLaplace h lambda u ^ count := by
  induction count with
  | zero => simp [centeredUniformContourWeightN]
  | succ count ih =>
      rw [centeredUniformContourWeightN, Function.iterate_succ_apply']
      change centeredUniformContourWeightN count h lambda W u *
          centeredUniformLaplace h lambda u = _
      rw [ih, pow_succ]
      ring

/-- Every finite centered-uniform factorization remains absolutely integrable. -/
theorem integrable_centeredUniformContourWeightN
    {h lambda : ℝ} (hh : 0 < h) (hlambda : 0 < lambda)
    {W : ℝ → ℂ} (hW : Integrable W) (count : ℕ) :
    Integrable (centeredUniformContourWeightN count h lambda W) := by
  induction count with
  | zero => simpa [centeredUniformContourWeightN] using hW
  | succ count ih =>
      rw [centeredUniformContourWeightN, Function.iterate_succ_apply']
      exact integrable_mul_centeredUniformLaplace hh hlambda ih

/-- Iterating the one-step Fubini theorem gives the exact finite-product
contour representation. -/
theorem centeredUniformAverageN_contourRepresentation
    {H : ℝ → ℝ} {W : ℝ → ℂ} {h lambda : ℝ}
    (hh : 0 < h) (hlambda : 0 < lambda) (hW : Integrable W)
    (hRepresentation : ∀ x : ℝ,
      (H x : ℂ) = ∫ u : ℝ, W u *
        Complex.exp ((lambda + u * Complex.I) * x))
    (count : ℕ) (x : ℝ) :
    (centeredUniformAverageN count h H x : ℂ) =
      ∫ u : ℝ,
        centeredUniformContourWeightN count h lambda W u *
          Complex.exp ((lambda + u * Complex.I) * x) := by
  induction count generalizing x with
  | zero => simpa [centeredUniformAverageN,
      centeredUniformContourWeightN] using hRepresentation x
  | succ count ih =>
      simpa only [centeredUniformAverageN, centeredUniformContourWeightN,
        Function.iterate_succ_apply'] using
          (centeredUniformAverage_contourRepresentation hh hlambda
            (integrable_centeredUniformContourWeightN hh hlambda hW count)
            (fun y => ih y) x)

/-- The centered Gaussian smoother averaged over `count` centered uniforms. -/
noncomputable def centeredHybridSmoothing
    (count : ℕ) (h sigma threshold : ℝ) : ℝ → ℝ :=
  centeredUniformAverageN count h
    (shiftedGaussianSmoothing sigma 0 threshold)

/-- The centered Gaussian base smoother is nonnegative. -/
theorem shiftedGaussianSmoothing_zero_nonneg
    {sigma threshold : ℝ} (x : ℝ) :
    0 ≤ shiftedGaussianSmoothing sigma 0 threshold x := by
  unfold shiftedGaussianSmoothing
  exact div_nonneg (ProbabilityTheory.cdf_nonneg _ _)
    (standardGaussianCDF_pos 0).le

/-- The centered Gaussian base smoother is monotone. -/
theorem monotone_shiftedGaussianSmoothing_zero
    {sigma threshold : ℝ} (hsigma : 0 < sigma) :
    Monotone (shiftedGaussianSmoothing sigma 0 threshold) := by
  intro x y hxy
  unfold shiftedGaussianSmoothing
  apply div_le_div_of_nonneg_right _ (standardGaussianCDF_pos 0).le
  apply strictMono_standardGaussianCDF.monotone
  apply (div_le_div_iff_of_pos_right hsigma).2
  linarith

/-- The centered Gaussian base has the exact reflection law around the strict
threshold. -/
theorem centeredReflection_shiftedGaussianSmoothing_zero
    {sigma threshold : ℝ} :
    CenteredReflection threshold
      (shiftedGaussianSmoothing sigma 0 threshold) := by
  intro z
  unfold shiftedGaussianSmoothing
  rw [standardGaussianCDF_zero]
  have hplus :
      (threshold + z - threshold + 0 * sigma) / sigma = z / sigma := by ring
  have hminus :
      (threshold - z - threshold + 0 * sigma) / sigma = -(z / sigma) := by ring
  rw [hplus, hminus, standardGaussianCDF_neg_eq_one_sub]
  ring

/-- Every centered Gaussian--uniform hybrid is nonnegative. -/
theorem centeredHybridSmoothing_nonneg
    {h sigma threshold : ℝ} (hh : 0 < h) (count : ℕ) (x : ℝ) :
    0 ≤ centeredHybridSmoothing count h sigma threshold x := by
  exact centeredUniformAverageN_nonneg hh
    shiftedGaussianSmoothing_zero_nonneg count x

/-- Every centered Gaussian--uniform hybrid is monotone and retains the exact
reflection law around the threshold. -/
theorem centeredHybridSmoothing_monotone_reflection
    {h sigma threshold : ℝ} (hh : 0 < h) (hsigma : 0 < sigma)
    (count : ℕ) :
    Monotone (centeredHybridSmoothing count h sigma threshold) ∧
      CenteredReflection threshold
        (centeredHybridSmoothing count h sigma threshold) := by
  exact centeredUniformAverageN_monotone_reflection hh
    (monotone_shiftedGaussianSmoothing_zero hsigma)
    centeredReflection_shiftedGaussianSmoothing_zero count

/-- The centered hybrid is a pointwise majorant of the strict upper step.
This is the semantic bridge from the exact contour identity to a probability
upper bound. -/
theorem strictUpperIndicator_le_centeredHybridSmoothing
    {h sigma threshold : ℝ} (hh : 0 < h) (hsigma : 0 < sigma)
    (count : ℕ) (x : ℝ) :
    strictUpperIndicator threshold x ≤
      centeredHybridSmoothing count h sigma threshold x := by
  by_cases hx : threshold < x
  · rw [strictUpperIndicator, if_pos hx]
    have hproperties :=
      centeredHybridSmoothing_monotone_reflection
        (threshold := threshold) hh hsigma count
    calc
      1 = centeredHybridSmoothing count h sigma threshold threshold :=
        (hproperties.2.eq_one_at_threshold).symm
      _ ≤ centeredHybridSmoothing count h sigma threshold x :=
        hproperties.1 hx.le
  · rw [strictUpperIndicator, if_neg hx]
    exact centeredHybridSmoothing_nonneg hh count x

/-- The pointwise hybrid majorant survives expectation. -/
theorem measureReal_strictUpper_preimage_le_integral_centeredHybridSmoothing
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {X : Omega → ℝ} (hX : Measurable X)
    {h sigma threshold : ℝ} (hh : 0 < h) (hsigma : 0 < sigma)
    (count : ℕ)
    (hsmooth : Integrable
      (fun omega => centeredHybridSmoothing count h sigma threshold (X omega)) mu) :
    mu.real (X ⁻¹' Set.Ioi threshold) ≤
      ∫ omega, centeredHybridSmoothing count h sigma threshold (X omega) ∂mu := by
  have hset : MeasurableSet (X ⁻¹' Set.Ioi threshold) :=
    measurableSet_Ioi.preimage hX
  have hindicator : Integrable
      (fun omega => strictUpperIndicator threshold (X omega)) mu := by
    have hfun : (fun omega => strictUpperIndicator threshold (X omega)) =
        (X ⁻¹' Set.Ioi threshold).indicator (fun _ => (1 : ℝ)) := by
      funext omega
      by_cases htail : threshold < X omega <;>
        simp [strictUpperIndicator, Set.indicator, htail]
    rw [hfun]
    exact (integrable_const (1 : ℝ)).indicator hset
  have hle :
      (∫ omega, strictUpperIndicator threshold (X omega) ∂mu) ≤
        ∫ omega, centeredHybridSmoothing count h sigma threshold (X omega) ∂mu := by
    apply integral_mono_ae hindicator hsmooth
    exact Filter.Eventually.of_forall fun omega =>
      strictUpperIndicator_le_centeredHybridSmoothing hh hsigma count (X omega)
  calc
    mu.real (X ⁻¹' Set.Ioi threshold) =
        ∫ omega, strictUpperIndicator threshold (X omega) ∂mu := by
      rw [show (fun omega => strictUpperIndicator threshold (X omega)) =
          (X ⁻¹' Set.Ioi threshold).indicator (fun _ => (1 : ℝ)) by
        funext omega
        by_cases htail : threshold < X omega <;>
          simp [strictUpperIndicator, Set.indicator, htail]]
      rw [integral_indicator hset, integral_const]
      simp
    _ ≤ _ := hle

/-- Exact contour representation of the centered hybrid smoother, obtained by
iterating the already verified shifted-Gaussian inversion. -/
theorem centeredHybridSmoothing_contourRepresentation
    {h sigma threshold lambda : ℝ}
    (hh : 0 < h) (hsigma : 0 < sigma) (hlambda : 0 < lambda)
    (count : ℕ) (x : ℝ) :
    (centeredHybridSmoothing count h sigma threshold x : ℂ) =
      ∫ u : ℝ,
        centeredUniformContourWeightN count h lambda
          (shiftedGaussianContourWeight sigma 0 threshold lambda) u *
            Complex.exp ((lambda + u * Complex.I) * x) := by
  exact centeredUniformAverageN_contourRepresentation hh hlambda
    (integrable_shiftedGaussianContourWeight hlambda hsigma)
    (shiftedGaussianSmoothing_contourRepresentation hlambda hsigma)
    count x

/-- Expectation-to-contour inequality for the centered hybrid, including all
Fubini and absolute-integrability obligations. -/
theorem integral_centeredHybridSmoothing_le_contour
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [SFinite mu]
    (X : Omega → ℝ) {h sigma threshold lambda : ℝ}
    (hX : Measurable X) (hh : 0 < h) (hsigma : 0 < sigma)
    (hlambda : 0 < lambda) (count : ℕ)
    (hReal : Integrable (fun omega => Real.exp (lambda * X omega)) mu) :
    (∫ omega, centeredHybridSmoothing count h sigma threshold (X omega) ∂mu) ≤
      ∫ u : ℝ,
        ‖centeredUniformContourWeightN count h lambda
          (shiftedGaussianContourWeight sigma 0 threshold lambda) u‖ *
        ‖complexMGF X mu (lambda + u * Complex.I)‖ := by
  exact integral_comp_le_integral_norm_complexMGF_of_contourRepresentation
    X (centeredHybridSmoothing count h sigma threshold)
      (centeredUniformContourWeightN count h lambda
        (shiftedGaussianContourWeight sigma 0 threshold lambda))
      id lambda hX
      (integrable_centeredUniformContourWeightN hh hlambda
        (integrable_shiftedGaussianContourWeight hlambda hsigma) count)
      measurable_id hReal
      (centeredHybridSmoothing_contourRepresentation hh hsigma hlambda count)

/-- Fully semantic strict-tail-to-contour bridge for the centered hybrid.
Only the subsequent deterministic enclosure of the contour norm is left to a
certificate checker. -/
theorem measureReal_strictUpper_preimage_le_centeredHybridContour
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {X : Omega → ℝ} (hX : Measurable X)
    {h sigma threshold lambda : ℝ}
    (hh : 0 < h) (hsigma : 0 < sigma) (hlambda : 0 < lambda)
    (count : ℕ)
    (hsmooth : Integrable
      (fun omega => centeredHybridSmoothing count h sigma threshold (X omega)) mu)
    (hReal : Integrable (fun omega => Real.exp (lambda * X omega)) mu) :
    mu.real (X ⁻¹' Set.Ioi threshold) ≤
      ∫ u : ℝ,
        ‖centeredUniformContourWeightN count h lambda
          (shiftedGaussianContourWeight sigma 0 threshold lambda) u‖ *
        ‖complexMGF X mu (lambda + u * Complex.I)‖ := by
  calc
    mu.real (X ⁻¹' Set.Ioi threshold) ≤
        ∫ omega,
          centeredHybridSmoothing count h sigma threshold (X omega) ∂mu :=
      measureReal_strictUpper_preimage_le_integral_centeredHybridSmoothing
        mu hX hh hsigma count hsmooth
    _ ≤ _ := integral_centeredHybridSmoothing_le_contour X hX hh hsigma
      hlambda count hReal

end CertifiedJL
