/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpIntegrability
import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpGaussianHalfMoment
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Exact complex quadratic MGF of the variance-one-half Gaussian

This module evaluates the complex Gaussian reference used in the sparse
upper-tail comparison. The condition `Re(s) < 1` is exactly the
integrability half-plane for a centered Gaussian of variance one half, and
the result uses Mathlib's principal complex power.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace CertifiedJL

/-- The centered variance-one-half Gaussian has complex quadratic MGF
`(1 - s)⁻¹ᐟ²` throughout the exact half-plane `Re(s) < 1`. -/
theorem integral_gaussianHalf_complexQuadraticExp
    {s : ℂ} (hs : s.re < 1) :
    (∫ x : ℝ, complexQuadraticExp s x
        ∂(gaussianReal 0 (2 : NNReal)⁻¹)) =
      (1 - s) ^ (-1 / 2 : ℂ) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [Complex.real_smul]
  have hsqrt_pi : Real.sqrt Real.pi ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
  have hsqrt_two : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  calc
    _ = (Real.sqrt Real.pi : ℂ)⁻¹ *
        ∫ x : ℝ, Complex.exp (-(1 - s) * (x : ℂ) ^ 2) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [gaussianPDFReal, complexQuadraticExp]
      norm_num [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_inv]
      have hconst :
          (Real.sqrt 2 : ℂ) *
              ((Real.sqrt Real.pi : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) =
            (Real.sqrt Real.pi : ℂ)⁻¹ := by
        calc
          _ = (Real.sqrt Real.pi : ℂ)⁻¹ *
              ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)⁻¹) := by ring
          _ = _ := by
            rw [mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hsqrt_two), mul_one]
      rw [hconst, mul_assoc, ← Complex.exp_add]
      congr 1
      ring_nf
    _ = (Real.sqrt Real.pi : ℂ)⁻¹ *
        ((Real.pi : ℂ) / (1 - s)) ^ (1 / 2 : ℂ) := by
      rw [integral_gaussian_complex]
      simpa using sub_pos.mpr hs
    _ = (1 - s) ^ (-1 / 2 : ℂ) := by
      have hbpos : 0 < (1 - s).re := by simpa using sub_pos.mpr hs
      have hb : (1 - s) ≠ 0 := by
        intro h
        rw [h] at hbpos
        simp at hbpos
      have hbarg : (1 - s).arg ≠ Real.pi := by
        intro harg
        have hneg := (Complex.arg_eq_pi_iff.mp harg).1
        linarith
      have hmul :
          ((Real.pi : ℂ) * (1 - s)⁻¹) ^ (1 / 2 : ℂ) =
            (Real.pi : ℂ) ^ (1 / 2 : ℂ) *
              ((1 - s)⁻¹) ^ (1 / 2 : ℂ) := by
        rw [Complex.cpow_def_of_ne_zero
          (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
            (inv_ne_zero hb)),
          Complex.cpow_def_of_ne_zero
            (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero),
          Complex.cpow_def_of_ne_zero (inv_ne_zero hb),
          Complex.log_ofReal_mul Real.pi_pos (inv_ne_zero hb),
          Complex.ofReal_log Real.pi_pos.le, add_mul, Complex.exp_add]
      rw [div_eq_mul_inv, hmul,
        Complex.inv_cpow (1 - s) (1 / 2 : ℂ) hbarg]
      have hpi : (Real.pi : ℂ) ^ (1 / 2 : ℂ) =
          (Real.sqrt Real.pi : ℂ) := by
        rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
          ← Complex.ofReal_cpow Real.pi_pos.le]
        norm_num [Real.sqrt_eq_rpow]
      rw [hpi, ← mul_assoc,
        inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hsqrt_pi), one_mul]
      rw [show (-1 / 2 : ℂ) = -(1 / 2 : ℂ) by ring, Complex.cpow_neg]

private theorem hasDerivAt_gaussianHalf_complexQuadraticExp_integral
    {s : ℂ} (hs : s.re < 1) :
    HasDerivAt
      (fun z : ℂ => ∫ x : ℝ, complexQuadraticExp z x
        ∂(gaussianReal 0 (2 : NNReal)⁻¹))
      (∫ x : ℝ, (x : ℂ) ^ 2 * complexQuadraticExp s x
        ∂(gaussianReal 0 (2 : NNReal)⁻¹)) s := by
  let lambda : ℝ := max 0 ((s.re + 1) / 2)
  have hslambda : s.re < lambda := by
    dsimp [lambda]
    apply lt_max_of_lt_right
    linarith
  have hlambda_nonneg : 0 ≤ lambda := by
    dsimp [lambda]
    exact le_max_left _ _
  have hlambda_lt : lambda < 1 := by
    dsimp [lambda]
    rw [max_lt_iff]
    constructor <;> linarith
  let radius : ℝ := lambda - s.re
  have hradius : 0 < radius := sub_pos.mpr hslambda
  let F : ℂ → ℝ → ℂ := fun z x => complexQuadraticExp z x
  let F' : ℂ → ℝ → ℂ := fun z x => (x : ℂ) ^ 2 * complexQuadraticExp z x
  let bound : ℝ → ℝ := fun x => |x| ^ 2 * Real.exp (lambda * x ^ 2)
  have hbound : Integrable bound (gaussianReal 0 (2 : NNReal)⁻¹) := by
    exact (gaussianHalf_quadraticExpEvenMomentBound
      hlambda_nonneg hlambda_lt).integrable 1
  have hFint : Integrable (F s) (gaussianReal 0 (2 : NNReal)⁻¹) := by
    exact integrable_gaussianReal_complexQuadraticExp
      (v := (2 : NNReal)⁻¹) (by norm_num) (by simpa using hs)
  have hderiv : ∀ x : ℝ, ∀ z : ℂ, HasDerivAt (fun w => F w x) (F' z x) z := by
    intro x z
    simpa [F, F', complexQuadraticExp, mul_comm] using
      ((hasDerivAt_id z).mul_const ((x : ℂ) ^ 2)).cexp
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (μ := gaussianReal 0 (2 : NNReal)⁻¹)
    (s := Metric.ball s radius) (bound := bound)
    (Metric.ball_mem_nhds s hradius) ?_ hFint ?_ ?_ hbound ?_).2
  · filter_upwards [] with z
    apply Continuous.aestronglyMeasurable
    dsimp [F, complexQuadraticExp]
    fun_prop
  · apply Continuous.aestronglyMeasurable
    dsimp [F', complexQuadraticExp]
    fun_prop
  · filter_upwards [] with x
    intro z hz
    have hzdist : ‖z - s‖ < radius := by
      simpa [Metric.mem_ball, dist_eq_norm_sub] using hz
    have hzre : z.re < lambda := by
      have hre : z.re - s.re ≤ ‖z - s‖ := by
        simpa [Complex.sub_re] using Complex.re_le_norm (z - s)
      dsimp [radius] at hzdist
      linarith
    change ‖(x : ℂ) ^ 2 * Complex.exp (z * (x : ℂ) ^ 2)‖ ≤
      |x| ^ 2 * Real.exp (lambda * x ^ 2)
    rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_exp]
    have hrexp : (z * (x : ℂ) ^ 2).re = z.re * x ^ 2 := by
      norm_num [pow_two, Complex.mul_re]
    rw [hrexp, Real.norm_eq_abs]
    gcongr
  · filter_upwards [] with x
    intro z _
    exact hderiv x z

/-- The first parameter derivative of the Gaussian quadratic MGF is the exact
tilted second moment. -/
theorem integral_gaussianHalf_sq_mul_complexQuadraticExp
    {s : ℂ} (hs : s.re < 1) :
    (∫ x : ℝ, (x : ℂ) ^ 2 * complexQuadraticExp s x
        ∂(gaussianReal 0 (2 : NNReal)⁻¹)) =
      (1 / 2 : ℂ) * (1 - s) ^ (-3 / 2 : ℂ) := by
  let G : ℂ → ℂ := fun z => ∫ x : ℝ, complexQuadraticExp z x
    ∂(gaussianReal 0 (2 : NNReal)⁻¹)
  let H : ℂ → ℂ := fun z => (1 - z) ^ (-1 / 2 : ℂ)
  have hG : HasDerivAt G
      (∫ x : ℝ, (x : ℂ) ^ 2 * complexQuadraticExp s x
        ∂(gaussianReal 0 (2 : NNReal)⁻¹)) s := by
    simpa [G] using hasDerivAt_gaussianHalf_complexQuadraticExp_integral hs
  have hbpos : 0 < (1 - s).re := by simpa using sub_pos.mpr hs
  have hbase : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := by
    simpa [sub_eq_add_neg] using (hasDerivAt_id s).neg.const_add (1 : ℂ)
  have hHraw := hbase.cpow_const (c := (-1 / 2 : ℂ))
    (Complex.mem_slitPlane_iff.mpr (Or.inl hbpos) : (1 - s) ∈ Complex.slitPlane)
  have hH : HasDerivAt H ((1 / 2 : ℂ) * (1 - s) ^ (-3 / 2 : ℂ)) s := by
    simpa [H] using hHraw.congr_deriv (by ring_nf)
  have heq : G =ᶠ[𝓝 s] H := by
    have hopen : IsOpen {z : ℂ | z.re < 1} :=
      isOpen_lt Complex.continuous_re continuous_const
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact integral_gaussianHalf_complexQuadraticExp hz
  have hG' := hH.congr_of_eventuallyEq heq
  exact hG.unique hG'

private theorem hasDerivAt_gaussianHalf_sqMoment_integral
    {s : ℂ} (hs : s.re < 1) :
    HasDerivAt
      (fun z : ℂ => ∫ x : ℝ, (x : ℂ) ^ 2 * complexQuadraticExp z x
        ∂(gaussianReal 0 (2 : NNReal)⁻¹))
      (∫ x : ℝ, (x : ℂ) ^ 4 * complexQuadraticExp s x
        ∂(gaussianReal 0 (2 : NNReal)⁻¹)) s := by
  let lambda : ℝ := max 0 ((s.re + 1) / 2)
  have hslambda : s.re < lambda := by
    dsimp [lambda]
    apply lt_max_of_lt_right
    linarith
  have hlambda_nonneg : 0 ≤ lambda := by
    dsimp [lambda]
    exact le_max_left _ _
  have hlambda_lt : lambda < 1 := by
    dsimp [lambda]
    rw [max_lt_iff]
    constructor <;> linarith
  let radius : ℝ := lambda - s.re
  have hradius : 0 < radius := sub_pos.mpr hslambda
  let F : ℂ → ℝ → ℂ := fun z x =>
    (x : ℂ) ^ 2 * complexQuadraticExp z x
  let F' : ℂ → ℝ → ℂ := fun z x =>
    (x : ℂ) ^ 4 * complexQuadraticExp z x
  let bound : ℝ → ℝ := fun x => |x| ^ 4 * Real.exp (lambda * x ^ 2)
  have hbound : Integrable bound (gaussianReal 0 (2 : NNReal)⁻¹) := by
    exact (gaussianHalf_quadraticExpEvenMomentBound
      hlambda_nonneg hlambda_lt).integrable 2
  have hFint : Integrable (F s) (gaussianReal 0 (2 : NNReal)⁻¹) := by
    exact integrable_gaussianReal_evenPow_mul_complexQuadraticExp
      (v := (2 : NNReal)⁻¹) (by norm_num) (by simpa using hs) 1
  have hderiv : ∀ x : ℝ, ∀ z : ℂ, HasDerivAt (fun w => F w x) (F' z x) z := by
    intro x z
    have hexp := ((hasDerivAt_id z).mul_const ((x : ℂ) ^ 2)).cexp
    have hconst : HasDerivAt (fun _ : ℂ => (x : ℂ) ^ 2) 0 z :=
      hasDerivAt_const z _
    have hprod := hconst.mul hexp
    refine (hprod.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [] with w
      simp [F, complexQuadraticExp, id_eq]
    · simp [F', complexQuadraticExp, id_eq]
      ring_nf
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (μ := gaussianReal 0 (2 : NNReal)⁻¹)
    (s := Metric.ball s radius) (bound := bound)
    (Metric.ball_mem_nhds s hradius) ?_ hFint ?_ ?_ hbound ?_).2
  · filter_upwards [] with z
    apply Continuous.aestronglyMeasurable
    dsimp [F, complexQuadraticExp]
    fun_prop
  · apply Continuous.aestronglyMeasurable
    dsimp [F', complexQuadraticExp]
    fun_prop
  · filter_upwards [] with x
    intro z hz
    have hzdist : ‖z - s‖ < radius := by
      simpa [Metric.mem_ball, dist_eq_norm_sub] using hz
    have hzre : z.re < lambda := by
      have hre : z.re - s.re ≤ ‖z - s‖ := by
        simpa [Complex.sub_re] using Complex.re_le_norm (z - s)
      dsimp [radius] at hzdist
      linarith
    change ‖(x : ℂ) ^ 4 * Complex.exp (z * (x : ℂ) ^ 2)‖ ≤
      |x| ^ 4 * Real.exp (lambda * x ^ 2)
    rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_exp]
    have hrexp : (z * (x : ℂ) ^ 2).re = z.re * x ^ 2 := by
      norm_num [pow_two, Complex.mul_re]
    rw [hrexp, Real.norm_eq_abs]
    gcongr
  · filter_upwards [] with x
    intro z _
    exact hderiv x z

/-- The second parameter derivative of the Gaussian quadratic MGF is the exact
tilted fourth moment. -/
theorem integral_gaussianHalf_fourthPow_mul_complexQuadraticExp
    {s : ℂ} (hs : s.re < 1) :
    (∫ x : ℝ, (x : ℂ) ^ 4 * complexQuadraticExp s x
        ∂(gaussianReal 0 (2 : NNReal)⁻¹)) =
      (3 / 4 : ℂ) * (1 - s) ^ (-5 / 2 : ℂ) := by
  let G : ℂ → ℂ := fun z =>
    ∫ x : ℝ, (x : ℂ) ^ 2 * complexQuadraticExp z x
      ∂(gaussianReal 0 (2 : NNReal)⁻¹)
  let H : ℂ → ℂ := fun z =>
    (1 / 2 : ℂ) * (1 - z) ^ (-3 / 2 : ℂ)
  have hG : HasDerivAt G
      (∫ x : ℝ, (x : ℂ) ^ 4 * complexQuadraticExp s x
        ∂(gaussianReal 0 (2 : NNReal)⁻¹)) s := by
    simpa [G] using hasDerivAt_gaussianHalf_sqMoment_integral hs
  have hbpos : 0 < (1 - s).re := by simpa using sub_pos.mpr hs
  have hbase : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := by
    simpa [sub_eq_add_neg] using (hasDerivAt_id s).neg.const_add (1 : ℂ)
  have hpow := hbase.cpow_const (c := (-3 / 2 : ℂ))
    (Complex.mem_slitPlane_iff.mpr (Or.inl hbpos) : (1 - s) ∈ Complex.slitPlane)
  have hconst : HasDerivAt (fun _ : ℂ => (1 / 2 : ℂ)) 0 s :=
    hasDerivAt_const s _
  have hprod := hconst.mul hpow
  have hH : HasDerivAt H ((3 / 4 : ℂ) * (1 - s) ^ (-5 / 2 : ℂ)) s := by
    refine (hprod.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [] with z
      rfl
    · try dsimp [H]
      ring_nf
  have heq : G =ᶠ[𝓝 s] H := by
    have hopen : IsOpen {z : ℂ | z.re < 1} :=
      isOpen_lt Complex.continuous_re continuous_const
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact integral_gaussianHalf_sq_mul_complexQuadraticExp hz
  have hG' := hH.congr_of_eventuallyEq heq
  exact hG.unique hG'

/-- The Gaussian expectation of the fourth spatial derivative has the exact
U4 reference value `12 * s² * (1 - s)⁻⁵ᐟ²`. -/
theorem integral_gaussianHalf_iteratedDeriv_four_complexQuadraticExp
    {s : ℂ} (hs : s.re < 1) :
    (∫ x : ℝ, iteratedDeriv 4 (complexQuadraticExp s) x
        ∂(gaussianReal 0 (2 : NNReal)⁻¹)) =
      12 * s ^ 2 * (1 - s) ^ (-5 / 2 : ℂ) := by
  have h0 := integrable_gaussianReal_evenPow_mul_complexQuadraticExp
    (s := s) (μ := 0) (v := (2 : NNReal)⁻¹)
    (by norm_num) (by simpa using hs) 0
  have h2 := integrable_gaussianReal_evenPow_mul_complexQuadraticExp
    (s := s) (μ := 0) (v := (2 : NNReal)⁻¹)
    (by norm_num) (by simpa using hs) 1
  have h4 := integrable_gaussianReal_evenPow_mul_complexQuadraticExp
    (s := s) (μ := 0) (v := (2 : NNReal)⁻¹)
    (by norm_num) (by simpa using hs) 2
  have h0' : Integrable (fun x : ℝ => complexQuadraticExp s x)
      (gaussianReal 0 (2 : NNReal)⁻¹) := by simpa using h0
  have h2' : Integrable (fun x : ℝ =>
      (x : ℂ) ^ 2 * complexQuadraticExp s x)
      (gaussianReal 0 (2 : NNReal)⁻¹) := by simpa using h2
  have h4' : Integrable (fun x : ℝ =>
      (x : ℂ) ^ 4 * complexQuadraticExp s x)
      (gaussianReal 0 (2 : NNReal)⁻¹) := by simpa using h4
  let f0 : ℝ → ℂ := fun x => (12 * s ^ 2) * complexQuadraticExp s x
  let f2 : ℝ → ℂ := fun x =>
    (48 * s ^ 3) * ((x : ℂ) ^ 2 * complexQuadraticExp s x)
  let f4 : ℝ → ℂ := fun x =>
    (16 * s ^ 4) * ((x : ℂ) ^ 4 * complexQuadraticExp s x)
  have hf0 : Integrable f0 (gaussianReal 0 (2 : NNReal)⁻¹) := h0'.const_mul _
  have hf2 : Integrable f2 (gaussianReal 0 (2 : NNReal)⁻¹) := h2'.const_mul _
  have hf4 : Integrable f4 (gaussianReal 0 (2 : NNReal)⁻¹) := h4'.const_mul _
  rw [show (fun x : ℝ => iteratedDeriv 4 (complexQuadraticExp s) x) =
      (fun x : ℝ =>
        (12 * s ^ 2) * complexQuadraticExp s x +
        (48 * s ^ 3) * ((x : ℂ) ^ 2 * complexQuadraticExp s x) +
        (16 * s ^ 4) * ((x : ℂ) ^ 4 * complexQuadraticExp s x)) by
    funext x
    rw [iteratedDeriv_four_complexQuadraticExp]
    simp only [complexQuadraticExpFourthPolynomialComplex]
    ring_nf]
  change (∫ x : ℝ, (f0 + f2) x + f4 x
      ∂(gaussianReal 0 (2 : NNReal)⁻¹)) = _
  rw [integral_add (hf0.add hf2) hf4]
  change (∫ x : ℝ, f0 x + f2 x ∂(gaussianReal 0 (2 : NNReal)⁻¹)) +
      ∫ x : ℝ, f4 x ∂(gaussianReal 0 (2 : NNReal)⁻¹) = _
  rw [integral_add hf0 hf2]
  dsimp [f0, f2, f4]
  simp only [integral_const_mul]
  rw [integral_gaussianHalf_complexQuadraticExp hs,
    integral_gaussianHalf_sq_mul_complexQuadraticExp hs,
    integral_gaussianHalf_fourthPow_mul_complexQuadraticExp hs]
  have hb : (1 - s) ≠ 0 := by
    intro h
    have hpos : 0 < (1 - s).re := by simpa using sub_pos.mpr hs
    rw [h] at hpos
    simp at hpos
  have hm0 : (1 - s) ^ (-1 / 2 : ℂ) =
      (1 - s) ^ 2 * (1 - s) ^ (-5 / 2 : ℂ) := by
    calc
      _ = (1 - s) ^ ((-5 / 2 : ℂ) + 2) := by
        congr 2
        ring
      _ = (1 - s) ^ (-5 / 2 : ℂ) * (1 - s) ^ (2 : ℂ) :=
        Complex.cpow_add _ _ hb
      _ = (1 - s) ^ (-5 / 2 : ℂ) * (1 - s) ^ (2 : ℕ) := by
        exact congrArg (fun z => (1 - s) ^ (-5 / 2 : ℂ) * z)
          (Complex.cpow_natCast (1 - s) 2)
      _ = _ := by ring_nf
  have hm2 : (1 - s) ^ (-3 / 2 : ℂ) =
      (1 - s) * (1 - s) ^ (-5 / 2 : ℂ) := by
    calc
      _ = (1 - s) ^ ((-5 / 2 : ℂ) + 1) := by
        congr 2
        ring
      _ = (1 - s) ^ (-5 / 2 : ℂ) * (1 - s) ^ (1 : ℂ) :=
        Complex.cpow_add _ _ hb
      _ = _ := by rw [Complex.cpow_one]; ring_nf
  rw [hm0, hm2]
  ring_nf


end CertifiedJL
