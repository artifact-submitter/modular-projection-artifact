/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperRow
import CertifiedJL.Model.Distributions.BalancedTernary.MGF
import CertifiedJL.Probability.Distributions.Rademacher.RademacherEntropyProfile
import CertifiedJL.Probability.Distributions.Rademacher.RademacherFourthMomentProfile
import CertifiedJL.Probability.Distributions.Gaussian.GaussianLinear
import CertifiedJL.Analysis.Gaussian.ShiftedGaussianInversion
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Real-axis sparse-row deficit

This file proves the entropy-profile and Gaussian-linearization ingredients
of the paper's U8 bound.  The final public theorem is stated for the actual
sparse-row quadratic MGF.
-/

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory

namespace CertifiedJL

/-- The one-dimensional real-axis cap from U8. -/
noncomputable def realRowDeficitCap (v : ℝ) : ℝ :=
  (1 + Real.exp (v / (1 + v))) / (2 * Real.sqrt (1 + v))

/-- A completed-square real Gaussian integral. -/
theorem integral_exp_neg_quadratic_add_linear
    {A : ℝ} (hA : 0 < A) (t : ℝ) :
    (∫ x : ℝ, Real.exp (-A * x ^ 2 / 2 + t * x)) =
      Real.exp (t ^ 2 / (2 * A)) * Real.sqrt (2 * Real.pi / A) := by
  have hA2 : 0 < A / 2 := by positivity
  have hpoint (x : ℝ) :
      -A * x ^ 2 / 2 + t * x =
        t ^ 2 / (2 * A) - (A / 2) * (x - t / A) ^ 2 := by
    field_simp [hA.ne']
    ring
  calc
    (∫ x : ℝ, Real.exp (-A * x ^ 2 / 2 + t * x)) =
        ∫ x : ℝ, Real.exp (t ^ 2 / (2 * A)) *
          Real.exp (-(A / 2) * (x - t / A) ^ 2) := by
            apply integral_congr_ae
            filter_upwards [] with x
            rw [hpoint, Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
            ring
    _ = Real.exp (t ^ 2 / (2 * A)) *
        ∫ x : ℝ, Real.exp (-(A / 2) * (x - t / A) ^ 2) := by
          rw [integral_const_mul]
    _ = Real.exp (t ^ 2 / (2 * A)) *
        ∫ x : ℝ, Real.exp (-(A / 2) * x ^ 2) := by
          congr 1
          calc
            (∫ x : ℝ, Real.exp (-(A / 2) * (x - t / A) ^ 2)) =
                ∫ x : ℝ, Real.exp (-(A / 2) * (x + -(t / A)) ^ 2) := by
                  congr 1
            _ = ∫ x : ℝ, Real.exp (-(A / 2) * x ^ 2) :=
              integral_add_right_eq_self
                (fun x : ℝ => Real.exp (-(A / 2) * x ^ 2)) (-(t / A))
    _ = Real.exp (t ^ 2 / (2 * A)) * Real.sqrt (Real.pi / (A / 2)) := by
          rw [integral_gaussian]
    _ = Real.exp (t ^ 2 / (2 * A)) * Real.sqrt (2 * Real.pi / A) := by
          congr 2
          field_simp [hA.ne']

/-- The same completed-square identity under the standard Gaussian law. -/
theorem integral_gaussianReal_exp_quadratic_add_linear
    {A : ℝ} (hA : 0 < A) (t : ℝ) :
    (∫ x : ℝ, Real.exp ((1 - A) * x ^ 2 / 2 + t * x)
        ∂gaussianReal 0 1) =
      Real.exp (t ^ 2 / (2 * A)) / Real.sqrt A := by
  have hsqrtA : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have hsqrtTwoPi : 0 < Real.sqrt (2 * Real.pi) := by positivity
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [smul_eq_mul, gaussianPDFReal]
  calc
    (∫ x : ℝ,
        (Real.sqrt (2 * Real.pi * (1 : NNReal)))⁻¹ *
          Real.exp (-(x - 0) ^ 2 / (2 * (1 : NNReal))) *
          Real.exp ((1 - A) * x ^ 2 / 2 + t * x)) =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        ∫ x : ℝ, Real.exp (-A * x ^ 2 / 2 + t * x) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with x
          norm_num only [NNReal.coe_one, mul_one, sub_zero]
          rw [mul_assoc, ← Real.exp_add]
          congr 1
          ring
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
        (Real.exp (t ^ 2 / (2 * A)) * Real.sqrt (2 * Real.pi / A)) := by
          rw [integral_exp_neg_quadratic_add_linear hA]
    _ = Real.exp (t ^ 2 / (2 * A)) / Real.sqrt A := by
      rw [Real.sqrt_div (by positivity : 0 ≤ 2 * Real.pi)]
      field_simp [hsqrtA.ne', hsqrtTwoPi.ne']

/-- Integrability companion to the standard-Gaussian completed-square identity. -/
theorem integrable_gaussianReal_exp_quadratic_add_linear
    {A : ℝ} (hA : 0 < A) (t : ℝ) :
    Integrable (fun x : ℝ =>
      Real.exp ((1 - A) * x ^ 2 / 2 + t * x)) (gaussianReal 0 1) := by
  let c : ℝ := (1 - A) / 2
  by_cases hc : c = 0
  · have hAone : A = 1 := by
      dsimp [c] at hc
      linarith
    simpa [hAone] using
      (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) t)
  · let shift : ℝ := t / (2 * c)
    have hOneA : 1 - A ≠ 0 := by
      intro hzero
      apply hc
      dsimp [c]
      rw [hzero]
      norm_num
    have hc_lt : c < 1 / (2 * (1 : ℝ)) := by
      dsimp [c]
      linarith
    have hcomplex := integrable_gaussianReal_shifted_complexQuadraticExp
      (s := (c : ℂ)) (μ := 0) (x := shift) (v := 1)
      (by norm_num) (by simpa using hc_lt)
    have hre := hcomplex.re.const_mul (Real.exp (-t ^ 2 / (4 * c)))
    convert hre using 1
    funext x
    have hrexp :
        (complexQuadraticExp (c : ℂ) (shift + x)).re =
          Real.exp (c * (shift + x) ^ 2) := by
      unfold complexQuadraticExp
      have harg :
          (c : ℂ) * ((shift + x : ℝ) : ℂ) ^ 2 =
            ((c * (shift + x) ^ 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [harg, Complex.exp_ofReal_re]
    change Real.exp ((1 - A) * x ^ 2 / 2 + t * x) =
      Real.exp (-t ^ 2 / (4 * c)) *
        (complexQuadraticExp (c : ℂ) (shift + x)).re
    rw [hrexp, ← Real.exp_add]
    dsimp only [shift, c]
    congr 1
    field_simp [hc, hOneA]
    ring

/-- Exact Gaussian evaluation of the entropy envelope's hyperbolic factor. -/
theorem integral_gaussianReal_exp_quadratic_mul_cosh_sq
    {A : ℝ} (hA : 0 < A) (k : ℝ) :
    (∫ x : ℝ, Real.exp ((1 - A) * x ^ 2 / 2) *
        Real.cosh (k * x) ^ 2 ∂gaussianReal 0 1) =
      (1 + Real.exp (2 * k ^ 2 / A)) / (2 * Real.sqrt A) := by
  let q : ℝ → ℝ := fun x => (1 - A) * x ^ 2 / 2
  let f : ℝ → ℝ → ℝ := fun t x => Real.exp (q x + t * x)
  have hpos : Integrable (f (2 * k)) (gaussianReal 0 1) := by
    simpa only [f, q] using
      integrable_gaussianReal_exp_quadratic_add_linear hA (2 * k)
  have hzero : Integrable (f 0) (gaussianReal 0 1) := by
    simpa only [f, q] using
      integrable_gaussianReal_exp_quadratic_add_linear hA 0
  have hneg : Integrable (f (-2 * k)) (gaussianReal 0 1) := by
    simpa only [f, q] using
      integrable_gaussianReal_exp_quadratic_add_linear hA (-2 * k)
  have hpoint (x : ℝ) :
      Real.exp (q x) * Real.cosh (k * x) ^ 2 =
        (f (2 * k) x + 2 * f 0 x + f (-2 * k) x) / 4 := by
    have hcosh : Real.cosh (k * x) ^ 2 =
        (Real.exp (2 * k * x) + 2 + Real.exp (-2 * k * x)) / 4 := by
      have hsqpos : Real.exp (k * x) ^ 2 = Real.exp (2 * k * x) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      have hsqneg : Real.exp (-(k * x)) ^ 2 = Real.exp (-2 * k * x) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      have hprod : Real.exp (k * x) * Real.exp (-(k * x)) = 1 := by
        rw [← Real.exp_add]
        simp
      calc
        Real.cosh (k * x) ^ 2 =
            ((Real.exp (k * x) + Real.exp (-(k * x))) / 2) ^ 2 := by
              rw [Real.cosh_eq]
        _ = (Real.exp (k * x) ^ 2 +
              2 * (Real.exp (k * x) * Real.exp (-(k * x))) +
              Real.exp (-(k * x)) ^ 2) / 4 := by ring
        _ = _ := by rw [hsqpos, hsqneg, hprod]; ring
    dsimp only [f]
    rw [hcosh]
    have hplus : Real.exp (q x + (2 * k) * x) =
        Real.exp (q x) * Real.exp (2 * k * x) := by rw [Real.exp_add]
    have hminus : Real.exp (q x + (-2 * k) * x) =
        Real.exp (q x) * Real.exp (-2 * k * x) := by rw [Real.exp_add]
    have hzeroexp : Real.exp (q x + 0 * x) = Real.exp (q x) := by ring
    rw [hplus, hminus, hzeroexp]
    ring
  calc
    (∫ x : ℝ, Real.exp ((1 - A) * x ^ 2 / 2) *
        Real.cosh (k * x) ^ 2 ∂gaussianReal 0 1) =
      ∫ x : ℝ, (f (2 * k) x + 2 * f 0 x + f (-2 * k) x) / 4
        ∂gaussianReal 0 1 := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact hpoint x
    _ = ((∫ x, f (2 * k) x ∂gaussianReal 0 1) +
          2 * (∫ x, f 0 x ∂gaussianReal 0 1) +
          (∫ x, f (-2 * k) x ∂gaussianReal 0 1)) / 4 := by
      rw [integral_div]
      congr 1
      calc
        (∫ x, f (2 * k) x + 2 * f 0 x + f (-2 * k) x
            ∂gaussianReal 0 1) =
          (∫ x, f (2 * k) x + 2 * f 0 x ∂gaussianReal 0 1) +
            ∫ x, f (-2 * k) x ∂gaussianReal 0 1 :=
              integral_add (hpos.add (hzero.const_mul 2)) hneg
        _ = (∫ x, f (2 * k) x ∂gaussianReal 0 1) +
              (∫ x, 2 * f 0 x ∂gaussianReal 0 1) +
              ∫ x, f (-2 * k) x ∂gaussianReal 0 1 := by
              rw [integral_add hpos (hzero.const_mul 2)]
        _ = _ := by rw [integral_const_mul]
    _ = (Real.exp ((2 * k) ^ 2 / (2 * A)) / Real.sqrt A +
          2 * (Real.exp (0 ^ 2 / (2 * A)) / Real.sqrt A) +
          Real.exp ((-2 * k) ^ 2 / (2 * A)) / Real.sqrt A) / 4 := by
      rw [integral_gaussianReal_exp_quadratic_add_linear hA,
        integral_gaussianReal_exp_quadratic_add_linear hA,
        integral_gaussianReal_exp_quadratic_add_linear hA]
    _ = (1 + Real.exp (2 * k ^ 2 / A)) / (2 * Real.sqrt A) := by
      have hsqrt : Real.sqrt A ≠ 0 := (Real.sqrt_pos.2 hA).ne'
      norm_num
      field_simp [hsqrt]
      ring

/-- Integrability companion for the hyperbolic Gaussian envelope. -/
theorem integrable_gaussianReal_exp_quadratic_mul_cosh_sq
    {A : ℝ} (hA : 0 < A) (k : ℝ) :
    Integrable (fun x : ℝ => Real.exp ((1 - A) * x ^ 2 / 2) *
      Real.cosh (k * x) ^ 2) (gaussianReal 0 1) := by
  let q : ℝ → ℝ := fun x => (1 - A) * x ^ 2 / 2
  let f : ℝ → ℝ → ℝ := fun t x => Real.exp (q x + t * x)
  have hpos : Integrable (f (2 * k)) (gaussianReal 0 1) := by
    simpa only [f, q] using
      integrable_gaussianReal_exp_quadratic_add_linear hA (2 * k)
  have hzero : Integrable (f 0) (gaussianReal 0 1) := by
    simpa only [f, q] using
      integrable_gaussianReal_exp_quadratic_add_linear hA 0
  have hneg : Integrable (f (-2 * k)) (gaussianReal 0 1) := by
    simpa only [f, q] using
      integrable_gaussianReal_exp_quadratic_add_linear hA (-2 * k)
  have hsum : Integrable (fun x =>
      (f (2 * k) x + 2 * f 0 x + f (-2 * k) x) / 4)
      (gaussianReal 0 1) :=
    ((hpos.add (hzero.const_mul 2)).add hneg).div_const 4
  refine hsum.congr (Filter.Eventually.of_forall fun x => ?_)
  dsimp only [f]
  have hcosh : Real.cosh (k * x) ^ 2 =
      (Real.exp (2 * k * x) + 2 + Real.exp (-2 * k * x)) / 4 := by
    have hprod : Real.exp (k * x) * Real.exp (-(k * x)) = 1 := by
      rw [← Real.exp_add]
      simp
    have hsqpos : Real.exp (k * x) ^ 2 = Real.exp (2 * k * x) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hsqneg : Real.exp (-(k * x)) ^ 2 = Real.exp (-2 * k * x) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    calc
      Real.cosh (k * x) ^ 2 =
          ((Real.exp (k * x) + Real.exp (-(k * x))) / 2) ^ 2 := by
            rw [Real.cosh_eq]
      _ = (Real.exp (k * x) ^ 2 +
            2 * (Real.exp (k * x) * Real.exp (-(k * x))) +
            Real.exp (-(k * x)) ^ 2) / 4 := by ring
      _ = _ := by rw [hsqpos, hsqneg, hprod]; ring
  rw [hcosh]
  have hplus : Real.exp (q x + (2 * k) * x) =
      Real.exp (q x) * Real.exp (2 * k * x) := by rw [Real.exp_add]
  have hminus : Real.exp (q x + (-2 * k) * x) =
      Real.exp (q x) * Real.exp (-2 * k * x) := by rw [Real.exp_add]
  have hzeroexp : Real.exp (q x + 0 * x) = Real.exp (q x) := by ring
  rw [hplus, hminus, hzeroexp]
  ring

/-- Pointwise form of the entropy envelope used before Gaussian integration. -/
theorem exp_entropyDefect_envelope_eq
    {lambda B G : ℝ} (hlambda : 0 ≤ lambda) (hB : 0 ≤ B) :
    Real.exp
        ((Real.sqrt (2 * lambda) * |G| / 2) ^ 2 -
          2 * Probability.rademacherEntropyDefect
            (Real.sqrt (2 * lambda) * |G| / 2 * B)) =
      Real.exp ((lambda - lambda * B ^ 2) * G ^ 2 / 2) *
        Real.cosh (Real.sqrt (2 * lambda) * B / 2 * G) ^ 2 := by
  let x : ℝ := Real.sqrt (2 * lambda) * |G| / 2
  let k : ℝ := Real.sqrt (2 * lambda) * B / 2
  have hsqrt_nonneg : 0 ≤ Real.sqrt (2 * lambda) := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt (2 * lambda)) ^ 2 = 2 * lambda :=
    Real.sq_sqrt (mul_nonneg (by norm_num) hlambda)
  have hx_sq : x ^ 2 = lambda * G ^ 2 / 2 := by
    dsimp only [x]
    rw [div_pow, mul_pow, hsqrt_sq, sq_abs]
    ring
  have hk : 0 ≤ k := by
    dsimp only [k]
    positivity
  have harg : x * B = |k * G| := by
    calc
      x * B = k * |G| := by
        dsimp only [x, k]
        ring
      _ = |k| * |G| := by rw [abs_of_nonneg hk]
      _ = |k * G| := (abs_mul k G).symm
  change Real.exp (x ^ 2 -
      2 * Probability.rademacherEntropyDefect (x * B)) = _
  rw [harg, Probability.rademacherEntropyDefect_abs]
  unfold Probability.rademacherEntropyDefect
  have hexponent :
      x ^ 2 - 2 * ((k * G) ^ 2 / 2 - Real.log (Real.cosh (k * G))) =
        (lambda - lambda * B ^ 2) * G ^ 2 / 2 +
          2 * Real.log (Real.cosh (k * G)) := by
    rw [hx_sq]
    dsimp only [k]
    ring_nf
    rw [show Real.sqrt (lambda * 2) ^ 2 = 2 * lambda by
      have hs := Real.sq_sqrt (mul_nonneg hlambda (by norm_num : (0 : ℝ) ≤ 2))
      nlinarith]
    ring
  rw [hexponent, Real.exp_add]
  have hcosh : Real.exp (Real.log (Real.cosh (k * G))) = Real.cosh (k * G) :=
    Real.exp_log (Real.cosh_pos _)
  rw [show (2 : ℝ) * Real.log (Real.cosh (k * G)) =
      Real.log (Real.cosh (k * G)) + Real.log (Real.cosh (k * G)) by ring,
    Real.exp_add, hcosh]
  dsimp only [k]
  ring

/-- Exact evaluation of the one-dimensional entropy envelope in U8. -/
theorem integral_gaussianReal_entropyDefect_envelope
    {lambda B : ℝ} (hlambda : 0 ≤ lambda) (hlambda_one : lambda < 1)
    (hB : 0 ≤ B) :
    (∫ G : ℝ, Real.exp
        ((Real.sqrt (2 * lambda) * |G| / 2) ^ 2 -
          2 * Probability.rademacherEntropyDefect
            (Real.sqrt (2 * lambda) * |G| / 2 * B))
        ∂gaussianReal 0 1) =
      (1 + Real.exp
        (lambda * B ^ 2 / (1 - lambda + lambda * B ^ 2))) /
        (2 * Real.sqrt (1 - lambda + lambda * B ^ 2)) := by
  let A : ℝ := 1 - lambda + lambda * B ^ 2
  let k : ℝ := Real.sqrt (2 * lambda) * B / 2
  have hA : 0 < A := by
    dsimp only [A]
    have hnonneg : 0 ≤ lambda * B ^ 2 :=
      mul_nonneg hlambda (sq_nonneg B)
    linarith
  have hpoint (G : ℝ) :
      Real.exp
          ((Real.sqrt (2 * lambda) * |G| / 2) ^ 2 -
            2 * Probability.rademacherEntropyDefect
              (Real.sqrt (2 * lambda) * |G| / 2 * B)) =
        Real.exp ((1 - A) * G ^ 2 / 2) * Real.cosh (k * G) ^ 2 := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt (2 * lambda) := Real.sqrt_nonneg _
    have hsqrt_sq : (Real.sqrt (2 * lambda)) ^ 2 = 2 * lambda := by
      exact Real.sq_sqrt (mul_nonneg (by norm_num) hlambda)
    have hsqrt_sq' : (Real.sqrt (lambda * 2)) ^ 2 = 2 * lambda := by
      simpa [mul_comm] using hsqrt_sq
    have hx_sq : (Real.sqrt (2 * lambda) * |G| / 2) ^ 2 =
        lambda * G ^ 2 / 2 := by
      rw [div_pow, mul_pow, hsqrt_sq, sq_abs]
      ring
    have hk : 0 ≤ k := by
      dsimp only [k]
      positivity
    have harg : Real.sqrt (2 * lambda) * |G| / 2 * B = |k * G| := by
      calc
        Real.sqrt (2 * lambda) * |G| / 2 * B = k * |G| := by
          dsimp only [k]
          ring
        _ = |k| * |G| := by rw [abs_of_nonneg hk]
        _ = |k * G| := (abs_mul k G).symm
    rw [harg, Probability.rademacherEntropyDefect_abs]
    unfold Probability.rademacherEntropyDefect
    have hexponent :
        (Real.sqrt (2 * lambda) * |G| / 2) ^ 2 -
            2 * ((k * G) ^ 2 / 2 - Real.log (Real.cosh (k * G))) =
          (1 - A) * G ^ 2 / 2 + 2 * Real.log (Real.cosh (k * G)) := by
      rw [hx_sq]
      dsimp only [A, k]
      ring_nf
      rw [hsqrt_sq']
      ring
    rw [hexponent, Real.exp_add]
    have hcosh : Real.exp (Real.log (Real.cosh (k * G))) = Real.cosh (k * G) :=
      Real.exp_log (Real.cosh_pos _)
    rw [show (2 : ℝ) * Real.log (Real.cosh (k * G)) =
        Real.log (Real.cosh (k * G)) + Real.log (Real.cosh (k * G)) by ring,
      Real.exp_add, hcosh]
    ring
  calc
    (∫ G : ℝ, Real.exp
        ((Real.sqrt (2 * lambda) * |G| / 2) ^ 2 -
          2 * Probability.rademacherEntropyDefect
            (Real.sqrt (2 * lambda) * |G| / 2 * B))
        ∂gaussianReal 0 1) =
      ∫ G : ℝ, Real.exp ((1 - A) * G ^ 2 / 2) *
        Real.cosh (k * G) ^ 2 ∂gaussianReal 0 1 := by
          apply integral_congr_ae
          filter_upwards [] with G
          exact hpoint G
    _ = (1 + Real.exp (2 * k ^ 2 / A)) / (2 * Real.sqrt A) :=
      integral_gaussianReal_exp_quadratic_mul_cosh_sq hA k
    _ = (1 + Real.exp
        (lambda * B ^ 2 / (1 - lambda + lambda * B ^ 2))) /
        (2 * Real.sqrt (1 - lambda + lambda * B ^ 2)) := by
      dsimp only [A, k]
      congr 3
      field_simp
      ring_nf
      rw [show Real.sqrt (lambda * 2) ^ 2 = 2 * lambda by
        have hs := Real.sq_sqrt (mul_nonneg hlambda (by norm_num : (0 : ℝ) ≤ 2))
        nlinarith]
      ring

/--
The actual sparse-row positive quadratic transform is a standard-Gaussian
average of its exact finite row MGF.
-/
theorem sparseRow_positiveQuadratic_gaussian
    (d : ℕ) (lambda : ℝ) (a : Fin d → ℝ) (hlambda : 0 ≤ lambda) :
    (∫ row, Real.exp (lambda * (realRowDot row a) ^ 2)
        ∂(sparseRademacherRow d).toMeasure) =
      ∫ G : ℝ,
        ∏ i, Real.cosh (Real.sqrt (2 * lambda) * G * a i / 2) ^ 2
        ∂gaussianReal 0 1 := by
  let μseed : Measure (SparseRowSeed d) :=
    (PMF.uniformOfFintype (SparseRowSeed d)).toMeasure
  let μgauss : Measure ℝ := gaussianReal 0 1
  let Z : SparseRowSeed d → ℝ := fun seed => realRowDot (sparseRow seed) a
  let f : SparseRowSeed d → ℝ → ℝ := fun seed G =>
    Real.exp (Real.sqrt (2 * lambda) * G * Z seed)
  have hZ : Measurable Z := measurable_of_finite _
  have hf_meas : Measurable (Function.uncurry f) := by
    exact Real.continuous_exp.measurable.comp
      (((measurable_const.mul measurable_snd).mul
        (hZ.comp measurable_fst)))
  have hf_int : Integrable (Function.uncurry f) (μseed.prod μgauss) := by
    rw [integrable_prod_iff hf_meas.aestronglyMeasurable]
    constructor
    · filter_upwards [] with seed
      convert (integrable_exp_mul_gaussianReal
        (μ := 0) (v := 1) (Real.sqrt (2 * lambda) * Z seed)) using 1
      funext G
      dsimp only [Function.uncurry_apply_pair, f]
      congr 1
      ring
    · have hinner :
          (fun seed => ∫ G, ‖f seed G‖ ∂μgauss) =
            fun seed => Real.exp (lambda * (Z seed) ^ 2) := by
        funext seed
        simp only [f, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        exact gaussian_exp_linear_kernel hlambda
      change Integrable (fun seed => ∫ G, ‖f seed G‖ ∂μgauss) μseed
      rw [hinner]
      obtain ⟨C, hC⟩ :=
        Finite.exists_le (fun seed : SparseRowSeed d =>
          Real.exp (lambda * (Z seed) ^ 2))
      exact Integrable.of_bound (measurable_of_finite _).aestronglyMeasurable
        C (Filter.Eventually.of_forall fun seed => by
          simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hC seed)
  calc
    (∫ row, Real.exp (lambda * (realRowDot row a) ^ 2)
        ∂(sparseRademacherRow d).toMeasure) =
      ∫ seed, Real.exp (lambda * (Z seed) ^ 2) ∂μseed := by
        rw [sparseRademacherRow_eq_map_uniformRowSeed]
        rw [← PMF.toMeasure_map
          (p := PMF.uniformOfFintype (SparseRowSeed d))
          (f := sparseRow) (measurable_of_finite _)]
        rw [integral_map_of_stronglyMeasurable
          (measurable_of_finite sparseRow)
          ((by fun_prop : Measurable
            (fun row : Fin d → ℤ =>
              Real.exp (lambda * (realRowDot row a) ^ 2))).stronglyMeasurable)]
    _ = ∫ seed, ∫ G, f seed G ∂μgauss ∂μseed := by
      apply integral_congr_ae
      filter_upwards [] with seed
      exact (gaussian_exp_linear_kernel hlambda).symm
    _ = ∫ G, ∫ seed, f seed G ∂μseed ∂μgauss :=
      integral_integral_swap hf_int
    _ = ∫ G : ℝ,
        ∏ i, Real.cosh (Real.sqrt (2 * lambda) * G * a i / 2) ^ 2
        ∂μgauss := by
      apply integral_congr_ae
      filter_upwards [] with G
      calc
        (∫ seed, f seed G ∂μseed) =
          ∫ row, Real.exp
              (realRowDot row (fun i => Real.sqrt (2 * lambda) * G * a i))
              ∂(sparseRademacherRow d).toMeasure := by
            rw [sparseRademacherRow_eq_map_uniformRowSeed]
            rw [← PMF.toMeasure_map
              (p := PMF.uniformOfFintype (SparseRowSeed d))
              (f := sparseRow) (measurable_of_finite _)]
            rw [integral_map_of_stronglyMeasurable
              (measurable_of_finite sparseRow)
              ((by fun_prop : Measurable
                (fun row : Fin d → ℤ => Real.exp (realRowDot row
                  (fun i => Real.sqrt (2 * lambda) * G * a i)))).stronglyMeasurable)]
            apply integral_congr_ae
            filter_upwards [] with seed
            dsimp only [f, Z]
            congr 1
            simp only [realRowDot, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
        _ = ∏ i, (1 +
              Real.cosh (Real.sqrt (2 * lambda) * G * a i)) / 2 := by
            exact sparseRowMGF _
        _ = ∏ i,
              Real.cosh (Real.sqrt (2 * lambda) * G * a i / 2) ^ 2 := by
            apply Finset.prod_congr rfl
            intro i _
            have harg : Real.sqrt (2 * lambda) * G * a i =
                2 * (Real.sqrt (2 * lambda) * G * a i / 2) := by ring
            calc
              (1 + Real.cosh (Real.sqrt (2 * lambda) * G * a i)) / 2 =
                  (1 + Real.cosh
                    (2 * (Real.sqrt (2 * lambda) * G * a i / 2))) / 2 := by
                    congr 2
                    exact congrArg Real.cosh harg
              _ = Real.cosh
                  (Real.sqrt (2 * lambda) * G * a i / 2) ^ 2 := by
                    rw [Real.cosh_two_mul]
                    nlinarith [Real.cosh_sq
                      (Real.sqrt (2 * lambda) * G * a i / 2)]

/-- The exact entropy-profile product bound before Gaussian integration. -/
theorem prod_cosh_sq_le_entropyDefect
    {d : ℕ} (a : Fin d → ℝ) {x B : ℝ}
    (hx : 0 ≤ x) (hB : 0 ≤ B)
    (hnorm : ∑ i, a i ^ 2 = 1)
    (hbound : ∀ i, |a i| ≤ B)
    (hfourth : ∑ i, a i ^ 4 = B ^ 4) :
    (∏ i, Real.cosh (x * a i) ^ 2) ≤
      Real.exp (x ^ 2 -
        2 * Probability.rademacherEntropyDefect (x * B)) := by
  have hent := Probability.sum_log_cosh_sub_quadratic_le
    a hx hB hbound hfourth
  have hsquare : ∑ i, (x * a i) ^ 2 = x ^ 2 := by
    simp only [mul_pow]
    rw [← Finset.mul_sum, hnorm, mul_one]
  have hlog :
      2 * ∑ i, Real.log (Real.cosh (x * a i)) ≤
        x ^ 2 - 2 * Probability.rademacherEntropyDefect (x * B) := by
    have hent' :
        (∑ i, Real.log (Real.cosh (x * a i))) -
            (∑ i, (x * a i) ^ 2) / 2 ≤
          -Probability.rademacherEntropyDefect (x * B) := by
      simpa only [Finset.sum_sub_distrib, Finset.sum_div] using hent
    rw [hsquare] at hent'
    linarith
  calc
    (∏ i, Real.cosh (x * a i) ^ 2) =
        Real.exp (2 * ∑ i, Real.log (Real.cosh (x * a i))) := by
      rw [show (∏ i, Real.cosh (x * a i) ^ 2) =
          (∏ i, Real.cosh (x * a i)) ^ 2 by rw [Finset.prod_pow]]
      rw [show (∏ i, Real.cosh (x * a i)) =
          Real.exp (∑ i, Real.log (Real.cosh (x * a i))) by
        rw [Real.exp_sum]
        apply Finset.prod_congr rfl
        intro i _
        exact (Real.exp_log (Real.cosh_pos _)).symm]
      rw [← Real.exp_nat_mul]
      norm_num
    _ ≤ _ := Real.exp_le_exp.mpr hlog

/-- U8 with an abstract fourth-moment scale `B`, before choosing its root. -/
theorem sparseRow_positiveQuadratic_le_entropyEnvelope
    {d : ℕ} (a : Fin d → ℝ) {lambda B : ℝ}
    (hlambda : 0 ≤ lambda) (hlambda_one : lambda < 1) (hB : 0 ≤ B)
    (hnorm : ∑ i, a i ^ 2 = 1)
    (hbound : ∀ i, |a i| ≤ B)
    (hfourth : ∑ i, a i ^ 4 = B ^ 4) :
    (∫ row, Real.exp (lambda * (realRowDot row a) ^ 2)
        ∂(sparseRademacherRow d).toMeasure) ≤
      (1 + Real.exp
        (lambda * B ^ 2 / (1 - lambda + lambda * B ^ 2))) /
        (2 * Real.sqrt (1 - lambda + lambda * B ^ 2)) := by
  rw [sparseRow_positiveQuadratic_gaussian d lambda a hlambda]
  let A : ℝ := 1 - lambda + lambda * B ^ 2
  let k : ℝ := Real.sqrt (2 * lambda) * B / 2
  have hA : 0 < A := by
    dsimp only [A]
    have hnonneg : 0 ≤ lambda * B ^ 2 :=
      mul_nonneg hlambda (sq_nonneg B)
    linarith
  let p : ℝ → ℝ := fun G =>
    ∏ i, Real.cosh (Real.sqrt (2 * lambda) * G * a i / 2) ^ 2
  let e : ℝ → ℝ := fun G =>
    Real.exp ((1 - A) * G ^ 2 / 2) * Real.cosh (k * G) ^ 2
  have hp_meas : Measurable p := by
    dsimp only [p]
    fun_prop
  have he_int : Integrable e (gaussianReal 0 1) := by
    simpa only [e] using
      integrable_gaussianReal_exp_quadratic_mul_cosh_sq hA k
  have hp_nonneg (G : ℝ) : 0 ≤ p G := by
    dsimp only [p]
    exact Finset.prod_nonneg fun i _ => sq_nonneg _
  have hpe (G : ℝ) : p G ≤ e G := by
    let x : ℝ := Real.sqrt (2 * lambda) * |G| / 2
    have hx : 0 ≤ x := by
      dsimp only [x]
      positivity
    have hsame : p G = ∏ i, Real.cosh (x * a i) ^ 2 := by
      dsimp only [p]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hG : 0 ≤ G
      · rw [show x * a i = Real.sqrt (2 * lambda) * G * a i / 2 by
          dsimp only [x]
          rw [abs_of_nonneg hG]
          ring]
      · have hGle : G ≤ 0 := le_of_not_ge hG
        rw [show x * a i = -(Real.sqrt (2 * lambda) * G * a i / 2) by
          dsimp only [x]
          rw [abs_of_nonpos hGle]
          ring,
          Real.cosh_neg]
    rw [hsame]
    calc
      (∏ i, Real.cosh (x * a i) ^ 2) ≤
          Real.exp (x ^ 2 -
            2 * Probability.rademacherEntropyDefect (x * B)) :=
        prod_cosh_sq_le_entropyDefect a hx hB hnorm hbound hfourth
      _ = Real.exp ((lambda - lambda * B ^ 2) * G ^ 2 / 2) *
          Real.cosh (Real.sqrt (2 * lambda) * B / 2 * G) ^ 2 := by
        dsimp only [x]
        exact exp_entropyDefect_envelope_eq hlambda hB
      _ = e G := by
        dsimp only [e, A, k]
        congr 2
        ring
  have hp_int : Integrable p (gaussianReal 0 1) := by
    apply he_int.mono_nonneg hp_meas.aestronglyMeasurable
    · exact Filter.Eventually.of_forall hp_nonneg
    · exact Filter.Eventually.of_forall hpe
  calc
    (∫ G, p G ∂gaussianReal 0 1) ≤ ∫ G, e G ∂gaussianReal 0 1 :=
      integral_mono hp_int he_int hpe
    _ = (1 + Real.exp (2 * k ^ 2 / A)) / (2 * Real.sqrt A) :=
      integral_gaussianReal_exp_quadratic_mul_cosh_sq hA k
    _ = (1 + Real.exp
        (lambda * B ^ 2 / (1 - lambda + lambda * B ^ 2))) /
        (2 * Real.sqrt (1 - lambda + lambda * B ^ 2)) := by
      dsimp only [A, k]
      congr 3
      field_simp
      ring_nf
      rw [show Real.sqrt (lambda * 2) ^ 2 = 2 * lambda by
        have hs := Real.sq_sqrt (mul_nonneg hlambda (by norm_num : (0 : ℝ) ≤ 2))
        nlinarith]
      ring

/--
The actual sparse-row real quadratic MGF satisfies the profile-dependent U8
deficit, with profile `sqrt (sum_i a_i^4)`.
-/
theorem realSparseRowDeficit_explicit
    {d : ℕ} (a : Fin d → ℝ) {lambda : ℝ}
    (hlambda : 0 ≤ lambda) (hlambda_one : lambda < 1)
    (hnorm : ∑ i, a i ^ 2 = 1) :
    (∫ row, Real.exp (lambda * (realRowDot row a) ^ 2)
        ∂(sparseRademacherRow d).toMeasure) ≤
      (1 + Real.exp
        (lambda * Real.sqrt (sparseProfileFourthMoment a) /
          (1 - lambda + lambda * Real.sqrt (sparseProfileFourthMoment a)))) /
        (2 * Real.sqrt
          (1 - lambda + lambda * Real.sqrt (sparseProfileFourthMoment a))) := by
  let B : ℝ := Probability.rademacherFourthMomentProfile a
  have hB : 0 ≤ B := Probability.rademacherFourthMomentProfile_nonneg a
  have hBpow : ∑ i, a i ^ 4 = B ^ 4 :=
    (Probability.rademacherFourthMomentProfile_pow_four a).symm
  have hBsq : B ^ 2 = Real.sqrt (sparseProfileFourthMoment a) := by
    dsimp only [B, Probability.rademacherFourthMomentProfile,
      sparseProfileFourthMoment]
    exact Real.sq_sqrt (Real.sqrt_nonneg _)
  have h := sparseRow_positiveQuadratic_le_entropyEnvelope a
    hlambda hlambda_one hB hnorm
    (Probability.abs_le_rademacherFourthMomentProfile a) hBpow
  rw [hBsq] at h
  exact h

/--
The factored paper form of U8: the Gaussian row MGF times the decreasing
profile cap `R`.
-/
theorem realSparseRowDeficit
    {d : ℕ} (a : Fin d → ℝ) {lambda : ℝ}
    (hlambda : 0 ≤ lambda) (hlambda_one : lambda < 1)
    (hnorm : ∑ i, a i ^ 2 = 1) :
    (∫ row, Real.exp (lambda * (realRowDot row a) ^ 2)
        ∂(sparseRademacherRow d).toMeasure) ≤
      (1 / Real.sqrt (1 - lambda)) *
        realRowDeficitCap
          (Real.sqrt (sparseProfileFourthMoment a) * lambda / (1 - lambda)) := by
  let rhoRoot : ℝ := Real.sqrt (sparseProfileFourthMoment a)
  let x : ℝ := 1 - lambda
  let v : ℝ := rhoRoot * lambda / x
  have hx : 0 < x := by dsimp only [x]; linarith
  have hsqrtx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hrho : 0 ≤ rhoRoot := by dsimp only [rhoRoot]; positivity
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hvone : 0 < 1 + v := by linarith
  have hden : 0 < x + lambda * rhoRoot := by positivity
  have hexponent : v / (1 + v) =
      lambda * rhoRoot / (x + lambda * rhoRoot) := by
    dsimp only [v]
    field_simp [hx.ne', hvone.ne', hden.ne']
  have hfactor : x + lambda * rhoRoot = x * (1 + v) := by
    dsimp only [v]
    field_simp [hx.ne']
  have hsqrtfactor : Real.sqrt (x + lambda * rhoRoot) =
      Real.sqrt x * Real.sqrt (1 + v) := by
    rw [hfactor, Real.sqrt_mul hx.le]
  have hexplicit := realSparseRowDeficit_explicit a hlambda hlambda_one hnorm
  change (∫ row, Real.exp (lambda * (realRowDot row a) ^ 2)
      ∂(sparseRademacherRow d).toMeasure) ≤
    (1 + Real.exp (lambda * rhoRoot / (x + lambda * rhoRoot))) /
      (2 * Real.sqrt (x + lambda * rhoRoot)) at hexplicit
  refine hexplicit.trans_eq ?_
  change (1 + Real.exp (lambda * rhoRoot / (x + lambda * rhoRoot))) /
      (2 * Real.sqrt (x + lambda * rhoRoot)) =
    1 / Real.sqrt x *
      ((1 + Real.exp (v / (1 + v))) / (2 * Real.sqrt (1 + v)))
  rw [hexponent, hsqrtfactor]
  field_simp [hsqrtx.ne', (Real.sqrt_pos.2 hvone).ne']

/-- The sparse-row complex quadratic MGF on a vertical line obeys the same U8 cap. -/
theorem norm_sparseRow_quadraticComplexMGF_le_realDeficit
    {d : ℕ} (a : Fin d → ℝ) {lambda u : ℝ}
    (hlambda : 0 ≤ lambda) (hlambda_one : lambda < 1)
    (hnorm : ∑ i, a i ^ 2 = 1) :
    ‖quadraticComplexMGF (fun row => realRowDot row a)
        (sparseRademacherRow d).toMeasure (lambda + u * Complex.I)‖ ≤
      (1 / Real.sqrt (1 - lambda)) *
        realRowDeficitCap
          (Real.sqrt (sparseProfileFourthMoment a) * lambda / (1 - lambda)) := by
  calc
    ‖quadraticComplexMGF (fun row => realRowDot row a)
        (sparseRademacherRow d).toMeasure (lambda + u * Complex.I)‖ ≤
      mgf (fun row => (realRowDot row a) ^ 2)
        (sparseRademacherRow d).toMeasure lambda := by
          simpa using norm_quadraticComplexMGF_le_real
            (fun row => realRowDot row a) (sparseRademacherRow d).toMeasure
              (lambda + u * Complex.I)
    _ = ∫ row, Real.exp (lambda * (realRowDot row a) ^ 2)
        ∂(sparseRademacherRow d).toMeasure := by rfl
    _ ≤ _ := realSparseRowDeficit a hlambda hlambda_one hnorm

/-- Derivative of the one-dimensional U8 profile cap. -/
theorem hasDerivAt_realRowDeficitCap {v : ℝ} (hv : -1 < v) :
    HasDerivAt realRowDeficitCap
      (((Real.exp (v / (1 + v)) / (1 + v) ^ 2) *
            (2 * Real.sqrt (1 + v)) -
          (1 + Real.exp (v / (1 + v))) * (1 / Real.sqrt (1 + v))) /
        (2 * Real.sqrt (1 + v)) ^ 2) v := by
  have hu : 0 < 1 + v := by linarith
  have hsqrt : 0 < Real.sqrt (1 + v) := Real.sqrt_pos.2 hu
  have ha : HasDerivAt (fun x : ℝ => x / (1 + x))
      (1 / (1 + v) ^ 2) v := by
    have hraw := (hasDerivAt_id v).div
      ((hasDerivAt_const v 1).add (hasDerivAt_id v)) hu.ne'
    exact hraw.congr_deriv (by
      simp only [Pi.add_apply, id_eq, one_mul, zero_add]
      field_simp [hu.ne']
      ring)
  have hnum : HasDerivAt
      (fun x : ℝ => 1 + Real.exp (x / (1 + x)))
      (Real.exp (v / (1 + v)) / (1 + v) ^ 2) v := by
    exact (ha.exp.const_add 1).congr_deriv (mul_one_div _ _)
  have hden : HasDerivAt (fun x : ℝ => 2 * Real.sqrt (1 + x))
      (1 / Real.sqrt (1 + v)) v := by
    have hs := (Real.hasDerivAt_sqrt hu.ne').comp v
      ((hasDerivAt_const v 1).add (hasDerivAt_id v))
    exact (hs.const_mul 2).congr_deriv (by field_simp [hsqrt.ne']; ring)
  unfold realRowDeficitCap
  exact hnum.div hden (by positivity)

/-- The U8 real-axis cap is decreasing on the nonnegative profile range. -/
theorem antitoneOn_realRowDeficitCap :
    AntitoneOn realRowDeficitCap (Set.Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
  · intro v hv
    have hv' : -1 < v := lt_of_lt_of_le (by norm_num) hv
    exact (hasDerivAt_realRowDeficitCap hv').continuousAt.continuousWithinAt
  · intro v hv
    have hv0 : 0 ≤ v := (interior_subset hv : v ∈ Set.Ici 0)
    exact (hasDerivAt_realRowDeficitCap (by linarith)).hasDerivWithinAt
  · intro v hv
    have hv0 : 0 ≤ v := (interior_subset hv : v ∈ Set.Ici 0)
    have hu : 0 < 1 + v := by linarith
    have hsqrt : 0 < Real.sqrt (1 + v) := Real.sqrt_pos.2 hu
    let a : ℝ := v / (1 + v)
    let E : ℝ := Real.exp a
    have ha : 0 ≤ a := by dsimp only [a]; positivity
    have hbase : 1 - a ≤ Real.exp (-a) := by
      nlinarith [Real.add_one_le_exp (-a)]
    have hmul : E * (1 - a) ≤ 1 := by
      calc
        E * (1 - a) ≤ E * Real.exp (-a) :=
          mul_le_mul_of_nonneg_left hbase (Real.exp_nonneg _)
        _ = 1 := by
          dsimp only [E]
          rw [← Real.exp_add]
          simp
    have hcore : E * (1 - 2 * a) ≤ 1 := by
      calc
        E * (1 - 2 * a) ≤ E * (1 - a) := by
          exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg _)
        _ ≤ 1 := hmul
    have hsqrt_sq : Real.sqrt (1 + v) ^ 2 = 1 + v :=
      Real.sq_sqrt hu.le
    have hcore' : E * (1 - v) ≤ 1 + v := by
      dsimp only [a] at hcore
      field_simp [hu.ne'] at hcore
      nlinarith
    have hstep : 2 * E ≤ (1 + v) * (1 + E) := by
      nlinarith [hcore']
    have hscaled : (1 + v) * (2 * E) ≤
        (1 + v) ^ 2 * (1 + E) := by
      simpa [pow_two, mul_assoc] using
        (mul_le_mul_of_nonneg_left hstep hu.le)
    have hnum :
        (Real.exp (v / (1 + v)) / (1 + v) ^ 2) *
              (2 * Real.sqrt (1 + v)) -
            (1 + Real.exp (v / (1 + v))) *
              (1 / Real.sqrt (1 + v)) ≤ 0 := by
      rw [sub_nonpos]
      have hright :
          (1 + Real.exp (v / (1 + v))) * (1 / Real.sqrt (1 + v)) =
            (1 + Real.exp (v / (1 + v))) / Real.sqrt (1 + v) := by
        exact mul_one_div _ _
      change Real.exp (v / (1 + v)) / (1 + v) ^ 2 *
          (2 * Real.sqrt (1 + v)) ≤
        (1 + Real.exp (v / (1 + v))) * (1 / Real.sqrt (1 + v))
      rw [hright]
      have hleft :
          Real.exp (v / (1 + v)) / (1 + v) ^ 2 *
              (2 * Real.sqrt (1 + v)) =
            (Real.exp (v / (1 + v)) * (2 * Real.sqrt (1 + v))) /
              (1 + v) ^ 2 := by ring
      rw [hleft]
      rw [div_le_div_iff₀ (sq_pos_of_pos hu) hsqrt]
      dsimp only [E] at hscaled
      nlinarith [hsqrt_sq]
    exact div_nonpos_of_nonpos_of_nonneg hnum (sq_nonneg _)

end CertifiedJL
