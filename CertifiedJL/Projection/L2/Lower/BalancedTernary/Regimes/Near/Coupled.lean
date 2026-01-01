/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Shared.CosineLaplace
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Shared.Scalar.LobePeriodization
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Shared.Scalar.LobeTail
import CertifiedJL.Projection.L2.Lower.BalancedTernary.WrappedFourier
import CertifiedJL.Analysis.Fourier.NormalizedCosineProduct
import CertifiedJL.Probability.Distributions.Gaussian.StandardGaussian
import Mathlib.Analysis.MeanInequalities
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Retained-coordinate scalar reduction for the threshold near band

The ordinary sparse scalar reduction separates every coordinate by Holder.
That loses the cancellation between a near-threshold coordinate and the
diffuse remainder precisely at the sharp `0.543` endpoint.  This file keeps
one coordinate inside every residual Holder factor.  Consequently the
arbitrary-dimensional profile reduces to coupled two-frequency Gaussian
moments rather than to a product of unrelated one-frequency moments.
-/

open scoped BigOperators ENNReal NNReal

open MeasureTheory ProbabilityTheory

namespace CertifiedJL

/-- The nonnegative Gaussian factor of the coordinate retained across the
residual Holder reduction. -/
noncomputable def retainedGaussianCosineFactor
    (s r : ℝ) (G : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.cos (Real.sqrt (s / 2) * G * Real.sqrt r) ^ 2)

/-- One coupled two-frequency moment.  The first frequency is retained with
full exponent two; `x` is a normalized residual squared mass and therefore
the second factor has reciprocal Holder exponent `2/x`. -/
noncomputable def retainedGaussianCosineMoment
    (s r x : ℝ) : ℝ≥0∞ :=
  ∫⁻ G : ℝ,
    retainedGaussianCosineFactor s r G *
      gaussianCosineHolderFactor (s * (1 - r)) x G
      ∂(gaussianReal 0 1)

/-- Real-integral form of the retained moment.  Keeping this bridge explicit
lets the analytic two-frequency estimates feed the ENNReal Holder product
without an untracked coercion. -/
theorem retainedGaussianCosineMoment_eq_ofReal_integral
    {s r x : ℝ} (hx : 0 < x) :
    retainedGaussianCosineMoment s r x =
      ENNReal.ofReal
        (∫ G : ℝ,
          Real.cos (Real.sqrt (s / 2) * G * Real.sqrt r) ^ 2 *
            |Real.cos
              (Real.sqrt ((s * (1 - r)) / (2 / x)) * G)| ^ (2 / x)
          ∂(gaussianReal 0 1)) := by
  let f : ℝ → ℝ := fun G =>
    Real.cos (Real.sqrt (s / 2) * G * Real.sqrt r) ^ 2 *
      |Real.cos
        (Real.sqrt ((s * (1 - r)) / (2 / x)) * G)| ^ (2 / x)
  have hpx : 0 < 2 / x := by positivity
  have hf : Integrable f (gaussianReal 0 1) := by
    refine Integrable.of_bound (by dsimp [f]; fun_prop) 1 ?_
    filter_upwards [] with G
    dsimp [f]
    rw [abs_mul, abs_sq,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact mul_le_one₀
      ((sq_le_one_iff_abs_le_one _).2 (Real.abs_cos_le_one _))
      (Real.rpow_nonneg (abs_nonneg _) _)
      (Real.rpow_le_one (abs_nonneg _) (Real.abs_cos_le_one _) hpx.le)
  have hf0 : ∀ G, 0 ≤ f G := fun G =>
    mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (abs_nonneg _) _)
  rw [retainedGaussianCosineMoment]
  calc
    (∫⁻ G : ℝ, retainedGaussianCosineFactor s r G *
        gaussianCosineHolderFactor (s * (1 - r)) x G
        ∂(gaussianReal 0 1)) =
      ∫⁻ G : ℝ, ENNReal.ofReal (f G) ∂(gaussianReal 0 1) := by
        apply lintegral_congr
        intro G
        dsimp [retainedGaussianCosineFactor,
          gaussianCosineHolderFactor, f]
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    _ = ENNReal.ofReal (∫ G : ℝ, f G ∂(gaussianReal 0 1)) :=
      (ofReal_integral_eq_lintegral_ofReal hf
        (Filter.Eventually.of_forall hf0)).symm
    _ = _ := rfl

/-! ## Exact geometry of the high-retained region -/

/-- The coarse compact-mass cap already puts the residual fraction below one
quarter in the high-retained region.  This is the seam needed by the first
three wrapped Fourier modes. -/
theorem thresholdNear_highRetained_residual_lt_quarter
    {x r : ℝ} (hx0 : 0 ≤ x) (hx : x < 4901 / 2500)
    (hr : 23 / 25 ≤ r) :
    x * (1 - r) < 1 / 4 := by
  have hfrac : 1 - r ≤ (2 / 25 : ℝ) := by linarith
  have hmul : x * (1 - r) ≤ x * (2 / 25 : ℝ) :=
    mul_le_mul_of_nonneg_left hfrac hx0
  have hend : x * (2 / 25 : ℝ) < 1 / 4 := by nlinarith
  exact hmul.trans_lt hend

/-- Using both the retained ratio and the coordinate cap gives the sharper
residual mass `4802/57500`, which is useful in the large-modulus spatial
branch. -/
theorem thresholdNear_highRetained_residual_le
    {x r aSq : ℝ} (hx0 : 0 ≤ x)
    (hr : 23 / 25 ≤ r) (ha : aSq = x * r)
    (hcap : aSq ≤ 2401 / 2500) :
    x * (1 - r) ≤ 4802 / 57500 := by
  have hratio : 23 * (1 - r) ≤ 2 * r := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hratio hx0
  have hxr : x * r ≤ 2401 / 2500 := by simpa [ha] using hcap
  nlinarith

/-- A residual below `B²/4` and the public margin `q ≥ 3B` place modes one
through three strictly inside the elementary cosine range. -/
theorem thresholdNear_threeMode_frequency
    {q : ℕ} {B V : ℝ} (hq : 0 < q) (hB : 0 < B)
    (hmargin : 3 * B ≤ (q : ℝ)) (hV0 : 0 < V)
    (hV : V < B ^ 2 / 4) :
    ∀ n ∈ Finset.range 3,
      Real.pi * |(((n + 1 : ℕ) : ℤ) : ℝ)| * Real.sqrt V / (q : ℝ) <
        Real.pi / 2 := by
  have hqReal : 0 < (q : ℝ) := by exact_mod_cast hq
  have hsqrt : Real.sqrt V < B / 2 := by
    have hsqrt0 := Real.sqrt_nonneg V
    have hsqrtSq := Real.sq_sqrt hV0.le
    nlinarith [sq_nonneg (Real.sqrt V - B / 2)]
  intro n hn
  have hn3 : (n : ℝ) + 1 ≤ 3 := by
    have hnlt : n < 3 := Finset.mem_range.1 hn
    exact_mod_cast (show n + 1 ≤ 3 by omega)
  have hfreq : (((n + 1 : ℕ) : ℤ) : ℝ) * Real.sqrt V < (q : ℝ) / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hn3 (Real.sqrt_nonneg V)
    have hthree : 3 * Real.sqrt V < 3 * B / 2 := by nlinarith
    have hqhalf : 3 * B / 2 ≤ (q : ℝ) / 2 := by nlinarith
    have hresult : ((n : ℝ) + 1) * Real.sqrt V < (q : ℝ) / 2 :=
      hmul.trans_lt (hthree.trans_le hqhalf)
    exact_mod_cast hresult
  have hnat : 0 ≤ (((n + 1 : ℕ) : ℤ) : ℝ) := by positivity
  rw [abs_of_nonneg hnat]
  apply (div_lt_iff₀ hqReal).2
  nlinarith [Real.pi_pos]

/-! ## Retained central lobe -/

/-- Cosine transform of a centered Gaussian with arbitrary positive
variance. -/
theorem gaussian_cosine_charFun_variance (v : ℝ≥0) (t : ℝ) :
    ∫ x : ℝ, Real.cos (t * x) ∂(gaussianReal 0 v) =
      Real.exp (-(v : ℝ) * t ^ 2 / 2) := by
  have h_int :
      Integrable (fun x : ℝ => Complex.exp ((t * x) * Complex.I))
        (gaussianReal 0 v) := by
    refine (integrable_const (1 : ℝ)).mono' ?_ ?_
    · fun_prop
    · filter_upwards with x
      simpa only [Complex.ofReal_mul] using
        (Complex.norm_exp_ofReal_mul_I (t * x)).le
  have h_re := integral_re h_int
  calc
    ∫ x : ℝ, Real.cos (t * x) ∂(gaussianReal 0 v) =
        ∫ x : ℝ, (Complex.exp ((t * x) * Complex.I)).re
          ∂(gaussianReal 0 v) := by
      congr 1
      funext x
      simpa only [Complex.ofReal_mul] using
        (Complex.exp_ofReal_mul_I_re (t * x)).symm
    _ = (MeasureTheory.charFun (gaussianReal 0 v) t).re := by
      rw [MeasureTheory.charFun_apply_real]
      rw [← RCLike.re_eq_complex_re]
      exact h_re
    _ = Real.exp (-(v : ℝ) * t ^ 2 / 2) := by
      rw [ProbabilityTheory.charFun_gaussianReal]
      simp [Complex.exp_re, pow_two]
      ring

/-- Multiplying the standard Gaussian density by a centered quadratic
exponential only changes its variance. -/
theorem gaussian_exp_neg_sq_mul_cos_integral
    {u : ℝ} (hu : 0 ≤ u) (t : ℝ) :
    (∫ x : ℝ, Real.exp (-u * x ^ 2 / 2) * Real.cos (t * x)
        ∂(gaussianReal 0 1)) =
      Real.exp (-t ^ 2 / (2 * (1 + u))) / Real.sqrt (1 + u) := by
  let A : ℝ := 1 + u
  have hA : 0 < A := by dsimp [A]; linarith
  let v : ℝ≥0 := ⟨A⁻¹, inv_nonneg.mpr hA.le⟩
  have hv : v ≠ 0 := by
    apply NNReal.coe_ne_zero.mp
    change A⁻¹ ≠ 0
    exact inv_ne_zero hA.ne'
  have hdensity (x : ℝ) :
      ProbabilityTheory.gaussianPDFReal 0 1 x *
          (Real.exp (-u * x ^ 2 / 2) * Real.cos (t * x)) =
        1 / Real.sqrt A *
          (ProbabilityTheory.gaussianPDFReal 0 v x * Real.cos (t * x)) := by
    unfold ProbabilityTheory.gaussianPDFReal
    norm_num only [NNReal.coe_one, mul_one, sub_zero]
    have hsqrtA : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
    have hsqrtTwoPi : 0 < Real.sqrt (2 * Real.pi) := by positivity
    have hsqrtDiv :
        Real.sqrt (2 * Real.pi / A) =
          Real.sqrt (2 * Real.pi) / Real.sqrt A := by
      exact Real.sqrt_div (by positivity) A
    have hvariance : (v : ℝ) = 1 / A := by
      change A⁻¹ = 1 / A
      rw [one_div]
    rw [hvariance]
    rw [show 2 * Real.pi * (1 / A) = 2 * Real.pi / A by ring,
      hsqrtDiv]
    have hexponent :
        -(x ^ 2) / 2 + (-u * x ^ 2 / 2) =
          -(x ^ 2) / (2 * (1 / A)) := by
      dsimp [A]
      field_simp [hA.ne']
      ring
    calc
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) *
          (Real.exp (-u * x ^ 2 / 2) * Real.cos (t * x)) =
        (Real.sqrt (2 * Real.pi))⁻¹ *
          (Real.exp (-x ^ 2 / 2) * Real.exp (-u * x ^ 2 / 2)) *
            Real.cos (t * x) := by ring
      _ = (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-(x ^ 2) / (2 * (1 / A))) *
            Real.cos (t * x) := by rw [← Real.exp_add, hexponent]
      _ = 1 / Real.sqrt A *
          ((Real.sqrt (2 * Real.pi) / Real.sqrt A)⁻¹ *
            Real.exp (-(x ^ 2) / (2 * (1 / A))) * Real.cos (t * x)) := by
        field_simp [hsqrtA.ne', hsqrtTwoPi.ne']
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul
    (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul]
  calc
    (∫ x : ℝ, ProbabilityTheory.gaussianPDFReal 0 1 x *
        (Real.exp (-u * x ^ 2 / 2) * Real.cos (t * x))) =
      ∫ x : ℝ, 1 / Real.sqrt A *
        (ProbabilityTheory.gaussianPDFReal 0 v x * Real.cos (t * x)) := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact hdensity x
    _ = 1 / Real.sqrt A *
        ∫ x : ℝ, ProbabilityTheory.gaussianPDFReal 0 v x *
          Real.cos (t * x) := by rw [integral_const_mul]
    _ = 1 / Real.sqrt A *
        ∫ x : ℝ, Real.cos (t * x) ∂(gaussianReal 0 v) := by
          rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul hv]
          simp only [smul_eq_mul]
    _ = 1 / Real.sqrt A * Real.exp (-(v : ℝ) * t ^ 2 / 2) := by
          rw [gaussian_cosine_charFun_variance]
    _ = Real.exp (-t ^ 2 / (2 * (1 + u))) /
        Real.sqrt (1 + u) := by
          rw [show (v : ℝ) = 1 / A by
            change A⁻¹ = 1 / A
            rw [one_div]]
          have hexponent :
              -(1 / A) * t ^ 2 / 2 = -t ^ 2 / (2 * (1 + u)) := by
            dsimp [A]
            field_simp [hA.ne']
          rw [hexponent]
          dsimp [A]
          ring

/-- Closed retained-coordinate central-lobe integral. -/
theorem gaussian_exp_neg_sq_mul_cos_sq_integral
    {u : ℝ} (hu : 0 ≤ u) (a : ℝ) :
    (∫ x : ℝ, Real.exp (-u * x ^ 2 / 2) * Real.cos (a * x) ^ 2
        ∂(gaussianReal 0 1)) =
      (1 + Real.exp (-2 * a ^ 2 / (1 + u))) /
        (2 * Real.sqrt (1 + u)) := by
  let f : ℝ → ℝ := fun x => Real.exp (-u * x ^ 2 / 2)
  let g : ℝ → ℝ := fun x =>
    Real.exp (-u * x ^ 2 / 2) * Real.cos ((2 * a) * x)
  have hf : Integrable f (gaussianReal 0 1) := by
    refine Integrable.of_bound (by fun_prop) 1 ?_
    filter_upwards [] with x
    have hexponent : -u * x ^ 2 / 2 ≤ 0 := by
      nlinarith [mul_nonneg hu (sq_nonneg x)]
    simpa [f, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)] using
      Real.exp_le_one_iff.mpr hexponent
  have hg : Integrable g (gaussianReal 0 1) := by
    refine Integrable.of_bound (by fun_prop) 1 ?_
    filter_upwards [] with x
    have hexp : Real.exp (-u * x ^ 2 / 2) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [mul_nonneg hu (sq_nonneg x)]
    dsimp [g]
    rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_one₀ hexp (abs_nonneg _) (Real.abs_cos_le_one _)
  have hpoint (x : ℝ) :
      Real.exp (-u * x ^ 2 / 2) * Real.cos (a * x) ^ 2 =
        (f x + g x) / 2 := by
    rw [Real.cos_sq]
    dsimp [f, g]
    ring
  calc
    (∫ x : ℝ, Real.exp (-u * x ^ 2 / 2) * Real.cos (a * x) ^ 2
        ∂(gaussianReal 0 1)) =
      ∫ x : ℝ, (f x + g x) / 2 ∂(gaussianReal 0 1) := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact hpoint x
    _ = ((∫ x : ℝ, f x ∂(gaussianReal 0 1)) +
        (∫ x : ℝ, g x ∂(gaussianReal 0 1))) / 2 := by
      rw [integral_div, integral_add hf hg]
    _ = (1 / Real.sqrt (1 + u) +
        Real.exp (-(2 * a) ^ 2 / (2 * (1 + u))) /
          Real.sqrt (1 + u)) / 2 := by
      rw [show (∫ x : ℝ, f x ∂(gaussianReal 0 1)) =
          1 / Real.sqrt (1 + u) by
        simpa [f] using gaussian_exp_neg_sq_mul_cos_integral hu 0,
        show (∫ x : ℝ, g x ∂(gaussianReal 0 1)) =
          Real.exp (-(2 * a) ^ 2 / (2 * (1 + u))) /
            Real.sqrt (1 + u) by
        simpa [g] using gaussian_exp_neg_sq_mul_cos_integral hu (2 * a)]
    _ = (1 + Real.exp (-2 * a ^ 2 / (1 + u))) /
        (2 * Real.sqrt (1 + u)) := by
      have hden : 1 + u ≠ 0 := by linarith
      have hexponent :
          -(2 * a) ^ 2 / (2 * (1 + u)) = -2 * a ^ 2 / (1 + u) := by
        field_simp [hden]
      rw [hexponent]
      ring

/-- For exponents between one and two, the chord joining the first two
integer powers is an elementary upper majorant.  This is the high-residual-
weight replacement for the much heavier Hermite interpolant. -/
theorem rpow_le_linear_sq {z α : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hα1 : 1 ≤ α) (hα2 : α ≤ 2) :
    z ^ α ≤ (2 - α) * z + (α - 1) * z ^ 2 := by
  by_cases hz : z = 0
  · subst z
    simp [Real.zero_rpow (by linarith : α ≠ 0)]
  have hzpos : 0 < z := lt_of_le_of_ne hz0 (Ne.symm hz)
  have hgeom := Real.geom_mean_le_arith_mean2_weighted
    (show 0 ≤ 2 - α by linarith) (show 0 ≤ α - 1 by linarith)
    hz0 (sq_nonneg z) (show (2 - α) + (α - 1) = 1 by ring)
  calc
    z ^ α = z ^ (2 - α) * (z ^ 2) ^ (α - 1) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hz0, ← Real.rpow_add hzpos]
      congr 1
      ring
    _ ≤ (2 - α) * z + (α - 1) * z ^ 2 := hgeom

/-- Exact mixed Gaussian cosine moment used to integrate the elementary
quadratic power majorant. -/
theorem gaussian_cos_sq_mul_cos_integral (A C : ℝ) :
    (∫ G : ℝ, Real.cos (A * G) ^ 2 * Real.cos (C * G)
        ∂(gaussianReal 0 1)) =
      (1 / 2 : ℝ) * Real.exp (-C ^ 2 / 2) +
        (1 / 4 : ℝ) *
          (Real.exp (-(C + 2 * A) ^ 2 / 2) +
            Real.exp (-(C - 2 * A) ^ 2 / 2)) := by
  let f : ℝ → ℝ := fun G => (1 / 2 : ℝ) * Real.cos (C * G)
  let g : ℝ → ℝ := fun G => (1 / 4 : ℝ) *
    (Real.cos ((C + 2 * A) * G) + Real.cos ((C - 2 * A) * G))
  have hf : Integrable f (gaussianReal 0 1) :=
    (gaussian_cos_integrable C).const_mul _
  have hg : Integrable g (gaussianReal 0 1) :=
    ((gaussian_cos_integrable (C + 2 * A)).add
      (gaussian_cos_integrable (C - 2 * A))).const_mul _
  have hpoint (G : ℝ) :
      Real.cos (A * G) ^ 2 * Real.cos (C * G) = f G + g G := by
    dsimp [f, g]
    rw [Real.cos_sq]
    have hprod := Real.two_mul_cos_mul_cos ((2 * A) * G) (C * G)
    rw [show (2 * A) * G + C * G = (C + 2 * A) * G by ring,
      show (2 * A) * G - C * G = -((C - 2 * A) * G) by ring,
      Real.cos_neg] at hprod
    rw [show 2 * (A * G) = (2 * A) * G by ring]
    linear_combination hprod / 4
  calc
    (∫ G : ℝ, Real.cos (A * G) ^ 2 * Real.cos (C * G)
        ∂(gaussianReal 0 1)) =
      ∫ G : ℝ, f G + g G ∂(gaussianReal 0 1) := by
        apply integral_congr_ae
        filter_upwards [] with G
        exact hpoint G
    _ = (∫ G : ℝ, f G ∂(gaussianReal 0 1)) +
        ∫ G : ℝ, g G ∂(gaussianReal 0 1) := integral_add hf hg
    _ = (1 / 2 : ℝ) *
          (∫ G : ℝ, Real.cos (C * G) ∂(gaussianReal 0 1)) +
        (1 / 4 : ℝ) *
          ((∫ G : ℝ, Real.cos ((C + 2 * A) * G)
              ∂(gaussianReal 0 1)) +
            ∫ G : ℝ, Real.cos ((C - 2 * A) * G)
              ∂(gaussianReal 0 1)) := by
        dsimp [f, g]
        rw [integral_const_mul, integral_const_mul,
          integral_add (gaussian_cos_integrable (C + 2 * A))
            (gaussian_cos_integrable (C - 2 * A))]
    _ = _ := by
      rw [gaussian_cosine_charFun, gaussian_cosine_charFun,
        gaussian_cosine_charFun]

/-- Exact retained-coordinate moment against a fourth residual cosine power. -/
theorem gaussian_cos_sq_mul_cos_pow_four_integral (A B : ℝ) :
    (∫ G : ℝ, Real.cos (A * G) ^ 2 * Real.cos (B * G) ^ 4
        ∂(gaussianReal 0 1)) =
      (3 / 8 : ℝ) *
          ((1 + Real.exp (-(2 * A) ^ 2 / 2)) / 2) +
        (1 / 2 : ℝ) *
          ((1 / 2 : ℝ) * Real.exp (-(2 * B) ^ 2 / 2) +
            (1 / 4 : ℝ) *
              (Real.exp (-(2 * B + 2 * A) ^ 2 / 2) +
                Real.exp (-(2 * B - 2 * A) ^ 2 / 2))) +
        (1 / 8 : ℝ) *
          ((1 / 2 : ℝ) * Real.exp (-(4 * B) ^ 2 / 2) +
            (1 / 4 : ℝ) *
              (Real.exp (-(4 * B + 2 * A) ^ 2 / 2) +
                Real.exp (-(4 * B - 2 * A) ^ 2 / 2))) := by
  let f : ℝ → ℝ := fun G => (3 / 8 : ℝ) * Real.cos (A * G) ^ 2
  let g : ℝ → ℝ := fun G => (1 / 2 : ℝ) *
    (Real.cos (A * G) ^ 2 * Real.cos ((2 * B) * G))
  let h : ℝ → ℝ := fun G => (1 / 8 : ℝ) *
    (Real.cos (A * G) ^ 2 * Real.cos ((4 * B) * G))
  have hbase : Integrable (fun G : ℝ => Real.cos (A * G) ^ 2)
      (gaussianReal 0 1) := by
    refine Integrable.of_bound (by fun_prop) 1 ?_
    filter_upwards [] with G
    rw [Real.norm_eq_abs, abs_sq]
    exact (sq_le_one_iff_abs_le_one (Real.cos (A * G))).2
      (Real.abs_cos_le_one _)
  have htwo : Integrable (fun G : ℝ =>
      Real.cos (A * G) ^ 2 * Real.cos ((2 * B) * G))
      (gaussianReal 0 1) := by
    refine Integrable.of_bound (by fun_prop) 1 ?_
    filter_upwards [] with G
    rw [Real.norm_eq_abs, abs_mul, abs_sq]
    exact mul_le_one₀
      ((sq_le_one_iff_abs_le_one (Real.cos (A * G))).2
        (Real.abs_cos_le_one _))
      (abs_nonneg _) (Real.abs_cos_le_one _)
  have hfour : Integrable (fun G : ℝ =>
      Real.cos (A * G) ^ 2 * Real.cos ((4 * B) * G))
      (gaussianReal 0 1) := by
    refine Integrable.of_bound (by fun_prop) 1 ?_
    filter_upwards [] with G
    rw [Real.norm_eq_abs, abs_mul, abs_sq]
    exact mul_le_one₀
      ((sq_le_one_iff_abs_le_one (Real.cos (A * G))).2
        (Real.abs_cos_le_one _))
      (abs_nonneg _) (Real.abs_cos_le_one _)
  have hf : Integrable f (gaussianReal 0 1) := hbase.const_mul _
  have hg : Integrable g (gaussianReal 0 1) := htwo.const_mul _
  have hh : Integrable h (gaussianReal 0 1) := hfour.const_mul _
  have hpoint (G : ℝ) :
      Real.cos (A * G) ^ 2 * Real.cos (B * G) ^ 4 =
        f G + g G + h G := by
    dsimp [f, g, h]
    have hdouble := Real.two_mul_cos_mul_cos
      (2 * (B * G)) (2 * (B * G))
    rw [show 2 * (B * G) + 2 * (B * G) = 4 * (B * G) by ring,
      sub_self, Real.cos_zero] at hdouble
    have hdouble' :
        2 * Real.cos ((2 * B) * G) * Real.cos ((2 * B) * G) =
          1 + Real.cos ((4 * B) * G) := by
      convert hdouble using 1 <;> ring
    have hcos4 : Real.cos (B * G) ^ 4 =
        (3 + 4 * Real.cos ((2 * B) * G) +
          Real.cos ((4 * B) * G)) / 8 := by
      rw [show Real.cos (B * G) ^ 4 =
          (Real.cos (B * G) ^ 2) ^ 2 by ring, Real.cos_sq]
      have hsquare : Real.cos ((2 * B) * G) ^ 2 =
          (1 + Real.cos ((4 * B) * G)) / 2 := by
        linear_combination hdouble' / 2
      rw [show 2 * (B * G) = (2 * B) * G by ring]
      nlinarith
    rw [hcos4]
    ring
  have hbaseval :
      (∫ G : ℝ, Real.cos (A * G) ^ 2 ∂(gaussianReal 0 1)) =
        (1 + Real.exp (-(2 * A) ^ 2 / 2)) / 2 := by
    have hzero := gaussian_cos_sq_mul_cos_integral A 0
    norm_num at hzero ⊢
    nlinarith
  calc
    (∫ G : ℝ, Real.cos (A * G) ^ 2 * Real.cos (B * G) ^ 4
        ∂(gaussianReal 0 1)) =
      ∫ G : ℝ, (f G + g G) + h G ∂(gaussianReal 0 1) := by
        apply integral_congr_ae
        filter_upwards [] with G
        exact hpoint G
    _ = ((∫ G : ℝ, f G ∂(gaussianReal 0 1)) +
          ∫ G : ℝ, g G ∂(gaussianReal 0 1)) +
        ∫ G : ℝ, h G ∂(gaussianReal 0 1) := by
      rw [show (∫ G : ℝ, f G + g G + h G ∂(gaussianReal 0 1)) =
          (∫ G : ℝ, f G + g G ∂(gaussianReal 0 1)) +
            ∫ G : ℝ, h G ∂(gaussianReal 0 1) by
        simpa only [Pi.add_apply] using integral_add (hf.add hg) hh,
        integral_add hf hg]
    _ = (3 / 8 : ℝ) *
          (∫ G : ℝ, Real.cos (A * G) ^ 2 ∂(gaussianReal 0 1)) +
        (1 / 2 : ℝ) *
          (∫ G : ℝ, Real.cos (A * G) ^ 2 * Real.cos ((2 * B) * G)
            ∂(gaussianReal 0 1)) +
        (1 / 8 : ℝ) *
          (∫ G : ℝ, Real.cos (A * G) ^ 2 * Real.cos ((4 * B) * G)
            ∂(gaussianReal 0 1)) := by
      dsimp [f, g, h]
      rw [integral_const_mul, integral_const_mul, integral_const_mul]
    _ = _ := by
      rw [hbaseval, gaussian_cos_sq_mul_cos_integral,
        gaussian_cos_sq_mul_cos_integral]

/-- In the residual-weight range `y ≥ 1/2`, the power chord reduces the
coupled retained moment to its exactly computable second and fourth powers. -/
theorem retainedGaussianRpowMoment_le_powerChord
    {A y : ℝ} (hy : 1 / 2 ≤ y) (hy1 : y ≤ 1) (B : ℝ) :
    (∫ G : ℝ, Real.cos (A * G) ^ 2 *
        |Real.cos (B * G)| ^ (2 / y)
        ∂(gaussianReal 0 1)) ≤
      (2 - 1 / y) *
          (∫ G : ℝ, Real.cos (A * G) ^ 2 * Real.cos (B * G) ^ 2
            ∂(gaussianReal 0 1)) +
        (1 / y - 1) *
          (∫ G : ℝ, Real.cos (A * G) ^ 2 * Real.cos (B * G) ^ 4
            ∂(gaussianReal 0 1)) := by
  have hy0 : 0 < y := by linarith
  let f : ℝ → ℝ := fun G => Real.cos (A * G) ^ 2 *
    |Real.cos (B * G)| ^ (2 / y)
  let g : ℝ → ℝ := fun G =>
    (2 - 1 / y) * (Real.cos (A * G) ^ 2 * Real.cos (B * G) ^ 2) +
      (1 / y - 1) * (Real.cos (A * G) ^ 2 * Real.cos (B * G) ^ 4)
  have hf : Integrable f (gaussianReal 0 1) := by
    refine Integrable.of_bound (by dsimp [f]; fun_prop) 1 ?_
    filter_upwards [] with G
    dsimp [f]
    rw [abs_mul, abs_sq,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    have hA : Real.cos (A * G) ^ 2 ≤ 1 :=
      (sq_le_one_iff_abs_le_one _).2 (Real.abs_cos_le_one _)
    have hR : |Real.cos (B * G)| ^ (2 / y) ≤ 1 := by
      exact Real.rpow_le_one (abs_nonneg _) (Real.abs_cos_le_one _)
        (by positivity)
    exact mul_le_one₀ hA (Real.rpow_nonneg (abs_nonneg _) _) hR
  have h2 : Integrable (fun G : ℝ =>
      Real.cos (A * G) ^ 2 * Real.cos (B * G) ^ 2)
      (gaussianReal 0 1) := by
    refine Integrable.of_bound (by fun_prop) 1 ?_
    filter_upwards [] with G
    rw [Real.norm_eq_abs, abs_mul, abs_sq, abs_sq]
    exact mul_le_one₀
      ((sq_le_one_iff_abs_le_one _).2 (Real.abs_cos_le_one _))
      (sq_nonneg _)
      ((sq_le_one_iff_abs_le_one _).2 (Real.abs_cos_le_one _))
  have h4 : Integrable (fun G : ℝ =>
      Real.cos (A * G) ^ 2 * Real.cos (B * G) ^ 4)
      (gaussianReal 0 1) := by
    refine Integrable.of_bound (by fun_prop) 1 ?_
    filter_upwards [] with G
    rw [Real.norm_eq_abs, abs_mul, abs_sq, abs_pow]
    have hA : Real.cos (A * G) ^ 2 ≤ 1 :=
      (sq_le_one_iff_abs_le_one _).2 (Real.abs_cos_le_one _)
    have hB : |Real.cos (B * G)| ^ 4 ≤ 1 := by
      exact pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _)
    exact mul_le_one₀ hA (by positivity) hB
  have hg : Integrable g (gaussianReal 0 1) :=
    (h2.const_mul _).add (h4.const_mul _)
  have hpoint (G : ℝ) : f G ≤ g G := by
    have hz0 : 0 ≤ Real.cos (B * G) ^ 2 := sq_nonneg _
    have hz1 : Real.cos (B * G) ^ 2 ≤ 1 :=
      (sq_le_one_iff_abs_le_one _).2 (Real.abs_cos_le_one _)
    have hα1 : 1 ≤ 1 / y := (le_div_iff₀ hy0).2 (by linarith)
    have hα2 : 1 / y ≤ 2 := (div_le_iff₀ hy0).2 (by linarith)
    have hpow := rpow_le_linear_sq hz0 hz1 hα1 hα2
    have hrpow : (Real.cos (B * G) ^ 2) ^ (1 / y) =
        |Real.cos (B * G)| ^ (2 / y) := by
      by_cases hc : Real.cos (B * G) = 0
      · rw [hc, abs_zero, zero_pow (by omega),
          Real.zero_rpow (div_ne_zero one_ne_zero hy0.ne'),
          Real.zero_rpow (div_ne_zero (by norm_num) hy0.ne')]
      rw [show Real.cos (B * G) ^ 2 = |Real.cos (B * G)| ^ 2 by
        exact (sq_abs _).symm,
        ← Real.rpow_natCast]
      rw [← Real.rpow_mul (abs_nonneg _)]
      congr 1
      field_simp [hy0.ne']
      norm_num
    rw [hrpow] at hpow
    dsimp [f, g]
    nlinarith [sq_nonneg (Real.cos (A * G))]
  calc
    (∫ G : ℝ, Real.cos (A * G) ^ 2 *
        |Real.cos (B * G)| ^ (2 / y)
        ∂(gaussianReal 0 1)) =
      ∫ G : ℝ, f G ∂(gaussianReal 0 1) := by rfl
    _ ≤ ∫ G : ℝ, g G ∂(gaussianReal 0 1) :=
      integral_mono hf hg hpoint
    _ = _ := by
      dsimp [g]
      rw [integral_add (h2.const_mul _) (h4.const_mul _),
        integral_const_mul, integral_const_mul]

/-! ## Coupled central-lobe periodization -/

/-- The retained coordinate is kept on the central residual cosine lobe;
away from that lobe it is discarded and the exact nonzero-image
periodization is used.  This is the coupled low-weight endpoint required by
the near-band Holder product. -/
theorem retainedGaussianRpowMoment_le_central_add_nonzero_images
    {A u y : ℝ} (hu : 0 < u) (hy : 0 < y) :
    (∫ G : ℝ, Real.cos (A * G) ^ 2 *
        |Real.cos (Real.sqrt (u / (2 / y)) * G)| ^ (2 / y)
        ∂(gaussianReal 0 1)) ≤
      (1 + Real.exp (-2 * A ^ 2 / (1 + u))) /
          (2 * Real.sqrt (1 + u)) +
        1 / Real.sqrt (1 + u) *
          ∑' k : {k : ℤ // k ≠ 0},
            Real.exp (-((2 / y) * ((k : ℤ) : ℝ) ^ 2 * Real.pi ^ 2) /
              (2 * (1 + u))) := by
  let p : ℝ := 2 / y
  let B : ℝ := Real.sqrt (u / p)
  let C : Set ℝ := {G : ℝ | B * G ∈ scalarLobe 0}
  have hp : 0 < p := by dsimp [p]; positivity
  have hu_div_p : 0 < u / p := div_pos hu hp
  have hB : 0 < B := Real.sqrt_pos.2 hu_div_p
  have hC : MeasurableSet C :=
    (measurableSet_scalarLobe 0).preimage (by fun_prop)
  let f : ℝ → ℝ := fun G => Real.cos (A * G) ^ 2 *
    |Real.cos (B * G)| ^ p
  have hf : Integrable f (gaussianReal 0 1) := by
    refine Integrable.of_bound (by dsimp [f]; fun_prop) 1 ?_
    filter_upwards [] with G
    dsimp [f]
    rw [abs_mul, abs_sq,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact mul_le_one₀
      ((sq_le_one_iff_abs_le_one _).2 (Real.abs_cos_le_one _))
      (Real.rpow_nonneg (abs_nonneg _) _)
      (Real.rpow_le_one (abs_nonneg _) (Real.abs_cos_le_one _) hp.le)
  have hcentral (G : ℝ) (hG : G ∈ C) :
      f G ≤ Real.exp (-u * G ^ 2 / 2) * Real.cos (A * G) ^ 2 := by
    have hcos := scalarLobe_cosineEnvelope hG
    have hpow := Real.rpow_le_rpow (abs_nonneg _) hcos hp.le
    have hpow_exp :
        (Real.exp (-((B * G - ((0 : ℤ) : ℝ) * Real.pi) ^ 2) / 2)) ^ p =
          Real.exp (-u * G ^ 2 / 2) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      have hBsquare : B ^ 2 = u / p := by
        dsimp [B]
        exact Real.sq_sqrt hu_div_p.le
      simp only [Int.cast_zero, zero_mul, sub_zero]
      rw [mul_pow, hBsquare]
      field_simp [hp.ne']
    rw [hpow_exp] at hpow
    dsimp [f]
    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_left hpow (sq_nonneg (Real.cos (A * G))))
  have houtside (G : ℝ) (_hG : G ∈ Cᶜ) :
      f G ≤ sparseScalarFIntegrand u p G := by
    dsimp [f, sparseScalarFIntegrand]
    have hcosSq : Real.cos (A * G) ^ 2 ≤ 1 :=
      (sq_le_one_iff_abs_le_one _).2 (Real.abs_cos_le_one _)
    have hpow0 : 0 ≤ |Real.cos (B * G)| ^ p :=
      Real.rpow_nonneg (abs_nonneg _) _
    have hBdef : B = Real.sqrt (u / p) := rfl
    rw [← hBdef]
    nlinarith
  have hcentral_integral :
      (∫ G in C, f G ∂(gaussianReal 0 1)) ≤
        (1 + Real.exp (-2 * A ^ 2 / (1 + u))) /
          (2 * Real.sqrt (1 + u)) := by
    calc
      (∫ G in C, f G ∂(gaussianReal 0 1)) ≤
          ∫ G in C, Real.exp (-u * G ^ 2 / 2) *
            Real.cos (A * G) ^ 2 ∂(gaussianReal 0 1) := by
        apply setIntegral_mono_on hf.integrableOn
          ((Integrable.of_bound (by fun_prop) 1 (by
            filter_upwards [] with G
            rw [Real.norm_eq_abs, abs_mul, abs_sq,
              abs_of_nonneg (Real.exp_nonneg _)]
            have hexp : Real.exp (-u * G ^ 2 / 2) ≤ 1 := by
              rw [Real.exp_le_one_iff]
              nlinarith [mul_nonneg hu.le (sq_nonneg G)]
            exact mul_le_one₀ hexp (sq_nonneg _)
              ((sq_le_one_iff_abs_le_one _).2 (Real.abs_cos_le_one _))
          ))).integrableOn hC hcentral
      _ ≤ ∫ G : ℝ, Real.exp (-u * G ^ 2 / 2) *
            Real.cos (A * G) ^ 2 ∂(gaussianReal 0 1) := by
        apply setIntegral_le_integral
          (Integrable.of_bound (by fun_prop) 1 (by
            filter_upwards [] with G
            rw [Real.norm_eq_abs, abs_mul, abs_sq,
              abs_of_nonneg (Real.exp_nonneg _)]
            have hexp : Real.exp (-u * G ^ 2 / 2) ≤ 1 := by
              rw [Real.exp_le_one_iff]
              nlinarith [mul_nonneg hu.le (sq_nonneg G)]
            exact mul_le_one₀ hexp (sq_nonneg _)
              ((sq_le_one_iff_abs_le_one _).2 (Real.abs_cos_le_one _))))
        filter_upwards [] with G
        exact mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)
      _ = _ := gaussian_exp_neg_sq_mul_cos_sq_integral hu.le A
  have houtside_integral :
      (∫ G in Cᶜ, f G ∂(gaussianReal 0 1)) ≤
        1 / Real.sqrt (1 + u) *
          ∑' k : {k : ℤ // k ≠ 0},
            Real.exp (-(p * ((k : ℤ) : ℝ) ^ 2 * Real.pi ^ 2) /
              (2 * (1 + u))) := by
    calc
      (∫ G in Cᶜ, f G ∂(gaussianReal 0 1)) ≤
          ∫ G in Cᶜ, sparseScalarFIntegrand u p G
            ∂(gaussianReal 0 1) := by
        apply setIntegral_mono_on hf.integrableOn
          (sparseScalarF_integrable hp).integrableOn hC.compl houtside
      _ ≤ _ := by
        simpa only [C, B] using
          sparseScalarF_compl_centralLobe_le_nonzero_images hu hp
  rw [show (2 / y : ℝ) = p by rfl,
    show Real.sqrt (u / (2 / y)) = B by rfl]
  rw [← integral_add_compl hC hf]
  exact add_le_add hcentral_integral houtside_integral

/-- Geometric closed form of the coupled central-lobe estimate. -/
theorem retainedGaussianRpowMoment_le_central_geometricTail
    {A u y : ℝ} (hu : 0 < u) (hy : 0 < y) :
    (∫ G : ℝ, Real.cos (A * G) ^ 2 *
        |Real.cos (Real.sqrt (u / (2 / y)) * G)| ^ (2 / y)
        ∂(gaussianReal 0 1)) ≤
      (1 + Real.exp (-2 * A ^ 2 / (1 + u))) /
          (2 * Real.sqrt (1 + u)) +
        1 / Real.sqrt (1 + u) *
          (2 * Real.exp (-(Real.pi ^ 2 / (y * (1 + u)))) /
            (1 - (Real.exp (-(Real.pi ^ 2 / (y * (1 + u))))) ^ 3)) := by
  let c : ℝ := Real.pi ^ 2 / (y * (1 + u))
  have hc : 0 < c := by dsimp [c]; positivity
  have hbase := retainedGaussianRpowMoment_le_central_add_nonzero_images
    (A := A) hu hy
  have hterm (k : {k : ℤ // k ≠ 0}) :
      -((2 / y) * ((k : ℤ) : ℝ) ^ 2 * Real.pi ^ 2) /
          (2 * (1 + u)) =
        -c * ((k : ℤ) : ℝ) ^ 2 := by
    dsimp [c]
    field_simp [hy.ne', (show 1 + u ≠ 0 by linarith)]
  have hsubtype :
      (∑' k : {k : ℤ // k ≠ 0},
          Real.exp (-c * ((k : ℤ) : ℝ) ^ 2)) =
        ∑' k : ℤ, if k = 0 then (0 : ℝ)
          else Real.exp (-c * (k : ℝ) ^ 2) := by
    let g : ℤ → ℝ := fun n => Real.exp (-c * (n : ℝ) ^ 2)
    calc
      (∑' k : {k : ℤ // k ≠ 0},
          Real.exp (-c * ((k : ℤ) : ℝ) ^ 2)) =
        ∑' k : {k : ℤ // k ≠ 0}, g k := by rfl
      _ = ∑' k : ℤ, {k : ℤ | k ≠ 0}.indicator g k :=
        tsum_subtype {k : ℤ | k ≠ 0} g
      _ = ∑' k : ℤ, if k = 0 then (0 : ℝ)
          else Real.exp (-c * (k : ℝ) ^ 2) := by
        apply tsum_congr
        intro k
        by_cases hk : k = 0
        · simp [Set.indicator, hk]
        · simp [Set.indicator, hk, g]
  have htail := scalarLobe_real_integer_exp_nonzero_geometricTail hc
  calc
    (∫ G : ℝ, Real.cos (A * G) ^ 2 *
        |Real.cos (Real.sqrt (u / (2 / y)) * G)| ^ (2 / y)
        ∂(gaussianReal 0 1)) ≤
      (1 + Real.exp (-2 * A ^ 2 / (1 + u))) /
          (2 * Real.sqrt (1 + u)) +
        1 / Real.sqrt (1 + u) *
          ∑' k : {k : ℤ // k ≠ 0},
            Real.exp (-((2 / y) * ((k : ℤ) : ℝ) ^ 2 * Real.pi ^ 2) /
              (2 * (1 + u))) := hbase
    _ = (1 + Real.exp (-2 * A ^ 2 / (1 + u))) /
          (2 * Real.sqrt (1 + u)) +
        1 / Real.sqrt (1 + u) *
          ∑' k : ℤ, if k = 0 then (0 : ℝ)
            else Real.exp (-c * (k : ℝ) ^ 2) := by
      congr 2
      rw [← hsubtype]
      apply tsum_congr
      intro k
      rw [hterm]
    _ ≤ (1 + Real.exp (-2 * A ^ 2 / (1 + u))) /
          (2 * Real.sqrt (1 + u)) +
        1 / Real.sqrt (1 + u) *
          (2 * Real.exp (-c) /
            (1 - (Real.exp (-c)) ^ 3)) := by
      gcongr
    _ = _ := by rfl

/-! ## Retaining the near coordinate in wrapped Fourier modes -/

/-- For every frequency in the elementary-cosine range, the residual
coordinates contribute their full Gaussian damping while the selected near
coordinate remains explicit.  This is the pointwise ingredient that prevents
the wrapped-image allowance from consuming the sharp near-band slack. -/
theorem sparseCyclicCosineModeInt_le_retained_residualExp
    {q d : ℕ} (w : Fin d → ℤ) (i : Fin d) (k : ℤ) (V : ℝ)
    (hq : 0 < q)
    (hV : 0 < V)
    (hresidual : ∑ j ∈ Finset.univ.erase i, (w j : ℝ) ^ 2 = V)
    (hfrequency :
      Real.pi * |(k : ℝ)| * Real.sqrt V / (q : ℝ) < Real.pi / 2) :
    sparseCyclicCosineModeInt q w k ≤
      Real.cos (Real.pi * (k : ℝ) * (w i : ℝ) / (q : ℝ)) ^ 2 *
        Real.exp
          (-((Real.pi * |(k : ℝ)| * Real.sqrt V / (q : ℝ)) ^ 2)) := by
  let v : EuclideanSpace ℝ (Fin d) :=
    WithLp.toLp 2 (fun j => if j = i then 0 else (w j : ℝ))
  have hqReal : 0 < (q : ℝ) := by exact_mod_cast hq
  have hvnormSq : ‖v‖ ^ 2 = V := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      ∑ j, v j ^ 2 =
          ∑ j ∈ Finset.univ.erase i, v j ^ 2 + v i ^ 2 := by
        exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
      _ = V := by
        have herase : ∑ j ∈ Finset.univ.erase i, v j ^ 2 = V := by
          convert hresidual using 1
          apply Finset.sum_congr rfl
          intro j hj
          simp only [v]
          rw [if_neg (Finset.mem_erase.1 hj).1]
        rw [herase]
        simp [v]
  have hv : v ≠ 0 := by
    intro hvzero
    have : ‖v‖ ^ 2 = 0 := by simp [hvzero]
    linarith
  let α : ℝ := Real.pi * |(k : ℝ)| * Real.sqrt V / (q : ℝ)
  have hα0 : 0 ≤ α := by dsimp [α]; positivity
  have hvnorm : ‖v‖ = Real.sqrt V := by
    apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [hvnormSq, Real.sq_sqrt hV.le]
  have hres := Probability.normalized_cosineProduct_le_exp_neg_sq
    v hv hα0 (by simpa [α] using hfrequency)
  have hfactor (j : Fin d) :
      (1 + Real.cos
          ((2 * Real.pi * (k : ℝ) / (q : ℝ)) * (w j : ℝ))) / 2 =
        Real.cos (Real.pi * (k : ℝ) * (w j : ℝ) / (q : ℝ)) ^ 2 := by
    rw [Real.cos_sq]
    ring
  have hresProduct :
      (∏ j ∈ Finset.univ.erase i,
          Real.cos (Real.pi * (k : ℝ) * (w j : ℝ) / (q : ℝ)) ^ 2) ≤
        Real.exp (-α ^ 2) := by
    calc
      _ = ∏ j, Real.cos (α * v j / ‖v‖) ^ 2 := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
        simp only [v, if_pos, mul_zero, zero_div, Real.cos_zero, one_pow,
          one_mul]
        apply Finset.prod_congr rfl
        intro j hj
        rw [if_neg (Finset.mem_erase.1 hj).1, hvnorm]
        congr 1
        by_cases hk : 0 ≤ (k : ℝ)
        · rw [show α * (w j : ℝ) / Real.sqrt V =
              Real.pi * (k : ℝ) * (w j : ℝ) / (q : ℝ) by
                dsimp [α]
                rw [abs_of_nonneg hk]
                field_simp [hqReal.ne', (Real.sqrt_pos.2 hV).ne']]
        · have hk' : (k : ℝ) ≤ 0 := le_of_not_ge hk
          rw [show α * (w j : ℝ) / Real.sqrt V =
              -(Real.pi * (k : ℝ) * (w j : ℝ) / (q : ℝ)) by
                dsimp [α]
                rw [abs_of_nonpos hk']
                field_simp [hqReal.ne', (Real.sqrt_pos.2 hV).ne'],
            Real.cos_neg]
      _ ≤ Real.exp (-α ^ 2) := hres
  unfold sparseCyclicCosineModeInt
  simp_rw [hfactor]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact mul_le_mul_of_nonneg_left hresProduct (sq_nonneg _)

/-- The Gaussian Fourier modes beyond frequency three admit a much smaller
tail than the generic nonzero-mode allowance. -/
theorem real_exp_neg_sq_nat_add_four_tsum_le {c : ℝ} (hc : 0 < c) :
    (∑' n : ℕ, Real.exp (-c * ((n + 4 : ℕ) : ℝ) ^ 2)) ≤
      Real.exp (-16 * c) / (1 - Real.exp (-9 * c)) := by
  let ρ : ℝ := Real.exp (-9 * c)
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom : Summable (fun n : ℕ => Real.exp (-16 * c) * ρ ^ n) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  have hterm (n : ℕ) :
    Real.exp (-c * ((n + 4 : ℕ) : ℝ) ^ 2) ≤
        Real.exp (-16 * c) * ρ ^ n := by
    rw [← Real.exp_nat_mul]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    cases n with
    | zero =>
        norm_num
        rw [mul_comm]
    | succ n =>
        push_cast
        nlinarith [sq_nonneg (n : ℝ)]
  have hsum : Summable
      (fun n : ℕ => Real.exp (-c * ((n + 4 : ℕ) : ℝ) ^ 2)) :=
    hgeom.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hterm
  calc
    (∑' n : ℕ, Real.exp (-c * ((n + 4 : ℕ) : ℝ) ^ 2)) ≤
        ∑' n : ℕ, Real.exp (-16 * c) * ρ ^ n :=
      hsum.tsum_le_tsum hterm hgeom
    _ = Real.exp (-16 * c) * (1 - ρ)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]
    _ = Real.exp (-16 * c) / (1 - Real.exp (-9 * c)) := by
      rfl

/-- Abstract three-mode truncation for an even nonnegative Fourier mode.
Only modes one through three use the supplied sharp bounds; every later mode
is absorbed by the frequency-four Gaussian tail. -/
theorem gaussianWeighted_evenMode_tsum_le_threeMode
    {c : ℝ} (hc : 0 < c) (mode low : ℤ → ℝ)
    (heven : mode.Even)
    (hmode0 : mode 0 ≤ 1)
    (hmode_nonneg : ∀ k, 0 ≤ mode k)
    (hmode_le_one : ∀ k, mode k ≤ 1)
    (hlow : ∀ n ∈ Finset.range 3, mode ((n + 1 : ℕ) : ℤ) ≤
      low ((n + 1 : ℕ) : ℤ)) :
    (∑' k : ℤ, Real.exp (-c * (k : ℝ) ^ 2) * mode k) ≤
      1 + 2 * (∑ n ∈ Finset.range 3,
        Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2) *
          low ((n + 1 : ℕ) : ℤ)) +
        2 * (Real.exp (-16 * c) / (1 - Real.exp (-9 * c))) := by
  let f : ℤ → ℝ := fun k => Real.exp (-c * (k : ℝ) ^ 2) * mode k
  have hbase : Summable (fun k : ℤ => Real.exp (-c * (k : ℝ) ^ 2)) :=
    summable_real_integer_exp_neg_sq hc
  have hf : Summable f := by
    apply hbase.of_norm_bounded
    intro k
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (hmode_nonneg k)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (hmode_le_one k)
  have hfeven : f.Even := by
    intro k
    dsimp [f]
    rw [heven k]
    congr 2
    norm_num
  have hpnat :
      (∑' n : ℕ+, f (n : ℤ)) =
        ∑' n : ℕ, f ((n + 1 : ℕ) : ℤ) := by
    simpa using (tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ => f (n : ℤ)))
  have hgn : Summable (fun n : ℕ => f ((n + 1 : ℕ) : ℤ)) := by
    exact hf.comp_injective (fun a b h => by
      have hab : a + 1 = b + 1 := by exact_mod_cast h
      omega)
  have hsplit :
      (∑' n : ℕ, f ((n + 1 : ℕ) : ℤ)) =
        (∑ n ∈ Finset.range 3, f ((n + 1 : ℕ) : ℤ)) +
          ∑' n : ℕ, f ((n + 4 : ℕ) : ℤ) := by
    rw [← hgn.sum_add_tsum_nat_add 3]
  have hfinite :
      (∑ n ∈ Finset.range 3, f ((n + 1 : ℕ) : ℤ)) ≤
        ∑ n ∈ Finset.range 3,
          Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2) *
            low ((n + 1 : ℕ) : ℤ) := by
    apply Finset.sum_le_sum
    intro n hn
    dsimp [f]
    exact mul_le_mul_of_nonneg_left (hlow n hn) (Real.exp_nonneg _)
  have htailTerm (n : ℕ) :
      f ((n + 4 : ℕ) : ℤ) ≤
        Real.exp (-c * ((n + 4 : ℕ) : ℝ) ^ 2) := by
    dsimp [f]
    exact mul_le_of_le_one_right (Real.exp_pos _).le
      (hmode_le_one ((n + 4 : ℕ) : ℤ))
  have htailSummable : Summable
      (fun n : ℕ => f ((n + 4 : ℕ) : ℤ)) := by
    have hgauss : Summable
        (fun n : ℕ => Real.exp (-c * ((n + 4 : ℕ) : ℝ) ^ 2)) := by
      exact (summable_real_integer_exp_neg_sq hc).comp_injective
        (fun a b h => by
          have hab : a + 4 = b + 4 := by exact_mod_cast h
          omega)
    exact hgauss.of_nonneg_of_le
      (fun n => mul_nonneg (Real.exp_nonneg _) (hmode_nonneg _)) htailTerm
  have htail :
      (∑' n : ℕ, f ((n + 4 : ℕ) : ℤ)) ≤
        Real.exp (-16 * c) / (1 - Real.exp (-9 * c)) := by
    calc
      _ ≤ ∑' n : ℕ, Real.exp (-c * ((n + 4 : ℕ) : ℝ) ^ 2) :=
        htailSummable.tsum_le_tsum htailTerm
          ((summable_real_integer_exp_neg_sq hc).comp_injective
            (fun a b h => by
              have hab : a + 4 = b + 4 := by exact_mod_cast h
              omega))
      _ ≤ _ := real_exp_neg_sq_nat_add_four_tsum_le hc
  have hsumParts :
      (∑ n ∈ Finset.range 3, f ((n + 1 : ℕ) : ℤ)) +
          ∑' n : ℕ, f ((n + 4 : ℕ) : ℤ) ≤
        (∑ n ∈ Finset.range 3,
          Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2) *
            low ((n + 1 : ℕ) : ℤ)) +
          Real.exp (-16 * c) / (1 - Real.exp (-9 * c)) :=
    add_le_add hfinite htail
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat hfeven hf, hpnat, hsplit]
  dsimp [f]
  norm_num only [Int.cast_zero, zero_pow, Real.exp_zero, one_mul,
    Nat.cast_add, Nat.cast_one, Int.cast_natCast, two_smul]
  have hzero : Real.exp (-c * 0) * mode 0 ≤ 1 := by
    simpa using hmode0
  have hdouble := mul_le_mul_of_nonneg_left hsumParts (by norm_num : (0 : ℝ) ≤ 2)
  norm_num only [Nat.cast_add, Nat.cast_one, Int.cast_natCast] at hdouble
  nlinarith

/-- Wrapped sparse-row expectation with the selected coordinate coupled to
the first three Fourier modes.  The tail starts at frequency four. -/
theorem sparseRow_wrappedGaussianKernel_le_retained_threeMode
    {q d : ℕ} (w : Fin d → ℤ) (i : Fin d) (V s : ℝ)
    (hq : 0 < q) (hs : 0 < s) (hV : 0 < V)
    (hresidual : ∑ j ∈ Finset.univ.erase i, (w j : ℝ) ^ 2 = V)
    (hfrequency : ∀ n ∈ Finset.range 3,
      Real.pi * |(((n + 1 : ℕ) : ℤ) : ℝ)| * Real.sqrt V / (q : ℝ) <
        Real.pi / 2) :
    (∫ row, wrappedGaussianKernel q s (∑ j, row j * w j)
        ∂(sparseRademacherRow d).toMeasure) ≤
      1 / Real.sqrt (s * (q : ℝ) ^ 2 / Real.pi) *
        (1 + 2 * (∑ n ∈ Finset.range 3,
          Real.exp
              (-(Real.pi ^ 2 / (s * (q : ℝ) ^ 2)) *
                ((n + 1 : ℕ) : ℝ) ^ 2) *
            (Real.cos
                (Real.pi * ((n + 1 : ℕ) : ℝ) * (w i : ℝ) / (q : ℝ)) ^ 2 *
              Real.exp
                (-((Real.pi * |(((n + 1 : ℕ) : ℤ) : ℝ)| * Real.sqrt V /
                  (q : ℝ)) ^ 2)))) +
          2 * (Real.exp
              (-16 * (Real.pi ^ 2 / (s * (q : ℝ) ^ 2))) /
            (1 - Real.exp
              (-9 * (Real.pi ^ 2 / (s * (q : ℝ) ^ 2)))))) := by
  let c : ℝ := Real.pi ^ 2 / (s * (q : ℝ) ^ 2)
  let mode : ℤ → ℝ := sparseCyclicCosineModeInt q w
  let low : ℤ → ℝ := fun k =>
    Real.cos (Real.pi * (k : ℝ) * (w i : ℝ) / (q : ℝ)) ^ 2 *
      Real.exp (-((Real.pi * |(k : ℝ)| * Real.sqrt V / (q : ℝ)) ^ 2))
  have hqReal : 0 < (q : ℝ) := by exact_mod_cast hq
  have hc : 0 < c := by dsimp [c]; positivity
  have hmodeEven : mode.Even := by
    intro k
    unfold mode sparseCyclicCosineModeInt
    apply Finset.prod_congr rfl
    intro j hj
    congr 2
    push_cast
    rw [show (2 * Real.pi * (-(k : ℝ)) / (q : ℝ)) * (w j : ℝ) =
        -((2 * Real.pi * (k : ℝ) / (q : ℝ)) * (w j : ℝ)) by ring,
      Real.cos_neg]
  have hmode0 : mode 0 ≤ 1 :=
    sparseCyclicCosineModeInt_le_one q w 0
  have hmode_nonneg : ∀ k, 0 ≤ mode k :=
    sparseCyclicCosineModeInt_nonneg q w
  have hmode_le_one : ∀ k, mode k ≤ 1 :=
    sparseCyclicCosineModeInt_le_one q w
  have hlow : ∀ n ∈ Finset.range 3,
      mode ((n + 1 : ℕ) : ℤ) ≤ low ((n + 1 : ℕ) : ℤ) := by
    intro n hn
    exact sparseCyclicCosineModeInt_le_retained_residualExp
      w i ((n + 1 : ℕ) : ℤ) V hq hV hresidual (hfrequency n hn)
  have hseries := gaussianWeighted_evenMode_tsum_le_threeMode
    hc mode low hmodeEven hmode0 hmode_nonneg hmode_le_one hlow
  rw [sparseRow_wrappedGaussianKernel_integral_eq w hq hs]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hweight (k : ℤ) :
      Real.exp
          (-Real.pi / (s * (q : ℝ) ^ 2 / Real.pi) * (k : ℝ) ^ 2) =
        Real.exp (-c * (k : ℝ) ^ 2) := by
    congr 1
    dsimp [c]
    field_simp [hqReal.ne', hs.ne']
  simp_rw [hweight]
  simpa [c, mode, low] using hseries

private theorem gaussian_cos_sq_mul_cos_sq_integrable (A B : ℝ) :
    Integrable (fun G : ℝ => Real.cos (A * G) ^ 2 * Real.cos (B * G) ^ 2)
      (gaussianReal 0 1) := by
  refine Integrable.of_bound (by fun_prop) 1 ?_
  filter_upwards [] with G
  rw [Real.norm_eq_abs, abs_mul, abs_sq, abs_sq]
  have hA : |Real.cos (A * G)| ≤ 1 := Real.abs_cos_le_one _
  have hB : |Real.cos (B * G)| ≤ 1 := Real.abs_cos_le_one _
  have hA2 : |Real.cos (A * G)| ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ (abs_nonneg _) hA 2
  have hB2 : |Real.cos (B * G)| ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ (abs_nonneg _) hB 2
  have hA2' : Real.cos (A * G) ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact hA2
  have hB2' : Real.cos (B * G) ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact hB2
  calc
    Real.cos (A * G) ^ 2 * Real.cos (B * G) ^ 2 ≤
        1 * Real.cos (B * G) ^ 2 :=
      mul_le_mul_of_nonneg_right hA2' (sq_nonneg _)
    _ ≤ 1 := by simpa using hB2'

/-- Exact two-frequency endpoint used when a residual coordinate carries all
of the residual Holder mass. -/
theorem gaussian_cos_sq_mul_cos_sq_integral (A B : ℝ) :
    (∫ G : ℝ, Real.cos (A * G) ^ 2 * Real.cos (B * G) ^ 2
        ∂(gaussianReal 0 1)) =
      (1 / 4 : ℝ) *
        (1 + Real.exp (-(2 * A) ^ 2 / 2) +
          Real.exp (-(2 * B) ^ 2 / 2) +
          (1 / 2 : ℝ) *
            (Real.exp (-(2 * A + 2 * B) ^ 2 / 2) +
              Real.exp (-(2 * A - 2 * B) ^ 2 / 2))) := by
  have hA := gaussian_cos_integrable (2 * A)
  have hB := gaussian_cos_integrable (2 * B)
  have hplus := gaussian_cos_integrable (2 * A + 2 * B)
  have hminus := gaussian_cos_integrable (2 * A - 2 * B)
  have hpoint (G : ℝ) :
      Real.cos (A * G) ^ 2 * Real.cos (B * G) ^ 2 =
        (1 / 4 : ℝ) *
          (1 + Real.cos ((2 * A) * G) + Real.cos ((2 * B) * G) +
            (1 / 2 : ℝ) *
              (Real.cos ((2 * A + 2 * B) * G) +
                Real.cos ((2 * A - 2 * B) * G))) := by
    rw [Real.cos_sq, Real.cos_sq]
    have hprod := Real.two_mul_cos_mul_cos ((2 * A) * G) ((2 * B) * G)
    rw [show (2 * A) * G + (2 * B) * G = (2 * A + 2 * B) * G by ring,
      show (2 * A) * G - (2 * B) * G = (2 * A - 2 * B) * G by ring] at hprod
    rw [show 2 * (A * G) = (2 * A) * G by ring,
      show 2 * (B * G) = (2 * B) * G by ring]
    linear_combination hprod / 8
  calc
    (∫ G : ℝ, Real.cos (A * G) ^ 2 * Real.cos (B * G) ^ 2
        ∂(gaussianReal 0 1)) =
      ∫ G : ℝ, (1 / 4 : ℝ) *
          (1 + Real.cos ((2 * A) * G) + Real.cos ((2 * B) * G) +
            (1 / 2 : ℝ) *
              (Real.cos ((2 * A + 2 * B) * G) +
                Real.cos ((2 * A - 2 * B) * G)))
        ∂(gaussianReal 0 1) := by
      apply integral_congr_ae
      filter_upwards [] with G
      exact hpoint G
    _ = (1 / 4 : ℝ) *
        (1 + (∫ G : ℝ, Real.cos ((2 * A) * G) ∂(gaussianReal 0 1)) +
          (∫ G : ℝ, Real.cos ((2 * B) * G) ∂(gaussianReal 0 1)) +
          (1 / 2 : ℝ) *
            ((∫ G : ℝ, Real.cos ((2 * A + 2 * B) * G)
                ∂(gaussianReal 0 1)) +
              (∫ G : ℝ, Real.cos ((2 * A - 2 * B) * G)
                ∂(gaussianReal 0 1)))) := by
      rw [integral_const_mul]
      have hone : Integrable (fun _ : ℝ => (1 : ℝ)) (gaussianReal 0 1) :=
        integrable_const 1
      have hleft : Integrable (fun G : ℝ =>
          1 + Real.cos ((2 * A) * G) + Real.cos ((2 * B) * G))
          (gaussianReal 0 1) := (hone.add hA).add hB
      have hright : Integrable (fun G : ℝ =>
          (1 / 2 : ℝ) *
            (Real.cos ((2 * A + 2 * B) * G) +
              Real.cos ((2 * A - 2 * B) * G)))
          (gaussianReal 0 1) := (hplus.add hminus).const_mul _
      rw [integral_add hleft hright]
      have hleft_eq :
          (∫ G : ℝ, 1 + Real.cos ((2 * A) * G) +
              Real.cos ((2 * B) * G) ∂(gaussianReal 0 1)) =
            1 + (∫ G : ℝ, Real.cos ((2 * A) * G)
                ∂(gaussianReal 0 1)) +
              (∫ G : ℝ, Real.cos ((2 * B) * G)
                ∂(gaussianReal 0 1)) := by
        calc
          (∫ G : ℝ, 1 + Real.cos ((2 * A) * G) +
              Real.cos ((2 * B) * G) ∂(gaussianReal 0 1)) =
              (∫ G : ℝ, 1 + Real.cos ((2 * A) * G)
                ∂(gaussianReal 0 1)) +
              (∫ G : ℝ, Real.cos ((2 * B) * G)
                ∂(gaussianReal 0 1)) := by
            simpa only [Pi.add_apply] using integral_add (hone.add hA) hB
          _ = ((∫ _G : ℝ, (1 : ℝ) ∂(gaussianReal 0 1)) +
                (∫ G : ℝ, Real.cos ((2 * A) * G)
                  ∂(gaussianReal 0 1))) +
              (∫ G : ℝ, Real.cos ((2 * B) * G)
                ∂(gaussianReal 0 1)) := by
            rw [integral_add hone hA]
          _ = _ := by rw [integral_const, probReal_univ]; simp
      have hright_eq :
          (∫ G : ℝ, (1 / 2 : ℝ) *
              (Real.cos ((2 * A + 2 * B) * G) +
                Real.cos ((2 * A - 2 * B) * G))
              ∂(gaussianReal 0 1)) =
            (1 / 2 : ℝ) *
              ((∫ G : ℝ, Real.cos ((2 * A + 2 * B) * G)
                  ∂(gaussianReal 0 1)) +
                (∫ G : ℝ, Real.cos ((2 * A - 2 * B) * G)
                  ∂(gaussianReal 0 1))) := by
        rw [integral_const_mul, integral_add hplus hminus]
      rw [hleft_eq, hright_eq]
    _ = _ := by
      rw [gaussian_cosine_charFun, gaussian_cosine_charFun,
        gaussian_cosine_charFun, gaussian_cosine_charFun]

private theorem ennreal_prod_rpow_eq_rpow_sum
    {ι : Type*} (D : ℝ≥0∞) (weight : ι → ℝ) (S : Finset ι)
    (hweight : ∀ i ∈ S, 0 ≤ weight i) :
    ∏ i ∈ S, D ^ (weight i) = D ^ (∑ i ∈ S, weight i) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | @insert i S hi ih =>
      have hi0 : 0 ≤ weight i := hweight i (by simp)
      have hS : ∀ j ∈ S, 0 ≤ weight j := by
        intro j hj
        exact hweight j (by simp [hj])
      have hsum0 : 0 ≤ ∑ j ∈ S, weight j := Finset.sum_nonneg hS
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih hS,
        ENNReal.rpow_add_of_nonneg _ _ hi0 hsum0]

/-- Generalized Holder on only the residual coordinates, with one coordinate
factor retained inside every norm.  The residual weights are normalized by
their exact mass `1-r`; no dimension or coordinate count enters the bound. -/
theorem retainedGaussianCosineHolder_on_finset
    {d : ℕ} (a : Fin d → ℝ) (s r : ℝ) (S : Finset (Fin d))
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hS : ∑ i ∈ S, a i ^ 2 = 1 - r)
    (hapos : ∀ i ∈ S, 0 < a i ^ 2) :
    ∫⁻ G : ℝ,
        retainedGaussianCosineFactor s r G *
          ∏ i ∈ S,
            ENNReal.ofReal
              (Real.cos (Real.sqrt (s / 2) * G * |a i|) ^ 2)
          ∂(gaussianReal 0 1) ≤
      ∏ i ∈ S,
        retainedGaussianCosineMoment s r (a i ^ 2 / (1 - r)) ^
          (a i ^ 2 / (1 - r)) := by
  let weight : Fin d → ℝ := fun i => a i ^ 2 / (1 - r)
  let Y : Fin d → ℝ → ℝ≥0∞ := fun i G =>
    retainedGaussianCosineFactor s r G *
      gaussianCosineHolderFactor (s * (1 - r)) (weight i) G
  have hone : 0 < 1 - r := sub_pos.mpr hr1
  have hweight_nonneg : ∀ i ∈ S, 0 ≤ weight i := by
    intro i hi
    exact div_nonneg (sq_nonneg _) hone.le
  have hweight_sum : ∑ i ∈ S, weight i = 1 := by
    dsimp [weight]
    rw [← Finset.sum_div, hS]
    exact div_self hone.ne'
  have hY : ∀ i ∈ S, AEMeasurable (Y i) (gaussianReal 0 1) := by
    intro i hi
    dsimp [Y, retainedGaussianCosineFactor,
      gaussianCosineHolderFactor]
    fun_prop
  have hholder := ENNReal.lintegral_prod_norm_pow_le
    (μ := gaussianReal 0 1) S (fun i hi => hY i hi)
      hweight_sum hweight_nonneg
  have hfactor (i : Fin d) (hi : i ∈ S) (G : ℝ) :
      gaussianCosineHolderFactor (s * (1 - r)) (weight i) G ^
          (weight i) =
        ENNReal.ofReal
          (Real.cos (Real.sqrt (s / 2) * G * |a i|) ^ 2) := by
    have hxi : 0 < weight i := div_pos (hapos i hi) hone
    have habs : 0 ≤ |a i| := abs_nonneg _
    have hsquare : |a i| ^ 2 / (1 - r) = weight i := by
      dsimp [weight]
      rw [sq_abs]
    have h := gaussianCosineHolderFactor_rpow_eq_cos_sq
      (s := s * (1 - r)) (x := weight i)
      (a := |a i| / Real.sqrt (1 - r)) (G := G) hxi
      (by positivity)
      (by
        rw [div_pow, Real.sq_sqrt hone.le]
        simpa [sq_abs, weight])
    rw [h]
    congr 2
    have hsqrt :
        Real.sqrt ((s * (1 - r)) / 2) *
              (|a i| / Real.sqrt (1 - r)) =
            Real.sqrt (s / 2) * |a i| := by
      by_cases hs : 0 ≤ s
      · rw [show (s * (1 - r)) / 2 = (s / 2) * (1 - r) by ring,
          Real.sqrt_mul (by positivity : 0 ≤ s / 2)]
        field_simp [ne_of_gt (Real.sqrt_pos.2 hone)]
      · have hsneg : s / 2 < 0 := by linarith
        have hmulneg : s * (1 - r) < 0 :=
          mul_neg_of_neg_of_pos (lt_of_not_ge hs) hone
        have hsprodneg : (s * (1 - r)) / 2 < 0 := by linarith
        rw [Real.sqrt_eq_zero_of_nonpos hsneg.le,
          Real.sqrt_eq_zero_of_nonpos hsprodneg.le]
        simp
    congr 1
    calc
      Real.sqrt ((s * (1 - r)) / 2) * G *
            (|a i| / Real.sqrt (1 - r)) =
          (Real.sqrt ((s * (1 - r)) / 2) *
            (|a i| / Real.sqrt (1 - r))) * G := by ring
      _ = (Real.sqrt (s / 2) * |a i|) * G := by rw [hsqrt]
      _ = Real.sqrt (s / 2) * G * |a i| := by ring
  have hcollapse (G : ℝ) :
      ∏ i ∈ S,
          retainedGaussianCosineFactor s r G ^ (weight i) =
        retainedGaussianCosineFactor s r G := by
    have hprod : ∏ i ∈ S,
        retainedGaussianCosineFactor s r G ^ (weight i) =
        retainedGaussianCosineFactor s r G ^
          (∑ i ∈ S, weight i) :=
      ennreal_prod_rpow_eq_rpow_sum
        (retainedGaussianCosineFactor s r G) weight S hweight_nonneg
    rw [hprod, hweight_sum, ENNReal.rpow_one]
  have hpoint (G : ℝ) :
      ∏ i ∈ S, Y i G ^ (weight i) =
        retainedGaussianCosineFactor s r G *
          ∏ i ∈ S,
            ENNReal.ofReal
              (Real.cos (Real.sqrt (s / 2) * G * |a i|) ^ 2) := by
    have hmul (i : Fin d) (hi : i ∈ S) :
        (Y i G) ^ (weight i) =
          retainedGaussianCosineFactor s r G ^ (weight i) *
            gaussianCosineHolderFactor (s * (1 - r)) (weight i) G ^
              (weight i) := by
      dsimp [Y]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (hweight_nonneg i hi)]
    calc
      ∏ i ∈ S, Y i G ^ (weight i) =
          ∏ i ∈ S,
            (retainedGaussianCosineFactor s r G ^ (weight i) *
              gaussianCosineHolderFactor (s * (1 - r)) (weight i) G ^
                (weight i)) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact hmul i hi
      _ = retainedGaussianCosineFactor s r G *
          ∏ i ∈ S,
            gaussianCosineHolderFactor (s * (1 - r)) (weight i) G ^
              (weight i) := by
        rw [Finset.prod_mul_distrib, hcollapse]
      _ = retainedGaussianCosineFactor s r G *
          ∏ i ∈ S,
            ENNReal.ofReal
              (Real.cos (Real.sqrt (s / 2) * G * |a i|) ^ 2) := by
        congr 1
        apply Finset.prod_congr rfl
        intro i hi
        exact hfactor i hi G
  calc
    ∫⁻ G : ℝ,
        retainedGaussianCosineFactor s r G *
          ∏ i ∈ S,
            ENNReal.ofReal
              (Real.cos (Real.sqrt (s / 2) * G * |a i|) ^ 2)
          ∂(gaussianReal 0 1) =
      ∫⁻ G : ℝ, ∏ i ∈ S, Y i G ^ (weight i)
          ∂(gaussianReal 0 1) := by
        apply lintegral_congr_ae
        filter_upwards [] with G
        exact (hpoint G).symm
    _ ≤ ∏ i ∈ S,
        (∫⁻ G : ℝ, Y i G ∂(gaussianReal 0 1)) ^ (weight i) :=
      hholder
    _ = ∏ i ∈ S,
        retainedGaussianCosineMoment s r (a i ^ 2 / (1 - r)) ^
          (a i ^ 2 / (1 - r)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rfl

/-- The row-level retained-coordinate reduction.  Unlike
`sparseScalarReduction`, the distinguished coordinate is not separated from
the remainder. -/
theorem sparseRow_retained_nonmodulated_le
    {d : ℕ} (a : Fin d → ℝ) (i : Fin d) (s r : ℝ)
    (S : Finset (Fin d))
    (hs : 0 ≤ s) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ∑ j, a j ^ 2 = 1) (hir : a i ^ 2 = r)
    (hi_nonzero : a i ≠ 0)
    (hS : ∀ j, j ∈ S ↔ j ≠ i ∧ a j ≠ 0) :
    ENNReal.ofReal
        (∫ row, Real.exp (-s * (realRowDot row a) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) ≤
      ∏ j ∈ S,
        retainedGaussianCosineMoment s r
            (a j ^ 2 / (1 - r)) ^
          (a j ^ 2 / (1 - r)) := by
  classical
  let b : Fin d → ℝ := fun j => |a j|
  have hsumS : ∑ j ∈ S, b j ^ 2 = 1 - r := by
    have herase : ∑ j ∈ Finset.univ.erase i, a j ^ 2 = 1 - r := by
      have hsplit := Finset.sum_erase_add (s := Finset.univ)
        (f := fun j => a j ^ 2) (Finset.mem_univ i)
      rw [ha, hir] at hsplit
      linarith
    calc
      ∑ j ∈ S, b j ^ 2 = ∑ j ∈ S, a j ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [b]
      _ = ∑ j ∈ Finset.univ.erase i, a j ^ 2 := by
        apply Finset.sum_subset
        · intro j hj
          exact Finset.mem_erase.2 ⟨(hS j).1 hj |>.1, Finset.mem_univ j⟩
        · intro j hj hnot
          have hji : j ≠ i := (Finset.mem_erase.1 hj).1
          have haj : a j = 0 := by
            by_contra hne
            exact hnot ((hS j).2 ⟨hji, hne⟩)
          simp [haj]
      _ = 1 - r := herase
  have hapos : ∀ j ∈ S, 0 < b j ^ 2 := by
    intro j hj
    have hne : a j ≠ 0 := (hS j).1 hj |>.2
    dsimp [b]
    positivity
  have hsqrt : Real.sqrt (2 * s) = 2 * Real.sqrt (s / 2) := by
    calc
      Real.sqrt (2 * s) = Real.sqrt (4 * (s / 2)) := by congr 1 <;> ring
      _ = Real.sqrt 4 * Real.sqrt (s / 2) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      _ = 2 * Real.sqrt (s / 2) := by
        have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4),
            Real.sqrt_nonneg (4 : ℝ)]
        rw [hsqrt4]
  have hhalf (j : Fin d) (G : ℝ) :
      (1 + Real.cos (Real.sqrt (2 * s) * G * a j)) / 2 =
        Real.cos (Real.sqrt (s / 2) * G * b j) ^ 2 := by
    rw [hsqrt, Real.cos_sq]
    by_cases hj : 0 ≤ a j
    · simp only [b, abs_of_nonneg hj]
      congr 2
      ring
    · have hj' : a j ≤ 0 := le_of_not_ge hj
      simp only [b, abs_of_nonpos hj']
      rw [show 2 * (Real.sqrt (s / 2) * G * -a j) =
          -(2 * Real.sqrt (s / 2) * G * a j) by ring,
        Real.cos_neg]
      congr 2
      ring
  let fG : ℝ → ℝ := fun G =>
    ∏ j, (1 + Real.cos (Real.sqrt (2 * s) * G * a j)) / 2
  have hf_meas : Measurable fG := by dsimp [fG]; fun_prop
  have hf_integrable : Integrable fG (gaussianReal 0 1) := by
    refine Integrable.of_bound hf_meas.aestronglyMeasurable 1 ?_
    filter_upwards [] with G
    have hnonneg : 0 ≤ fG G := by
      dsimp [fG]
      apply Finset.prod_nonneg
      intro j hj
      linarith [Real.neg_one_le_cos (Real.sqrt (2 * s) * G * a j)]
    have hle : fG G ≤ 1 := by
      dsimp [fG]
      apply Finset.prod_le_one
      · intro j hj
        linarith [Real.neg_one_le_cos (Real.sqrt (2 * s) * G * a j)]
      · intro j hj
        linarith [Real.cos_le_one (Real.sqrt (2 * s) * G * a j)]
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hofreal :
      ENNReal.ofReal (∫ G, fG G ∂(gaussianReal 0 1)) =
        ∫⁻ G, ENNReal.ofReal (fG G) ∂(gaussianReal 0 1) :=
    ofReal_integral_eq_lintegral_ofReal hf_integrable
      (Filter.Eventually.of_forall fun G => by
        dsimp [fG]
        apply Finset.prod_nonneg
        intro j hj
        linarith [Real.neg_one_le_cos (Real.sqrt (2 * s) * G * a j)])
  have hpoint (G : ℝ) :
      ENNReal.ofReal (fG G) =
        retainedGaussianCosineFactor s r G *
          ∏ j ∈ S, ENNReal.ofReal
            (Real.cos (Real.sqrt (s / 2) * G * b j) ^ 2) := by
    have hprod : fG G =
        ∏ j, Real.cos (Real.sqrt (s / 2) * G * b j) ^ 2 := by
      dsimp [fG]
      apply Finset.prod_congr rfl
      intro j hj
      exact hhalf j G
    rw [hprod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ENNReal.ofReal_mul (sq_nonneg _)]
    have hiabs : b i = Real.sqrt r := by
      have hsquare : b i ^ 2 = r := by simpa [b] using hir
      apply (sq_eq_sq₀ (by positivity : 0 ≤ b i)
        (Real.sqrt_nonneg r)).mp
      rw [hsquare, Real.sq_sqrt hr0]
    rw [hiabs]
    change ENNReal.ofReal _ * ENNReal.ofReal
        (∏ j ∈ Finset.univ.erase i,
          Real.cos (Real.sqrt (s / 2) * G * b j) ^ 2) = _
    rw [ENNReal.ofReal_prod_of_nonneg]
    · congr 1
      symm
      apply Finset.prod_subset
      · intro j hj
        exact Finset.mem_erase.2 ⟨(hS j).1 hj |>.1, Finset.mem_univ j⟩
      · intro j hj hnot
        have hji : j ≠ i := (Finset.mem_erase.1 hj).1
        have haj : a j = 0 := by
          by_contra hne
          exact hnot ((hS j).2 ⟨hji, hne⟩)
        simp [b, haj]
    · intro j hj
      positivity
  have hfour := sparseRow_negativeLaplace_fourier d s a hs
  calc
    ENNReal.ofReal
        (∫ row, Real.exp (-s * (realRowDot row a) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) =
        ENNReal.ofReal (∫ G, fG G ∂(gaussianReal 0 1)) := by
      rw [hfour]
    _ = ∫⁻ G, ENNReal.ofReal (fG G) ∂(gaussianReal 0 1) := hofreal
    _ = ∫⁻ G,
        retainedGaussianCosineFactor s r G *
          ∏ j ∈ S, ENNReal.ofReal
            (Real.cos (Real.sqrt (s / 2) * G * b j) ^ 2)
          ∂(gaussianReal 0 1) := by
      apply lintegral_congr_ae
      filter_upwards [] with G
      exact hpoint G
    _ ≤ ∏ j ∈ S,
        retainedGaussianCosineMoment s r (b j ^ 2 / (1 - r)) ^
          (b j ^ 2 / (1 - r)) :=
      by simpa [b] using
        retainedGaussianCosineHolder_on_finset b s r S hr0 hr1 hsumS hapos
    _ = ∏ j ∈ S,
        retainedGaussianCosineMoment s r (a j ^ 2 / (1 - r)) ^
          (a j ^ 2 / (1 - r)) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [b]

/-- A uniform bound for every coupled residual Holder moment tensorizes back
to the same bound because the normalized residual weights sum to one. -/
theorem sparseRow_retained_nonmodulated_le_of_moment_cap
    {d : ℕ} (a : Fin d → ℝ) (i : Fin d) (s r C : ℝ)
    (S : Finset (Fin d))
    (hs : 0 ≤ s) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ∑ j, a j ^ 2 = 1) (hir : a i ^ 2 = r)
    (hi_nonzero : a i ≠ 0)
    (hS : ∀ j, j ∈ S ↔ j ≠ i ∧ a j ≠ 0)
    (hC : 0 ≤ C)
    (hmoment : ∀ j, j ∈ S →
      retainedGaussianCosineMoment s r (a j ^ 2 / (1 - r)) ≤
        ENNReal.ofReal C) :
    ENNReal.ofReal
        (∫ row, Real.exp (-s * (realRowDot row a) ^ 2)
          ∂(sparseRademacherRow d).toMeasure) ≤
      ENNReal.ofReal C := by
  have hreduce := sparseRow_retained_nonmodulated_le
    a i s r S hs hr0 hr1 ha hir hi_nonzero hS
  refine hreduce.trans ?_
  have hone : 0 < 1 - r := sub_pos.mpr hr1
  have hweight0 : ∀ j ∈ S, 0 ≤ a j ^ 2 / (1 - r) := by
    intro j hj
    exact div_nonneg (sq_nonneg _) hone.le
  have hsumS : ∑ j ∈ S, a j ^ 2 = 1 - r := by
    have herase : ∑ j ∈ Finset.univ.erase i, a j ^ 2 = 1 - r := by
      have hsplit := Finset.sum_erase_add (s := Finset.univ)
        (f := fun j => a j ^ 2) (Finset.mem_univ i)
      rw [ha, hir] at hsplit
      linarith
    calc
      ∑ j ∈ S, a j ^ 2 = ∑ j ∈ Finset.univ.erase i, a j ^ 2 := by
        apply Finset.sum_subset
        · intro j hj
          exact Finset.mem_erase.2 ⟨(hS j).1 hj |>.1, Finset.mem_univ j⟩
        · intro j hj hnot
          have hji : j ≠ i := (Finset.mem_erase.1 hj).1
          have haj : a j = 0 := by
            by_contra hne
            exact hnot ((hS j).2 ⟨hji, hne⟩)
          simp [haj]
      _ = 1 - r := herase
  have hweightSum : ∑ j ∈ S, a j ^ 2 / (1 - r) = 1 := by
    rw [← Finset.sum_div, hsumS]
    exact div_self hone.ne'
  calc
    (∏ j ∈ S,
        retainedGaussianCosineMoment s r (a j ^ 2 / (1 - r)) ^
          (a j ^ 2 / (1 - r))) ≤
      ∏ j ∈ S, ENNReal.ofReal C ^ (a j ^ 2 / (1 - r)) := by
        apply Finset.prod_le_prod
        · intro j hj
          positivity
        · intro j hj
          exact ENNReal.rpow_le_rpow (hmoment j hj) (hweight0 j hj)
    _ = ENNReal.ofReal
        (∏ j ∈ S, C ^ (a j ^ 2 / (1 - r))) := by
      rw [ENNReal.ofReal_prod_of_nonneg]
      · apply Finset.prod_congr rfl
        intro j hj
        rw [ENNReal.ofReal_rpow_of_nonneg hC (hweight0 j hj)]
      · intro j hj
        positivity
    _ = ENNReal.ofReal C := by
      congr 1
      rw [← Real.rpow_sum_of_nonneg hC hweight0, hweightSum,
        Real.rpow_one]

end CertifiedJL
