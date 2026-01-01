/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpGaussianHalfMoment
import CertifiedJL.Analysis.Gaussian.GaussianEvenMomentDomination
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Even-moment comparison for the quadratic exponential

This module begins the comparison half of U3c.  The mixed-moment hypothesis
in the paper first yields domination of every even moment of the hybrid sum
by the corresponding variance-one-half Gaussian moment.  Here that collapsed
consequence is packaged explicitly and lifted term by term to every finite
Taylor partial sum.  Passing these nonnegative partial sums to the exponential
is the next theorem in this layer.
-/

namespace CertifiedJL

open MeasureTheory
open scoped Nat

/-- The raw `2ℓ`-th moment of the centered Gaussian with variance one half. -/
noncomputable def gaussianHalfEvenMoment (ell : ℕ) : ℝ :=
  (Nat.doubleFactorial (2 * ell - 1) : ℝ) / (2 : ℝ) ^ ell

/-- The parametric centered-Gaussian moment agrees with the established
closed variance-one-half formula. -/
theorem centeredGaussianEvenMoment_half (ell : ℕ) :
    centeredGaussianEvenMoment (2 : NNReal)⁻¹ ell = gaussianHalfEvenMoment ell := by
  have h := integral_gaussianHalf_abs_evenPow_mul_exp_sq
    ell (lambda := 0) (by norm_num)
  norm_num [gaussianHalfTiltedEvenMomentMajorant] at h
  simpa [centeredGaussianEvenMoment, gaussianHalfEvenMoment] using h

/-- A law's even moments are termwise dominated by those of the centered
Gaussian with variance one half.

This is the one-variable consequence of the paper's stronger mixed-even-
moment comparison.  It does not itself assert a tilted exponential bound. -/
structure GaussianHalfEvenMomentDomination (μ : Measure ℝ) : Prop where
  integrable (ell : ℕ) : Integrable (fun x : ℝ => |x| ^ (2 * ell)) μ
  integral_le (ell : ℕ) :
    (∫ x : ℝ, |x| ^ (2 * ell) ∂μ) ≤ gaussianHalfEvenMoment ell

/-- The variance-one-half Gaussian realizes the raw even-moment comparison
with equality. -/
theorem gaussianHalf_evenMomentDomination :
    GaussianHalfEvenMomentDomination
      (ProbabilityTheory.gaussianReal 0 (2 : NNReal)⁻¹) := by
  refine ⟨?_, ?_⟩
  · intro ell
    have h := (gaussianHalf_quadraticExpEvenMomentBound
      (lambda := 0) (by norm_num) (by norm_num)).integrable ell
    simpa using h
  · intro ell
    have h := integral_gaussianHalf_abs_evenPow_mul_exp_sq
      ell (lambda := 0) (by norm_num)
    norm_num [gaussianHalfTiltedEvenMomentMajorant] at h
    simpa [gaussianHalfEvenMoment] using h.le

/-- Mass-one parametric domination at variance at most one half specializes
to the established U3c interface. -/
theorem GaussianEvenMomentDomination.gaussianHalf
    {μ : Measure ℝ} {variance : NNReal}
    (h : GaussianEvenMomentDomination μ 1 variance)
    (hvariance : variance ≤ (2 : NNReal)⁻¹) :
    GaussianHalfEvenMomentDomination μ := by
  have hhalf := h.variance_mono hvariance
  refine ⟨fun ell => hhalf.integrable_abs_pow (2 * ell), ?_⟩
  intro ell
  simpa [centeredGaussianEvenMoment_half] using hhalf.integral_even_le ell

/-- The `n`-th nonnegative Taylor term of the tilted `2ℓ`-th moment
integrand. -/
noncomputable def quadraticExpTiltedMomentTerm
    (ell : ℕ) (lambda : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (lambda ^ n / (n ! : ℝ)) * |x| ^ (2 * (ell + n))

/-- The `N`-term nonnegative Taylor approximation to the tilted `2ℓ`-th
moment integrand. -/
noncomputable def quadraticExpTiltedMomentPartialSum
    (ell : ℕ) (lambda : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, quadraticExpTiltedMomentTerm ell lambda n x

/-- The tilted even-moment integrand is the sum of its nonnegative Taylor
terms. -/
theorem hasSum_quadraticExpTiltedMoment_terms
    (ell : ℕ) (lambda x : ℝ) :
    HasSum (fun n : ℕ => quadraticExpTiltedMomentTerm ell lambda n x)
      (|x| ^ (2 * ell) * Real.exp (lambda * x ^ 2)) := by
  unfold quadraticExpTiltedMomentTerm
  have h := (NormedSpace.expSeries_div_hasSum_exp (lambda * x ^ 2)).mul_left
    (|x| ^ (2 * ell))
  rw [Real.exp_eq_exp_ℝ]
  refine h.congr_fun (fun n => ?_)
  rw [pow_mul, pow_add]
  norm_num [sq_abs]
  rw [show |x| ^ (2 * ell) = (x ^ 2) ^ ell by rw [pow_mul, sq_abs]]
  rw [mul_pow]
  ring

/-- Each finite tilted-moment partial sum is integrable under raw even-moment
domination. -/
theorem integrable_quadraticExpTiltedMomentPartialSum
    {μ : Measure ℝ} (h : GaussianHalfEvenMomentDomination μ)
    (ell : ℕ) (lambda : ℝ) (N : ℕ) :
    Integrable (quadraticExpTiltedMomentPartialSum ell lambda N) μ := by
  unfold quadraticExpTiltedMomentPartialSum
  simp only [quadraticExpTiltedMomentTerm]
  exact integrable_finsetSum _ fun n _ =>
    (h.integrable (ell + n)).const_mul (lambda ^ n / (n ! : ℝ))

/-- Raw Gaussian-half moment domination transfers term by term to every
finite nonnegative Taylor approximation of the tilted moment. -/
theorem integral_quadraticExpTiltedMomentPartialSum_le
    {μ : Measure ℝ} (h : GaussianHalfEvenMomentDomination μ)
    (ell : ℕ) {lambda : ℝ} (hlambda : 0 ≤ lambda) (N : ℕ) :
    (∫ x : ℝ, quadraticExpTiltedMomentPartialSum ell lambda N x ∂μ) ≤
      ∑ n ∈ Finset.range N,
        (lambda ^ n / (n ! : ℝ)) * gaussianHalfEvenMoment (ell + n) := by
  unfold quadraticExpTiltedMomentPartialSum
  simp only [quadraticExpTiltedMomentTerm]
  rw [integral_finsetSum _ fun n _ =>
    (h.integrable (ell + n)).const_mul (lambda ^ n / (n ! : ℝ))]
  simp only [integral_const_mul]
  apply Finset.sum_le_sum
  intro n hn
  exact mul_le_mul_of_nonneg_left (h.integral_le (ell + n)) (by positivity)

private theorem integrable_quadraticExpTiltedMomentTerm_gaussianHalf
    (ell n : ℕ) (lambda : ℝ) :
    Integrable (quadraticExpTiltedMomentTerm ell lambda n)
      (ProbabilityTheory.gaussianReal 0 (2 : NNReal)⁻¹) := by
  unfold quadraticExpTiltedMomentTerm
  have hraw := (gaussianHalf_quadraticExpEvenMomentBound
    (lambda := 0) (by norm_num) (by norm_num)).integrable (ell + n)
  have hraw' : Integrable (fun x : ℝ => |x| ^ (2 * (ell + n)))
      (ProbabilityTheory.gaussianReal 0 (2 : NNReal)⁻¹) := by
    simpa using hraw
  exact hraw'.const_mul _

private theorem integral_quadraticExpTiltedMomentTerm_gaussianHalf
    (ell n : ℕ) (lambda : ℝ) :
    (∫ x : ℝ, quadraticExpTiltedMomentTerm ell lambda n x
        ∂(ProbabilityTheory.gaussianReal 0 (2 : NNReal)⁻¹)) =
      (lambda ^ n / (n ! : ℝ)) * gaussianHalfEvenMoment (ell + n) := by
  unfold quadraticExpTiltedMomentTerm
  rw [integral_const_mul]
  have h := integral_gaussianHalf_abs_evenPow_mul_exp_sq
    (ell + n) (lambda := 0) (by norm_num)
  norm_num [gaussianHalfTiltedEvenMomentMajorant] at h
  have h' :
      (∫ x : ℝ, |x| ^ (2 * (ell + n))
          ∂(ProbabilityTheory.gaussianReal 0 (2 : NNReal)⁻¹)) =
        gaussianHalfEvenMoment (ell + n) := by
    simpa [gaussianHalfEvenMoment] using h
  exact congrArg (fun z : ℝ => (lambda ^ n / (n ! : ℝ)) * z) h'

private theorem quadraticExpTiltedMomentTerm_nonneg
    (ell n : ℕ) {lambda : ℝ} (hlambda : 0 ≤ lambda) (x : ℝ) :
    0 ≤ quadraticExpTiltedMomentTerm ell lambda n x := by
  unfold quadraticExpTiltedMomentTerm
  positivity

private theorem hasSum_gaussianHalf_tiltedMoment_terms
    (ell : ℕ) {lambda : ℝ} (hlambda_nonneg : 0 ≤ lambda)
    (hlambda_lt_one : lambda < 1) :
    HasSum (fun n : ℕ =>
      (lambda ^ n / (n ! : ℝ)) * gaussianHalfEvenMoment (ell + n))
      (gaussianHalfTiltedEvenMomentMajorant ell lambda) := by
  have hpack := gaussianHalf_quadraticExpEvenMomentBound
    hlambda_nonneg hlambda_lt_one
  have hseries : HasSum (fun n : ℕ =>
      ∫ x : ℝ, quadraticExpTiltedMomentTerm ell lambda n x
        ∂(ProbabilityTheory.gaussianReal 0 (2 : NNReal)⁻¹))
      (∫ x : ℝ, |x| ^ (2 * ell) * Real.exp (lambda * x ^ 2)
        ∂(ProbabilityTheory.gaussianReal 0 (2 : NNReal)⁻¹)) := by
    apply hasSum_integral_of_dominated_convergence
      (bound := fun n x => quadraticExpTiltedMomentTerm ell lambda n x)
    · intro n
      exact (integrable_quadraticExpTiltedMomentTerm_gaussianHalf ell n lambda).1
    · intro n
      exact ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (quadraticExpTiltedMomentTerm_nonneg ell n hlambda_nonneg x)]
    · exact ae_of_all _ fun x =>
        (hasSum_quadraticExpTiltedMoment_terms ell lambda x).summable
    · exact (hpack.integrable ell).congr (ae_of_all _ fun x =>
        (hasSum_quadraticExpTiltedMoment_terms ell lambda x).tsum_eq.symm)
    · exact ae_of_all _ fun x =>
        hasSum_quadraticExpTiltedMoment_terms ell lambda x
  have hseries' := hseries.congr_fun fun n =>
    (integral_quadraticExpTiltedMomentTerm_gaussianHalf ell n lambda).symm
  rw [integral_gaussianHalf_abs_evenPow_mul_exp_sq ell hlambda_lt_one] at hseries'
  exact hseries'

private theorem integrable_quadraticExpTiltedMomentTerm
    {μ : Measure ℝ} (h : GaussianHalfEvenMomentDomination μ)
    (ell n : ℕ) (lambda : ℝ) :
    Integrable (quadraticExpTiltedMomentTerm ell lambda n) μ := by
  unfold quadraticExpTiltedMomentTerm
  exact (h.integrable (ell + n)).const_mul _

private theorem integral_quadraticExpTiltedMomentTerm_le
    {μ : Measure ℝ} (h : GaussianHalfEvenMomentDomination μ)
    (ell n : ℕ) {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    (∫ x : ℝ, quadraticExpTiltedMomentTerm ell lambda n x ∂μ) ≤
      (lambda ^ n / (n ! : ℝ)) * gaussianHalfEvenMoment (ell + n) := by
  unfold quadraticExpTiltedMomentTerm
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (h.integral_le (ell + n)) (by positivity)

private theorem integrable_and_integral_le_tiltedMoment_of_massEvenMomentBound
    {μ : Measure ℝ} {mass : ℝ}
    (hintegrable : ∀ ell : ℕ, Integrable (fun x : ℝ => |x| ^ (2 * ell)) μ)
    (hle : ∀ ell : ℕ,
      (∫ x : ℝ, |x| ^ (2 * ell) ∂μ) ≤ mass * gaussianHalfEvenMoment ell)
    (ell : ℕ) {lambda : ℝ} (hlambda_nonneg : 0 ≤ lambda)
    (hlambda_lt_one : lambda < 1) :
    Integrable (fun x : ℝ => |x| ^ (2 * ell) * Real.exp (lambda * x ^ 2)) μ ∧
      (∫ x : ℝ, |x| ^ (2 * ell) * Real.exp (lambda * x ^ 2) ∂μ) ≤
        mass * gaussianHalfTiltedEvenMomentMajorant ell lambda := by
  let F : ℕ → ℝ → ℝ := fun n => quadraticExpTiltedMomentTerm ell lambda n
  let R : ℕ → ℝ := fun n =>
    mass * ((lambda ^ n / (n ! : ℝ)) * gaussianHalfEvenMoment (ell + n))
  have hFint : ∀ n, Integrable (F n) μ := fun n => by
    unfold F quadraticExpTiltedMomentTerm
    exact (hintegrable (ell + n)).const_mul _
  have hFnonneg : ∀ n x, 0 ≤ F n x := fun n x =>
    quadraticExpTiltedMomentTerm_nonneg ell n hlambda_nonneg x
  have hRsum : HasSum R
      (mass * gaussianHalfTiltedEvenMomentMajorant ell lambda) := by
    simpa only [R] using
      (hasSum_gaussianHalf_tiltedMoment_terms ell hlambda_nonneg
        hlambda_lt_one).mul_left mass
  have hterm_le : ∀ n, (∫ x : ℝ, F n x ∂μ) ≤ R n := fun n => by
    unfold F R quadraticExpTiltedMomentTerm
    rw [integral_const_mul]
    have hcoefficient : 0 ≤ lambda ^ n / (n ! : ℝ) := by positivity
    calc
      (lambda ^ n / (n ! : ℝ)) *
          (∫ x : ℝ, |x| ^ (2 * (ell + n)) ∂μ) ≤
          (lambda ^ n / (n ! : ℝ)) *
            (mass * gaussianHalfEvenMoment (ell + n)) :=
        mul_le_mul_of_nonneg_left (hle (ell + n)) hcoefficient
      _ = mass * ((lambda ^ n / (n ! : ℝ)) *
          gaussianHalfEvenMoment (ell + n)) := by ring
  have hintegral_nonneg : ∀ n, 0 ≤ ∫ x : ℝ, F n x ∂μ := fun n =>
    integral_nonneg (hFnonneg n)
  have hsumIntegral : Summable (fun n => ∫ x : ℝ, F n x ∂μ) :=
    Summable.of_nonneg_of_le hintegral_nonneg hterm_le hRsum.summable
  have hnormIntegral :
      (fun n => ∫ x : ℝ, ‖F n x‖ ∂μ) =
        (fun n => ∫ x : ℝ, F n x ∂μ) := by
    funext n
    apply integral_congr_ae
    exact ae_of_all _ fun x => Real.norm_of_nonneg (hFnonneg n x)
  have hsumNorm : Summable (fun n => ∫ x : ℝ, ‖F n x‖ ∂μ) := by
    rw [hnormIntegral]
    exact hsumIntegral
  have hfinite : HasFiniteIntegral
      (fun x : ℝ => |x| ^ (2 * ell) * Real.exp (lambda * x ^ 2)) μ := by
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => by positivity)]
    calc
      (∫⁻ x : ℝ, ENNReal.ofReal
          (|x| ^ (2 * ell) * Real.exp (lambda * x ^ 2)) ∂μ) =
          ∫⁻ x : ℝ, ∑' n, ENNReal.ofReal (F n x) ∂μ := by
        apply lintegral_congr
        intro x
        rw [← ENNReal.ofReal_tsum_of_nonneg (hFnonneg · x)
          (hasSum_quadraticExpTiltedMoment_terms ell lambda x).summable]
        congr 1
        exact (hasSum_quadraticExpTiltedMoment_terms ell lambda x).tsum_eq.symm
      _ = ∑' n, ∫⁻ x : ℝ, ENNReal.ofReal (F n x) ∂μ := by
        rw [lintegral_tsum]
        intro n
        exact (hFint n).aemeasurable.ennreal_ofReal
      _ = ∑' n, ENNReal.ofReal (∫ x : ℝ, F n x ∂μ) := by
        congr 1
        funext n
        exact (ofReal_integral_eq_lintegral_ofReal (hFint n)
          (ae_of_all _ (hFnonneg n))).symm
      _ < ⊤ := hsumIntegral.tsum_ofReal_lt_top
  have hintegrable : Integrable
      (fun x : ℝ => |x| ^ (2 * ell) * Real.exp (lambda * x ^ 2)) μ :=
    ⟨by fun_prop, hfinite⟩
  have hseries := hasSum_integral_of_summable_integral_norm hFint hsumNorm
  have hfun : (fun x : ℝ => ∑' n, F n x) =
      (fun x : ℝ => |x| ^ (2 * ell) * Real.exp (lambda * x ^ 2)) := by
    funext x
    exact (hasSum_quadraticExpTiltedMoment_terms ell lambda x).tsum_eq
  rw [hfun] at hseries
  refine ⟨hintegrable, ?_⟩
  rw [← hseries.tsum_eq, ← hRsum.tsum_eq]
  exact Summable.tsum_le_tsum hterm_le hsumIntegral hRsum.summable

/-- Even-moment domination by the variance-one-half Gaussian implies the
exact tilted-moment interface on the paper's domain `0 ≤ lambda < 1`.

This is the nonnegative-series transfer in U3c: no tilted exponential bound
is assumed. -/
theorem quadraticExpEvenMomentBound_of_evenMomentDomination
    {μ : Measure ℝ} (h : GaussianHalfEvenMomentDomination μ)
    {lambda : ℝ} (hlambda_nonneg : 0 ≤ lambda) (hlambda_lt_one : lambda < 1) :
    QuadraticExpEvenMomentBound μ lambda :=
  ⟨hlambda_nonneg, hlambda_lt_one,
    fun ell => (integrable_and_integral_le_tiltedMoment_of_massEvenMomentBound
      (mass := 1) h.integrable
      (fun ell => by simpa using h.integral_le ell)
      ell hlambda_nonneg hlambda_lt_one).1,
    fun ell => by
      simpa using
        (integrable_and_integral_le_tiltedMoment_of_massEvenMomentBound
          (mass := 1) h.integrable
          (fun ell => by simpa using h.integral_le ell)
          ell hlambda_nonneg hlambda_lt_one).2⟩

/-- Parametric raw-moment domination transfers to tilted moments with its
mass factor intact, after weakening the variance to one half. -/
theorem tiltedEvenMoment_le_of_gaussianEvenMomentDomination
    {μ : Measure ℝ} {mass : ℝ} {variance : NNReal}
    (h : GaussianEvenMomentDomination μ mass variance)
    (hvariance : variance ≤ (2 : NNReal)⁻¹)
    (ell : ℕ) {lambda : ℝ} (hlambda_nonneg : 0 ≤ lambda)
    (hlambda_lt_one : lambda < 1) :
    Integrable (fun x : ℝ => |x| ^ (2 * ell) * Real.exp (lambda * x ^ 2)) μ ∧
      (∫ x : ℝ, |x| ^ (2 * ell) * Real.exp (lambda * x ^ 2) ∂μ) ≤
        mass * gaussianHalfTiltedEvenMomentMajorant ell lambda := by
  have hhalf := h.variance_mono hvariance
  exact integrable_and_integral_le_tiltedMoment_of_massEvenMomentBound
    (mass := mass) (fun n => hhalf.integrable_abs_pow (2 * n))
    (fun n => by
      simpa [centeredGaussianEvenMoment_half] using hhalf.integral_even_le n)
    ell hlambda_nonneg hlambda_lt_one

private theorem pointwiseMajorant_six_mass_fun_eq (rho lambda : ℝ) :
    (fun x : ℝ => quadraticExpDerivativePointwiseMajorant 6 rho lambda x) =
      (fun x : ℝ =>
        ((120 * rho ^ 3) * (|x| ^ (2 * 0) * Real.exp (lambda * x ^ 2)) +
          (720 * rho ^ 4) * (|x| ^ (2 * 1) * Real.exp (lambda * x ^ 2))) +
        ((480 * rho ^ 5) * (|x| ^ (2 * 2) * Real.exp (lambda * x ^ 2)) +
          (64 * rho ^ 6) * (|x| ^ (2 * 3) * Real.exp (lambda * x ^ 2)))) := by
  funext x
  rw [quadraticExpDerivativePointwiseMajorant_six]
  norm_num
  ring

/-- The mass-parametric sixth-derivative majorant.  Unlike the mass-one U3c
consumer below, this theorem retains the factor needed by positive stop-loss
measures. -/
theorem integrable_and_integral_norm_six_le_of_gaussianEvenMomentDomination
    {μ : Measure ℝ} {mass : ℝ} {variance : NNReal}
    (h : GaussianEvenMomentDomination μ mass variance)
    (hvariance : variance ≤ (2 : NNReal)⁻¹) (s : ℂ)
    (hs_nonneg : 0 ≤ s.re) (hs_lt_one : s.re < 1) :
    Integrable (fun x : ℝ => ‖iteratedDeriv 6 (complexQuadraticExp s) x‖) μ ∧
      (∫ x : ℝ, ‖iteratedDeriv 6 (complexQuadraticExp s) x‖ ∂μ) ≤
        mass * quadraticExpDerivativeMajorant 6 ‖s‖ s.re := by
  have h0 := tiltedEvenMoment_le_of_gaussianEvenMomentDomination
    h hvariance 0 hs_nonneg hs_lt_one
  have h1 := tiltedEvenMoment_le_of_gaussianEvenMomentDomination
    h hvariance 1 hs_nonneg hs_lt_one
  have h2 := tiltedEvenMoment_le_of_gaussianEvenMomentDomination
    h hvariance 2 hs_nonneg hs_lt_one
  have h3 := tiltedEvenMoment_le_of_gaussianEvenMomentDomination
    h hvariance 3 hs_nonneg hs_lt_one
  have ha := h0.1.const_mul (120 * ‖s‖ ^ 3)
  have hb := h1.1.const_mul (720 * ‖s‖ ^ 4)
  have hc := h2.1.const_mul (480 * ‖s‖ ^ 5)
  have hd := h3.1.const_mul (64 * ‖s‖ ^ 6)
  have hab : Integrable (fun x : ℝ =>
      (120 * ‖s‖ ^ 3) * (|x| ^ (2 * 0) * Real.exp (s.re * x ^ 2)) +
      (720 * ‖s‖ ^ 4) * (|x| ^ (2 * 1) * Real.exp (s.re * x ^ 2))) μ :=
    ha.add hb
  have hcd : Integrable (fun x : ℝ =>
      (480 * ‖s‖ ^ 5) * (|x| ^ (2 * 2) * Real.exp (s.re * x ^ 2)) +
      (64 * ‖s‖ ^ 6) * (|x| ^ (2 * 3) * Real.exp (s.re * x ^ 2))) μ :=
    hc.add hd
  have hmajor : Integrable
      (fun x : ℝ => quadraticExpDerivativePointwiseMajorant 6 ‖s‖ s.re x) μ := by
    rw [pointwiseMajorant_six_mass_fun_eq]
    exact hab.add hcd
  have hpointwise : ∀ x : ℝ,
      ‖iteratedDeriv 6 (complexQuadraticExp s) x‖ ≤
        quadraticExpDerivativePointwiseMajorant 6 ‖s‖ s.re x :=
    norm_iteratedDeriv_six_complexQuadraticExp_le s
  have hnorm : Integrable
      (fun x : ℝ => ‖iteratedDeriv 6 (complexQuadraticExp s) x‖) μ := by
    refine Integrable.mono' hmajor ?_ ?_
    · have hcont : Continuous
          (fun x : ℝ => ‖iteratedDeriv 6 (complexQuadraticExp s) x‖) := by
        have hfun :
            (fun x : ℝ => ‖iteratedDeriv 6 (complexQuadraticExp s) x‖) =
              fun x : ℝ => ‖(120 * s ^ 3 + 720 * s ^ 4 * (x : ℂ) ^ 2 +
                480 * s ^ 5 * (x : ℂ) ^ 4 + 64 * s ^ 6 * (x : ℂ) ^ 6) *
                  complexQuadraticExp s x‖ := by
          funext x
          rw [iteratedDeriv_six_complexQuadraticExp]
        rw [hfun]
        simp only [complexQuadraticExp]
        fun_prop
      exact hcont.aestronglyMeasurable
    · filter_upwards [] with x
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hpointwise x
  have hintegral := integral_mono hnorm hmajor hpointwise
  refine ⟨hnorm, hintegral.trans ?_⟩
  rw [pointwiseMajorant_six_mass_fun_eq]
  rw [integral_add hab hcd, integral_add ha hb, integral_add hc hd]
  simp only [integral_const_mul]
  calc
    _ ≤ (120 * ‖s‖ ^ 3) *
          (mass * gaussianHalfTiltedEvenMomentMajorant 0 s.re) +
        (720 * ‖s‖ ^ 4) *
          (mass * gaussianHalfTiltedEvenMomentMajorant 1 s.re) +
        (480 * ‖s‖ ^ 5) *
          (mass * gaussianHalfTiltedEvenMomentMajorant 2 s.re) +
        (64 * ‖s‖ ^ 6) *
          (mass * gaussianHalfTiltedEvenMomentMajorant 3 s.re) := by
      have hle0 := mul_le_mul_of_nonneg_left h0.2
        (by positivity : 0 ≤ 120 * ‖s‖ ^ 3)
      have hle1 := mul_le_mul_of_nonneg_left h1.2
        (by positivity : 0 ≤ 720 * ‖s‖ ^ 4)
      have hle2 := mul_le_mul_of_nonneg_left h2.2
        (by positivity : 0 ≤ 480 * ‖s‖ ^ 5)
      have hle3 := mul_le_mul_of_nonneg_left h3.2
        (by positivity : 0 ≤ 64 * ‖s‖ ^ 6)
      linarith
    _ = mass * quadraticExpDerivativeMajorant 6 ‖s‖ s.re := by
      rw [quadraticExpDerivativeMajorant_six]
      norm_num [gaussianHalfTiltedEvenMomentMajorant]
      ring

/-- Inequality-only wrapper for the mass-parametric sixth-derivative
majorant. -/
theorem integral_norm_six_le_of_gaussianEvenMomentDomination
    {μ : Measure ℝ} {mass : ℝ} {variance : NNReal}
    (h : GaussianEvenMomentDomination μ mass variance)
    (hvariance : variance ≤ (2 : NNReal)⁻¹) (s : ℂ)
    (hs_nonneg : 0 ≤ s.re) (hs_lt_one : s.re < 1) :
    (∫ x : ℝ, ‖iteratedDeriv 6 (complexQuadraticExp s) x‖ ∂μ) ≤
      mass * quadraticExpDerivativeMajorant 6 ‖s‖ s.re :=
  (integrable_and_integral_norm_six_le_of_gaussianEvenMomentDomination
    h hvariance s hs_nonneg hs_lt_one).2

/-- The concrete sixth-derivative U3c bound obtained from raw even-moment
domination by the variance-one-half Gaussian. -/
theorem integral_norm_iteratedDeriv_six_complexQuadraticExp_le_of_evenMomentDomination
    {μ : Measure ℝ} (h : GaussianHalfEvenMomentDomination μ) (s : ℂ)
    (hs_nonneg : 0 ≤ s.re) (hs_lt_one : s.re < 1) :
    (∫ x : ℝ, ‖iteratedDeriv 6 (complexQuadraticExp s) x‖ ∂μ) ≤
      quadraticExpDerivativeMajorant 6 ‖s‖ s.re := by
  exact integral_norm_iteratedDeriv_six_complexQuadraticExp_le s
    (quadraticExpEvenMomentBound_of_evenMomentDomination h hs_nonneg hs_lt_one)

/-- The concrete eighth-derivative U3c bound obtained from raw even-moment
domination by the variance-one-half Gaussian. -/
theorem integral_norm_iteratedDeriv_eight_complexQuadraticExp_le_of_evenMomentDomination
    {μ : Measure ℝ} (h : GaussianHalfEvenMomentDomination μ) (s : ℂ)
    (hs_nonneg : 0 ≤ s.re) (hs_lt_one : s.re < 1) :
    (∫ x : ℝ, ‖iteratedDeriv 8 (complexQuadraticExp s) x‖ ∂μ) ≤
      quadraticExpDerivativeMajorant 8 ‖s‖ s.re := by
  exact integral_norm_iteratedDeriv_eight_complexQuadraticExp_le s
    (quadraticExpEvenMomentBound_of_evenMomentDomination h hs_nonneg hs_lt_one)

end CertifiedJL
