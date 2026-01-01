/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Transcendental.Trigonometric.Pi
import CertifiedJL.Probability.NormalApproximation.Tyurin.EnvelopeBounds

/-!
# Certificate-facing upper bound for Tyurin's D-star functional

This file combines the global I.29 kernel bound with an endpoint-vanishing
right-half bound.  Their pointwise minimum is the kernel envelope used by
finite certificates.  The discrepancy factors are replaced by the finite
right-sum envelopes from `TyurinEnvelopeBounds`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace CertifiedJL
namespace Probability

/-- The scaled form of the relaxed I.29 bound. -/
noncomputable def scaledPrawitzI29Envelope (u : ℝ) : ℝ :=
  (513 / 500 : ℝ) / (2 * Real.pi * |u|)

/-- The scaled endpoint-vanishing kernel envelope. -/
noncomputable def scaledPrawitzEndpointEnvelope
    (U u : ℝ) : ℝ :=
  (1 / U) *
    ((1 - |u| / U) / 2 +
      Real.pi * (1 - |u| / U) ^ 2 / 4)

/--
The certificate kernel envelope: I.29 on the inner half-band and the
minimum of I.29 and the endpoint estimate on the outer half-band.
-/
noncomputable def scaledPrawitzCertificateEnvelope
    (U u : ℝ) : ℝ :=
  if U / 2 ≤ |u| then
    min (scaledPrawitzI29Envelope u)
      (scaledPrawitzEndpointEnvelope U u)
  else
    scaledPrawitzI29Envelope u

private lemma norm_prawitzKernel_eq_abs (t : ℝ) :
    ‖prawitzKernel t‖ = ‖prawitzKernel |t|‖ := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · have htneg : t < 0 := lt_of_not_ge ht
    rw [abs_of_neg htneg, prawitzKernel_neg, Complex.norm_conj]

/-- Scaled I.29, with the bandwidth canceled exactly. -/
theorem norm_scaledPrawitzKernel_le_i29
    {U u : ℝ} (hU : 0 < U) (hu : u ≠ 0)
    (hinside : |u| ≤ U) :
    ‖scaledPrawitzKernel U u‖ ≤
      scaledPrawitzI29Envelope u := by
  have hratio0 : 0 < |u / U| := by
    rw [abs_div, abs_of_pos hU]
    positivity
  have hratio1 : |u / U| ≤ 1 := by
    rw [abs_div, abs_of_pos hU, div_le_one hU]
    exact hinside
  have hk := norm_prawitzKernel_le_i29 hratio0 hratio1
  unfold scaledPrawitzKernel scaledPrawitzI29Envelope
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_div, abs_one, abs_of_pos hU]
  rw [abs_div, abs_of_pos hU] at hk
  calc
    (1 / U) * ‖prawitzKernel (u / U)‖ ≤
        (1 / U) *
          ((513 / 500 : ℝ) /
            (2 * Real.pi * (|u| / U))) := by
      exact mul_le_mul_of_nonneg_left hk (by positivity)
    _ = (513 / 500 : ℝ) /
        (2 * Real.pi * |u|) := by
      field_simp [hU.ne', hu]

/-- Scaled endpoint-vanishing bound on the outer half-band. -/
theorem norm_scaledPrawitzKernel_le_endpoint
    {U u : ℝ} (hU : 0 < U)
    (hhalf : U / 2 ≤ |u|) (hinside : |u| ≤ U) :
    ‖scaledPrawitzKernel U u‖ ≤
      scaledPrawitzEndpointEnvelope U u := by
  let s : ℝ := |u| / U
  have hsHalf : 1 / 2 ≤ s := by
    dsimp only [s]
    rw [le_div_iff₀ hU]
    nlinarith
  have hsOne : s ≤ 1 := by
    dsimp only [s]
    exact (div_le_one hU).2 hinside
  have hratioAbs : |u / U| = s := by
    dsimp only [s]
    rw [abs_div, abs_of_pos hU]
  have hnormRatio :
      ‖prawitzKernel (u / U)‖ = ‖prawitzKernel s‖ := by
    rw [norm_prawitzKernel_eq_abs, hratioAbs]
  unfold scaledPrawitzKernel scaledPrawitzEndpointEnvelope
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_div, abs_one, abs_of_pos hU, hnormRatio]
  rcases hsOne.eq_or_lt with hsEq | hsOne
  · rw [hsEq, prawitzKernel_one, norm_zero]
    have habsRatio : |u| / U = 1 := by
      simpa only [s] using hsEq
    rw [habsRatio]
    norm_num
  · have hk := norm_prawitzKernel_le_endpoint hsHalf hsOne
    exact mul_le_mul_of_nonneg_left hk (by positivity)

/-- The certificate envelope bounds the scaled kernel away from zero. -/
theorem norm_scaledPrawitzKernel_le_certificateEnvelope
    {U u : ℝ} (hU : 0 < U) (hu : u ≠ 0)
    (hinside : |u| ≤ U) :
    ‖scaledPrawitzKernel U u‖ ≤
      scaledPrawitzCertificateEnvelope U u := by
  have hi29 :=
    norm_scaledPrawitzKernel_le_i29 hU hu hinside
  unfold scaledPrawitzCertificateEnvelope
  by_cases hhalf : U / 2 ≤ |u|
  · rw [if_pos hhalf, le_min_iff]
    exact ⟨hi29,
      norm_scaledPrawitzKernel_le_endpoint hU hhalf hinside⟩
  · rw [if_neg hhalf]
    exact hi29

/-- Finite trapezoidal-certificate integrand for the core discrepancy term. -/
noncomputable def tyurinCoreTrapezoidCertificateIntegrand
    (n : ℕ) (L U : ℝ) (u : ℝ) : ℝ :=
  scaledPrawitzCertificateEnvelope U u *
    min (tyurinDeltaOneTrapezoidUpper n L u)
      (tyurinDeltaTwoTrapezoidUpper n L u)

/-- Certificate integrand for the outer product-envelope term. -/
noncomputable def tyurinOuterCertificateIntegrand
    (L U : ℝ) (u : ℝ) : ℝ :=
  scaledPrawitzCertificateEnvelope U u *
    tyurinProductEnvelope L u

/--
An exp-only rational upper bound for the sharp Gaussian budget.  The
parameter `e` is supplied by a certificate for
`exp (-(U₀²)/2) ≤ e`.
-/
noncomputable def tyurinRationalGaussianBudget
    (U₀ U e : ℝ) : ℝ :=
  (251 / 100 : ℝ) / (2 * U) -
    (1 - e) / U ^ 2 +
    (63 / 20 : ℝ) ^ 2 * (251 / 100 : ℝ) /
      (36 * U ^ 3) +
    (50 / 157 : ℝ) * e / U₀ ^ 2

theorem prawitzGaussianSharpClosedBudget_le_rational
    {U₀ U e : ℝ} (hU₀ : 0 < U₀) (hU : 0 < U)
    (he0 : 0 ≤ e)
    (hexp : Real.exp (-(U₀ ^ 2) / 2) ≤ e) :
    prawitzGaussianSharpClosedBudget U₀ U ≤
      tyurinRationalGaussianBudget U₀ U e := by
  have hsqrt :
      Real.sqrt (2 * Real.pi) ≤ (251 / 100 : ℝ) :=
    (sqrt_two_pi_lt_251_div_100).le
  have hpi :
      Real.pi ≤ (63 / 20 : ℝ) :=
    (pi_lt_63_div_20).le
  have hpiSq :
      Real.pi ^ 2 ≤ (63 / 20 : ℝ) ^ 2 :=
    (sq_le_sq₀ Real.pi_pos.le (by norm_num)).2 hpi
  have hsqrt0 : 0 ≤ Real.sqrt (2 * Real.pi) :=
    Real.sqrt_nonneg _
  have hpiRat0 : 0 ≤ (63 / 20 : ℝ) ^ 2 := sq_nonneg _
  have hprod :
      Real.pi ^ 2 * Real.sqrt (2 * Real.pi) ≤
        (63 / 20 : ℝ) ^ 2 * (251 / 100 : ℝ) :=
    mul_le_mul hpiSq hsqrt hsqrt0 hpiRat0
  have hinvPi :
      1 / Real.pi ≤ (50 / 157 : ℝ) := by
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [pi_gt_157_div_50]
  have hexp0 :
      0 ≤ Real.exp (-(U₀ ^ 2) / 2) := Real.exp_nonneg _
  have htailNumerator :
      Real.exp (-(U₀ ^ 2) / 2) * (1 / Real.pi) ≤
        e * (50 / 157 : ℝ) :=
    mul_le_mul hexp hinvPi (by positivity) he0
  unfold prawitzGaussianSharpClosedBudget
    prawitzGaussianSharpCoreBudget
    tyurinRationalGaussianBudget
  have hfirst :
      Real.sqrt (2 * Real.pi) / (2 * U) ≤
        (251 / 100 : ℝ) / (2 * U) :=
    div_le_div_of_nonneg_right hsqrt (by positivity)
  have hnegative :
      -(1 - Real.exp (-(U₀ ^ 2) / 2)) / U ^ 2 ≤
        -(1 - e) / U ^ 2 := by
    have :
        -(1 - Real.exp (-(U₀ ^ 2) / 2)) ≤ -(1 - e) := by
      linarith
    exact div_le_div_of_nonneg_right this (sq_nonneg U)
  have hthird :
      Real.pi ^ 2 * Real.sqrt (2 * Real.pi) /
          (36 * U ^ 3) ≤
        (63 / 20 : ℝ) ^ 2 * (251 / 100 : ℝ) /
          (36 * U ^ 3) :=
    div_le_div_of_nonneg_right hprod (by positivity)
  have htail :
      Real.exp (-(U₀ ^ 2) / 2) /
          (Real.pi * U₀ ^ 2) ≤
        (50 / 157 : ℝ) * e / U₀ ^ 2 := by
    calc
      Real.exp (-(U₀ ^ 2) / 2) /
          (Real.pi * U₀ ^ 2) =
          (Real.exp (-(U₀ ^ 2) / 2) * (1 / Real.pi)) /
            U₀ ^ 2 := by
        field_simp [Real.pi_ne_zero, hU₀.ne']
      _ ≤ (e * (50 / 157 : ℝ)) / U₀ ^ 2 :=
        div_le_div_of_nonneg_right htailNumerator (sq_nonneg U₀)
      _ = (50 / 157 : ℝ) * e / U₀ ^ 2 := by ring
  have hsum :=
    add_le_add
      (add_le_add (add_le_add hfirst hnegative) hthird)
      htail
  simpa only [sub_eq_add_neg, neg_div] using hsum

/--
The finite-envelope D-star upper functional.  Numerical integration of its
two one-dimensional integrands is deliberately delegated to a separate
mesh certificate.
-/
noncomputable def tyurinCertificateDStarUpper
    (n : ℕ) (L U₀ U e : ℝ) : ℝ :=
  (2 * (∫ u : ℝ in 0..U₀,
      tyurinCoreTrapezoidCertificateIntegrand n L U u) +
    2 * (∫ u : ℝ in U₀..U,
      tyurinOuterCertificateIntegrand L U u) +
    tyurinRationalGaussianBudget U₀ U e) / L

theorem tyurinDeltaOne_nonneg
    {L t : ℝ} (hL : 0 ≤ L) :
    0 ≤ tyurinDeltaOne L t := by
  unfold tyurinDeltaOne
  have hintegral :
      0 ≤ ∫ s : ℝ in 0..|t|,
        s ^ 2 / 2 * Real.exp (s ^ 2 / 2) := by
    apply intervalIntegral.integral_nonneg
    · exact abs_nonneg _
    · intro s _
      positivity
  positivity

theorem tyurinDeltaTwo_nonneg
    {L t : ℝ} (hL : 0 < L) :
    0 ≤ tyurinDeltaTwo L t := by
  let T : ℝ := |t|
  let R : ℝ := lyapunovThirdRoot L
  let A : ℝ := 5 / (3 * R)
  have hT : 0 ≤ T := abs_nonneg _
  have hR : 0 < R := by
    dsimp only [R]
    unfold lyapunovThirdRoot
    positivity
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  unfold tyurinDeltaTwo
  dsimp only
  by_cases hbranch : T * R ≤ 5 / 3
  · rw [if_pos hbranch]
    have hintegral :
        0 ≤ ∫ s : ℝ in 0..T,
          s ^ 2 / 2 *
            Real.exp (lyapunovVarianceCap L * s ^ 2 / 2) := by
      apply intervalIntegral.integral_nonneg hT
      intro s _
      positivity
    positivity
  · rw [if_neg hbranch]
    have hAT : A ≤ T := by
      have hstrict : 5 / 3 < T * R := lt_of_not_ge hbranch
      dsimp only [A]
      rw [div_le_iff₀ (by positivity : 0 < 3 * R)]
      nlinarith
    have hfirst :
        0 ≤ ∫ s : ℝ in 0..A,
          s ^ 2 / 2 *
            Real.exp (lyapunovVarianceCap L * s ^ 2 / 2) := by
      apply intervalIntegral.integral_nonneg hA
      intro s _
      positivity
    have hsecond :
        0 ≤ ∫ s : ℝ in A..T,
          s ^ 2 / (2 * tyurinRationalEll) *
            Real.exp (L * s ^ 3 / 5) := by
      apply intervalIntegral.integral_nonneg hAT
      intro s _
      have hEll : 0 < tyurinRationalEll := by
        unfold tyurinRationalEll
        positivity
      positivity
    positivity

theorem tyurinProductEnvelope_nonneg (L t : ℝ) :
    0 ≤ tyurinProductEnvelope L t := by
  unfold tyurinProductEnvelope
  positivity

private theorem measurable_tyurinDeltaOne (L : ℝ) :
    Measurable (tyurinDeltaOne L) := by
  unfold tyurinDeltaOne
  fun_prop

private theorem measurable_tyurinDeltaTwo (L : ℝ) :
    Measurable (tyurinDeltaTwo L) := by
  unfold tyurinDeltaTwo
  dsimp only
  apply Measurable.ite
  · exact measurableSet_le
      ((continuous_abs.mul continuous_const).measurable)
      measurable_const
  · fun_prop
  · fun_prop

private theorem measurable_tyurinProductEnvelope (L : ℝ) :
    Measurable (tyurinProductEnvelope L) := by
  unfold tyurinProductEnvelope tyurinB
  apply Measurable.exp
  apply Measurable.div_const
  apply Measurable.ite
  · exact measurableSet_lt
      (measurable_const.mul continuous_abs.measurable)
      measurable_const
  · fun_prop
  · apply Measurable.ite
    · exact measurableSet_le
        (measurable_const.mul continuous_abs.measurable)
        measurable_const
    · fun_prop
    · fun_prop

private theorem measurable_scaledPrawitzCertificateEnvelope (U : ℝ) :
    Measurable (scaledPrawitzCertificateEnvelope U) := by
  unfold scaledPrawitzCertificateEnvelope
    scaledPrawitzI29Envelope
    scaledPrawitzEndpointEnvelope
  apply Measurable.ite
  · exact measurableSet_le measurable_const continuous_abs.measurable
  · fun_prop
  · fun_prop

private theorem measurable_tyurinDeltaOneTrapezoidUpper
    (n : ℕ) (L : ℝ) :
    Measurable (tyurinDeltaOneTrapezoidUpper n L) := by
  unfold tyurinDeltaOneTrapezoidUpper sqExpSqTrapezoid
    trapezoidal_integral
  fun_prop

private theorem measurable_tyurinDeltaTwoTrapezoidUpper
    (n : ℕ) (L : ℝ) :
    Measurable (tyurinDeltaTwoTrapezoidUpper n L) := by
  unfold tyurinDeltaTwoTrapezoidUpper
  dsimp only
  apply Measurable.ite
  · exact measurableSet_le
      ((continuous_abs.mul continuous_const).measurable)
      measurable_const
  · unfold sqExpSqTrapezoid trapezoidal_integral
    fun_prop
  · unfold sqExpSqTrapezoid sqExpCubeTrapezoid
      trapezoidal_integral
    fun_prop

private theorem measurable_tyurinCoreTrapezoidCertificateIntegrand
    (n : ℕ) (L U : ℝ) :
    Measurable (tyurinCoreTrapezoidCertificateIntegrand n L U) :=
  (measurable_scaledPrawitzCertificateEnvelope U).mul
    ((measurable_tyurinDeltaOneTrapezoidUpper n L).min
      (measurable_tyurinDeltaTwoTrapezoidUpper n L))

private theorem measurable_tyurinOuterCertificateIntegrand
    (L U : ℝ) :
    Measurable (tyurinOuterCertificateIntegrand L U) :=
  (measurable_scaledPrawitzCertificateEnvelope U).mul
    (measurable_tyurinProductEnvelope L)

theorem measurable_tyurinCoreIntegrand (L U : ℝ) :
    Measurable
      (fun u : ℝ =>
        ‖scaledPrawitzKernel U u‖ *
          min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)) :=
  (measurable_scaledPrawitzKernel U).norm.mul
    ((measurable_tyurinDeltaOne L).min
      (measurable_tyurinDeltaTwo L))

theorem measurable_tyurinOuterIntegrand (L U : ℝ) :
    Measurable
      (fun u : ℝ =>
        ‖scaledPrawitzKernel U u‖ *
          tyurinProductEnvelope L u) :=
  (measurable_scaledPrawitzKernel U).norm.mul
    (measurable_tyurinProductEnvelope L)

private theorem scaledPrawitzCertificateEnvelope_le_i29
    (U u : ℝ) :
    scaledPrawitzCertificateEnvelope U u ≤
      scaledPrawitzI29Envelope u := by
  unfold scaledPrawitzCertificateEnvelope
  split_ifs
  · exact min_le_left _ _
  · rfl

private theorem tyurinDeltaOneTrapezoidUpper_nonneg
    {n : ℕ} {L u : ℝ} (hn : 0 < n) (hL : 0 ≤ L) :
    0 ≤ tyurinDeltaOneTrapezoidUpper n L u := by
  unfold tyurinDeltaOneTrapezoidUpper
  exact mul_nonneg (mul_nonneg hL (Real.exp_nonneg _))
    (sqExpSqTrapezoid_nonneg hn (abs_nonneg _))

/--
The Gaussian factors in the first finite discrepancy envelope cancel
exactly.  This is the removable-singularity estimate at the heart of
the core integrability proof.
-/
private theorem tyurinDeltaOneTrapezoidUpper_le_cubic
    {n : ℕ} {L u : ℝ} (hn : 0 < n) (hL : 0 ≤ L)
    (hu : 0 ≤ u) :
    tyurinDeltaOneTrapezoidUpper n L u ≤ L * u ^ 3 / 2 := by
  have hsum :=
    sqExpSqTrapezoid_le_endpoint
      (n := n) (c := (1 : ℝ)) (T := u) hn hu (by norm_num)
  unfold tyurinDeltaOneTrapezoidUpper
  rw [abs_of_nonneg hu]
  calc
    L * Real.exp (-(u ^ 2) / 2) * sqExpSqTrapezoid n 1 u ≤
        L * Real.exp (-(u ^ 2) / 2) *
          (u ^ 3 / 2 * Real.exp (1 * u ^ 2 / 2)) := by
      exact mul_le_mul_of_nonneg_left hsum
        (mul_nonneg hL (Real.exp_nonneg _))
    _ = L * u ^ 3 / 2 := by
      rw [show (1 : ℝ) * u ^ 2 / 2 = u ^ 2 / 2 by ring,
        show
          L * Real.exp (-(u ^ 2) / 2) *
              (u ^ 3 / 2 * Real.exp (u ^ 2 / 2)) =
            L * u ^ 3 / 2 *
              (Real.exp (-(u ^ 2) / 2) *
                Real.exp (u ^ 2 / 2)) by ring,
        ← Real.exp_add]
      ring_nf
      rw [Real.exp_zero]
      ring

theorem tyurinCoreTrapezoidCertificateIntegrand_le
    {n : ℕ} {L U₀ U u : ℝ}
    (hn : 0 < n) (hL : 0 < L) (hU₀ : 0 < U₀)
    (hU : 0 < U) (hcut : U₀ ≤ U)
    (hu0 : 0 ≤ u) (huU₀ : u ≤ U₀) :
    tyurinCoreTrapezoidCertificateIntegrand n L U u ≤
      (513 / 500 : ℝ) * L * U₀ ^ 2 / 4 := by
  have hinside : u ≤ U := huU₀.trans hcut
  have henvelope0 : 0 ≤ scaledPrawitzCertificateEnvelope U u := by
    by_cases hu : u = 0
    · subst u
      have hhalf : ¬ U / 2 ≤ (0 : ℝ) := by linarith
      simp [scaledPrawitzCertificateEnvelope, hhalf,
        scaledPrawitzI29Envelope]
    · exact (norm_nonneg _).trans
        (norm_scaledPrawitzKernel_le_certificateEnvelope
          hU hu (by simpa [abs_of_nonneg hu0] using hinside))
  have hdelta0 :
      0 ≤ tyurinDeltaOneTrapezoidUpper n L u :=
    tyurinDeltaOneTrapezoidUpper_nonneg hn hL.le
  have hdelta :
      min (tyurinDeltaOneTrapezoidUpper n L u)
          (tyurinDeltaTwoTrapezoidUpper n L u) ≤
        tyurinDeltaOneTrapezoidUpper n L u :=
    min_le_left _ _
  have hi29 :
      scaledPrawitzCertificateEnvelope U u ≤
        scaledPrawitzI29Envelope u :=
    scaledPrawitzCertificateEnvelope_le_i29 U u
  have hcubic :=
    tyurinDeltaOneTrapezoidUpper_le_cubic hn hL.le hu0
  unfold tyurinCoreTrapezoidCertificateIntegrand
  calc
    scaledPrawitzCertificateEnvelope U u *
        min (tyurinDeltaOneTrapezoidUpper n L u)
          (tyurinDeltaTwoTrapezoidUpper n L u) ≤
      scaledPrawitzCertificateEnvelope U u *
        tyurinDeltaOneTrapezoidUpper n L u :=
        mul_le_mul_of_nonneg_left hdelta henvelope0
    _ ≤ scaledPrawitzI29Envelope u *
        tyurinDeltaOneTrapezoidUpper n L u :=
        mul_le_mul_of_nonneg_right hi29 hdelta0
    _ ≤ scaledPrawitzI29Envelope u * (L * u ^ 3 / 2) := by
        apply mul_le_mul_of_nonneg_left hcubic
        unfold scaledPrawitzI29Envelope
        positivity
    _ ≤ (513 / 500 : ℝ) * L * U₀ ^ 2 / 4 := by
      unfold scaledPrawitzI29Envelope
      by_cases hu : u = 0
      · subst u
        simp only [abs_zero, mul_zero, div_zero, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
        positivity
      · rw [abs_of_nonneg hu0]
        have huPos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
        have hpiOne : 1 ≤ Real.pi := by
          nlinarith [Real.pi_gt_three]
        have huSq : u ^ 2 ≤ U₀ ^ 2 := by
          nlinarith
        calc
          (513 / 500 : ℝ) / (2 * Real.pi * u) *
              (L * u ^ 3 / 2) =
            (513 / 500 : ℝ) * L * u ^ 2 /
              (4 * Real.pi) := by
                field_simp [Real.pi_ne_zero, hu]
                ring
          _ ≤ (513 / 500 : ℝ) * L * u ^ 2 / 4 := by
                apply div_le_div_of_nonneg_left
                · positivity
                · norm_num
                · nlinarith [Real.pi_pos]
          _ ≤ (513 / 500 : ℝ) * L * U₀ ^ 2 / 4 := by
                gcongr

private theorem tyurinProductEnvelope_le
    {L U u : ℝ} (hL : 0 < L) (hU : 0 ≤ U)
    (hu0 : 0 ≤ u) (huU : u ≤ U) :
    tyurinProductEnvelope L u ≤
      Real.exp (2 * L * tyurinRationalA * U ^ 3) := by
  apply Real.exp_le_exp.mpr
  unfold tyurinB
  rw [abs_of_nonneg hu0]
  by_cases hfirst : 2 * L * u < tyurinRationalM
  · rw [if_pos hfirst]
    have hA : 0 ≤ tyurinRationalA := by
      unfold tyurinRationalA
      norm_num
    have hcube : u ^ 3 ≤ U ^ 3 := by
      nlinarith [mul_self_le_mul_self hu0 huU]
    calc
      (-u ^ 2 + 2 * (2 * L) * tyurinRationalA * u ^ 3) / 2 ≤
          (2 * (2 * L) * tyurinRationalA * u ^ 3) / 2 := by
            nlinarith [sq_nonneg u]
      _ = 2 * L * tyurinRationalA * u ^ 3 := by ring
      _ ≤ 2 * L * tyurinRationalA * U ^ 3 := by
            gcongr
  · rw [if_neg hfirst]
    by_cases hsecond : 2 * L * u ≤ 2 * Real.pi
    · rw [if_pos hsecond]
      have hgammaSq : 0 < (2 * L) ^ 2 :=
        sq_pos_of_pos (by positivity)
      have hcos : 0 ≤ 1 - Real.cos (2 * L * u) := by
        nlinarith [Real.neg_one_le_cos (2 * L * u),
          Real.cos_le_one (2 * L * u)]
      have hbranch :
          -2 * tyurinCosineLoss / (2 * L) ^ 2 *
              (1 - Real.cos (2 * L * u)) ≤ 0 := by
        have hcoeff :
            -2 * tyurinCosineLoss / (2 * L) ^ 2 ≤ 0 := by
          apply div_nonpos_of_nonpos_of_nonneg _ hgammaSq.le
          unfold tyurinCosineLoss
          norm_num
        exact mul_nonpos_of_nonpos_of_nonneg hcoeff hcos
      have hrhs : 0 ≤
          2 * L * tyurinRationalA * U ^ 3 := by
        unfold tyurinRationalA
        positivity
      nlinarith
    · rw [if_neg hsecond]
      unfold tyurinRationalA
      norm_num
      positivity

private theorem tyurinOuterCertificateIntegrand_le
    {L U₀ U u : ℝ} (hL : 0 < L) (hU₀ : 0 < U₀)
    (hU : 0 < U) (hu0 : U₀ ≤ u) (huU : u ≤ U) :
    tyurinOuterCertificateIntegrand L U u ≤
      (513 / 500 : ℝ) / (2 * U₀) *
        Real.exp (2 * L * tyurinRationalA * U ^ 3) := by
  have huPos : 0 < u := hU₀.trans_le hu0
  have hpiOne : 1 ≤ Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hden : 2 * U₀ ≤ 2 * Real.pi * u := by
    calc
      2 * U₀ ≤ 2 * u := by linarith
      _ ≤ 2 * Real.pi * u := by nlinarith
  have hi29 :
      scaledPrawitzI29Envelope u ≤
        (513 / 500 : ℝ) / (2 * U₀) := by
    unfold scaledPrawitzI29Envelope
    rw [abs_of_pos huPos]
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * Real.pi * u)
      (by positivity : 0 < 2 * U₀)).2
    exact mul_le_mul_of_nonneg_left hden (by norm_num)
  have hkernel :
      scaledPrawitzCertificateEnvelope U u ≤
        (513 / 500 : ℝ) / (2 * U₀) :=
    (scaledPrawitzCertificateEnvelope_le_i29 U u).trans hi29
  have hproduct :=
    tyurinProductEnvelope_le hL hU.le (hU₀.le.trans hu0) huU
  unfold tyurinOuterCertificateIntegrand
  calc
    scaledPrawitzCertificateEnvelope U u *
        tyurinProductEnvelope L u ≤
      ((513 / 500 : ℝ) / (2 * U₀)) *
        tyurinProductEnvelope L u := by
          exact mul_le_mul_of_nonneg_right hkernel
            (tyurinProductEnvelope_nonneg L u)
    _ ≤ (513 / 500 : ℝ) / (2 * U₀) *
        Real.exp (2 * L * tyurinRationalA * U ^ 3) := by
          exact mul_le_mul_of_nonneg_left hproduct (by positivity)

/-- Pointwise core domination used by the D-star upper theorem. -/
theorem tyurinCoreIntegrand_le_trapezoidCertificate
    {n : ℕ} {L U u : ℝ}
    (hn : 0 < n) (hL : 0 < L) (hU : 0 < U)
    (hu0 : 0 ≤ u) (huU : u ≤ U) :
    ‖scaledPrawitzKernel U u‖ *
        min (tyurinDeltaOne L u) (tyurinDeltaTwo L u) ≤
      tyurinCoreTrapezoidCertificateIntegrand n L U u := by
  by_cases hu : u = 0
  · subst u
    have hhalf : ¬ U / 2 ≤ (0 : ℝ) := by
      linarith
    have hmin :
        min (tyurinDeltaOne L 0) (tyurinDeltaTwo L 0) = 0 := by
      rw [min_eq_left]
      · simp [tyurinDeltaOne]
      · simpa [tyurinDeltaOne] using
          tyurinDeltaTwo_nonneg (t := 0) hL
    rw [hmin, mul_zero]
    simp [tyurinCoreTrapezoidCertificateIntegrand,
      scaledPrawitzCertificateEnvelope, hhalf,
      scaledPrawitzI29Envelope]
  · have hkernel :=
      norm_scaledPrawitzKernel_le_certificateEnvelope
        hU hu (by simpa [abs_of_nonneg hu0] using huU)
    have hdeltaOne :=
      tyurinDeltaOne_le_trapezoidUpper (t := u) hn hL.le
    have hdeltaTwo :=
      tyurinDeltaTwo_le_trapezoidUpper (t := u) hn hL
    have hdelta :
        min (tyurinDeltaOne L u) (tyurinDeltaTwo L u) ≤
          min (tyurinDeltaOneTrapezoidUpper n L u)
            (tyurinDeltaTwoTrapezoidUpper n L u) :=
      min_le_min hdeltaOne hdeltaTwo
    have hmin0 :
        0 ≤ min (tyurinDeltaOne L u) (tyurinDeltaTwo L u) :=
      le_min (tyurinDeltaOne_nonneg hL.le)
        (tyurinDeltaTwo_nonneg hL)
    have henvelope0 :
        0 ≤ scaledPrawitzCertificateEnvelope U u :=
      (norm_nonneg _).trans hkernel
    unfold tyurinCoreTrapezoidCertificateIntegrand
    exact mul_le_mul hkernel hdelta hmin0 henvelope0

/-- Pointwise outer domination used by the D-star upper theorem. -/
theorem tyurinOuterIntegrand_le_certificate
    {L U u : ℝ} (hU : 0 < U)
    (hu0 : 0 < u) (huU : u ≤ U) :
    ‖scaledPrawitzKernel U u‖ *
        tyurinProductEnvelope L u ≤
      tyurinOuterCertificateIntegrand L U u := by
  have hkernel :=
    norm_scaledPrawitzKernel_le_certificateEnvelope
      hU hu0.ne' (by simpa [abs_of_pos hu0] using huU)
  unfold tyurinOuterCertificateIntegrand
  exact mul_le_mul_of_nonneg_right hkernel
    (tyurinProductEnvelope_nonneg L u)

private theorem tyurinCoreCertificate_nonneg
    {n : ℕ} {L U u : ℝ}
    (hn : 0 < n) (hL : 0 < L) (hU : 0 < U)
    (hu0 : 0 ≤ u) (huU : u ≤ U) :
    0 ≤ tyurinCoreTrapezoidCertificateIntegrand n L U u := by
  have hactual :
      0 ≤ ‖scaledPrawitzKernel U u‖ *
          min (tyurinDeltaOne L u) (tyurinDeltaTwo L u) := by
    exact mul_nonneg (norm_nonneg _)
      (le_min (tyurinDeltaOne_nonneg hL.le)
        (tyurinDeltaTwo_nonneg hL))
  exact hactual.trans
    (tyurinCoreIntegrand_le_trapezoidCertificate
      hn hL hU hu0 huU)

private theorem tyurinOuterCertificate_nonneg
    {L U u : ℝ} (hU : 0 < U)
    (hu0 : 0 < u) (huU : u ≤ U) :
    0 ≤ tyurinOuterCertificateIntegrand L U u := by
  have hactual :
      0 ≤ ‖scaledPrawitzKernel U u‖ *
          tyurinProductEnvelope L u :=
    mul_nonneg (norm_nonneg _) (tyurinProductEnvelope_nonneg L u)
  exact hactual.trans
    (tyurinOuterIntegrand_le_certificate hU hu0 huU)

private theorem intervalIntegrable_tyurinCoreCertificate
    {n : ℕ} {L U₀ U : ℝ}
    (hn : 0 < n) (hL : 0 < L) (hU₀ : 0 < U₀)
    (hU : 0 < U) (hcut : U₀ ≤ U) :
    IntervalIntegrable
      (tyurinCoreTrapezoidCertificateIntegrand n L U)
      volume 0 U₀ := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hU₀.le]
  refine Measure.integrableOn_of_bounded
    (M := (513 / 500 : ℝ) * L * U₀ ^ 2 / 4)
    measure_Icc_lt_top.ne
    (measurable_tyurinCoreTrapezoidCertificateIntegrand
      n L U).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact tyurinCoreTrapezoidCertificateIntegrand_le
      hn hL hU₀ hU hcut hu.1 hu.2
  · exact tyurinCoreCertificate_nonneg
      hn hL hU hu.1 (hu.2.trans hcut)

theorem intervalIntegrable_tyurinCoreIntegrand
    {n : ℕ} {L U₀ U : ℝ}
    (hn : 0 < n) (hL : 0 < L) (hU₀ : 0 < U₀)
    (hU : 0 < U) (hcut : U₀ ≤ U) :
    IntervalIntegrable
      (fun u : ℝ =>
        ‖scaledPrawitzKernel U u‖ *
          min (tyurinDeltaOne L u) (tyurinDeltaTwo L u))
      volume 0 U₀ := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hU₀.le]
  refine Measure.integrableOn_of_bounded
    (M := (513 / 500 : ℝ) * L * U₀ ^ 2 / 4)
    measure_Icc_lt_top.ne
    (measurable_tyurinCoreIntegrand L U).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  have hactual0 :
      0 ≤ ‖scaledPrawitzKernel U u‖ *
          min (tyurinDeltaOne L u) (tyurinDeltaTwo L u) := by
    exact mul_nonneg (norm_nonneg _)
      (le_min (tyurinDeltaOne_nonneg hL.le)
        (tyurinDeltaTwo_nonneg hL))
  rw [Real.norm_eq_abs, abs_of_nonneg hactual0]
  exact (tyurinCoreIntegrand_le_trapezoidCertificate
      hn hL hU hu.1 (hu.2.trans hcut)).trans
    (tyurinCoreTrapezoidCertificateIntegrand_le
      hn hL hU₀ hU hcut hu.1 hu.2)

private theorem intervalIntegrable_tyurinOuterCertificate
    {L U₀ U : ℝ} (hL : 0 < L) (hU₀ : 0 < U₀)
    (hU : 0 < U) (hcut : U₀ ≤ U) :
    IntervalIntegrable
      (tyurinOuterCertificateIntegrand L U)
      volume U₀ U := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hcut]
  refine Measure.integrableOn_of_bounded
    (M := (513 / 500 : ℝ) / (2 * U₀) *
      Real.exp (2 * L * tyurinRationalA * U ^ 3))
    measure_Icc_lt_top.ne
    (measurable_tyurinOuterCertificateIntegrand
      L U).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact tyurinOuterCertificateIntegrand_le
      hL hU₀ hU hu.1 hu.2
  · exact tyurinOuterCertificate_nonneg
      hU (hU₀.trans_le hu.1) hu.2

theorem intervalIntegrable_tyurinOuterIntegrand
    {L U₀ U : ℝ} (hL : 0 < L) (hU₀ : 0 < U₀)
    (hU : 0 < U) (hcut : U₀ ≤ U) :
    IntervalIntegrable
      (fun u : ℝ =>
        ‖scaledPrawitzKernel U u‖ *
          tyurinProductEnvelope L u)
      volume U₀ U := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hcut]
  refine Measure.integrableOn_of_bounded
    (M := (513 / 500 : ℝ) / (2 * U₀) *
      Real.exp (2 * L * tyurinRationalA * U ^ 3))
    measure_Icc_lt_top.ne
    (measurable_tyurinOuterIntegrand L U).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  have hactual0 :
      0 ≤ ‖scaledPrawitzKernel U u‖ *
          tyurinProductEnvelope L u :=
    mul_nonneg (norm_nonneg _) (tyurinProductEnvelope_nonneg L u)
  rw [Real.norm_eq_abs, abs_of_nonneg hactual0]
  exact (tyurinOuterIntegrand_le_certificate
      hU (hU₀.trans_le hu.1) hu.2).trans
    (tyurinOuterCertificateIntegrand_le
      hL hU₀ hU hu.1 hu.2)

/--
Analytic D-star upper theorem.  All measurability, compact-interval
integrability, probabilistic estimates, and kernel inequalities are
discharged internally; callers supply only numerical parameter inequalities.
-/
theorem tyurinRationalDStar_le_certificateUpper
    {n : ℕ} {L U₀ U e : ℝ}
    (hn : 0 < n) (hL : 0 < L) (hU₀ : 0 < U₀)
    (hU : 0 < U) (hcut : U₀ ≤ U)
    (he0 : 0 ≤ e)
    (hexp : Real.exp (-(U₀ ^ 2) / 2) ≤ e) :
    tyurinRationalDStar L U₀ U ≤
      tyurinCertificateDStarUpper n L U₀ U e := by
  have hcoreActual :=
    intervalIntegrable_tyurinCoreIntegrand
      hn hL hU₀ hU hcut
  have hcoreCertificate :=
    intervalIntegrable_tyurinCoreCertificate
      hn hL hU₀ hU hcut
  have houterActual :=
    intervalIntegrable_tyurinOuterIntegrand
      hL hU₀ hU hcut
  have houterCertificate :=
    intervalIntegrable_tyurinOuterCertificate
      hL hU₀ hU hcut
  have hcore :
      (∫ u : ℝ in 0..U₀,
        ‖scaledPrawitzKernel U u‖ *
          min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)) ≤
        ∫ u : ℝ in 0..U₀,
          tyurinCoreTrapezoidCertificateIntegrand n L U u := by
    apply intervalIntegral.integral_mono_on hU₀.le
      hcoreActual hcoreCertificate
    intro u hu
    exact tyurinCoreIntegrand_le_trapezoidCertificate
      hn hL hU hu.1 (hu.2.trans hcut)
  have houter :
      (∫ u : ℝ in U₀..U,
        ‖scaledPrawitzKernel U u‖ *
          tyurinProductEnvelope L u) ≤
        ∫ u : ℝ in U₀..U,
          tyurinOuterCertificateIntegrand L U u := by
    apply intervalIntegral.integral_mono_on hcut
      houterActual houterCertificate
    intro u hu
    exact tyurinOuterIntegrand_le_certificate
      hU (hU₀.trans_le hu.1) hu.2
  unfold tyurinRationalDStar tyurinCertificateDStarUpper
  have hgaussian :=
    prawitzGaussianSharpClosedBudget_le_rational
      hU₀ hU he0 hexp
  apply (div_le_div_iff₀ hL hL).2
  nlinarith

/-! ## Contract canaries -/

example (n : ℕ) (L U u : ℝ) :
    tyurinCoreTrapezoidCertificateIntegrand n L U u =
      scaledPrawitzCertificateEnvelope U u *
        min (tyurinDeltaOneTrapezoidUpper n L u)
          (tyurinDeltaTwoTrapezoidUpper n L u) :=
  rfl

/--
This pins the assumption-free public interface.  It fails if compact
integrability is accidentally pushed back onto certificate callers.
-/
example
    {n : ℕ} {L U₀ U e : ℝ}
    (hn : 0 < n) (hL : 0 < L) (hU₀ : 0 < U₀)
    (hU : 0 < U) (hcut : U₀ ≤ U)
    (he0 : 0 ≤ e)
    (hexp : Real.exp (-(U₀ ^ 2) / 2) ≤ e) :
    tyurinRationalDStar L U₀ U ≤
      tyurinCertificateDStarUpper n L U₀ U e :=
  tyurinRationalDStar_le_certificateUpper
    hn hL hU₀ hU hcut he0 hexp

end Probability
end CertifiedJL
