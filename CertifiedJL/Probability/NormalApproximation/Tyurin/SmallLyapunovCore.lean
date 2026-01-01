/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.NormalApproximation.Tyurin.DStarCertificate
import CertifiedJL.Probability.NormalApproximation.Tyurin.ProductCertificate

/-!
# Tyurin's all-the-way-to-zero Lyapunov estimate

This module proves the small-Lyapunov part of the quantitative
Berry--Esseen estimate directly.  It does not appeal to Prawitz's separately
tabulated small-parameter estimate I.52.

For `0 < L ≤ 1/50`, put

* `R = L^(1/3)`,
* `A = 5/(3R)`, the endpoint of Tyurin's first `deltaTwo` branch, and
* `U = (157/50)/L`, the Prawitz bandwidth.

The proof splits the outer Fourier integral into the cubic bands
`[A,1/L]`, `[1/L,2/L]`, a uniformly damped cosine band, and the
endpoint-reflected cosine band.  Every transcendental estimate is reduced
to an exact Gaussian integral or to the elementary inequality
`x^n/n! ≤ exp x`.
-/

open MeasureTheory ProbabilityTheory Set

namespace CertifiedJL
namespace Probability

/-- The branch endpoint in the all-the-way-to-zero argument. -/
noncomputable def tyurinSmallBranchCutoff (L : ℝ) : ℝ :=
  5 / (3 * lyapunovThirdRoot L)

/-- The fixed Prawitz bandwidth used in the small-Lyapunov argument. -/
noncomputable def tyurinSmallBandwidth (L : ℝ) : ℝ :=
  (157 / 50 : ℝ) / L

theorem small_root_pos
    {L : ℝ} (hL : 0 < L) :
    0 < lyapunovThirdRoot L := by
  unfold lyapunovThirdRoot
  positivity

theorem small_root_le_three_tenths
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ 1 / 50) :
    lyapunovThirdRoot L ≤ 3 / 10 := by
  let R := lyapunovThirdRoot L
  have hR0 : 0 ≤ R := lyapunovThirdRoot_nonneg hL.le
  have hR3 : R ^ 3 = L := lyapunovThirdRoot_cube hL.le
  by_contra h
  have hgt : 3 / 10 < R := lt_of_not_ge h
  have hcubegt : (3 / 10 : ℝ) ^ 3 < R ^ 3 := by
    nlinarith [sq_nonneg (R - 3 / 10)]
  rw [hR3] at hcubegt
  norm_num at hcubegt hsmall
  linarith

private theorem small_variance_cap_le
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ 1 / 50) :
    lyapunovVarianceCap L ≤ 9 / 100 := by
  have hR :=
    small_root_le_three_tenths hL hsmall
  have hR0 := lyapunovThirdRoot_nonneg hL.le
  rw [← lyapunovThirdRoot_sq hL.le]
  nlinarith [sq_nonneg (lyapunovThirdRoot L - 3 / 10)]

theorem small_branchCutoff_pos
    {L : ℝ} (hL : 0 < L) :
    0 < tyurinSmallBranchCutoff L := by
  unfold tyurinSmallBranchCutoff
  exact div_pos (by norm_num)
    (mul_pos (by norm_num) (small_root_pos hL))

theorem small_bandwidth_pos
    {L : ℝ} (hL : 0 < L) :
    0 < tyurinSmallBandwidth L := by
  unfold tyurinSmallBandwidth
  positivity

private theorem small_branchCutoff_mul_root
    {L : ℝ} (hL : 0 < L) :
    tyurinSmallBranchCutoff L * lyapunovThirdRoot L = 5 / 3 := by
  unfold tyurinSmallBranchCutoff
  field_simp [(small_root_pos hL).ne']

theorem small_branchCutoff_le_inv
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ 1 / 50) :
    tyurinSmallBranchCutoff L ≤ 1 / L := by
  let R := lyapunovThirdRoot L
  have hR0 : 0 < R := small_root_pos hL
  have hR3 : R ^ 3 = L := lyapunovThirdRoot_cube hL.le
  have hR : R ≤ 3 / 10 :=
    small_root_le_three_tenths hL hsmall
  unfold tyurinSmallBranchCutoff
  dsimp only [R] at hR0 hR3 hR ⊢
  rw [div_le_div_iff₀ (by positivity : 0 < 3 * R) hL]
  rw [← hR3]
  have : R ^ 2 ≤ 9 / 100 := by
    nlinarith [sq_nonneg (R - 3 / 10)]
  nlinarith

theorem small_two_inv_le_bandwidth
    {L : ℝ} (hL : 0 < L) :
    2 / L ≤ tyurinSmallBandwidth L := by
  unfold tyurinSmallBandwidth
  apply div_le_div_of_nonneg_right (by norm_num) hL.le

private theorem small_branchCutoff_le_bandwidth
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ 1 / 50) :
    tyurinSmallBranchCutoff L ≤ tyurinSmallBandwidth L := by
  have honeTwo : 1 / L ≤ 2 / L := by
    exact div_le_div_of_nonneg_right (by norm_num) hL.le
  exact (small_branchCutoff_le_inv hL hsmall).trans
    (honeTwo.trans (small_two_inv_le_bandwidth hL))

private theorem small_bandwidth_lt_pi_div
    {L : ℝ} (hL : 0 < L) :
    tyurinSmallBandwidth L < Real.pi / L := by
  unfold tyurinSmallBandwidth
  exact div_lt_div_of_pos_right pi_gt_157_div_50 hL

/-! ## A reusable half-Gaussian second moment -/

private theorem integral_Ioi_sq_mul_exp_neg_half_sq :
    (∫ x : ℝ in Ioi 0, x ^ 2 * Real.exp (-(x ^ 2) / 2)) =
      Real.sqrt (2 * Real.pi) / 2 := by
  let f : ℝ → ℝ :=
    fun x => x ^ 2 * Real.exp (-(x ^ 2) / 2)
  have hf : Integrable f := by
    simpa only [f] using integrable_sq_mul_exp_neg_half_sq
  have heven (x : ℝ) : f (-x) = f x := by
    simp only [f, neg_sq]
  have hleft :
      (∫ x : ℝ in Iic 0, f x) =
        ∫ x : ℝ in Ioi 0, f x := by
    calc
      (∫ x : ℝ in Iic 0, f x) =
          ∫ x : ℝ in Iic 0, f (-x) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro x _
        exact (heven x).symm
      _ = ∫ x : ℝ in Ioi 0, f x := by
        simp
  have hsplit :=
    integral_add_compl (μ := volume) (s := Ioi (0 : ℝ))
      measurableSet_Ioi hf
  rw [compl_Ioi, hleft] at hsplit
  have hfull :
      (∫ x : ℝ, f x) = Real.sqrt (2 * Real.pi) := by
    simpa only [f] using integral_sq_mul_exp_neg_half_sq
  rw [hfull] at hsplit
  linarith

/--
The half-line second moment after an arbitrary positive linear rescaling.
This form avoids introducing the Gamma function into the small-L argument.
-/
private theorem integral_Ioi_sq_mul_exp_scaled
    {s : ℝ} (hs : 0 < s) :
    (∫ x : ℝ in Ioi 0,
        x ^ 2 * Real.exp (-((s * x) ^ 2) / 2)) =
      Real.sqrt (2 * Real.pi) / (2 * s ^ 3) := by
  let g : ℝ → ℝ :=
    fun y => y ^ 2 * Real.exp (-(y ^ 2) / 2)
  have hscale :=
    integral_comp_mul_left_Ioi g 0 hs
  have hrewrite :
      (fun x : ℝ => g (s * x)) =
        fun x => s ^ 2 *
          (x ^ 2 * Real.exp (-((s * x) ^ 2) / 2)) := by
    funext x
    dsimp only [g]
    ring_nf
  rw [hrewrite, integral_const_mul] at hscale
  have hsne : s ≠ 0 := hs.ne'
  dsimp only [g] at hscale
  rw [mul_zero, integral_Ioi_sq_mul_exp_neg_half_sq] at hscale
  have hscale' :
      s ^ 2 *
          (∫ x : ℝ in Ioi 0,
            x ^ 2 * Real.exp (-((s * x) ^ 2) / 2)) =
        s⁻¹ * (Real.sqrt (2 * Real.pi) / 2) := by
    simpa only [smul_eq_mul] using hscale
  apply (eq_div_iff (by positivity : 2 * s ^ 3 ≠ 0)).2
  calc
    (∫ x : ℝ in Ioi 0,
        x ^ 2 * Real.exp (-((s * x) ^ 2) / 2)) *
          (2 * s ^ 3) =
        2 * s *
          (s ^ 2 *
            ∫ x : ℝ in Ioi 0,
              x ^ 2 * Real.exp (-((s * x) ^ 2) / 2)) := by ring
    _ = 2 * s * (s⁻¹ * (Real.sqrt (2 * Real.pi) / 2)) := by
      rw [hscale']
    _ = Real.sqrt (2 * Real.pi) := by
      field_simp [hsne]

private theorem integral_Ioi_sq_exp_neg_nine_twentieth_le :
    (∫ x : ℝ in Ioi 0,
        x ^ 2 * Real.exp (-(9 / 20 : ℝ) * x ^ 2)) ≤
      (25100 / 1458 : ℝ) / 10 := by
  let s : ℝ := Real.sqrt (9 / 10)
  have hs : 0 < s := by
    dsimp only [s]
    positivity
  have hsSq : s ^ 2 = 9 / 10 := by
    dsimp only [s]
    rw [Real.sq_sqrt]
    norm_num
  have hsLower : 9 / 10 ≤ s := by
    dsimp only [s]
    have hs0 : 0 ≤ Real.sqrt (9 / 10) := Real.sqrt_nonneg _
    have hsSq' : Real.sqrt (9 / 10) ^ 2 = 9 / 10 := by
      rw [Real.sq_sqrt]
      norm_num
    nlinarith [sq_nonneg (Real.sqrt (9 / 10) - 9 / 10)]
  have hmoment := integral_Ioi_sq_mul_exp_scaled hs
  have hintegrand :
      (fun x : ℝ =>
        x ^ 2 * Real.exp (-(9 / 20 : ℝ) * x ^ 2)) =
      fun x => x ^ 2 * Real.exp (-((s * x) ^ 2) / 2) := by
    funext x
    congr 2
    rw [mul_pow, hsSq]
    ring
  rw [hintegrand, hmoment]
  have hsCube : (9 / 10 : ℝ) ^ 3 ≤ s ^ 3 := by
    nlinarith [sq_nonneg (s - 9 / 10)]
  have hsqrt :
      Real.sqrt (2 * Real.pi) < 251 / 100 :=
    sqrt_two_pi_lt_251_div_100
  apply le_of_lt
  rw [div_lt_iff₀ (by positivity : 0 < 2 * s ^ 3)]
  have : 0 < s ^ 3 := by positivity
  calc
    Real.sqrt (2 * Real.pi)
        < 251 / 100 := hsqrt
    _ ≤ ((25100 / 1458 : ℝ) / 10) *
          (2 * s ^ 3) := by
      calc
        (251 / 100 : ℝ) =
            ((25100 / 1458 : ℝ) / 10) *
              (2 * (9 / 10 : ℝ) ^ 3) := by norm_num
        _ ≤ ((25100 / 1458 : ℝ) / 10) *
              (2 * s ^ 3) := by gcongr

private theorem integrable_sq_exp_neg_nine_twentieth :
    Integrable
      (fun x : ℝ =>
        x ^ 2 * Real.exp (-(9 / 20 : ℝ) * x ^ 2)) := by
  have h :=
    integrable_rpow_mul_exp_neg_mul_sq
      (by norm_num : (0 : ℝ) < 9 / 20)
      (by norm_num : (-1 : ℝ) < 2)
  convert h using 1
  ext x
  rw [Real.rpow_two]

/-! ## The discrepancy core -/

private theorem small_core_pointwise
    {L u : ℝ} (hL : 0 < L) (hsmall : L ≤ 1 / 50)
    (hu0 : 0 ≤ u) (huA : u ≤ tyurinSmallBranchCutoff L) :
    ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
        min (tyurinDeltaOne L u) (tyurinDeltaTwo L u) ≤
      (513 / 500 : ℝ) * L / (12 * Real.pi) *
        (u ^ 2 * Real.exp (-(9 / 20 : ℝ) * u ^ 2)) := by
  by_cases hu : u = 0
  · subst u
    have hmin :
        min (tyurinDeltaOne L 0) (tyurinDeltaTwo L 0) = 0 := by
      rw [min_eq_left]
      · simp [tyurinDeltaOne]
      · simpa [tyurinDeltaOne] using
          tyurinDeltaTwo_nonneg (t := 0) hL
    simp [hmin]
  · have huPos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
    have hU : 0 < tyurinSmallBandwidth L :=
      small_bandwidth_pos hL
    have huU : |u| ≤ tyurinSmallBandwidth L := by
      rw [abs_of_pos huPos]
      exact huA.trans (small_branchCutoff_le_bandwidth hL hsmall)
    have hkernel :=
      norm_scaledPrawitzKernel_le_i29 hU hu huU
    have hbranch :
        |u| * lyapunovThirdRoot L ≤ 5 / 3 := by
      rw [abs_of_pos huPos]
      calc
        u * lyapunovThirdRoot L ≤
            tyurinSmallBranchCutoff L * lyapunovThirdRoot L := by
          gcongr
          exact lyapunovThirdRoot_nonneg hL.le
        _ = 5 / 3 := small_branchCutoff_mul_root hL
    have hdelta :=
      tyurinDeltaTwo_le_firstClosed hL.le hbranch
    have hcap := small_variance_cap_le hL hsmall
    have hexp :
        Real.exp
            (-((1 - lyapunovVarianceCap L) * |u| ^ 2) / 2) ≤
          Real.exp (-(9 / 20 : ℝ) * u ^ 2) := by
      apply Real.exp_le_exp.mpr
      rw [abs_of_pos huPos]
      have hfactor :
          0 ≤ (1 / 10 - lyapunovVarianceCap L) * u ^ 2 :=
        mul_nonneg (by nlinarith) (sq_nonneg u)
      nlinarith
    have hdeltaClosed :
        tyurinDeltaTwo L u ≤
          L * u ^ 3 / 6 *
            Real.exp (-(9 / 20 : ℝ) * u ^ 2) := by
      calc
        tyurinDeltaTwo L u ≤
            L * |u| ^ 3 / 6 *
              Real.exp
                (-((1 - lyapunovVarianceCap L) * |u| ^ 2) / 2) :=
          hdelta
        _ ≤ L * u ^ 3 / 6 *
              Real.exp (-(9 / 20 : ℝ) * u ^ 2) := by
          rw [abs_of_pos huPos]
          have hexp' :
              Real.exp
                  (-((1 - lyapunovVarianceCap L) * u ^ 2) / 2) ≤
                Real.exp (-(9 / 20 : ℝ) * u ^ 2) := by
            simpa [abs_of_pos huPos] using hexp
          exact mul_le_mul_of_nonneg_left hexp' (by positivity)
    have hdelta0 : 0 ≤ tyurinDeltaTwo L u :=
      tyurinDeltaTwo_nonneg hL
    have hmin :
        min (tyurinDeltaOne L u) (tyurinDeltaTwo L u) ≤
          tyurinDeltaTwo L u :=
      min_le_right _ _
    calc
      ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
          min (tyurinDeltaOne L u) (tyurinDeltaTwo L u) ≤
        ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
          tyurinDeltaTwo L u := by
            gcongr
      _ ≤ scaledPrawitzI29Envelope u *
          tyurinDeltaTwo L u := by
            exact mul_le_mul_of_nonneg_right hkernel hdelta0
      _ ≤ scaledPrawitzI29Envelope u *
          (L * u ^ 3 / 6 *
            Real.exp (-(9 / 20 : ℝ) * u ^ 2)) := by
            apply mul_le_mul_of_nonneg_left hdeltaClosed
            unfold scaledPrawitzI29Envelope
            positivity
      _ = (513 / 500 : ℝ) * L / (12 * Real.pi) *
          (u ^ 2 * Real.exp (-(9 / 20 : ℝ) * u ^ 2)) := by
            unfold scaledPrawitzI29Envelope
            rw [abs_of_pos huPos]
            field_simp [Real.pi_ne_zero, hu]
            ring

/--
The normalized Prawitz discrepancy core costs less than `19/200` in the
small-Lyapunov regime.
-/
theorem tyurinSmall_core_normalized_lt
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ 1 / 50) :
    (2 * (∫ u : ℝ in 0..tyurinSmallBranchCutoff L,
      ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
        min (tyurinDeltaOne L u) (tyurinDeltaTwo L u))) / L <
      19 / 200 := by
  let A := tyurinSmallBranchCutoff L
  let U := tyurinSmallBandwidth L
  let f : ℝ → ℝ := fun u =>
    (513 / 500 : ℝ) * L / (12 * Real.pi) *
      (u ^ 2 * Real.exp (-(9 / 20 : ℝ) * u ^ 2))
  have hA : 0 < A := small_branchCutoff_pos hL
  have hU : 0 < U := small_bandwidth_pos hL
  have hAU : A ≤ U := small_branchCutoff_le_bandwidth hL hsmall
  have hactualInt :=
    intervalIntegrable_tyurinCoreIntegrand
      (n := 1) (L := L) (U₀ := A) (U := U)
      (by norm_num) hL hA hU hAU
  have hfInt : IntervalIntegrable f volume 0 A := by
    exact
      ((integrable_sq_exp_neg_nine_twentieth.const_mul
        ((513 / 500 : ℝ) * L / (12 * Real.pi))).integrableOn
        |>.intervalIntegrable)
  have hcore :
      (∫ u : ℝ in 0..A,
        ‖scaledPrawitzKernel U u‖ *
          min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)) ≤
        ∫ u : ℝ in 0..A, f u := by
    apply intervalIntegral.integral_mono_on hA.le hactualInt hfInt
    intro u hu
    exact small_core_pointwise hL hsmall hu.1 hu.2
  have hfNonneg : ∀ u, 0 ≤ f u := by
    intro u
    dsimp only [f]
    positivity
  have hset :
      (∫ u : ℝ in 0..A, f u) ≤
        ∫ u : ℝ in Ioi 0, f u := by
    rw [intervalIntegral.integral_of_le hA.le]
    apply setIntegral_mono_set
      ((integrable_sq_exp_neg_nine_twentieth.const_mul
        ((513 / 500 : ℝ) * L / (12 * Real.pi))).integrableOn)
      (ae_of_all _ hfNonneg)
    exact ae_of_all _ fun u hu => Ioc_subset_Ioi_self hu
  have hmoment :=
    integral_Ioi_sq_exp_neg_nine_twentieth_le
  have hpiInv :
      1 / Real.pi < (50 / 157 : ℝ) := by
    rw [div_lt_iff₀ Real.pi_pos]
    nlinarith [pi_gt_157_div_50]
  have hfIoi :
      (∫ u : ℝ in Ioi 0, f u) <
        L * (19 / 400 : ℝ) := by
    rw [show (∫ u : ℝ in Ioi 0, f u) =
        ((513 / 500 : ℝ) * L / (12 * Real.pi)) *
          ∫ u : ℝ in Ioi 0,
            u ^ 2 * Real.exp (-(9 / 20 : ℝ) * u ^ 2) by
      rw [← MeasureTheory.integral_const_mul]
      ]
    have hcoeff :
        (513 / 500 : ℝ) * L / (12 * Real.pi) <
          (513 / 500 : ℝ) * L / 12 * (50 / 157) := by
      have hpos : 0 < (513 / 500 : ℝ) * L / 12 := by positivity
      rw [show (513 / 500 : ℝ) * L / (12 * Real.pi) =
          ((513 / 500 : ℝ) * L / 12) * (1 / Real.pi) by
        field_simp [Real.pi_ne_zero]
        ]
      exact mul_lt_mul_of_pos_left hpiInv hpos
    have hmoment0 :
        0 ≤ ∫ u : ℝ in Ioi 0,
          u ^ 2 * Real.exp (-(9 / 20 : ℝ) * u ^ 2) := by
      apply setIntegral_nonneg
      · exact measurableSet_Ioi
      intro u _
      positivity
    have hmomentPos :
        0 < ∫ u : ℝ in Ioi 0,
          u ^ 2 * Real.exp (-(9 / 20 : ℝ) * u ^ 2) := by
      let s : ℝ := Real.sqrt (9 / 10)
      have hs : 0 < s := by
        dsimp only [s]
        positivity
      have hsSq : s ^ 2 = 9 / 10 := by
        dsimp only [s]
        rw [Real.sq_sqrt]
        norm_num
      rw [show (fun u : ℝ =>
          u ^ 2 * Real.exp (-(9 / 20 : ℝ) * u ^ 2)) =
          fun u => u ^ 2 * Real.exp (-((s * u) ^ 2) / 2) by
        funext u
        congr 2
        rw [mul_pow, hsSq]
        ring]
      rw [integral_Ioi_sq_mul_exp_scaled hs]
      positivity
    calc
      ((513 / 500 : ℝ) * L / (12 * Real.pi)) *
          (∫ u : ℝ in Ioi 0,
            u ^ 2 * Real.exp (-(9 / 20 : ℝ) * u ^ 2))
          < ((513 / 500 : ℝ) * L / 12 * (50 / 157)) *
              (∫ u : ℝ in Ioi 0,
                u ^ 2 * Real.exp (-(9 / 20 : ℝ) * u ^ 2)) := by
            exact mul_lt_mul_of_pos_right hcoeff
              hmomentPos
      _ ≤ ((513 / 500 : ℝ) * L / 12 * (50 / 157)) *
              ((25100 / 1458 : ℝ) / 10) := by
            gcongr
      _ < L * (19 / 400 : ℝ) := by
            have : 0 < L := hL
            norm_num
            nlinarith
  have hcore' :
      (∫ u : ℝ in 0..A,
        ‖scaledPrawitzKernel U u‖ *
          min (tyurinDeltaOne L u) (tyurinDeltaTwo L u)) <
        L * (19 / 400 : ℝ) :=
    hcore.trans_lt (hset.trans_lt hfIoi)
  dsimp only [A, U] at hcore' ⊢
  rw [div_lt_iff₀ hL]
  nlinarith

/-! ## The closed Gaussian terms -/

theorem exp_neg_le_six_div_cube
    {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ 6 / x ^ 3 := by
  have hTaylor :=
    Real.pow_div_factorial_le_exp x hx.le 3
  norm_num at hTaylor
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_le_div_iff₀ (Real.exp_pos x)
    (by positivity : 0 < x ^ 3)).2
  nlinarith

/--
The sharp closed Gaussian budget is no larger than the weighted budget once
the bandwidth is at least one.  This is the explicit composition bridge
between `tyurinRationalDStar` and the small-L certificate.
-/
theorem prawitzGaussianSharpClosedBudget_le_weighted
    {U₀ U : ℝ} (hU : 1 ≤ U) :
    prawitzGaussianSharpClosedBudget U₀ U ≤
      prawitzGaussianWeightedClosedBudget U₀ U := by
  have hU0 : 0 < U := one_pos.trans_le hU
  have hsqrt :
      Real.sqrt (2 * Real.pi) ≤ (251 / 100 : ℝ) :=
    sqrt_two_pi_lt_251_div_100.le
  have hthird :
      Real.pi ^ 2 * Real.sqrt (2 * Real.pi) /
          (36 * U ^ 3) ≤
        (37 / 96 : ℝ) * Real.pi ^ 2 / U ^ 2 := by
    have hsqrtU :
        Real.sqrt (2 * Real.pi) ≤ (111 / 8 : ℝ) * U := by
      calc
        Real.sqrt (2 * Real.pi) ≤ 251 / 100 := hsqrt
        _ ≤ (111 / 8 : ℝ) * U := by
          nlinarith
    have hsmall :
        Real.sqrt (2 * Real.pi) / (36 * U) ≤ 37 / 96 := by
      rw [div_le_iff₀ (by positivity : 0 < 36 * U)]
      nlinarith
    calc
      Real.pi ^ 2 * Real.sqrt (2 * Real.pi) /
          (36 * U ^ 3) =
        (Real.pi ^ 2 / U ^ 2) *
          (Real.sqrt (2 * Real.pi) / (36 * U)) := by
        field_simp [hU0.ne', Real.pi_ne_zero]
      _ ≤ (Real.pi ^ 2 / U ^ 2) * (37 / 96) := by
        gcongr
      _ = (37 / 96 : ℝ) * Real.pi ^ 2 / U ^ 2 := by ring
  unfold prawitzGaussianSharpClosedBudget
    prawitzGaussianSharpCoreBudget
    prawitzGaussianWeightedClosedBudget
  have hnegative :
      -(1 - Real.exp (-(U₀ ^ 2) / 2)) / U ^ 2 ≤ 0 := by
    have hexp : Real.exp (-(U₀ ^ 2) / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg U₀]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg U)
  have hlead :
      Real.sqrt (2 * Real.pi) / (2 * U) -
          (1 - Real.exp (-(U₀ ^ 2) / 2)) / U ^ 2 ≤
        Real.sqrt (2 * Real.pi) / (2 * U) + 0 := by
    calc
      Real.sqrt (2 * Real.pi) / (2 * U) -
            (1 - Real.exp (-(U₀ ^ 2) / 2)) / U ^ 2 =
          Real.sqrt (2 * Real.pi) / (2 * U) +
            (-(1 - Real.exp (-(U₀ ^ 2) / 2)) / U ^ 2) := by ring
      _ ≤ Real.sqrt (2 * Real.pi) / (2 * U) + 0 :=
        by
          simpa [add_comm] using
            add_le_add_right hnegative
              (Real.sqrt (2 * Real.pi) / (2 * U))
  calc
    Real.sqrt (2 * Real.pi) / (2 * U) -
          (1 - Real.exp (-(U₀ ^ 2) / 2)) / U ^ 2 +
          Real.pi ^ 2 * Real.sqrt (2 * Real.pi) / (36 * U ^ 3) +
          Real.exp (-(U₀ ^ 2) / 2) / (Real.pi * U₀ ^ 2)
        ≤ Real.sqrt (2 * Real.pi) / (2 * U) + 0 +
          ((37 / 96 : ℝ) * Real.pi ^ 2 / U ^ 2) +
          Real.exp (-(U₀ ^ 2) / 2) / (Real.pi * U₀ ^ 2) := by
      exact add_le_add
        (add_le_add
          hlead
          hthird)
        le_rfl
    _ = Real.sqrt (2 * Real.pi) / (2 * U) +
          (37 / 96 : ℝ) * Real.pi ^ 2 / U ^ 2 +
          Real.exp (-(U₀ ^ 2) / 2) / (Real.pi * U₀ ^ 2) := by ring

theorem tyurinRationalDStar_le_small
    {L U₀ U : ℝ} (hL : 0 < L) (hU : 1 ≤ U) :
    tyurinRationalDStar L U₀ U ≤
      tyurinSmallRationalDStar L U₀ U := by
  unfold tyurinRationalDStar tyurinSmallRationalDStar
  exact div_le_div_of_nonneg_right
    (add_le_add_right
      (prawitzGaussianSharpClosedBudget_le_weighted hU) _)
    hL.le

theorem one_le_tyurinSmallBandwidth
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ 1 / 50) :
    1 ≤ tyurinSmallBandwidth L := by
  unfold tyurinSmallBandwidth
  rw [le_div_iff₀ hL]
  norm_num at hsmall ⊢
  linarith

private theorem small_gaussian_tail_normalized_lt
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ 1 / 50) :
    Real.exp (-(tyurinSmallBranchCutoff L ^ 2) / 2) /
          (Real.pi * tyurinSmallBranchCutoff L ^ 2) / L <
      1 / 1000 := by
  let R := lyapunovThirdRoot L
  have hR : 0 < R := small_root_pos hL
  have hRle : R ≤ 3 / 10 :=
    small_root_le_three_tenths hL hsmall
  have hR3 : R ^ 3 = L := lyapunovThirdRoot_cube hL.le
  have hA :
      tyurinSmallBranchCutoff L ^ 2 = 25 / (9 * R ^ 2) := by
    unfold tyurinSmallBranchCutoff
    dsimp only [R]
    field_simp [hR.ne']
    ring
  have hx : 0 < 25 / (18 * R ^ 2) := by positivity
  have hexp :
      Real.exp (-(tyurinSmallBranchCutoff L ^ 2) / 2) ≤
        6 / (25 / (18 * R ^ 2)) ^ 3 := by
    rw [hA]
    convert exp_neg_le_six_div_cube hx using 1
    ring_nf
  have hinvPi :
      1 / Real.pi < (50 / 157 : ℝ) := by
    rw [div_lt_iff₀ Real.pi_pos]
    nlinarith [pi_gt_157_div_50]
  have hexp0 :
      0 ≤ Real.exp (-(tyurinSmallBranchCutoff L ^ 2) / 2) :=
    Real.exp_nonneg _
  rw [hA, ← hR3]
  have hidentity :
      Real.exp (-(25 / (9 * R ^ 2)) / 2) /
            (Real.pi * (25 / (9 * R ^ 2))) / R ^ 3 =
        Real.exp (-(25 / (9 * R ^ 2)) / 2) *
          (1 / Real.pi) * (9 / (25 * R)) := by
    field_simp [Real.pi_ne_zero, hR.ne']
  rw [hidentity]
  have hexp' :
      Real.exp (-(25 / (9 * R ^ 2)) / 2) ≤
        6 / (25 / (18 * R ^ 2)) ^ 3 := by
    simpa [hA] using hexp
  calc
    Real.exp (-(25 / (9 * R ^ 2)) / 2) *
          (1 / Real.pi) * (9 / (25 * R))
        < (6 / (25 / (18 * R ^ 2)) ^ 3) *
            (50 / 157) * (9 / (25 * R)) := by
      have hlast : 0 < 9 / (25 * R) := by positivity
      have hfirst :
          Real.exp (-(25 / (9 * R ^ 2)) / 2) *
              (1 / Real.pi) <
            (6 / (25 / (18 * R ^ 2)) ^ 3) *
              (50 / 157) := by
        calc
          Real.exp (-(25 / (9 * R ^ 2)) / 2) *
                (1 / Real.pi) ≤
              (6 / (25 / (18 * R ^ 2)) ^ 3) *
                (1 / Real.pi) := by
            gcongr
          _ < (6 / (25 / (18 * R ^ 2)) ^ 3) *
                (50 / 157) := by
            exact mul_lt_mul_of_pos_left hinvPi (by positivity)
      exact mul_lt_mul_of_pos_right hfirst hlast
    _ = (6 * (18 / 25 : ℝ) ^ 3 * (50 / 157) *
          (9 / 25)) * R ^ 5 := by
      field_simp [hR.ne']
    _ ≤ (6 * (18 / 25 : ℝ) ^ 3 * (50 / 157) *
          (9 / 25)) * (3 / 10 : ℝ) ^ 5 := by
      gcongr
    _ < 1 / 1000 := by norm_num

/--
The normalized weighted Gaussian contribution costs less than `409/1000`.
-/
theorem tyurinSmall_gaussian_normalized_lt
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ 1 / 50) :
    prawitzGaussianWeightedClosedBudget
        (tyurinSmallBranchCutoff L) (tyurinSmallBandwidth L) / L <
      409 / 1000 := by
  have hsqrt :
      Real.sqrt (2 * Real.pi) < (251 / 100 : ℝ) :=
    sqrt_two_pi_lt_251_div_100
  have hpi :
      Real.pi < (63 / 20 : ℝ) :=
    pi_lt_63_div_20
  have htermOne :
      Real.sqrt (2 * Real.pi) /
            (2 * tyurinSmallBandwidth L) / L <
        2 / 5 := by
    unfold tyurinSmallBandwidth
    field_simp [hL.ne']
    nlinarith
  have htermTwo :
      (37 / 96 : ℝ) * Real.pi ^ 2 /
            tyurinSmallBandwidth L ^ 2 / L <
        1 / 125 := by
    have hpiSq :
        Real.pi ^ 2 < (63 / 20 : ℝ) ^ 2 :=
      (sq_lt_sq₀ Real.pi_pos.le (by norm_num)).2 hpi
    unfold tyurinSmallBandwidth
    field_simp [hL.ne']
    have hL0 : 0 < L := hL
    nlinarith
  have htail :=
    small_gaussian_tail_normalized_lt hL hsmall
  unfold prawitzGaussianWeightedClosedBudget
  rw [show
      (Real.sqrt (2 * Real.pi) / (2 * tyurinSmallBandwidth L) +
          (37 / 96 : ℝ) * Real.pi ^ 2 / tyurinSmallBandwidth L ^ 2 +
          Real.exp (-(tyurinSmallBranchCutoff L ^ 2) / 2) /
            (Real.pi * tyurinSmallBranchCutoff L ^ 2)) / L =
        Real.sqrt (2 * Real.pi) /
            (2 * tyurinSmallBandwidth L) / L +
          (37 / 96 : ℝ) * Real.pi ^ 2 /
            tyurinSmallBandwidth L ^ 2 / L +
          Real.exp (-(tyurinSmallBranchCutoff L ^ 2) / 2) /
            (Real.pi * tyurinSmallBranchCutoff L ^ 2) / L by ring]
  nlinarith

end Probability
end CertifiedJL
