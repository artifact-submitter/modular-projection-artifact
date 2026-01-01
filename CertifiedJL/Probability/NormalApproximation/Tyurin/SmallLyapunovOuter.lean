/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.NormalApproximation.Tyurin.SmallLyapunovCore

/-!
# Outer Fourier bands in Tyurin's small-Lyapunov estimate

This module controls the part of the Prawitz integral beyond Tyurin's
first-branch cutoff.  It treats two cubic bands, a uniformly damped cosine
band, and the endpoint-reflected cosine band separately.  The split makes
the two distinct mechanisms visible: Gaussian decay away from the endpoint
and cancellation between the vanishing Prawitz kernel and the returning
characteristic-function envelope at the endpoint.
-/

open MeasureTheory ProbabilityTheory Set

namespace CertifiedJL
namespace Probability

/-! ## Product-envelope bands -/

private theorem intervalIntegral_le_Ioi
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntegrableOn f (Ioi a))
    (hnonneg : ∀ x, 0 ≤ f x) :
    (∫ x : ℝ in a..b, f x) ≤ ∫ x : ℝ in Ioi a, f x := by
  rw [intervalIntegral.integral_of_le hab]
  apply setIntegral_mono_set hf
    (ae_of_all _ fun x => hnonneg x)
  exact ae_of_all _ fun _ hx => Ioc_subset_Ioi_self hx

private theorem small_product_le_firstBand
    {L u : ℝ} (hL : 0 < L) (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / L) :
    tyurinProductEnvelope L u ≤
      Real.exp (-(3 / 10 : ℝ) * u ^ 2) := by
  have hLu : L * u ≤ 1 := by
    simpa [mul_comm] using (le_div_iff₀ hL).mp hu
  have hbranch : 2 * L * |u| < tyurinRationalM := by
    rw [abs_of_nonneg hu0]
    unfold tyurinRationalM
    nlinarith
  rw [tyurinProductEnvelope, tyurinB, if_pos hbranch]
  apply Real.exp_le_exp.mpr
  rw [abs_of_nonneg hu0]
  unfold tyurinRationalA
  have hscaled : 0 ≤ (1 - L * u) * u ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg u)
  nlinarith

private theorem small_product_le_secondBand_of_lt
    {L u : ℝ} (hL : 0 < L) (hu0 : 0 ≤ u)
    (hu : u < 2 / L) :
    tyurinProductEnvelope L u ≤
      Real.exp (-(9 / 100 : ℝ) * u ^ 2) := by
  have hLu : L * u < 2 := by
    simpa [mul_comm] using (lt_div_iff₀ hL).mp hu
  have hbranch : 2 * L * |u| < tyurinRationalM := by
    rw [abs_of_nonneg hu0]
    unfold tyurinRationalM
    nlinarith
  rw [tyurinProductEnvelope, tyurinB, if_pos hbranch]
  apply Real.exp_le_exp.mpr
  rw [abs_of_nonneg hu0]
  unfold tyurinRationalA
  have hscaled : 0 ≤ (2 - L * u) * u ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg u)
  nlinarith

private theorem rationalCosineLower_ge_two_fifths
    {x : ℝ} (hx0 : 4 ≤ x) (hx1 : x ≤ 189 / 40) :
    2 / 5 ≤ tyurinRationalCosineLower x := by
  unfold tyurinRationalCosineLower
  split_ifs with hfirst hmiddle
  · have hy0 : 0 ≤ x - 157 / 50 := by
      norm_num at hx0 ⊢
      linarith
    have hy : x - 157 / 50 ≤ 317 / 200 := by
      linarith
    have hsq :
        (x - 157 / 50) ^ 2 ≤ (317 / 200 : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (x - 157 / 50)]
    nlinarith
  · norm_num
  · have hx : x = 189 / 40 := by
      exact le_antisymm hx1 (le_of_not_gt hmiddle)
    rw [hx]
    norm_num

private theorem small_product_le_middleBand
    {L u : ℝ} (hL : 0 < L) (hu0 : 0 ≤ u)
    (hleft : 2 / L ≤ u) (hright : u ≤ 189 / (80 * L)) :
    tyurinProductEnvelope L u ≤
      Real.exp (-(49 / 500 : ℝ) / L ^ 2) := by
  have hx0 : 4 ≤ 2 * L * u := by
    rw [div_le_iff₀ hL] at hleft
    nlinarith
  have hx1 : 2 * L * u ≤ 189 / 40 := by
    rw [le_div_iff₀ (mul_pos (by norm_num) hL)] at hright
    nlinarith
  have hxU : 2 * L * u ≤ 157 / 25 := by
    norm_num at hx1 ⊢
    linarith
  have hbranch0 :
      ¬(2 * L * |u| < tyurinRationalM) := by
    rw [abs_of_nonneg hu0]
    unfold tyurinRationalM
    linarith
  have hbranch1 :
      2 * L * |u| ≤ 2 * Real.pi := by
    rw [abs_of_nonneg hu0]
    nlinarith [pi_gt_157_div_50]
  have hlowerCos :=
    tyurinRationalCosineLower_le_one_sub_cos hx0 hxU
  have hlowerRat :=
    rationalCosineLower_ge_two_fifths hx0 hx1
  have hlower :
      (2 / 5 : ℝ) ≤ 1 - Real.cos (2 * L * u) :=
    hlowerRat.trans hlowerCos
  rw [tyurinProductEnvelope, tyurinB, if_neg hbranch0,
    if_pos hbranch1]
  apply Real.exp_le_exp.mpr
  have hfactor :
      0 ≤ tyurinCosineLoss / (4 * L ^ 2) := by
    unfold tyurinCosineLoss
    positivity
  have hscaled :=
    mul_le_mul_of_nonneg_left hlower hfactor
  have hmain :
      (49 / 500 : ℝ) / L ^ 2 ≤
        tyurinCosineLoss / (4 * L ^ 2) *
          (1 - Real.cos (2 * L * u)) := by
    calc
      (49 / 500 : ℝ) / L ^ 2 =
          tyurinCosineLoss / (4 * L ^ 2) * (2 / 5) := by
        unfold tyurinCosineLoss
        field_simp [hL.ne']
        norm_num
      _ ≤ _ := hscaled
  calc
    -2 * tyurinCosineLoss / (2 * L) ^ 2 *
          (1 - Real.cos (2 * L * u)) / 2 =
        -(tyurinCosineLoss / (4 * L ^ 2) *
          (1 - Real.cos (2 * L * u))) := by
      field_simp [hL.ne']
      ring
    _ ≤ -((49 / 500 : ℝ) / L ^ 2) := neg_le_neg hmain
    _ = -(49 / 500 : ℝ) / L ^ 2 := by ring

private theorem rationalCosineLower_endpoint_quadratic
    {x : ℝ} (hx0 : 189 / 40 ≤ x) (hx1 : x ≤ 157 / 25) :
    (3 / 8 : ℝ) * (157 / 25 - x) ^ 2 ≤
      tyurinRationalCosineLower x := by
  have hfirst : ¬x ≤ 471 / 100 := by
    norm_num at hx0 ⊢
    linarith
  have hmiddle : ¬x < 189 / 40 := not_lt.mpr hx0
  rw [tyurinRationalCosineLower, if_neg hfirst, if_neg hmiddle]
  let z : ℝ := 157 / 25 - x
  have hz0 : 0 ≤ z := by
    dsimp only [z]
    linarith
  have hz : z ≤ 8 / 5 := by
    dsimp only [z]
    norm_num at hx0 ⊢
    linarith
  have hzsq : z ^ 2 ≤ (8 / 5 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg z]
  dsimp only [z] at *
  have hnonneg :
      0 ≤ (157 / 25 - x) ^ 2 *
        (1 / 8 - (157 / 25 - x) ^ 2 / 24) := by
    have : 0 ≤ 1 / 8 - (157 / 25 - x) ^ 2 / 24 := by
      nlinarith
    positivity
  nlinarith [sq_nonneg (157 / 25 - x)]

private theorem small_product_le_endpointBand
    {L u : ℝ} (hL : 0 < L) (hu0 : 0 ≤ u)
    (hleft : 189 / (80 * L) ≤ u)
    (hright : u ≤ tyurinSmallBandwidth L) :
    tyurinProductEnvelope L u ≤
      Real.exp
        (-(147 / 400 : ℝ) *
          (tyurinSmallBandwidth L - u) ^ 2) := by
  have hx0 : 189 / 40 ≤ 2 * L * u := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hL)] at hleft
    nlinarith
  have hx1 : 2 * L * u ≤ 157 / 25 := by
    unfold tyurinSmallBandwidth at hright
    rw [le_div_iff₀ hL] at hright
    nlinarith
  have hxFour : 4 ≤ 2 * L * u := by
    norm_num at hx0 ⊢
    linarith
  have hbranch0 :
      ¬(2 * L * |u| < tyurinRationalM) := by
    rw [abs_of_nonneg hu0]
    unfold tyurinRationalM
    linarith
  have hbranch1 :
      2 * L * |u| ≤ 2 * Real.pi := by
    rw [abs_of_nonneg hu0]
    nlinarith [pi_gt_157_div_50]
  have hlowerCos :=
    tyurinRationalCosineLower_le_one_sub_cos hxFour hx1
  have hlowerRat :=
    rationalCosineLower_endpoint_quadratic hx0 hx1
  have hlower :
      (3 / 8 : ℝ) * (157 / 25 - 2 * L * u) ^ 2 ≤
        1 - Real.cos (2 * L * u) :=
    hlowerRat.trans hlowerCos
  have hgap :
      157 / 25 - 2 * L * u =
        2 * L * (tyurinSmallBandwidth L - u) := by
    unfold tyurinSmallBandwidth
    field_simp [hL.ne']
    ring_nf
  rw [tyurinProductEnvelope, tyurinB, if_neg hbranch0,
    if_pos hbranch1]
  apply Real.exp_le_exp.mpr
  rw [hgap] at hlower
  have hfactor : 0 < tyurinCosineLoss / (4 * L ^ 2) := by
    unfold tyurinCosineLoss
    positivity
  have hscaled :=
    mul_le_mul_of_nonneg_left hlower hfactor.le
  calc
    -2 * tyurinCosineLoss / (2 * L) ^ 2 *
          (1 - Real.cos (2 * L * u)) / 2 =
        -(tyurinCosineLoss / (4 * L ^ 2) *
          (1 - Real.cos (2 * L * u))) := by
      field_simp [hL.ne']
      ring_nf
    _ ≤ -(tyurinCosineLoss / (4 * L ^ 2) *
          ((3 / 8 : ℝ) *
            (2 * L * (tyurinSmallBandwidth L - u)) ^ 2)) :=
      neg_le_neg hscaled
    _ = -(147 / 400 : ℝ) *
          (tyurinSmallBandwidth L - u) ^ 2 := by
      unfold tyurinCosineLoss
      field_simp [hL.ne']
      ring

/-! ## Integrating the first three outer bands -/

private theorem small_outer_actual_intervalIntegrable
    {L a b : ℝ} (hL : 0 < L)
    (hA : tyurinSmallBranchCutoff L ≤ a) (hab : a ≤ b)
    (hbU : b ≤ tyurinSmallBandwidth L) :
    IntervalIntegrable
      (fun u : ℝ =>
        ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
          tyurinProductEnvelope L u)
      volume a b := by
  have hA0 : 0 < tyurinSmallBranchCutoff L :=
    small_branchCutoff_pos hL
  have hU0 : 0 < tyurinSmallBandwidth L :=
    small_bandwidth_pos hL
  have hAU : tyurinSmallBranchCutoff L ≤ tyurinSmallBandwidth L :=
    hA.trans (hab.trans hbU)
  have hfull :=
    intervalIntegrable_tyurinOuterIntegrand
      (L := L) (U₀ := tyurinSmallBranchCutoff L)
      (U := tyurinSmallBandwidth L) hL hA0 hU0 hAU
  apply hfull.mono_set
  rw [uIcc_of_le hab, uIcc_of_le hAU]
  exact Icc_subset_Icc hA hbU

private theorem small_outer_first_pointwise
    {L u : ℝ} (hL : 0 < L)
    (huA : tyurinSmallBranchCutoff L ≤ u) (hu : u ≤ 1 / L) :
    ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
        tyurinProductEnvelope L u ≤
      ((513 / 500 : ℝ) /
          (2 * Real.pi * tyurinSmallBranchCutoff L)) *
        Real.exp (-(3 / 10 : ℝ) * u ^ 2) := by
  have hA0 := small_branchCutoff_pos hL
  have hu0 : 0 ≤ u := hA0.le.trans huA
  have huU :
      |u| ≤ tyurinSmallBandwidth L := by
    rw [abs_of_nonneg hu0]
    exact hu.trans
      ((by
        exact (div_le_div_of_nonneg_right (by norm_num) hL.le).trans
          (small_two_inv_le_bandwidth hL)) :
        1 / L ≤ tyurinSmallBandwidth L)
  have hkernel :=
    norm_scaledPrawitzKernel_le_i29
      (small_bandwidth_pos hL) (ne_of_gt (hA0.trans_le huA)) huU
  have hkernelA :
      scaledPrawitzI29Envelope u ≤
        (513 / 500 : ℝ) /
          (2 * Real.pi * tyurinSmallBranchCutoff L) := by
    unfold scaledPrawitzI29Envelope
    rw [abs_of_pos (hA0.trans_le huA)]
    exact div_le_div_of_nonneg_left (by norm_num)
      (by positivity)
      (mul_le_mul_of_nonneg_left huA
        (mul_nonneg (by norm_num) Real.pi_pos.le))
  have hproduct :=
    small_product_le_firstBand hL hu0 hu
  calc
    ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
          tyurinProductEnvelope L u ≤
        scaledPrawitzI29Envelope u *
          tyurinProductEnvelope L u :=
      mul_le_mul_of_nonneg_right hkernel
        (tyurinProductEnvelope_nonneg L u)
    _ ≤ scaledPrawitzI29Envelope u *
          Real.exp (-(3 / 10 : ℝ) * u ^ 2) := by
      apply mul_le_mul_of_nonneg_left hproduct
      unfold scaledPrawitzI29Envelope
      positivity
    _ ≤ ((513 / 500 : ℝ) /
          (2 * Real.pi * tyurinSmallBranchCutoff L)) *
        Real.exp (-(3 / 10 : ℝ) * u ^ 2) :=
      mul_le_mul_of_nonneg_right hkernelA (Real.exp_nonneg _)

theorem tyurinSmall_outer_first_normalized_lt
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ 1 / 50) :
    (2 * (∫ u : ℝ in tyurinSmallBranchCutoff L..1 / L,
      ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
        tyurinProductEnvelope L u)) / L <
      1 / 200 := by
  let R := lyapunovThirdRoot L
  let A := tyurinSmallBranchCutoff L
  let g : ℝ → ℝ := fun u =>
    ((513 / 500 : ℝ) / (2 * Real.pi * A)) *
      Real.exp (-(3 / 10 : ℝ) * u ^ 2)
  have hR : 0 < R := small_root_pos hL
  have hRle : R ≤ 3 / 10 :=
    small_root_le_three_tenths hL hsmall
  have hR3 : R ^ 3 = L := lyapunovThirdRoot_cube hL.le
  have hA : 0 < A := small_branchCutoff_pos hL
  have hAinv : A ≤ 1 / L := small_branchCutoff_le_inv hL hsmall
  have hactualInt :=
    small_outer_actual_intervalIntegrable hL le_rfl hAinv
      ((by
        exact (div_le_div_of_nonneg_right (by norm_num) hL.le).trans
          (small_two_inv_le_bandwidth hL)) :
        1 / L ≤ tyurinSmallBandwidth L)
  have hgInt : IntervalIntegrable g volume A (1 / L) := by
    exact ((integrable_exp_neg_mul_sq
      (by norm_num : (0 : ℝ) < 3 / 10)).const_mul
        ((513 / 500 : ℝ) / (2 * Real.pi * A))).intervalIntegrable
  have hintegral :
      (∫ u : ℝ in A..1 / L,
        ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
          tyurinProductEnvelope L u) ≤
        ∫ u : ℝ in A..1 / L, g u := by
    apply intervalIntegral.integral_mono_on hAinv
      hactualInt hgInt
    intro u hu
    exact small_outer_first_pointwise hL hu.1 hu.2
  have hgNonneg : ∀ u, 0 ≤ g u := by
    intro u
    dsimp only [g]
    positivity
  have hgTail :
      (∫ u : ℝ in A..1 / L, g u) ≤
        ((513 / 500 : ℝ) / (2 * Real.pi * A)) *
          (Real.exp (-(3 / 10 : ℝ) * A ^ 2) /
            (2 * (3 / 10 : ℝ) * A)) := by
    calc
      (∫ u : ℝ in A..1 / L, g u) ≤
          ∫ u : ℝ in Ioi A, g u :=
        intervalIntegral_le_Ioi hAinv
          ((integrable_exp_neg_mul_sq
            (by norm_num : (0 : ℝ) < 3 / 10)).const_mul
              ((513 / 500 : ℝ) /
                (2 * Real.pi * A))).integrableOn
          hgNonneg
      _ = ((513 / 500 : ℝ) / (2 * Real.pi * A)) *
            ∫ u : ℝ in Ioi A,
              Real.exp (-(3 / 10 : ℝ) * u ^ 2) := by
        rw [← MeasureTheory.integral_const_mul]
      _ ≤ ((513 / 500 : ℝ) / (2 * Real.pi * A)) *
            (Real.exp (-(3 / 10 : ℝ) * A ^ 2) /
              (2 * (3 / 10 : ℝ) * A)) := by
        gcongr
        exact integral_Ioi_exp_neg_mul_sq_le
          (by norm_num) hA
  have hAsq : A ^ 2 = 25 / (9 * R ^ 2) := by
    unfold A tyurinSmallBranchCutoff
    dsimp only [R]
    field_simp [hR.ne']
    ring_nf
  have hx : 0 < 5 / (6 * R ^ 2) := by positivity
  have hexp :
      Real.exp (-(3 / 10 : ℝ) * A ^ 2) ≤
        6 / (5 / (6 * R ^ 2)) ^ 3 := by
    rw [hAsq]
    convert exp_neg_le_six_div_cube hx using 1
    ring_nf
  have hinvPi :
      1 / Real.pi < (50 / 157 : ℝ) := by
    rw [div_lt_iff₀ Real.pi_pos]
    nlinarith [pi_gt_157_div_50]
  have hscalar :
      (2 / L) *
        (((513 / 500 : ℝ) / (2 * Real.pi * A)) *
          (Real.exp (-(3 / 10 : ℝ) * A ^ 2) /
            (2 * (3 / 10 : ℝ) * A))) <
        1 / 200 := by
    rw [hAsq, ← hR3]
    have hidentity :
        (2 / R ^ 3) *
          ((513 / 500 : ℝ) /
            (2 * Real.pi * tyurinSmallBranchCutoff L) *
            (Real.exp (-(3 / 10 : ℝ) *
                (25 / (9 * R ^ 2))) /
              (2 * (3 / 10 : ℝ) *
                tyurinSmallBranchCutoff L))) =
          (513 / 500 : ℝ) * (1 / Real.pi) *
            (5 / 3) * (9 / 25) *
            Real.exp (-(5 / (6 * R ^ 2))) / R := by
      unfold tyurinSmallBranchCutoff
      dsimp only [R]
      field_simp [Real.pi_ne_zero, hR.ne']
      ring_nf
    rw [hidentity]
    have hexp' :
        Real.exp (-(5 / (6 * R ^ 2))) ≤
          6 / (5 / (6 * R ^ 2)) ^ 3 := by
      have heq :
          -(3 / 10 : ℝ) * A ^ 2 =
            -(5 / (6 * R ^ 2)) := by
        rw [hAsq]
        field_simp [hR.ne']
        ring
      rw [← heq]
      exact hexp
    calc
      (513 / 500 : ℝ) * (1 / Real.pi) *
            (5 / 3) * (9 / 25) *
            Real.exp (-(5 / (6 * R ^ 2))) / R
          < (513 / 500 : ℝ) * (50 / 157) *
            (5 / 3) * (9 / 25) *
            (6 / (5 / (6 * R ^ 2)) ^ 3) / R := by
        have hpositive :
            0 < (513 / 500 : ℝ) * (5 / 3) * (9 / 25) / R := by
          positivity
        have hprod :
            (1 / Real.pi) *
                Real.exp (-(5 / (6 * R ^ 2))) <
              (50 / 157 : ℝ) *
                (6 / (5 / (6 * R ^ 2)) ^ 3) := by
          calc
            (1 / Real.pi) *
                  Real.exp (-(5 / (6 * R ^ 2))) ≤
              (1 / Real.pi) *
                  (6 / (5 / (6 * R ^ 2)) ^ 3) := by
              gcongr
            _ < (50 / 157 : ℝ) *
                  (6 / (5 / (6 * R ^ 2)) ^ 3) := by
              exact mul_lt_mul_of_pos_right hinvPi (by positivity)
        have hmul := mul_lt_mul_of_pos_left hprod hpositive
        calc
          (513 / 500 : ℝ) * (1 / Real.pi) *
                (5 / 3) * (9 / 25) *
                Real.exp (-(5 / (6 * R ^ 2))) / R =
              ((513 / 500 : ℝ) * (5 / 3) *
                (9 / 25) / R) *
                ((1 / Real.pi) *
                  Real.exp (-(5 / (6 * R ^ 2)))) := by ring
          _ < ((513 / 500 : ℝ) * (5 / 3) *
                (9 / 25) / R) *
                ((50 / 157 : ℝ) *
                  (6 / (5 / (6 * R ^ 2)) ^ 3)) := hmul
          _ = (513 / 500 : ℝ) * (50 / 157) *
                (5 / 3) * (9 / 25) *
                (6 / (5 / (6 * R ^ 2)) ^ 3) / R := by ring
      _ = (513 / 500 : ℝ) * (50 / 157) *
            (5 / 3) * (9 / 25) *
            6 * (6 / 5 : ℝ) ^ 3 * R ^ 5 := by
        field_simp [hR.ne']
      _ ≤ (513 / 500 : ℝ) * (50 / 157) *
            (5 / 3) * (9 / 25) *
            6 * (6 / 5 : ℝ) ^ 3 * (3 / 10 : ℝ) ^ 5 := by
        gcongr
      _ < 1 / 200 := by norm_num
  rw [div_eq_mul_inv, show (2 *
      (∫ u : ℝ in A..1 / L,
        ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
          tyurinProductEnvelope L u)) * L⁻¹ =
      (2 / L) *
        (∫ u : ℝ in A..1 / L,
          ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
            tyurinProductEnvelope L u) by ring]
  exact (mul_le_mul_of_nonneg_left
    (hintegral.trans hgTail) (by positivity : 0 ≤ 2 / L)).trans_lt
      hscalar

private theorem exp_neg_le_one_div
    {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ 1 / x := by
  have hxe : x ≤ Real.exp x := by
    have := Real.add_one_le_exp x
    linarith
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le hx hxe

private theorem small_product_le_secondBand_endpoint
    {L : ℝ} (hL : 0 < L) :
    tyurinProductEnvelope L (2 / L) ≤
      Real.exp (-(9 / 100 : ℝ) * (2 / L) ^ 2) := by
  have hu0 : 0 ≤ 2 / L := by positivity
  have hx : 2 * L * (2 / L) = 4 := by
    field_simp [hL.ne']
    norm_num
  have hcosCert :=
    tyurinProductEnvelope_le_cosineCertificate
      hL hu0 (by rw [hx]) (by
        rw [hx]
        nlinarith [Real.pi_gt_three])
  have hbranch :
      tyurinCosineCertificateLower 4 =
        2 - (4 - Real.pi) ^ 2 / 2 := by
    unfold tyurinCosineCertificateLower
    rw [if_pos]
    nlinarith [Real.pi_gt_three]
  have hlower :
      (72 / 49 : ℝ) ≤ tyurinCosineCertificateLower 4 := by
    rw [hbranch]
    have hgap : 0 ≤ 4 - Real.pi := by
      nlinarith [Real.pi_lt_four]
    have hgapLe : 4 - Real.pi ≤ 43 / 50 := by
      nlinarith [pi_gt_157_div_50]
    nlinarith [sq_nonneg (4 - Real.pi),
      mul_self_le_mul_self hgap hgapLe]
  calc
    tyurinProductEnvelope L (2 / L) ≤
        Real.exp
          (-(tyurinCosineLoss / (4 * L ^ 2) *
            tyurinCosineCertificateLower
              (2 * L * (2 / L)))) := hcosCert
    _ ≤ Real.exp (-(9 / 100 : ℝ) * (2 / L) ^ 2) := by
      apply Real.exp_le_exp.mpr
      rw [hx]
      have hfactor :
          0 < tyurinCosineLoss / (4 * L ^ 2) := by
        unfold tyurinCosineLoss
        positivity
      have hscaled :=
        mul_le_mul_of_nonneg_left hlower hfactor.le
      unfold tyurinCosineLoss at hscaled ⊢
      field_simp [hL.ne'] at hscaled ⊢
      norm_num at hscaled ⊢
      nlinarith

private theorem small_product_le_secondBand
    {L u : ℝ} (hL : 0 < L) (hu0 : 0 ≤ u)
    (hu : u ≤ 2 / L) :
    tyurinProductEnvelope L u ≤
      Real.exp (-(9 / 100 : ℝ) * u ^ 2) := by
  rcases hu.eq_or_lt with h | h
  · subst u
    exact small_product_le_secondBand_endpoint hL
  · exact small_product_le_secondBand_of_lt hL hu0 h

private theorem small_outer_second_pointwise
    {L u : ℝ} (hL : 0 < L)
    (hu : 1 / L ≤ u) (hu2 : u ≤ 2 / L) :
    ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
        tyurinProductEnvelope L u ≤
      ((513 / 500 : ℝ) * L / (2 * Real.pi)) *
        Real.exp (-(9 / 100 : ℝ) * u ^ 2) := by
  have hu0 : 0 < u := (by positivity : 0 < 1 / L).trans_le hu
  have huU : |u| ≤ tyurinSmallBandwidth L := by
    rw [abs_of_pos hu0]
    exact hu2.trans (small_two_inv_le_bandwidth hL)
  have hkernel :=
    norm_scaledPrawitzKernel_le_i29
      (small_bandwidth_pos hL) hu0.ne' huU
  have hkernelL :
      scaledPrawitzI29Envelope u ≤
        (513 / 500 : ℝ) * L / (2 * Real.pi) := by
    unfold scaledPrawitzI29Envelope
    rw [abs_of_pos hu0]
    have hLu : 1 ≤ L * u := by
      have := (div_le_iff₀ hL).mp hu
      simpa [mul_comm] using this
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi * u)).2
    field_simp [Real.pi_ne_zero]
    nlinarith
  have hproduct :=
    small_product_le_secondBand hL hu0.le hu2
  calc
    ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
          tyurinProductEnvelope L u ≤
        scaledPrawitzI29Envelope u *
          tyurinProductEnvelope L u :=
      mul_le_mul_of_nonneg_right hkernel
        (tyurinProductEnvelope_nonneg L u)
    _ ≤ scaledPrawitzI29Envelope u *
          Real.exp (-(9 / 100 : ℝ) * u ^ 2) := by
      apply mul_le_mul_of_nonneg_left hproduct
      unfold scaledPrawitzI29Envelope
      positivity
    _ ≤ ((513 / 500 : ℝ) * L / (2 * Real.pi)) *
          Real.exp (-(9 / 100 : ℝ) * u ^ 2) :=
      mul_le_mul_of_nonneg_right hkernelL (Real.exp_nonneg _)

theorem tyurinSmall_outer_second_normalized_lt
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ 1 / 50) :
    (2 * (∫ u : ℝ in 1 / L..2 / L,
      ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
        tyurinProductEnvelope L u)) / L <
      1 / 5000 := by
  let a : ℝ := 1 / L
  let b : ℝ := 2 / L
  let g : ℝ → ℝ := fun u =>
    ((513 / 500 : ℝ) * L / (2 * Real.pi)) *
      Real.exp (-(9 / 100 : ℝ) * u ^ 2)
  have hab : a ≤ b := by
    dsimp only [a, b]
    exact div_le_div_of_nonneg_right (by norm_num) hL.le
  have hAb :
      tyurinSmallBranchCutoff L ≤ a :=
    small_branchCutoff_le_inv hL hsmall
  have hbU : b ≤ tyurinSmallBandwidth L :=
    small_two_inv_le_bandwidth hL
  have hactualInt :=
    small_outer_actual_intervalIntegrable hL hAb hab hbU
  have hgInt : IntervalIntegrable g volume a b :=
    ((integrable_exp_neg_mul_sq
      (by norm_num : (0 : ℝ) < 9 / 100)).const_mul
        ((513 / 500 : ℝ) * L / (2 * Real.pi))).intervalIntegrable
  have hintegral :
      (∫ u : ℝ in a..b,
        ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
          tyurinProductEnvelope L u) ≤
        ∫ u : ℝ in a..b, g u := by
    apply intervalIntegral.integral_mono_on hab hactualInt hgInt
    intro u hu
    exact small_outer_second_pointwise hL hu.1 hu.2
  have hgTail :
      (∫ u : ℝ in a..b, g u) ≤
        ((513 / 500 : ℝ) * L / (2 * Real.pi)) *
          (Real.exp (-(9 / 100 : ℝ) * a ^ 2) /
            (2 * (9 / 100 : ℝ) * a)) := by
    calc
      (∫ u : ℝ in a..b, g u) ≤ ∫ u : ℝ in Ioi a, g u :=
        intervalIntegral_le_Ioi hab
          ((integrable_exp_neg_mul_sq
            (by norm_num : (0 : ℝ) < 9 / 100)).const_mul
              ((513 / 500 : ℝ) * L / (2 * Real.pi))).integrableOn
          (fun _ => by dsimp only [g]; positivity)
      _ = ((513 / 500 : ℝ) * L / (2 * Real.pi)) *
            ∫ u : ℝ in Ioi a,
              Real.exp (-(9 / 100 : ℝ) * u ^ 2) := by
        rw [← MeasureTheory.integral_const_mul]
      _ ≤ _ := by
        gcongr
        exact integral_Ioi_exp_neg_mul_sq_le
          (by norm_num) (by dsimp only [a]; positivity)
  have hx : 0 < (9 / 100 : ℝ) * a ^ 2 := by
    dsimp only [a]
    positivity
  have hexp :
      Real.exp (-(9 / 100 : ℝ) * a ^ 2) ≤
        1 / ((9 / 100 : ℝ) * a ^ 2) := by
    convert exp_neg_le_one_div hx using 1
    ring_nf
  have hinvPi :
      1 / Real.pi < (50 / 157 : ℝ) := by
    rw [div_lt_iff₀ Real.pi_pos]
    nlinarith [pi_gt_157_div_50]
  have hscalar :
      (2 / L) *
        (((513 / 500 : ℝ) * L / (2 * Real.pi)) *
          (Real.exp (-(9 / 100 : ℝ) * a ^ 2) /
            (2 * (9 / 100 : ℝ) * a))) <
        1 / 5000 := by
    have hprod :
        (1 / Real.pi) *
            Real.exp (-(9 / 100 : ℝ) * a ^ 2) <
          (50 / 157 : ℝ) *
            (1 / ((9 / 100 : ℝ) * a ^ 2)) := by
      calc
        (1 / Real.pi) * Real.exp (-(9 / 100 : ℝ) * a ^ 2)
            ≤ (1 / Real.pi) *
                (1 / ((9 / 100 : ℝ) * a ^ 2)) := by
          gcongr
        _ < (50 / 157 : ℝ) *
                (1 / ((9 / 100 : ℝ) * a ^ 2)) :=
          mul_lt_mul_of_pos_right hinvPi (by positivity)
    dsimp only [a] at *
    have hbound :
        L ^ 3 ≤ (1 / 50 : ℝ) ^ 3 := by
      nlinarith [sq_nonneg (L - 1 / 50)]
    calc
      (2 / L) *
          ((513 / 500 : ℝ) * L / (2 * Real.pi) *
            (Real.exp (-(9 / 100 : ℝ) * (1 / L) ^ 2) /
              (2 * (9 / 100 : ℝ) * (1 / L))))
          = ((513 / 500 : ℝ) * (50 / 9) * L) *
              ((1 / Real.pi) *
                Real.exp (-(9 / 100 : ℝ) * (1 / L) ^ 2)) := by
        field_simp [hL.ne', Real.pi_ne_zero]
        ring
      _ < ((513 / 500 : ℝ) * (50 / 9) * L) *
              ((50 / 157 : ℝ) *
                (1 / ((9 / 100 : ℝ) * (1 / L) ^ 2))) := by
        have hpos : 0 < (513 / 500 : ℝ) * (50 / 9) * L := by
          positivity
        exact mul_lt_mul_of_pos_left hprod hpos
      _ = (513 / 500 : ℝ) * (50 / 157) *
              (5000 / 81) * L ^ 3 := by
        field_simp [hL.ne']
        ring
      _ ≤ (513 / 500 : ℝ) * (50 / 157) *
              (5000 / 81) * (1 / 50 : ℝ) ^ 3 := by
        gcongr
      _ < 1 / 5000 := by norm_num
  rw [div_eq_mul_inv, show (2 *
      (∫ u : ℝ in a..b,
        ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
          tyurinProductEnvelope L u)) * L⁻¹ =
      (2 / L) *
        (∫ u : ℝ in a..b,
          ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
            tyurinProductEnvelope L u) by ring]
  exact (mul_le_mul_of_nonneg_left
    (hintegral.trans hgTail) (by positivity : 0 ≤ 2 / L)).trans_lt
      hscalar

private theorem small_outer_middle_pointwise
    {L u : ℝ} (hL : 0 < L)
    (hu : 2 / L ≤ u) (hub : u ≤ 189 / (80 * L)) :
    ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
        tyurinProductEnvelope L u ≤
      ((513 / 500 : ℝ) * L / (4 * Real.pi)) *
        Real.exp (-(49 / 500 : ℝ) / L ^ 2) := by
  have hu0 : 0 < u := (by positivity : 0 < 2 / L).trans_le hu
  have huU : |u| ≤ tyurinSmallBandwidth L := by
    rw [abs_of_pos hu0]
    unfold tyurinSmallBandwidth
    rw [le_div_iff₀ hL]
    rw [le_div_iff₀ (mul_pos (by norm_num) hL)] at hub
    norm_num at hub ⊢
    linarith
  have hkernel :=
    norm_scaledPrawitzKernel_le_i29
      (small_bandwidth_pos hL) hu0.ne' huU
  have hkernelL :
      scaledPrawitzI29Envelope u ≤
        (513 / 500 : ℝ) * L / (4 * Real.pi) := by
    unfold scaledPrawitzI29Envelope
    rw [abs_of_pos hu0]
    have hLu : 2 ≤ L * u := by
      have := (div_le_iff₀ hL).mp hu
      simpa [mul_comm] using this
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi * u)).2
    field_simp [Real.pi_ne_zero]
    nlinarith
  have hproduct :=
    small_product_le_middleBand hL hu0.le hu hub
  calc
    ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
          tyurinProductEnvelope L u ≤
        scaledPrawitzI29Envelope u *
          tyurinProductEnvelope L u :=
      mul_le_mul_of_nonneg_right hkernel
        (tyurinProductEnvelope_nonneg L u)
    _ ≤ scaledPrawitzI29Envelope u *
          Real.exp (-(49 / 500 : ℝ) / L ^ 2) := by
      apply mul_le_mul_of_nonneg_left hproduct
      unfold scaledPrawitzI29Envelope
      positivity
    _ ≤ ((513 / 500 : ℝ) * L / (4 * Real.pi)) *
          Real.exp (-(49 / 500 : ℝ) / L ^ 2) :=
      mul_le_mul_of_nonneg_right hkernelL (Real.exp_nonneg _)

theorem tyurinSmall_outer_middle_normalized_lt
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ 1 / 50) :
    (2 * (∫ u : ℝ in 2 / L..189 / (80 * L),
      ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
        tyurinProductEnvelope L u)) / L <
      13 / 1000 := by
  let a : ℝ := 2 / L
  let b : ℝ := 189 / (80 * L)
  let C : ℝ :=
    ((513 / 500 : ℝ) * L / (4 * Real.pi)) *
      Real.exp (-(49 / 500 : ℝ) / L ^ 2)
  have hab : a ≤ b := by
    dsimp only [a, b]
    field_simp [hL.ne']
    norm_num
  have hAb :
      tyurinSmallBranchCutoff L ≤ a :=
    (small_branchCutoff_le_inv hL hsmall).trans
      (div_le_div_of_nonneg_right (by norm_num) hL.le)
  have hbU : b ≤ tyurinSmallBandwidth L := by
    dsimp only [b]
    unfold tyurinSmallBandwidth
    field_simp [hL.ne']
    norm_num
  have hactualInt :=
    small_outer_actual_intervalIntegrable hL hAb hab hbU
  have hconstantInt : IntervalIntegrable (fun _ : ℝ => C) volume a b :=
    intervalIntegrable_const
  have hintegral :
      (∫ u : ℝ in a..b,
        ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
          tyurinProductEnvelope L u) ≤
        ∫ _u : ℝ in a..b, C := by
    apply intervalIntegral.integral_mono_on hab
      hactualInt hconstantInt
    intro u hu
    exact small_outer_middle_pointwise hL hu.1 hu.2
  have hlength :
      (∫ _u : ℝ in a..b, C) =
        (29 / (80 * L) : ℝ) * C := by
    rw [intervalIntegral.integral_const]
    dsimp only [a, b]
    congr 1
    field_simp [hL.ne']
    ring
  have hx : 0 < (49 / 500 : ℝ) / L ^ 2 := by positivity
  have hexp :
      Real.exp (-(49 / 500 : ℝ) / L ^ 2) ≤
        1 / ((49 / 500 : ℝ) / L ^ 2) := by
    convert exp_neg_le_one_div hx using 1
    ring_nf
  have hinvPi :
      1 / Real.pi < (50 / 157 : ℝ) := by
    rw [div_lt_iff₀ Real.pi_pos]
    nlinarith [pi_gt_157_div_50]
  have hscalar :
      (2 / L) * ((29 / (80 * L) : ℝ) * C) <
        13 / 1000 := by
    dsimp only [C]
    have hprod :
        (1 / Real.pi) *
            Real.exp (-(49 / 500 : ℝ) / L ^ 2) <
          (50 / 157 : ℝ) *
            (1 / ((49 / 500 : ℝ) / L ^ 2)) := by
      calc
        (1 / Real.pi) * Real.exp (-(49 / 500 : ℝ) / L ^ 2)
            ≤ (1 / Real.pi) *
                (1 / ((49 / 500 : ℝ) / L ^ 2)) := by
          gcongr
        _ < (50 / 157 : ℝ) *
                (1 / ((49 / 500 : ℝ) / L ^ 2)) :=
          mul_lt_mul_of_pos_right hinvPi (by positivity)
    have hpos : 0 < (513 / 500 : ℝ) * (29 / 160) / L := by
      positivity
    have hmul := mul_lt_mul_of_pos_left hprod hpos
    calc
      (2 / L) * ((29 / (80 * L) : ℝ) *
          ((513 / 500 : ℝ) * L / (4 * Real.pi) *
            Real.exp (-(49 / 500 : ℝ) / L ^ 2))) =
        ((513 / 500 : ℝ) * (29 / 160) / L) *
          ((1 / Real.pi) *
            Real.exp (-(49 / 500 : ℝ) / L ^ 2)) := by
        field_simp [hL.ne', Real.pi_ne_zero]
        ring
      _ < ((513 / 500 : ℝ) * (29 / 160) / L) *
          ((50 / 157 : ℝ) *
            (1 / ((49 / 500 : ℝ) / L ^ 2))) := hmul
      _ = (513 / 500 : ℝ) * (29 / 160) *
          (50 / 157) * (500 / 49) * L := by
        field_simp [hL.ne']
      _ ≤ (513 / 500 : ℝ) * (29 / 160) *
          (50 / 157) * (500 / 49) * (1 / 50) := by
        gcongr
      _ < 13 / 1000 := by norm_num
  rw [div_eq_mul_inv, show (2 *
      (∫ u : ℝ in a..b,
        ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
          tyurinProductEnvelope L u)) * L⁻¹ =
      (2 / L) *
        (∫ u : ℝ in a..b,
          ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
            tyurinProductEnvelope L u) by ring]
  exact (mul_le_mul_of_nonneg_left
    (hintegral.trans_eq hlength) (by positivity : 0 ≤ 2 / L)).trans_lt
      hscalar

/-! ## The endpoint-reflected band -/

private noncomputable def smallEndpointEnvelope
    (U q : ℝ) : ℝ :=
  (q / (2 * U ^ 2) + Real.pi * q ^ 2 / (4 * U ^ 3)) *
    Real.exp (-(147 / 400 : ℝ) * q ^ 2)

private theorem small_outer_endpoint_pointwise
    {L u : ℝ} (hL : 0 < L)
    (hu : 189 / (80 * L) ≤ u)
    (huU : u ≤ tyurinSmallBandwidth L) :
    ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
        tyurinProductEnvelope L u ≤
      smallEndpointEnvelope (tyurinSmallBandwidth L)
        (tyurinSmallBandwidth L - u) := by
  let U := tyurinSmallBandwidth L
  let q := U - u
  have hU : 0 < U := small_bandwidth_pos hL
  have hu0 : 0 < u := (by positivity : 0 < 189 / (80 * L)).trans_le hu
  have hq0 : 0 ≤ q := sub_nonneg.mpr huU
  have hinside : |u| ≤ U := by
    rw [abs_of_pos hu0]
    exact huU
  have hhalf : U / 2 ≤ |u| := by
    rw [abs_of_pos hu0]
    calc
      U / 2 ≤ 189 / (80 * L) := by
        unfold U tyurinSmallBandwidth
        field_simp [hL.ne']
        norm_num
      _ ≤ u := hu
  have hkernel :=
    norm_scaledPrawitzKernel_le_endpoint hU hhalf hinside
  have hkernelEq :
      scaledPrawitzEndpointEnvelope U u =
        q / (2 * U ^ 2) +
          Real.pi * q ^ 2 / (4 * U ^ 3) := by
    unfold scaledPrawitzEndpointEnvelope
    rw [abs_of_pos hu0]
    dsimp only [q]
    field_simp [hU.ne']
  have hproduct :=
    small_product_le_endpointBand hL hu0.le hu huU
  unfold smallEndpointEnvelope
  dsimp only [U, q] at *
  rw [hkernelEq] at hkernel
  exact mul_le_mul hkernel hproduct
    (tyurinProductEnvelope_nonneg L u)
    (by
      have hq0' :
          0 ≤ tyurinSmallBandwidth L - u := sub_nonneg.mpr huU
      positivity)

private theorem q_exp_half_le_six_fifths
    (q : ℝ) :
    q * Real.exp (-(147 / 800 : ℝ) * q ^ 2) ≤ 6 / 5 := by
  have hquad :
      q ≤ (6 / 5 : ℝ) *
        (1 + (147 / 800 : ℝ) * q ^ 2) := by
    nlinarith [sq_nonneg (147 * q - 400)]
  have hexp :
      1 + (147 / 800 : ℝ) * q ^ 2 ≤
        Real.exp ((147 / 800 : ℝ) * q ^ 2) :=
    by
      simpa [add_comm] using
        Real.add_one_le_exp ((147 / 800 : ℝ) * q ^ 2)
  have hqexp :
      q ≤ (6 / 5 : ℝ) *
        Real.exp ((147 / 800 : ℝ) * q ^ 2) :=
    hquad.trans (mul_le_mul_of_nonneg_left hexp (by norm_num))
  calc
    q * Real.exp (-(147 / 800 : ℝ) * q ^ 2) ≤
        ((6 / 5 : ℝ) *
          Real.exp ((147 / 800 : ℝ) * q ^ 2)) *
            Real.exp (-(147 / 800 : ℝ) * q ^ 2) :=
      mul_le_mul_of_nonneg_right hqexp (Real.exp_nonneg _)
    _ = 6 / 5 := by
      rw [show
          (147 / 800 : ℝ) * q ^ 2 =
            -(-(147 / 800 : ℝ) * q ^ 2) by ring,
        Real.exp_neg]
      field_simp [Real.exp_ne_zero]

private theorem sq_exp_endpoint_le_firstMoment
    {q : ℝ} (hq : 0 ≤ q) :
    q ^ 2 * Real.exp (-(147 / 400 : ℝ) * q ^ 2) ≤
      (6 / 5 : ℝ) * q *
        Real.exp (-(147 / 800 : ℝ) * q ^ 2) := by
  have hhalf := q_exp_half_le_six_fifths q
  have hexp0 :
      0 ≤ Real.exp (-(147 / 800 : ℝ) * q ^ 2) :=
    Real.exp_nonneg _
  calc
    q ^ 2 * Real.exp (-(147 / 400 : ℝ) * q ^ 2) =
        (q * Real.exp (-(147 / 800 : ℝ) * q ^ 2)) *
          (q * Real.exp (-(147 / 800 : ℝ) * q ^ 2)) := by
      rw [show
          Real.exp (-(147 / 400 : ℝ) * q ^ 2) =
            Real.exp (-(147 / 800 : ℝ) * q ^ 2) *
              Real.exp (-(147 / 800 : ℝ) * q ^ 2) by
        rw [← Real.exp_add]
        congr 1
        ring]
      ring
    _ ≤ (6 / 5 : ℝ) *
          (q * Real.exp (-(147 / 800 : ℝ) * q ^ 2)) :=
      mul_le_mul_of_nonneg_right hhalf
        (mul_nonneg hq hexp0)
    _ = (6 / 5 : ℝ) * q *
          Real.exp (-(147 / 800 : ℝ) * q ^ 2) := by ring

private theorem integral_Ioi_smallEndpointEnvelope_le
    {U : ℝ} (hU : 0 < U) :
    (∫ q : ℝ in Ioi 0, smallEndpointEnvelope U q) ≤
      (1 / (2 * U ^ 2)) * (200 / 147 : ℝ) +
        (Real.pi / (4 * U ^ 3)) * (160 / 49 : ℝ) := by
  let f₁ : ℝ → ℝ := fun q =>
    (1 / (2 * U ^ 2)) *
      (q * Real.exp (-(147 / 400 : ℝ) * q ^ 2))
  let f₂ : ℝ → ℝ := fun q =>
    (Real.pi / (4 * U ^ 3)) *
      ((6 / 5 : ℝ) * q *
        Real.exp (-(147 / 800 : ℝ) * q ^ 2))
  have hdom :
      ∀ q ∈ Ioi (0 : ℝ),
        smallEndpointEnvelope U q ≤ f₁ q + f₂ q := by
    intro q hq
    have hq0 : 0 ≤ q := hq.le
    have hsq := sq_exp_endpoint_le_firstMoment hq0
    unfold smallEndpointEnvelope f₁ f₂
    have hcoeff : 0 ≤ Real.pi / (4 * U ^ 3) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hsq hcoeff
    calc
      (q / (2 * U ^ 2) + Real.pi * q ^ 2 / (4 * U ^ 3)) *
            Real.exp (-(147 / 400) * q ^ 2) =
          f₁ q + (Real.pi / (4 * U ^ 3)) *
            (q ^ 2 * Real.exp (-(147 / 400) * q ^ 2)) := by
        unfold f₁
        ring
      _ ≤ f₁ q + (Real.pi / (4 * U ^ 3)) *
            ((6 / 5 : ℝ) * q *
              Real.exp (-(147 / 800) * q ^ 2)) :=
        by
          simpa [add_comm] using add_le_add_left hscaled (f₁ q)
      _ = f₁ q + f₂ q := by
        unfold f₂
        ring
  have hf₁ : IntegrableOn f₁ (Ioi 0) := by
    exact ((integrable_mul_exp_neg_mul_sq
      (by norm_num : (0 : ℝ) < 147 / 400)).const_mul
        (1 / (2 * U ^ 2))).integrableOn
  have hf₂ : IntegrableOn f₂ (Ioi 0) := by
    convert ((integrable_mul_exp_neg_mul_sq
      (by norm_num : (0 : ℝ) < 147 / 800)).const_mul
        ((Real.pi / (4 * U ^ 3)) * (6 / 5))).integrableOn using 1
    ext q
    unfold f₂
    ring
  have henvInt : IntegrableOn (smallEndpointEnvelope U) (Ioi 0) := by
    refine Integrable.mono'
      (hf₁.add hf₂)
      (by
        unfold smallEndpointEnvelope
        fun_prop)
      ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hdom q hq
    · unfold smallEndpointEnvelope
      have hq0 : 0 ≤ q := hq.le
      positivity
  have hint :
      (∫ q : ℝ in Ioi 0, smallEndpointEnvelope U q) ≤
        (∫ q : ℝ in Ioi 0, f₁ q) +
          ∫ q : ℝ in Ioi 0, f₂ q := by
    rw [← integral_add hf₁ hf₂]
    exact setIntegral_mono_on henvInt (hf₁.add hf₂)
      measurableSet_Ioi hdom
  rw [show (∫ q : ℝ in Ioi 0, f₁ q) =
      (1 / (2 * U ^ 2)) * (200 / 147 : ℝ) by
    unfold f₁
    rw [MeasureTheory.integral_const_mul,
      integral_Ioi_mul_exp_neg_mul_sq
        (by norm_num : (0 : ℝ) < 147 / 400)
        (by norm_num : (0 : ℝ) ≤ 0)]
    norm_num,
    show (∫ q : ℝ in Ioi 0, f₂ q) =
      (Real.pi / (4 * U ^ 3)) * (160 / 49 : ℝ) by
    unfold f₂
    rw [show (fun q : ℝ =>
        Real.pi / (4 * U ^ 3) *
          (6 / 5 * q * Real.exp (-(147 / 800) * q ^ 2))) =
        fun q => (Real.pi / (4 * U ^ 3) * (6 / 5)) *
          (q * Real.exp (-(147 / 800) * q ^ 2)) by
      funext q; ring,
      MeasureTheory.integral_const_mul,
      integral_Ioi_mul_exp_neg_mul_sq
        (by norm_num : (0 : ℝ) < 147 / 800)
        (by norm_num : (0 : ℝ) ≤ 0)]
    simp [Real.exp_zero]
    ring] at hint
  convert hint using 1

private theorem integrable_smallEndpointEnvelope
    {U : ℝ} :
    Integrable (smallEndpointEnvelope U) := by
  have h₁ :=
    (integrable_mul_exp_neg_mul_sq
      (by norm_num : (0 : ℝ) < 147 / 400)).const_mul
        (1 / (2 * U ^ 2))
  have h₂base :=
    integrable_rpow_mul_exp_neg_mul_sq
      (by norm_num : (0 : ℝ) < 147 / 400)
      (by norm_num : (-1 : ℝ) < 2)
  have h₂ :
      Integrable (fun q : ℝ =>
        (Real.pi / (4 * U ^ 3)) *
          (q ^ 2 * Real.exp (-(147 / 400 : ℝ) * q ^ 2))) := by
    convert h₂base.const_mul (Real.pi / (4 * U ^ 3)) using 1
    ext q
    rw [Real.rpow_two]
  refine (h₁.add h₂).congr ?_
  filter_upwards with q
  simp only [Pi.add_apply]
  unfold smallEndpointEnvelope
  ring

theorem tyurinSmall_outer_endpoint_normalized_lt
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ 1 / 50) :
    (2 * (∫ u : ℝ in 189 / (80 * L)..tyurinSmallBandwidth L,
      ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
        tyurinProductEnvelope L u)) / L <
      3 / 1000 := by
  let a : ℝ := 189 / (80 * L)
  let U : ℝ := tyurinSmallBandwidth L
  have ha : 0 < a := by
    dsimp only [a]
    positivity
  have hU : 0 < U := small_bandwidth_pos hL
  have haU : a ≤ U := by
    dsimp only [a, U]
    unfold tyurinSmallBandwidth
    field_simp [hL.ne']
    norm_num
  have hAa :
      tyurinSmallBranchCutoff L ≤ a :=
    (small_branchCutoff_le_inv hL hsmall).trans
      (by
        dsimp only [a]
        field_simp [hL.ne']
        norm_num)
  have hactualInt :=
    small_outer_actual_intervalIntegrable hL hAa haU le_rfl
  have henvInt :
      IntervalIntegrable
        (fun u => smallEndpointEnvelope U (U - u))
        volume a U := by
    have hcont :
        Continuous (fun u => smallEndpointEnvelope U (U - u)) := by
      unfold smallEndpointEnvelope
      fun_prop
    exact hcont.intervalIntegrable (μ := volume) a U
  have hintegral :
      (∫ u : ℝ in a..U,
        ‖scaledPrawitzKernel U u‖ *
          tyurinProductEnvelope L u) ≤
        ∫ u : ℝ in a..U,
          smallEndpointEnvelope U (U - u) := by
    apply intervalIntegral.integral_mono_on haU
      hactualInt henvInt
    intro u hu
    exact small_outer_endpoint_pointwise hL hu.1 hu.2
  have hreflect :
      (∫ u : ℝ in a..U,
        smallEndpointEnvelope U (U - u)) =
        ∫ q : ℝ in 0..U - a,
          smallEndpointEnvelope U q := by
    simpa only [sub_self] using
      intervalIntegral.integral_comp_sub_left
        (smallEndpointEnvelope U) U (a := a) (b := U)
  have hgap : 0 ≤ U - a := sub_nonneg.mpr haU
  have htoIoi :
      (∫ q : ℝ in 0..U - a,
        smallEndpointEnvelope U q) ≤
        ∫ q : ℝ in Ioi 0, smallEndpointEnvelope U q := by
    rw [intervalIntegral.integral_of_le hgap]
    apply setIntegral_mono_set
      integrable_smallEndpointEnvelope.integrableOn
      ?_
      (ae_of_all _ fun _ hq => Ioc_subset_Ioi_self hq)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
    unfold smallEndpointEnvelope
    have hq0 : 0 ≤ q := hq.le
    positivity
  have hclosed :=
    integral_Ioi_smallEndpointEnvelope_le hU
  have hpi : Real.pi < (63 / 20 : ℝ) :=
    pi_lt_63_div_20
  have hscalar :
      (2 / L) *
        ((1 / (2 * U ^ 2)) * (200 / 147 : ℝ) +
          (Real.pi / (4 * U ^ 3)) * (160 / 49 : ℝ)) <
        3 / 1000 := by
    have hpiTerm :
        Real.pi / (4 * U ^ 3) * (160 / 49 : ℝ) <
          (63 / 20 : ℝ) / (4 * U ^ 3) * (160 / 49) := by
      gcongr
    have hLle : L ^ 2 ≤ (1 / 50 : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (L - 1 / 50)]
    unfold U tyurinSmallBandwidth
    calc
      (2 / L) *
          (1 / (2 * ((157 / 50 : ℝ) / L) ^ 2) * (200 / 147) +
            Real.pi / (4 * ((157 / 50 : ℝ) / L) ^ 3) *
              (160 / 49)) <
        (2 / L) *
          (1 / (2 * ((157 / 50 : ℝ) / L) ^ 2) * (200 / 147) +
            (63 / 20 : ℝ) /
              (4 * ((157 / 50 : ℝ) / L) ^ 3) *
                (160 / 49)) := by
        gcongr
      _ = (500000 / (147 * 157 ^ 2) : ℝ) * L +
          (80 * (63 / 20 : ℝ) * 50 ^ 3 /
            (49 * 157 ^ 3)) * L ^ 2 := by
        field_simp [hL.ne']
        ring
      _ ≤ (500000 / (147 * 157 ^ 2) : ℝ) * (1 / 50) +
          (80 * (63 / 20 : ℝ) * 50 ^ 3 /
            (49 * 157 ^ 3)) * (1 / 50 : ℝ) ^ 2 := by
        gcongr
      _ < 3 / 1000 := by norm_num
  dsimp only [a, U] at hintegral hreflect htoIoi ⊢
  rw [div_eq_mul_inv, show (2 *
      (∫ u : ℝ in 189 / (80 * L)..tyurinSmallBandwidth L,
        ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
          tyurinProductEnvelope L u)) * L⁻¹ =
      (2 / L) *
        (∫ u : ℝ in 189 / (80 * L)..tyurinSmallBandwidth L,
          ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
            tyurinProductEnvelope L u) by ring]
  have hchain :=
    hintegral.trans
      (hreflect.le.trans
        (htoIoi.trans hclosed))
  exact (mul_le_mul_of_nonneg_left hchain
    (by positivity : 0 ≤ 2 / L)).trans_lt hscalar

/-! ## Recombining the four outer bands -/

/--
The complete normalized outer integral costs less than `11/500`.  This
theorem is the only outer-integral estimate needed by the final small-
Lyapunov assembly; the four preceding theorems expose the independently
checked band budgets.
-/
theorem tyurinSmall_outer_normalized_lt
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ 1 / 50) :
    (2 * (∫ u : ℝ in
      tyurinSmallBranchCutoff L..tyurinSmallBandwidth L,
      ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
        tyurinProductEnvelope L u)) / L <
      11 / 500 := by
  let f : ℝ → ℝ := fun u =>
    ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
      tyurinProductEnvelope L u
  let a := tyurinSmallBranchCutoff L
  let b : ℝ := 1 / L
  let c : ℝ := 2 / L
  let d : ℝ := 189 / (80 * L)
  let e := tyurinSmallBandwidth L
  have hab : a ≤ b := small_branchCutoff_le_inv hL hsmall
  have hbc : b ≤ c := by
    dsimp only [b, c]
    exact div_le_div_of_nonneg_right (by norm_num) hL.le
  have hcd : c ≤ d := by
    dsimp only [c, d]
    field_simp [hL.ne']
    norm_num
  have hde : d ≤ e := by
    dsimp only [d, e]
    unfold tyurinSmallBandwidth
    field_simp [hL.ne']
    norm_num
  have h₁ : IntervalIntegrable f volume a b := by
    exact small_outer_actual_intervalIntegrable hL le_rfl hab
      (hbc.trans (hcd.trans hde))
  have h₂ : IntervalIntegrable f volume b c := by
    exact small_outer_actual_intervalIntegrable hL hab hbc
      (hcd.trans hde)
  have h₃ : IntervalIntegrable f volume c d := by
    exact small_outer_actual_intervalIntegrable hL
      (hab.trans hbc) hcd hde
  have h₄ : IntervalIntegrable f volume d e := by
    exact small_outer_actual_intervalIntegrable hL
      (hab.trans (hbc.trans hcd)) hde le_rfl
  have hsplit :
      (∫ u : ℝ in a..e, f u) =
        (∫ u : ℝ in a..b, f u) +
        (∫ u : ℝ in b..c, f u) +
        (∫ u : ℝ in c..d, f u) +
        (∫ u : ℝ in d..e, f u) := by
    have habc :=
      intervalIntegral.integral_add_adjacent_intervals h₁ h₂
    have hacd :=
      intervalIntegral.integral_add_adjacent_intervals (h₁.trans h₂) h₃
    have hade :=
      intervalIntegral.integral_add_adjacent_intervals
        ((h₁.trans h₂).trans h₃) h₄
    calc
      (∫ u : ℝ in a..e, f u) =
          (∫ u : ℝ in a..d, f u) +
            ∫ u : ℝ in d..e, f u := hade.symm
      _ = ((∫ u : ℝ in a..c, f u) +
            ∫ u : ℝ in c..d, f u) +
            ∫ u : ℝ in d..e, f u := by rw [hacd]
      _ = (((∫ u : ℝ in a..b, f u) +
              ∫ u : ℝ in b..c, f u) +
            ∫ u : ℝ in c..d, f u) +
            ∫ u : ℝ in d..e, f u := by rw [habc]
  have hone := tyurinSmall_outer_first_normalized_lt hL hsmall
  have htwo := tyurinSmall_outer_second_normalized_lt hL hsmall
  have hthree := tyurinSmall_outer_middle_normalized_lt hL hsmall
  have hfour := tyurinSmall_outer_endpoint_normalized_lt hL hsmall
  dsimp only [a, b, c, d, e, f] at hsplit ⊢
  rw [hsplit]
  rw [show
      (2 *
        ((∫ u : ℝ in tyurinSmallBranchCutoff L..1 / L,
            ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
              tyurinProductEnvelope L u) +
          (∫ u : ℝ in 1 / L..2 / L,
            ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
              tyurinProductEnvelope L u) +
          (∫ u : ℝ in 2 / L..189 / (80 * L),
            ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
              tyurinProductEnvelope L u) +
          (∫ u : ℝ in 189 / (80 * L)..tyurinSmallBandwidth L,
            ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
              tyurinProductEnvelope L u))) / L =
        (2 * (∫ u : ℝ in tyurinSmallBranchCutoff L..1 / L,
            ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
              tyurinProductEnvelope L u)) / L +
        (2 * (∫ u : ℝ in 1 / L..2 / L,
            ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
              tyurinProductEnvelope L u)) / L +
        (2 * (∫ u : ℝ in 2 / L..189 / (80 * L),
            ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
              tyurinProductEnvelope L u)) / L +
        (2 * (∫ u : ℝ in 189 / (80 * L)..tyurinSmallBandwidth L,
            ‖scaledPrawitzKernel (tyurinSmallBandwidth L) u‖ *
              tyurinProductEnvelope L u)) / L by ring]
  nlinarith

end Probability
end CertifiedJL
