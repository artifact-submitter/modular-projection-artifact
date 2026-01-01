/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.SmoothBounds.PowerSums

/-!
# Degree-ten correction for the sparse `21/50` endpoint

This endpoint-specific correction turns exact Rademacher moments through
degree ten into the polynomial tail bound needed by the `21/50` theorem.
-/

open scoped BigOperators

namespace CertifiedJL.SparseLInfLower21Over50

open Probability

noncomputable def twentyOneFiftiethMomentCorrection
    (S2 S3 S4 S5 : ℝ) : ℝ :=
  -(1469481 / 2500) * S2 + (214446 / 625) * S3 +
    (8204 / 5) * S2 ^ 2 - (79696 / 25) * S4 -
    6720 * S2 * S3 + 7936 * S5

theorem twentyOneFiftieth_large_max_cubic_nonpos
    {m : ℝ} (hm0 : (4981 / 12400 : ℝ) ≤ m) (hm1 : m ≤ 1) :
    -(1469481 / 2500 : ℝ) + (1239946 / 625) * m -
      (79696 / 25) * m ^ 2 + 1216 * m ^ 3 ≤ 0 := by
  let u : ℝ := (m - 4981 / 12400) / (7419 / 12400)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; norm_num at *; linarith
  have hu' : 0 ≤ 1 - u := by linarith
  have hm : m = 4981 / 12400 + (7419 / 12400) * u := by
    dsimp [u]
    field_simp
    ring
  rw [hm]
  have hbern :
      (-6745664819261 / 29791000000 : ℝ) * (1 - u) ^ 3 +
        3 * (-53850609843 / 240250000 : ℝ) * u * (1 - u) ^ 2 +
        3 * (-1656118379 / 3875000 : ℝ) * u ^ 2 * (1 - u) +
        (-1439297 / 2500 : ℝ) * u ^ 3 ≤ 0 := by
    have h0 : (-6745664819261 / 29791000000 : ℝ) ≤ 0 := by norm_num
    have h1 : (-53850609843 / 240250000 : ℝ) ≤ 0 := by norm_num
    have h2 : (-1656118379 / 3875000 : ℝ) ≤ 0 := by norm_num
    have h3 : (-1439297 / 2500 : ℝ) ≤ 0 := by norm_num
    have hb0 := mul_nonpos_of_nonpos_of_nonneg h0 (pow_nonneg hu' 3)
    have hb1 : 3 * (-53850609843 / 240250000 : ℝ) * u * (1 - u) ^ 2 ≤ 0 := by
      have hc : 3 * (-53850609843 / 240250000 : ℝ) ≤ 0 := by norm_num
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hc hu0) (pow_nonneg hu' 2)
    have hb2 : 3 * (-1656118379 / 3875000 : ℝ) * u ^ 2 * (1 - u) ≤ 0 := by
      have hc : 3 * (-1656118379 / 3875000 : ℝ) ≤ 0 := by norm_num
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hc (pow_nonneg hu0 2)) hu'
    have hb3 := mul_nonpos_of_nonpos_of_nonneg h3 (pow_nonneg hu0 3)
    linarith
  have hid :
      (-(1469481 / 2500 : ℝ) +
          (1239946 / 625) * (4981 / 12400 + (7419 / 12400) * u) -
          (79696 / 25) * (4981 / 12400 + (7419 / 12400) * u) ^ 2 +
          1216 * (4981 / 12400 + (7419 / 12400) * u) ^ 3) =
        (-6745664819261 / 29791000000 : ℝ) * (1 - u) ^ 3 +
          3 * (-53850609843 / 240250000 : ℝ) * u * (1 - u) ^ 2 +
          3 * (-1656118379 / 3875000 : ℝ) * u ^ 2 * (1 - u) +
          (-1439297 / 2500 : ℝ) * u ^ 3 := by
    ring
  rw [hid]
  exact hbern

set_option maxHeartbeats 1000000 in
theorem twentyOneFiftiethMomentCorrection_nonpos
    {ι : Type*} [Fintype ι] (x : ι → ℝ) (m : ℝ)
    (hx : ∀ i, 0 ≤ x i) (hle : ∀ i, x i ≤ m)
    (hmax : ∃ i, x i = m) (hsum : ∑ i, x i = 1) :
    twentyOneFiftiethMomentCorrection (powerSum x 2) (powerSum x 3)
      (powerSum x 4) (powerSum x 5) ≤ 0 := by
  have hm0 : 0 ≤ m := by obtain ⟨i, rfl⟩ := hmax; exact hx i
  have hm1 : m ≤ 1 := by
    obtain ⟨i, hi⟩ := hmax
    rw [← hi, ← hsum]
    exact Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
  let S2 := powerSum x 2
  let S3 := powerSum x 3
  let S4 := powerSum x 4
  let S5 := powerSum x 5
  have hS2 : 0 ≤ S2 := powerSum_nonneg hx 2
  have hS3 : 0 ≤ S3 := powerSum_nonneg hx 3
  have hS4 : 0 ≤ S4 := powerSum_nonneg hx 4
  have hS5 : 0 ≤ S5 := powerSum_nonneg hx 5
  have hS2m : S2 ≤ m := powerSum_two_le_max hx hle hsum
  have hS3m : S3 ≤ m * S2 := powerSum_three_le_max_mul_two hx hle
  have hS5m : S5 ≤ m * S4 := powerSum_five_le_max_mul_four hx hle
  have hS4m : S4 ≤ m ^ 2 * S2 := powerSum_four_le_max_sq_mul_two hx hle
  have hm3 : m ^ 3 ≤ S3 := max_cube_le_powerSum_three hx hmax
  have hS2sq : S2 ^ 2 ≤ S3 := by
    simpa only [S2, S3] using powerSum_two_sq_le_powerSum_three hx hsum
  by_cases hm : m ≤ (4981 / 12400 : ℝ)
  · have h45 : 7936 * S5 ≤ (79696 / 25 : ℝ) * S4 := by
      calc
        7936 * S5 ≤ 7936 * (m * S4) := by nlinarith
        _ ≤ (79696 / 25 : ℝ) * S4 := by nlinarith
    have hquad :
        (8204 / 5 : ℝ) * S2 - 6720 * S2 ^ 2 ≤
          (8204 / 5 : ℝ) ^ 2 / (4 * 6720) := by
      nlinarith [sq_nonneg ((2 * 6720 : ℝ) * S2 - 8204 / 5)]
    have hcoef :
        -(1469481 / 2500 : ℝ) + (214446 / 625) * m +
          (8204 / 5 : ℝ) ^ 2 / (4 * 6720) ≤ 0 := by
      calc
        _ ≤ -(1469481 / 2500 : ℝ) +
            (214446 / 625) * (4981 / 12400) +
            (8204 / 5 : ℝ) ^ 2 / (4 * 6720) := by nlinarith
        _ ≤ 0 := by norm_num
    unfold twentyOneFiftiethMomentCorrection
    dsimp [S2, S3, S4, S5] at *
    nlinarith [mul_nonneg hS2 hS3,
      mul_nonpos_of_nonneg_of_nonpos hS2 hcoef,
      mul_le_mul_of_nonneg_left hquad hS2]
  · have hmlo : (4981 / 12400 : ℝ) ≤ m := le_of_not_ge hm
    have hcoef := twentyOneFiftieth_large_max_cubic_nonpos hmlo hm1
    have hedm : 0 ≤ 7936 * m - 79696 / 25 := by nlinarith
    have h45 :
        7936 * S5 - (79696 / 25 : ℝ) * S4 ≤
          (7936 * m - 79696 / 25) * (m ^ 2 * S2) := by
      have hfirst :
          7936 * S5 - (79696 / 25 : ℝ) * S4 ≤
            (7936 * m - 79696 / 25) * S4 := by nlinarith
      exact hfirst.trans (mul_le_mul_of_nonneg_left hS4m hedm)
    unfold twentyOneFiftiethMomentCorrection
    dsimp [S2, S3, S4, S5] at *
    have hneg := mul_le_mul_of_nonneg_left hm3
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6720) hS2)
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hS2 hcoef,
      hneg]

end CertifiedJL.SparseLInfLower21Over50
