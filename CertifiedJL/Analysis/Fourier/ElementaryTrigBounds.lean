/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Lightweight elementary trigonometric bounds

Only alternating Taylor series and rational arithmetic are used here.
-/

open Filter Set Topology
open scoped BigOperators

namespace CertifiedJL.Probability

private lemma cosTailTerm_antitone {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 2) :
    Antitone (fun n : ℕ =>
      x ^ (2 * (n + 1)) / ((2 * (n + 1)).factorial : ℝ)) := by
  apply antitone_nat_of_succ_le
  intro n
  have hx2 : x ^ 2 ≤ 5 / 2 := by
    have hpi := Real.pi_lt_d2
    nlinarith [sq_nonneg (x - Real.pi / 2)]
  have hden : (5 / 2 : ℝ) ≤
      ((2 * n + 3 : ℕ) : ℝ) * (2 * n + 4 : ℕ) := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    norm_num
    nlinarith
  have hdenPos : 0 <
      ((2 * n + 3 : ℕ) : ℝ) * (2 * n + 4 : ℕ) := by
    positivity
  have hratio :
      x ^ 2 /
          (((2 * n + 3 : ℕ) : ℝ) * (2 * n + 4 : ℕ)) ≤ 1 :=
    (div_le_one hdenPos).2 (hx2.trans hden)
  calc
    x ^ (2 * ((n + 1) + 1)) /
        ((2 * ((n + 1) + 1)).factorial : ℝ) =
        (x ^ (2 * (n + 1)) / ((2 * (n + 1)).factorial : ℝ)) *
          (x ^ 2 /
            (((2 * n + 3 : ℕ) : ℝ) * (2 * n + 4 : ℕ))) := by
      rw [show 2 * ((n + 1) + 1) = 2 * (n + 1) + 2 by omega,
        pow_add]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one, Nat.cast_ofNat]
      field_simp
      ring
    _ ≤
        (x ^ (2 * (n + 1)) / ((2 * (n + 1)).factorial : ℝ)) * 1 := by
      exact mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = x ^ (2 * (n + 1)) / ((2 * (n + 1)).factorial : ℝ) := by
      ring

private lemma cosTail_tendsto {x : ℝ} :
    let g : ℕ → ℝ :=
      fun n => x ^ (2 * (n + 1)) /
        ((2 * (n + 1)).factorial : ℝ)
    Tendsto
      (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * g i)
      atTop (𝓝 (1 - Real.cos x)) := by
  dsimp only
  have hshift :
      HasSum
        (fun n : ℕ =>
          (-1 : ℝ) ^ (n + 1) *
            x ^ (2 * (n + 1)) /
              ((2 * (n + 1)).factorial : ℝ))
        (Real.cos x - 1) := by
    have hraw := (hasSum_nat_add_iff' 1).2 (Real.hasSum_cos x)
    have hone :
        (∑ i ∈ Finset.range 1,
          (-1 : ℝ) ^ i * x ^ (2 * i) /
            ((2 * i).factorial : ℝ)) = 1 := by
      norm_num
    rw [hone] at hraw
    exact hraw
  have hneg := hshift.neg
  have heq :
      (fun n : ℕ =>
        -((-1 : ℝ) ^ (n + 1) *
          x ^ (2 * (n + 1)) /
            ((2 * (n + 1)).factorial : ℝ))) =
      (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (x ^ (2 * (n + 1)) /
            ((2 * (n + 1)).factorial : ℝ))) := by
    funext n
    simp only [_root_.pow_succ]
    ring
  rw [heq] at hneg
  simpa only [neg_sub] using hneg.tendsto_sum_nat

/-- Sixth-order alternating-series lower bound for cosine on `[0, π/2]`. -/
lemma elementary_cos_taylor_six_le {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 2) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤
      Real.cos x := by
  let g : ℕ → ℝ :=
    fun n => x ^ (2 * (n + 1)) /
      ((2 * (n + 1)).factorial : ℝ)
  have hg : Antitone g := cosTailTerm_antitone hx0 hx
  have h := hg.tendsto_le_alternating_series
    (by simpa only [g] using cosTail_tendsto (x := x)) 1
  norm_num [g, Finset.sum_range_succ] at h ⊢
  linarith

end CertifiedJL.Probability

