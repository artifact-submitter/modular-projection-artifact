/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Fourier.Prawitz.Kernel
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Sharp scalar bounds for the Prawitz kernel

This file isolates the one-variable analytic estimates traditionally
numbered I.29 and I.30 in Prawitz's treatment of the Berry--Esseen theorem.
The probability and smoothing layers consume only these concrete kernel
bounds; the alternating-series and scalar-certificate work belongs here.
-/

open Filter Set Topology
open scoped BigOperators
open scoped ComplexConjugate

namespace CertifiedJL
namespace Probability

lemma prawitzSinTerm_antitone {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 2) :
    Antitone (fun n : ℕ =>
      x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) := by
  apply antitone_nat_of_succ_le
  intro n
  have hx2 : x ^ 2 ≤ 5 / 2 := by
    have hpi := Real.pi_lt_d2
    nlinarith [sq_nonneg (x - Real.pi / 2)]
  have hden : (5 / 2 : ℝ) ≤
      ((2 * n + 2 : ℕ) : ℝ) * (2 * n + 3 : ℕ) := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    norm_num
    nlinarith
  have hdenPos : 0 <
      ((2 * n + 2 : ℕ) : ℝ) * (2 * n + 3 : ℕ) := by
    positivity
  have hratio :
      x ^ 2 /
          (((2 * n + 2 : ℕ) : ℝ) * (2 * n + 3 : ℕ)) ≤ 1 :=
    (div_le_one hdenPos).2 (hx2.trans hden)
  calc
    x ^ (2 * (n + 1) + 1) /
        ((2 * (n + 1) + 1).factorial : ℝ) =
        (x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) *
          (x ^ 2 /
            (((2 * n + 2 : ℕ) : ℝ) * (2 * n + 3 : ℕ))) := by
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega,
        pow_add]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one, Nat.cast_ofNat]
      field_simp
      ring
    _ ≤ (x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) * 1 := by
      exact mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by
      ring

/--
Fifth-order alternating-series upper bound for sine on `[0, π/2]`.
-/
lemma sin_le_taylor_five {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 2) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  let f : ℕ → ℝ :=
    fun n => x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)
  have hf : Antitone f := prawitzSinTerm_antitone hx0 hx
  have hsum :
      Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i)
        atTop (𝓝 (Real.sin x)) := by
    simpa only [f, div_eq_mul_inv, mul_assoc] using
      (Real.hasSum_sin x).tendsto_sum_nat
  have h := hf.tendsto_le_alternating_series hsum 1
  norm_num [f, Finset.sum_range_succ] at h ⊢
  linarith

/--
Third-order alternating-series lower bound for sine on `[0, π/2]`.
-/
lemma sin_taylor_three_le {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 2) :
    x - x ^ 3 / 6 ≤ Real.sin x := by
  let f : ℕ → ℝ :=
    fun n => x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)
  have hf : Antitone f := prawitzSinTerm_antitone hx0 hx
  have hsum :
      Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i)
        atTop (𝓝 (Real.sin x)) := by
    simpa only [f, div_eq_mul_inv, mul_assoc] using
      (Real.hasSum_sin x).tendsto_sum_nat
  have h := hf.alternating_series_le_tendsto hsum 1
  norm_num [f, Finset.sum_range_succ] at h ⊢
  linarith

/--
Seventh-order alternating-series lower bound for sine on `[0, π/2]`.
-/
lemma sin_taylor_seven_le {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 2) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤
      Real.sin x := by
  let f : ℕ → ℝ :=
    fun n => x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)
  have hf : Antitone f := prawitzSinTerm_antitone hx0 hx
  have hsum :
      Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i)
        atTop (𝓝 (Real.sin x)) := by
    simpa only [f, div_eq_mul_inv, mul_assoc] using
      (Real.hasSum_sin x).tendsto_sum_nat
  have h := hf.alternating_series_le_tendsto hsum 2
  norm_num [f, Finset.sum_range_succ] at h ⊢
  linarith

/-- Arbitrary-order lower alternating Taylor sum for sine on `[0,π/2]`.
This is the executable high-precision interface used by exact trigonometric
certificate checkers. -/
theorem sin_taylor_evenSum_le {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 2) (k : ℕ) :
    (∑ i ∈ Finset.range (2 * k),
        (-1 : ℝ) ^ i *
          (x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ))) ≤
      Real.sin x := by
  let f : ℕ → ℝ :=
    fun n => x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)
  have hf : Antitone f := prawitzSinTerm_antitone hx0 hx
  have hsum :
      Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i)
        atTop (𝓝 (Real.sin x)) := by
    simpa only [f, div_eq_mul_inv, mul_assoc] using
      (Real.hasSum_sin x).tendsto_sum_nat
  exact hf.alternating_series_le_tendsto hsum k

/-- Arbitrary-order upper alternating Taylor sum for sine on `[0,π/2]`. -/
theorem sin_le_taylor_oddSum {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 2) (k : ℕ) :
    Real.sin x ≤
      ∑ i ∈ Finset.range (2 * k + 1),
        (-1 : ℝ) ^ i *
          (x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)) := by
  let f : ℕ → ℝ :=
    fun n => x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)
  have hf : Antitone f := prawitzSinTerm_antitone hx0 hx
  have hsum :
      Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i)
        atTop (𝓝 (Real.sin x)) := by
    simpa only [f, div_eq_mul_inv, mul_assoc] using
      (Real.hasSum_sin x).tendsto_sum_nat
  exact hf.tendsto_le_alternating_series hsum k

lemma prawitzCosTailTerm_antitone {x : ℝ}
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

/--
Sixth-order alternating-series lower bound for cosine on `[0, π/2]`.
-/
lemma cos_taylor_six_le {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 2) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤
      Real.cos x := by
  let g : ℕ → ℝ :=
    fun n => x ^ (2 * (n + 1)) /
      ((2 * (n + 1)).factorial : ℝ)
  have hg : Antitone g := prawitzCosTailTerm_antitone hx0 hx
  have h := hg.tendsto_le_alternating_series
    (by simpa only [g] using cosTail_tendsto (x := x)) 1
  norm_num [g, Finset.sum_range_succ] at h ⊢
  linarith

/--
Fourth-order alternating-series upper bound for cosine on `[0, π/2]`.
-/
lemma cos_le_taylor_four {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 2) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let g : ℕ → ℝ :=
    fun n => x ^ (2 * (n + 1)) /
      ((2 * (n + 1)).factorial : ℝ)
  have hg : Antitone g := prawitzCosTailTerm_antitone hx0 hx
  have h := hg.alternating_series_le_tendsto
    (by simpa only [g] using cosTail_tendsto (x := x)) 1
  norm_num [g, Finset.sum_range_succ] at h ⊢
  linarith

/-- Arbitrary-order lower Taylor enclosure for cosine on `[0,π/2]`. -/
theorem cos_taylor_lowerSum_le {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 2) (k : ℕ) :
    1 - (∑ i ∈ Finset.range (2 * k + 1),
        (-1 : ℝ) ^ i *
          (x ^ (2 * (i + 1)) /
            ((2 * (i + 1)).factorial : ℝ))) ≤ Real.cos x := by
  let g : ℕ → ℝ :=
    fun n => x ^ (2 * (n + 1)) /
      ((2 * (n + 1)).factorial : ℝ)
  have hg : Antitone g := prawitzCosTailTerm_antitone hx0 hx
  have hupper := hg.tendsto_le_alternating_series
    (by simpa only [g] using cosTail_tendsto (x := x)) k
  dsimp only [g] at hupper ⊢
  linarith

/-- Arbitrary-order upper Taylor enclosure for cosine on `[0,π/2]`. -/
theorem cos_le_taylor_upperSum {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 2) (k : ℕ) :
    Real.cos x ≤
      1 - (∑ i ∈ Finset.range (2 * k),
        (-1 : ℝ) ^ i *
          (x ^ (2 * (i + 1)) /
            ((2 * (i + 1)).factorial : ℝ))) := by
  let g : ℕ → ℝ :=
    fun n => x ^ (2 * (n + 1)) /
      ((2 * (n + 1)).factorial : ℝ)
  have hg : Antitone g := prawitzCosTailTerm_antitone hx0 hx
  have hlower := hg.alternating_series_le_tendsto
    (by simpa only [g] using cosTail_tendsto (x := x)) k
  dsimp only [g] at hlower ⊢
  linarith

/--
Positive-frequency component identity for the Prawitz correction.  It is
the algebraic starting point of I.30.
-/
theorem prawitzKernel_sub_principal_pos
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    prawitzKernel t - Complex.I / (2 * Real.pi * t) =
      (((1 - t) / 2 : ℝ) : ℂ) +
        ((((1 - t) / 2 *
          (Real.cot (Real.pi * t) -
            1 / (Real.pi * t)) : ℝ) : ℂ) *
          Complex.I) := by
  have habs : |t| = t := abs_of_pos ht0
  have hsign : Real.sign t = 1 := Real.sign_of_pos ht0
  rw [prawitzKernel, prawitzKernelReal_of_abs_lt_one,
    prawitzKernelImag_of_abs_lt_one]
  · rw [habs, hsign]
    push_cast
    field_simp [Real.pi_ne_zero, ht0.ne']
    ring
  · simpa [habs] using ht1
  · simpa [habs] using ht1

private lemma pi_mul_sq_le_five_halves_of_le_half
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    (Real.pi * t) ^ 2 ≤ 5 / 2 := by
  have hpi := Real.pi_lt_d2
  have hmul : Real.pi * t ≤ Real.pi / 2 :=
    mul_le_mul_of_nonneg_left (by simpa using ht) Real.pi_pos.le
  have hmul0 : 0 ≤ Real.pi * t := mul_nonneg Real.pi_pos.le ht0
  nlinarith [sq_nonneg (Real.pi * t - Real.pi / 2)]

private lemma cot_le_inv_of_pos_of_le_pi_div_two
    {x : ℝ} (hx0 : 0 < x) (hx : x ≤ Real.pi / 2) :
    Real.cot x ≤ 1 / x := by
  by_cases heq : x = Real.pi / 2
  · rw [heq, Real.cot_eq_cos_div_sin]
    simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, div_one,
      one_div, inv_div]
    positivity
  · have hxlt : x < Real.pi / 2 := lt_of_le_of_ne hx heq
    have hcos : 0 < Real.cos x :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hxlt⟩
    have hsin : 0 < Real.sin x :=
      Real.sin_pos_of_pos_of_lt_pi hx0
        (hxlt.trans (half_lt_self Real.pi_pos))
    have htan := Real.le_tan hx0.le hxlt
    rw [Real.tan_eq_sin_div_cos] at htan
    rw [Real.cot_eq_cos_div_sin]
    exact (div_le_div_iff₀ hsin hx0).2
      (by simpa [mul_comm] using (le_div_iff₀ hcos).1 htan)

/--
Upper control of the cotangent residual on the left half of the Prawitz
band.  The rational denominator is chosen so that its square composes
directly with the I.30 norm estimate.
-/
private lemma inv_sub_cot_le_left
    {x : ℝ} (hx0 : 0 < x) (hx : x ≤ Real.pi / 2) :
    1 / x - Real.cot x ≤
      x / (3 * (1 - x ^ 2 / 10)) := by
  have hx2 : x ^ 2 ≤ 5 / 2 := by
    have hpi := Real.pi_lt_d2
    nlinarith [sq_nonneg (x - Real.pi / 2)]
  have hfactor : 0 < 1 - x ^ 2 / 10 := by
    nlinarith
  have hsin : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx0
      (hx.trans_lt (half_lt_self Real.pi_pos))
  have hsinLower := sin_taylor_three_le hx0.le hx
  have hsinUpper := sin_le_taylor_five hx0.le hx
  have hcosLower := cos_taylor_six_le hx0.le hx
  have hnum :
      Real.sin x - x * Real.cos x ≤
        x ^ 3 / 3 - x ^ 5 / 30 + x ^ 7 / 720 := by
    nlinarith
  have hz1 : x ^ 2 - 5 / 2 ≤ 0 := by linarith
  have hz2 : x ^ 2 - 63 / 2 ≤ 0 := by nlinarith
  have hpoly :
      0 ≤ (x ^ 2 - 5 / 2) * (x ^ 2 - 63 / 2) :=
    mul_nonneg_of_nonpos_of_nonpos hz1 hz2
  have hscalar :
      3 * (1 - x ^ 2 / 10) *
          (x ^ 3 / 3 - x ^ 5 / 30 + x ^ 7 / 720) ≤
        x ^ 2 * (x - x ^ 3 / 6) := by
    nlinarith [pow_nonneg hx0.le 5]
  have hcross :
      3 * (1 - x ^ 2 / 10) *
          (Real.sin x - x * Real.cos x) ≤
        x ^ 2 * Real.sin x := by
    calc
      3 * (1 - x ^ 2 / 10) *
          (Real.sin x - x * Real.cos x) ≤
          3 * (1 - x ^ 2 / 10) *
            (x ^ 3 / 3 - x ^ 5 / 30 + x ^ 7 / 720) := by
        exact mul_le_mul_of_nonneg_left hnum
          (mul_nonneg (by norm_num) hfactor.le)
      _ ≤ x ^ 2 * (x - x ^ 3 / 6) := hscalar
      _ ≤ x ^ 2 * Real.sin x :=
        mul_le_mul_of_nonneg_left hsinLower (sq_nonneg x)
  rw [Real.cot_eq_cos_div_sin]
  rw [show 1 / x - Real.cos x / Real.sin x =
      (Real.sin x - x * Real.cos x) /
        (x * Real.sin x) by
    field_simp [hx0.ne', hsin.ne']]
  rw [div_le_div_iff₀
    (mul_pos hx0 hsin)
    (mul_pos (by norm_num) hfactor)]
  nlinarith

private lemma prawitzCorrection_components_sq_le_left
    {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 2) :
    ((1 - t) / 2) ^ 2 +
        (((1 - t) / 2) *
          (Real.cot (Real.pi * t) -
            1 / (Real.pi * t))) ^ 2 ≤
      ((1 - t + Real.pi ^ 2 * t ^ 2 / 18) / 2) ^ 2 := by
  let x : ℝ := Real.pi * t
  let f : ℝ := 1 - x ^ 2 / 10
  let d : ℝ := 1 / x - Real.cot x
  have hx0 : 0 < x := mul_pos Real.pi_pos ht0
  have hxhalf : x ≤ Real.pi / 2 := by
    dsimp only [x]
    exact mul_le_mul_of_nonneg_left (by simpa using ht) Real.pi_pos.le
  have hx2 : x ^ 2 ≤ 5 / 2 :=
    pi_mul_sq_le_five_halves_of_le_half ht0.le ht
  have hf : 0 < f := by
    dsimp only [f]
    nlinarith
  have htOne : t ≤ 1 := ht.trans (by norm_num)
  have honeSub : 0 ≤ 1 - t := sub_nonneg.mpr htOne
  have hd0 : 0 ≤ d := by
    dsimp only [d]
    linarith [cot_le_inv_of_pos_of_le_pi_div_two hx0 hxhalf]
  have hd :
      d ≤ x / (3 * f) := by
    simpa only [d, f] using inv_sub_cot_le_left hx0 hxhalf
  have hpi2 : Real.pi ^ 2 < 10 := by
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hfactor :
      1 - t ≤ f ^ 2 := by
    dsimp only [f, x]
    have hpi2t : Real.pi ^ 2 * t ≤ 5 := by
      exact (mul_le_mul_of_nonneg_right hpi2.le ht0.le).trans
        (by nlinarith)
    have htFactor : 0 ≤ 1 - Real.pi ^ 2 * t / 5 := by
      nlinarith
    have hprod :
        0 ≤ t * (1 - Real.pi ^ 2 * t / 5) :=
      mul_nonneg ht0.le htFactor
    nlinarith [sq_nonneg (Real.pi ^ 2 * t ^ 2 / 10)]
  have hdmul :
      3 * f * d ≤ x := by
    have := (le_div_iff₀ (mul_pos (by norm_num) hf)).1 hd
    nlinarith
  have hdmul0 : 0 ≤ 3 * f * d := by positivity
  have hdsq :
      9 * f ^ 2 * d ^ 2 ≤ x ^ 2 := by
    calc
      9 * f ^ 2 * d ^ 2 = (3 * f * d) ^ 2 := by ring
      _ ≤ x ^ 2 := (sq_le_sq₀ hdmul0 hx0.le).2 hdmul
  have hweighted :
      9 * (1 - t) * d ^ 2 ≤ x ^ 2 := by
    have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
    nlinarith
  have himag :
      (((1 - t) / 2) *
          (Real.cot (Real.pi * t) -
            1 / (Real.pi * t))) ^ 2 ≤
        (1 - t) * x ^ 2 / 36 := by
    have hcot :
        Real.cot (Real.pi * t) -
            1 / (Real.pi * t) = -d := by
      dsimp only [d, x]
      ring
    rw [hcot]
    nlinarith [mul_nonneg honeSub (sq_nonneg d)]
  have htarget :
      (1 - t) * x ^ 2 / 36 =
        2 * ((1 - t) / 2) * (x ^ 2 / 36) := by ring
  rw [htarget] at himag
  have hA : 0 ≤ (1 - t) / 2 := by positivity
  have hC : 0 ≤ x ^ 2 / 36 := by positivity
  have hpi :
      Real.pi ^ 2 * t ^ 2 = x ^ 2 := by
    dsimp only [x]
    ring
  rw [hpi]
  nlinarith [sq_nonneg ((1 - t) / 2 + x ^ 2 / 36)]

/--
The first Bernoulli term in the cotangent residual on `[0, π/2]`.
-/
private lemma one_third_mul_le_inv_sub_cot
    {x : ℝ} (hx0 : 0 < x) (hx : x ≤ Real.pi / 2) :
    x / 3 ≤ 1 / x - Real.cot x := by
  have hx2 : x ^ 2 ≤ 5 / 2 := by
    have hpi := Real.pi_lt_d2
    nlinarith [sq_nonneg (x - Real.pi / 2)]
  have hfactor : 0 ≤ 1 - x ^ 2 / 3 := by nlinarith
  have hsin : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx0
      (hx.trans_lt (half_lt_self Real.pi_pos))
  have hsinLower := sin_taylor_three_le hx0.le hx
  have hcosUpper := cos_le_taylor_four hx0.le hx
  have hcross :
      x * Real.cos x ≤ (1 - x ^ 2 / 3) * Real.sin x := by
    calc
      x * Real.cos x ≤
          x * (1 - x ^ 2 / 2 + x ^ 4 / 24) :=
        mul_le_mul_of_nonneg_left hcosUpper hx0.le
      _ ≤ (1 - x ^ 2 / 3) * (x - x ^ 3 / 6) := by
        nlinarith [pow_nonneg hx0.le 5]
      _ ≤ (1 - x ^ 2 / 3) * Real.sin x :=
        mul_le_mul_of_nonneg_left hsinLower hfactor
  rw [Real.cot_eq_cos_div_sin]
  rw [show 1 / x - Real.cos x / Real.sin x =
      (Real.sin x - x * Real.cos x) /
        (x * Real.sin x) by
    field_simp [hx0.ne', hsin.ne']]
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3)
    (mul_pos hx0 hsin)]
  nlinarith

/--
The first two Bernoulli terms in the cotangent residual.  This is the
cancellation estimate needed for the near-zero part of I.29.
-/
private lemma one_third_mul_add_one_fortyfifth_mul_cube_le_inv_sub_cot
    {x : ℝ} (hx0 : 0 < x) (hx : x ≤ Real.pi / 2) :
    x / 3 + x ^ 3 / 45 ≤ 1 / x - Real.cot x := by
  have hx2 : x ^ 2 ≤ 5 / 2 := by
    have hpi := Real.pi_lt_d2
    nlinarith [sq_nonneg (x - Real.pi / 2)]
  have hfactor : 0 ≤ 1 - x ^ 2 / 3 - x ^ 4 / 45 := by
    have hx4 : x ^ 4 ≤ (5 / 2 : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (5 / 2 - x ^ 2)]
    nlinarith
  have hsin : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx0
      (hx.trans_lt (half_lt_self Real.pi_pos))
  have hsinLower := sin_taylor_seven_le hx0.le hx
  have hcosUpper := cos_le_taylor_four hx0.le hx
  have hpoly :
      0 ≤ x ^ 7 *
        (11 / 15120 - x ^ 2 / 8400 + x ^ 4 / 226800) := by
    have hx7 : 0 ≤ x ^ 7 := pow_nonneg hx0.le 7
    have hbracket :
        0 ≤ 11 / 15120 - x ^ 2 / 8400 +
          x ^ 4 / 226800 := by
      nlinarith [sq_nonneg (x ^ 2)]
    exact mul_nonneg hx7 hbracket
  have hcross :
      x * Real.cos x ≤
        (1 - x ^ 2 / 3 - x ^ 4 / 45) * Real.sin x := by
    calc
      x * Real.cos x ≤
          x * (1 - x ^ 2 / 2 + x ^ 4 / 24) :=
        mul_le_mul_of_nonneg_left hcosUpper hx0.le
      _ ≤ (1 - x ^ 2 / 3 - x ^ 4 / 45) *
          (x - x ^ 3 / 6 + x ^ 5 / 120 -
            x ^ 7 / 5040) := by
        nlinarith
      _ ≤ (1 - x ^ 2 / 3 - x ^ 4 / 45) *
          Real.sin x :=
        mul_le_mul_of_nonneg_left hsinLower hfactor
  rw [Real.cot_eq_cos_div_sin]
  rw [show 1 / x - Real.cos x / Real.sin x =
      (Real.sin x - x * Real.cos x) /
        (x * Real.sin x) by
    field_simp [hx0.ne', hsin.ne']]
  rw [le_div_iff₀ (mul_pos hx0 hsin)]
  nlinarith

/--
A rational upper envelope for the squared, `2πt`-scaled Prawitz kernel on
the left half-band.  The proof is an exact Bernstein-basis certificate,
split at `t = 1/4`; all displayed integer coefficients are positive.
-/
private lemma prawitzI29_left_rational_certificate
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    (1571 / 500 : ℝ) ^ 2 * t ^ 2 * (1 - t) ^ 2 +
        (1 - (1 - t) *
          (((6283 / 2000 : ℝ) ^ 2 * t ^ 2) / 3 +
            ((6283 / 2000 : ℝ) ^ 4 * t ^ 4) / 45)) ^ 2 ≤
      (513 / 500 : ℝ) ^ 2 := by
  by_cases hquarter : t ≤ 1 / 4
  · have hx0 : 0 ≤ 4 * t := by positivity
    have hy0 : 0 ≤ 1 - 4 * t := by linarith
    have hcertificate :
        (543581798400000000000000000000000000 : ℝ) *
          ((513 / 500 : ℝ) ^ 2 -
            ((1571 / 500 : ℝ) ^ 2 * t ^ 2 * (1 - t) ^ 2 +
              (1 - (1 - t) *
                (((6283 / 2000 : ℝ) ^ 2 * t ^ 2) / 3 +
                  ((6283 / 2000 : ℝ) ^ 4 * t ^ 4) / 45)) ^ 2)) =
          28633714812518400000000000000000000 *
              (1 - 4 * t) ^ 10 +
            286337148125184000000000000000000000 *
              (4 * t) * (1 - 4 * t) ^ 9 +
            1176647494533120000000000000000000000 *
              (4 * t) ^ 2 * (1 - 4 * t) ^ 8 +
            2652904704599654400000000000000000000 *
              (4 * t) ^ 3 * (1 - 4 * t) ^ 7 +
            3628693809714341521981440000000000000 *
              (4 * t) ^ 4 * (1 - 4 * t) ^ 6 +
            3099830815269200650567680000000000000 *
              (4 * t) ^ 5 * (1 - 4 * t) ^ 5 +
            1617161507776556296676567992320000000 *
              (4 * t) ^ 6 * (1 - 4 * t) ^ 4 +
            469479357362150471481587973120000000 *
              (4 * t) ^ 7 * (1 - 4 * t) ^ 3 +
            57702177557575934792256625540508144 *
              (4 * t) ^ 8 * (1 - 4 * t) ^ 2 +
            790363067957774243953720710762216 *
              (4 * t) ^ 9 * (1 - 4 * t) +
            501255539150261174495523506535831 *
              (4 * t) ^ 10 := by
      ring
    have hright : 0 ≤
          28633714812518400000000000000000000 *
              (1 - 4 * t) ^ 10 +
            286337148125184000000000000000000000 *
              (4 * t) * (1 - 4 * t) ^ 9 +
            1176647494533120000000000000000000000 *
              (4 * t) ^ 2 * (1 - 4 * t) ^ 8 +
            2652904704599654400000000000000000000 *
              (4 * t) ^ 3 * (1 - 4 * t) ^ 7 +
            3628693809714341521981440000000000000 *
              (4 * t) ^ 4 * (1 - 4 * t) ^ 6 +
            3099830815269200650567680000000000000 *
              (4 * t) ^ 5 * (1 - 4 * t) ^ 5 +
            1617161507776556296676567992320000000 *
              (4 * t) ^ 6 * (1 - 4 * t) ^ 4 +
            469479357362150471481587973120000000 *
              (4 * t) ^ 7 * (1 - 4 * t) ^ 3 +
            57702177557575934792256625540508144 *
              (4 * t) ^ 8 * (1 - 4 * t) ^ 2 +
            790363067957774243953720710762216 *
              (4 * t) ^ 9 * (1 - 4 * t) +
            501255539150261174495523506535831 *
              (4 * t) ^ 10 := by
      positivity
    nlinarith
  · have hquarter' : 1 / 4 ≤ t := le_of_not_ge hquarter
    have hx0 : 0 ≤ 4 * t - 1 := by linarith
    have hy0 : 0 ≤ 2 - 4 * t := by linarith
    have hcertificate :
        (543581798400000000000000000000000000 : ℝ) *
          ((513 / 500 : ℝ) ^ 2 -
            ((1571 / 500 : ℝ) ^ 2 * t ^ 2 * (1 - t) ^ 2 +
              (1 - (1 - t) *
                (((6283 / 2000 : ℝ) ^ 2 * t ^ 2) / 3 +
                  ((6283 / 2000 : ℝ) ^ 4 * t ^ 4) / 45)) ^ 2)) =
          501255539150261174495523506535831 *
              (2 - 4 * t) ^ 10 +
            9234747715047449245956749419954404 *
              (4 * t - 1) * (2 - 4 * t) ^ 9 +
            133701639381383009810283883923237836 *
              (4 * t - 1) ^ 2 * (2 - 4 * t) ^ 8 +
            821148519357395721580884819452768960 *
              (4 * t - 1) ^ 3 * (2 - 4 * t) ^ 7 +
            2660189021032207647035137093505095136 *
              (4 * t - 1) ^ 4 * (2 - 4 * t) ^ 6 +
            5169169528127687327349915011715962240 *
              (4 * t - 1) ^ 5 * (2 - 4 * t) ^ 5 +
            6382425482872392202979941693017435008 *
              (4 * t - 1) ^ 6 * (2 - 4 * t) ^ 4 +
            5073409694974887644185845311923284992 *
              (4 * t - 1) ^ 7 * (2 - 4 * t) ^ 3 +
            2524812174589392610662918948851075840 *
              (4 * t - 1) ^ 8 * (2 - 4 * t) ^ 2 +
            717852129822100178759814957027648512 *
              (4 * t - 1) ^ 9 * (2 - 4 * t) +
            89182618091707707791178154272521216 *
              (4 * t - 1) ^ 10 := by
      ring
    have hright : 0 ≤
          501255539150261174495523506535831 *
              (2 - 4 * t) ^ 10 +
            9234747715047449245956749419954404 *
              (4 * t - 1) * (2 - 4 * t) ^ 9 +
            133701639381383009810283883923237836 *
              (4 * t - 1) ^ 2 * (2 - 4 * t) ^ 8 +
            821148519357395721580884819452768960 *
              (4 * t - 1) ^ 3 * (2 - 4 * t) ^ 7 +
            2660189021032207647035137093505095136 *
              (4 * t - 1) ^ 4 * (2 - 4 * t) ^ 6 +
            5169169528127687327349915011715962240 *
              (4 * t - 1) ^ 5 * (2 - 4 * t) ^ 5 +
            6382425482872392202979941693017435008 *
              (4 * t - 1) ^ 6 * (2 - 4 * t) ^ 4 +
            5073409694974887644185845311923284992 *
              (4 * t - 1) ^ 7 * (2 - 4 * t) ^ 3 +
            2524812174589392610662918948851075840 *
              (4 * t - 1) ^ 8 * (2 - 4 * t) ^ 2 +
            717852129822100178759814957027648512 *
              (4 * t - 1) ^ 9 * (2 - 4 * t) +
            89182618091707707791178154272521216 *
              (4 * t - 1) ^ 10 := by
      positivity
    nlinarith

/-- Exact positive-frequency component formula inside the support band. -/
private lemma prawitzKernel_eq_components_pos
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    prawitzKernel t =
      (((1 - t) / 2 : ℝ) : ℂ) +
        (((((1 - t) * Real.cot (Real.pi * t) +
          1 / Real.pi) / 2 : ℝ) : ℂ) * Complex.I) := by
  have habs : |t| = t := abs_of_pos ht0
  have hsign : Real.sign t = 1 := Real.sign_of_pos ht0
  rw [prawitzKernel, prawitzKernelReal_of_abs_lt_one,
    prawitzKernelImag_of_abs_lt_one]
  · rw [habs, hsign]
  · simpa [habs] using ht1
  · simpa [habs] using ht1

/--
I.29 on the left half-band.  The proof exposes the cancellation in the
imaginary component and then invokes the rational Bernstein certificate.
-/
private lemma norm_prawitzKernel_le_i29_left
    {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 2) :
    ‖prawitzKernel t‖ ≤
      (513 / 500 : ℝ) / (2 * Real.pi * t) := by
  let x : ℝ := Real.pi * t
  let d : ℝ := 1 / x - Real.cot x
  let q : ℝ := 1 - (1 - t) * x * d
  let qBar : ℝ :=
    1 - (1 - t) *
      (((6283 / 2000 : ℝ) ^ 2 * t ^ 2) / 3 +
        ((6283 / 2000 : ℝ) ^ 4 * t ^ 4) / 45)
  have ht1 : t < 1 := ht.trans_lt (by norm_num)
  have hx0 : 0 < x := by
    dsimp only [x]
    positivity
  have hxhalf : x ≤ Real.pi / 2 := by
    dsimp only [x]
    exact mul_le_mul_of_nonneg_left
      (by simpa using ht) Real.pi_pos.le
  have hsin : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx0
      (hxhalf.trans_lt (half_lt_self Real.pi_pos))
  have hcos : 0 ≤ Real.cos x :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by nlinarith [Real.pi_pos]) hxhalf
  have hcot : 0 ≤ Real.cot x := by
    rw [Real.cot_eq_cos_div_sin]
    positivity
  have hd :=
    one_third_mul_add_one_fortyfifth_mul_cube_le_inv_sub_cot
      hx0 hxhalf
  have hpiLower : (6283 / 2000 : ℝ) < Real.pi := by
    convert Real.pi_gt_d4 using 1
    norm_num
  have hpiUpper : Real.pi < (1571 / 500 : ℝ) := by
    have h := Real.pi_lt_d4
    norm_num at h ⊢
    linarith
  have hxLower :
      (6283 / 2000 : ℝ) * t ≤ x := by
    dsimp only [x]
    exact mul_le_mul_of_nonneg_right hpiLower.le ht0.le
  have hxLower0 : 0 ≤ (6283 / 2000 : ℝ) * t := by
    positivity
  have hx2Lower :
      ((6283 / 2000 : ℝ) * t) ^ 2 ≤ x ^ 2 :=
    (sq_le_sq₀ hxLower0 hx0.le).2 hxLower
  have hx4Lower :
      ((6283 / 2000 : ℝ) * t) ^ 4 ≤ x ^ 4 := by
    have hsq0 : 0 ≤ ((6283 / 2000 : ℝ) * t) ^ 2 :=
      sq_nonneg _
    have hx20 : 0 ≤ x ^ 2 := sq_nonneg _
    calc
      ((6283 / 2000 : ℝ) * t) ^ 4 =
          (((6283 / 2000 : ℝ) * t) ^ 2) ^ 2 := by ring
      _ ≤ (x ^ 2) ^ 2 :=
        (sq_le_sq₀ hsq0 hx20).2 hx2Lower
      _ = x ^ 4 := by ring
  have honeSub : 0 ≤ 1 - t := by linarith
  have hxd :
      ((6283 / 2000 : ℝ) ^ 2 * t ^ 2) / 3 +
          ((6283 / 2000 : ℝ) ^ 4 * t ^ 4) / 45 ≤
        x * d := by
    have hmul :
        x * (x / 3 + x ^ 3 / 45) ≤ x * d :=
      mul_le_mul_of_nonneg_left hd hx0.le
    calc
      ((6283 / 2000 : ℝ) ^ 2 * t ^ 2) / 3 +
          ((6283 / 2000 : ℝ) ^ 4 * t ^ 4) / 45 ≤
          x ^ 2 / 3 + x ^ 4 / 45 := by
        nlinarith
      _ = x * (x / 3 + x ^ 3 / 45) := by ring
      _ ≤ x * d := hmul
  have hqUpper : q ≤ qBar := by
    dsimp only [q, qBar]
    simpa only [mul_assoc] using
      sub_le_sub_left
        (mul_le_mul_of_nonneg_left hxd honeSub) 1
  have hqIdentity :
      q = t + (1 - t) * x * Real.cot x := by
    dsimp only [q, d]
    field_simp [hx0.ne']
    ring
  have hq0 : 0 ≤ q := by
    rw [hqIdentity]
    positivity
  have hqBar0 : 0 ≤ qBar := hq0.trans hqUpper
  have hqSq : q ^ 2 ≤ qBar ^ 2 :=
    (sq_le_sq₀ hq0 hqBar0).2 hqUpper
  have hpiSq :
      Real.pi ^ 2 ≤ (1571 / 500 : ℝ) ^ 2 :=
    (sq_le_sq₀ Real.pi_pos.le (by norm_num)).2 hpiUpper.le
  have hrealFactor :
      0 ≤ t ^ 2 * (1 - t) ^ 2 := by positivity
  have hrealSq :
      (x * (1 - t)) ^ 2 ≤
        (1571 / 500 : ℝ) ^ 2 * t ^ 2 * (1 - t) ^ 2 := by
    dsimp only [x]
    calc
      (Real.pi * t * (1 - t)) ^ 2 =
          Real.pi ^ 2 * (t ^ 2 * (1 - t) ^ 2) := by ring
      _ ≤ (1571 / 500 : ℝ) ^ 2 *
          (t ^ 2 * (1 - t) ^ 2) :=
        mul_le_mul_of_nonneg_right hpiSq hrealFactor
      _ = _ := by ring
  have hcertificate :=
    prawitzI29_left_rational_certificate ht0.le ht
  have hsum :
      (x * (1 - t)) ^ 2 + q ^ 2 ≤
        (513 / 500 : ℝ) ^ 2 := by
    calc
      (x * (1 - t)) ^ 2 + q ^ 2 ≤
          (1571 / 500 : ℝ) ^ 2 * t ^ 2 *
              (1 - t) ^ 2 + qBar ^ 2 :=
        add_le_add hrealSq hqSq
      _ ≤ (513 / 500 : ℝ) ^ 2 := by
        simpa only [qBar] using hcertificate
  have hkernel := prawitzKernel_eq_components_pos ht0 ht1
  have hscaled :
      (2 * Real.pi * t * ‖prawitzKernel t‖) ^ 2 =
        (x * (1 - t)) ^ 2 + q ^ 2 := by
    rw [hkernel, mul_pow, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_im, Complex.I_re, mul_zero, Complex.I_im,
      sub_zero, add_zero, zero_add, mul_one]
    rw [hqIdentity]
    dsimp only [x]
    field_simp [Real.pi_ne_zero]
    ring
  have hscale0 :
      0 ≤ 2 * Real.pi * t * ‖prawitzKernel t‖ := by
    positivity
  have hc0 : 0 ≤ (513 / 500 : ℝ) := by norm_num
  have hscaledLe :
      2 * Real.pi * t * ‖prawitzKernel t‖ ≤
        (513 / 500 : ℝ) := by
    exact (sq_le_sq₀ hscale0 hc0).1
      (hscaled ▸ hsum)
  apply (le_div_iff₀
    (by positivity : 0 < 2 * Real.pi * t)).2
  simpa [mul_assoc, mul_comm, mul_left_comm] using hscaledLe

/--
On the right half-band the `2πt`-scaled kernel norm is at most one, leaving
substantial room below the I.29 constant.
-/
private lemma norm_prawitzKernel_le_i29_right
    {t : ℝ} (ht : 1 / 2 ≤ t) (ht1 : t < 1) :
    ‖prawitzKernel t‖ ≤
      1 / (2 * Real.pi * t) := by
  let x : ℝ := Real.pi * t
  let y : ℝ := Real.pi * (1 - t)
  let q : ℝ := t - (1 - t) * x * Real.cot y
  have ht0 : 0 < t := (by norm_num : (0 : ℝ) < 1 / 2).trans_le ht
  have honeSub : 0 ≤ 1 - t := by linarith
  have hx0 : 0 < x := by
    dsimp only [x]
    positivity
  have hy0 : 0 < y := by
    dsimp only [y]
    positivity
  have hyhalf : y ≤ Real.pi / 2 := by
    dsimp only [y]
    have : 1 - t ≤ 1 / 2 := by linarith
    exact mul_le_mul_of_nonneg_left
      (by simpa using this) Real.pi_pos.le
  have hsiny : 0 < Real.sin y :=
    Real.sin_pos_of_pos_of_lt_pi hy0
      (hyhalf.trans_lt (half_lt_self Real.pi_pos))
  have hcosy : 0 ≤ Real.cos y :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by nlinarith [Real.pi_pos]) hyhalf
  have hcoty0 : 0 ≤ Real.cot y := by
    rw [Real.cot_eq_cos_div_sin]
    positivity
  have hcotyUpper :=
    cot_le_inv_of_pos_of_le_pi_div_two hy0 hyhalf
  have hcotSymm :
      Real.cot x = -Real.cot y := by
    dsimp only [x, y]
    rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
    rw [show Real.pi * t = Real.pi -
        Real.pi * (1 - t) by ring]
    simp
    ring
  have hqUpper : q ≤ t := by
    dsimp only [q]
    exact sub_le_self t
      (mul_nonneg (mul_nonneg honeSub hx0.le) hcoty0)
  have hweighted :
      (1 - t) * x * Real.cot y ≤ t := by
    have hcoef : 0 ≤ (1 - t) * x := by positivity
    calc
      (1 - t) * x * Real.cot y ≤
          (1 - t) * x * (1 / y) :=
        mul_le_mul_of_nonneg_left hcotyUpper hcoef
      _ = t := by
        dsimp only [x, y]
        field_simp [Real.pi_ne_zero, (sub_pos.mpr ht1).ne']
  have hq0 : 0 ≤ q := by
    dsimp only [q]
    linarith
  have hqSq : q ^ 2 ≤ t ^ 2 :=
    (sq_le_sq₀ hq0 ht0.le).2 hqUpper
  have hpiSq : Real.pi ^ 2 < 10 := by
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hrealFactor :
      0 ≤ t ^ 2 * (1 - t) ^ 2 := by positivity
  have hrealSq :
      (x * (1 - t)) ^ 2 ≤
        10 * t ^ 2 * (1 - t) ^ 2 := by
    dsimp only [x]
    calc
      (Real.pi * t * (1 - t)) ^ 2 =
          Real.pi ^ 2 * (t ^ 2 * (1 - t) ^ 2) := by ring
      _ ≤ 10 * (t ^ 2 * (1 - t) ^ 2) :=
        mul_le_mul_of_nonneg_right hpiSq.le hrealFactor
      _ = _ := by ring
  let s : ℝ := t - 1 / 2
  have hs0 : 0 ≤ s := by
    dsimp only [s]
    linarith
  have hinner :
      0 ≤ 10 * s ^ 3 + 5 * (s - 3 / 20) ^ 2 + 11 / 80 := by
    positivity
  have hpoly :
      10 * t ^ 2 * (1 - t) ^ 2 + t ^ 2 ≤ 1 := by
    have hfactor :
        0 ≤ (1 - t) *
          (10 * s ^ 3 + 5 * (s - 3 / 20) ^ 2 + 11 / 80) :=
      mul_nonneg honeSub hinner
    dsimp only [s] at hfactor
    nlinarith
  have hsum :
      (x * (1 - t)) ^ 2 + q ^ 2 ≤ 1 := by
    calc
      (x * (1 - t)) ^ 2 + q ^ 2 ≤
          10 * t ^ 2 * (1 - t) ^ 2 + t ^ 2 :=
        add_le_add hrealSq hqSq
      _ ≤ 1 := hpoly
  have hkernel := prawitzKernel_eq_components_pos ht0 ht1
  have hscaled :
      (2 * Real.pi * t * ‖prawitzKernel t‖) ^ 2 =
        (x * (1 - t)) ^ 2 + q ^ 2 := by
    rw [hkernel, mul_pow, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_im, Complex.I_re, mul_zero, Complex.I_im,
      sub_zero, add_zero, zero_add, mul_one]
    dsimp only [q, x]
    rw [hcotSymm]
    dsimp only [y]
    field_simp [Real.pi_ne_zero]
    ring
  have hscale0 :
      0 ≤ 2 * Real.pi * t * ‖prawitzKernel t‖ := by
    positivity
  have hscaledLe :
      2 * Real.pi * t * ‖prawitzKernel t‖ ≤ 1 := by
    exact (sq_le_sq₀ hscale0 (by norm_num)).1
      (hscaled ▸ (by simpa only [one_pow] using hsum))
  apply (le_div_iff₀
    (by positivity : 0 < 2 * Real.pi * t)).2
  simpa [mul_assoc, mul_comm, mul_left_comm] using hscaledLe

/-- I.29 on the closed positive support band. -/
private theorem norm_prawitzKernel_le_i29_of_pos
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ‖prawitzKernel t‖ ≤
      (513 / 500 : ℝ) / (2 * Real.pi * t) := by
  rcases ht1.eq_or_lt with rfl | ht1
  · rw [prawitzKernel_one, norm_zero]
    positivity
  by_cases hhalf : t ≤ 1 / 2
  · exact norm_prawitzKernel_le_i29_left ht0 hhalf
  · have hright :=
      norm_prawitzKernel_le_i29_right
        (le_of_not_ge hhalf) ht1
    calc
      ‖prawitzKernel t‖ ≤ 1 / (2 * Real.pi * t) :=
        hright
      _ ≤ (513 / 500 : ℝ) / (2 * Real.pi * t) := by
        exact div_le_div_of_nonneg_right (by norm_num)
          (by positivity)

/--
Prawitz's kernel-height inequality I.29, with the historical constant
slightly relaxed from `1.0253` to the exact rational `513/500 = 1.026`.
-/
theorem norm_prawitzKernel_le_i29
    {t : ℝ} (ht0 : 0 < |t|) (ht1 : |t| ≤ 1) :
    ‖prawitzKernel t‖ ≤
      (513 / 500 : ℝ) / (2 * Real.pi * |t|) := by
  by_cases hnonneg : 0 ≤ t
  · have htpos : 0 < t := by
      simpa [abs_of_nonneg hnonneg] using ht0
    simpa [abs_of_nonneg hnonneg] using
      norm_prawitzKernel_le_i29_of_pos htpos
        (by simpa [abs_of_nonneg hnonneg] using ht1)
  · have htneg : t < 0 := lt_of_not_ge hnonneg
    have h :=
      norm_prawitzKernel_le_i29_of_pos
        (show 0 < -t by linarith)
        (by simpa [abs_of_neg htneg] using ht1)
    rw [prawitzKernel_neg, Complex.norm_conj] at h
    simpa [abs_of_neg htneg] using h

/--
Endpoint-vanishing kernel bound on the right half of the support.  This
complements I.29 in outer-band certificates, where retaining the factor
`1 - t` is essential.
-/
theorem norm_prawitzKernel_le_endpoint
    {t : ℝ} (ht : 1 / 2 ≤ t) (ht1 : t < 1) :
    ‖prawitzKernel t‖ ≤
      (1 - t) / 2 + Real.pi * (1 - t) ^ 2 / 4 := by
  let y : ℝ := Real.pi * (1 - t)
  let d : ℝ := 1 / y - Real.cot y
  have ht0 : 0 < t := (by norm_num : (0 : ℝ) < 1 / 2).trans_le ht
  have honeSub : 0 ≤ 1 - t := by linarith
  have hy0 : 0 < y := by
    dsimp only [y]
    positivity
  have hyhalf : y ≤ Real.pi / 2 := by
    dsimp only [y]
    have : 1 - t ≤ 1 / 2 := by linarith
    exact mul_le_mul_of_nonneg_left
      (by simpa using this) Real.pi_pos.le
  have hy2 : y ^ 2 ≤ 5 / 2 := by
    have hpi := Real.pi_lt_d2
    nlinarith [sq_nonneg (y - Real.pi / 2)]
  have hfactor : 0 < 1 - y ^ 2 / 10 := by
    nlinarith
  have hd0 : 0 ≤ d := by
    dsimp only [d]
    linarith [cot_le_inv_of_pos_of_le_pi_div_two hy0 hyhalf]
  have hdUpperRaw := inv_sub_cot_le_left hy0 hyhalf
  have hdUpper : d ≤ y / 2 := by
    dsimp only [d] at hdUpperRaw ⊢
    calc
      1 / y - Real.cot y ≤
          y / (3 * (1 - y ^ 2 / 10)) := hdUpperRaw
      _ ≤ y / 2 := by
        rw [div_le_div_iff₀
          (mul_pos (by norm_num) hfactor)
          (by norm_num : (0 : ℝ) < 2)]
        nlinarith
  have hcotSymm :
      Real.cot (Real.pi * t) = -Real.cot y := by
    dsimp only [y]
    rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
    rw [show Real.pi * t = Real.pi -
        Real.pi * (1 - t) by ring]
    simp
    ring
  have himagIdentity :
      ((1 - t) * Real.cot (Real.pi * t) +
          1 / Real.pi) / 2 =
        (1 - t) * d / 2 := by
    rw [hcotSymm]
    dsimp only [d, y]
    field_simp [Real.pi_ne_zero, (sub_pos.mpr ht1).ne']
    ring
  have himag0 :
      0 ≤ ((1 - t) * Real.cot (Real.pi * t) +
          1 / Real.pi) / 2 := by
    rw [himagIdentity]
    positivity
  have himagUpper :
      ((1 - t) * Real.cot (Real.pi * t) +
          1 / Real.pi) / 2 ≤
        Real.pi * (1 - t) ^ 2 / 4 := by
    rw [himagIdentity]
    calc
      (1 - t) * d / 2 ≤ (1 - t) * (y / 2) / 2 := by
        gcongr
      _ = Real.pi * (1 - t) ^ 2 / 4 := by
        dsimp only [y]
        ring
  rw [prawitzKernel_eq_components_pos ht0 ht1]
  calc
    ‖(((1 - t) / 2 : ℝ) : ℂ) +
        (((((1 - t) * Real.cot (Real.pi * t) +
          1 / Real.pi) / 2 : ℝ) : ℂ) * Complex.I)‖ ≤
        ‖(((1 - t) / 2 : ℝ) : ℂ)‖ +
          ‖(((((1 - t) * Real.cot (Real.pi * t) +
            1 / Real.pi) / 2 : ℝ) : ℂ) * Complex.I)‖ :=
      norm_add_le _ _
    _ = (1 - t) / 2 +
        ((1 - t) * Real.cot (Real.pi * t) +
          1 / Real.pi) / 2 := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_I, mul_one]
      rw [abs_of_nonneg (by positivity), abs_of_nonneg himag0]
    _ ≤ (1 - t) / 2 +
        Real.pi * (1 - t) ^ 2 / 4 :=
      add_le_add le_rfl himagUpper

private lemma rightCorrectionEnvelope_le_three_eighths
    {t : ℝ} (ht : 1 / 2 ≤ t) (ht1 : t < 1) :
    1 / (Real.pi * t) -
        Real.pi * (1 - t) ^ 2 / 3 ≤
      3 / 8 := by
  let g : ℝ → ℝ := fun z =>
    1 / (Real.pi * z) - Real.pi * (1 - z) ^ 2 / 3
  have hcontinuous : ContinuousOn g (Icc (1 / 2) 1) := by
    apply ContinuousOn.sub
    · exact continuousOn_const.div
        (continuousOn_const.mul continuousOn_id)
        (fun z hz => mul_ne_zero Real.pi_ne_zero (by
          have := hz.1
          norm_num at this ⊢
          linarith))
    · fun_prop
  have hanti : StrictAntiOn g (Icc (1 / 2) 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hcontinuous
    intro z hz
    rw [interior_Icc] at hz
    have hz0 : 0 < z := by linarith [hz.1]
    have hz1 : z < 1 := hz.2
    have hzmax :
        z ^ 2 * (1 - z) ≤ 4 / 27 := by
      have hnonneg :
          0 ≤ (z - 2 / 3) ^ 2 * (z + 1 / 3) := by
        positivity
      nlinarith
    have hpi2 : Real.pi ^ 2 < 10 := by
      nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have hnum :
        2 * Real.pi ^ 2 * z ^ 2 * (1 - z) < 3 := by
      have hzNonneg : 0 ≤ z ^ 2 * (1 - z) :=
        mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hz1.le)
      calc
        2 * Real.pi ^ 2 * z ^ 2 * (1 - z) <
            2 * 10 * (z ^ 2 * (1 - z)) := by
          simpa only [mul_assoc] using
            mul_lt_mul_of_pos_right
              (mul_lt_mul_of_pos_left hpi2
                (by norm_num : (0 : ℝ) < 2))
              (mul_pos (sq_pos_of_pos hz0) (sub_pos.mpr hz1))
        _ ≤ 2 * 10 * (4 / 27 : ℝ) := by gcongr
        _ < 3 := by norm_num
    have hderiv :
        HasDerivAt g
          (-1 / (Real.pi * z ^ 2) +
            2 * Real.pi * (1 - z) / 3) z := by
      dsimp only [g]
      have hfirst :
          HasDerivAt (fun w : ℝ => 1 / (Real.pi * w))
            (-1 / (Real.pi * z ^ 2)) z := by
        convert
          ((hasDerivAt_const z (1 : ℝ)).div
          ((hasDerivAt_const z Real.pi).mul
            (hasDerivAt_id z))
          (mul_ne_zero Real.pi_ne_zero hz0.ne')) using 1 <;> try rfl
        simp only [Pi.mul_apply, id_eq, zero_mul, mul_one, zero_add,
          one_mul]
        field_simp [Real.pi_ne_zero, hz0.ne']
        ring
      have hsecond :
          HasDerivAt (fun w : ℝ => Real.pi * (1 - w) ^ 2 / 3)
            (-2 * Real.pi * (1 - z) / 3) z := by
        convert
          (((hasDerivAt_const z Real.pi).mul
            (((hasDerivAt_const z (1 : ℝ)).sub
              (hasDerivAt_id z)).pow 2)).div_const 3) using 1 <;> try rfl
        simp only [Pi.sub_apply, id_eq, zero_mul, zero_sub,
          Nat.cast_ofNat, Nat.reduceSubDiff, pow_one, mul_neg, mul_one,
          zero_add]
        ring
      convert hfirst.sub hsecond using 1 <;> try rfl
      ring
    rw [hderiv.deriv]
    have hden : 0 < 3 * Real.pi * z ^ 2 := by positivity
    calc
      -1 / (Real.pi * z ^ 2) +
          2 * Real.pi * (1 - z) / 3 =
          (-3 + 2 * Real.pi ^ 2 * z ^ 2 * (1 - z)) /
            (3 * Real.pi * z ^ 2) := by
        field_simp [Real.pi_ne_zero, hz0.ne']
      _ < 0 := div_neg_of_neg_of_pos (by linarith) hden
  have hhalfMem : (1 / 2 : ℝ) ∈ Icc (1 / 2) 1 := by norm_num
  have htMem : t ∈ Icc (1 / 2) 1 := ⟨ht, ht1.le⟩
  have hmonotone :
      g t ≤ g (1 / 2) := by
    rcases ht.eq_or_lt with rfl | hlt
    · exact le_rfl
    · exact (hanti hhalfMem htMem hlt).le
  have hpiLower : (3.1415 : ℝ) < Real.pi :=
    Real.pi_gt_d4
  have hhalf :
      g (1 / 2) ≤ 3 / 8 := by
    dsimp only [g]
    norm_num
    calc
      2 * Real.pi⁻¹ =
          2 / Real.pi := by ring
      _ ≤ 3 / 8 + Real.pi * (1 / 4) / 3 := by
        rw [div_le_iff₀ Real.pi_pos]
        nlinarith [sq_nonneg (Real.pi - 3.1415)]
  exact hmonotone.trans hhalf

private lemma prawitzCorrection_components_sq_le_right
    {t : ℝ} (ht : 1 / 2 ≤ t) (ht1 : t < 1) :
    ((1 - t) / 2) ^ 2 +
        (((1 - t) / 2) *
          (Real.cot (Real.pi * t) -
            1 / (Real.pi * t))) ^ 2 ≤
      ((1 - t + Real.pi ^ 2 * t ^ 2 / 18) / 2) ^ 2 := by
  let x : ℝ := Real.pi * t
  let y : ℝ := Real.pi * (1 - t)
  let d : ℝ := 1 / x - Real.cot x
  have ht0 : 0 < t := (by norm_num : (0 : ℝ) < 1 / 2).trans_le ht
  have htOne : t ≤ 1 := ht1.le
  have hx0 : 0 < x := mul_pos Real.pi_pos ht0
  have hxltPi : x < Real.pi := by
    dsimp only [x]
    nlinarith [Real.pi_pos]
  have hy0 : 0 < y := by
    dsimp only [y]
    positivity
  have hyhalf : y ≤ Real.pi / 2 := by
    dsimp only [y]
    have honeSub : 1 - t ≤ 1 / 2 := by linarith
    exact mul_le_mul_of_nonneg_left
      (by simpa using honeSub) Real.pi_pos.le
  have hsinx : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx0 hxltPi
  have hcosx : Real.cos x ≤ 0 := by
    exact Real.cos_nonpos_of_pi_div_two_le_of_le
      (by
        dsimp only [x]
        exact mul_le_mul_of_nonneg_left
          (by simpa using ht) Real.pi_pos.le)
      (by linarith [hxltPi, Real.pi_pos])
  have hd0 : 0 ≤ d := by
    dsimp only [d]
    rw [Real.cot_eq_cos_div_sin]
    have hcot : Real.cos x / Real.sin x ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hcosx hsinx.le
    have hinv : 0 ≤ 1 / x := by positivity
    linarith
  have hcotSymm :
      Real.cot x = -Real.cot y := by
    dsimp only [x, y]
    rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
    rw [show Real.pi * t = Real.pi -
        Real.pi * (1 - t) by ring]
    simp
    ring
  have hyResidual :=
    one_third_mul_le_inv_sub_cot hy0 hyhalf
  have hdUpper :
      d ≤ 1 / x + 1 / y - y / 3 := by
    dsimp only [d]
    rw [hcotSymm]
    linarith
  have hweighted :
      (1 - t) * d ≤
        1 / x - y ^ 2 / (3 * Real.pi) := by
    have hrelation : 1 - t = y / Real.pi := by
      dsimp only [y]
      field_simp [Real.pi_ne_zero]
    rw [hrelation]
    have hcoef : 0 ≤ y / Real.pi := by positivity
    calc
      y / Real.pi * d ≤
          y / Real.pi * (1 / x + 1 / y - y / 3) :=
        mul_le_mul_of_nonneg_left hdUpper hcoef
      _ = 1 / x - y ^ 2 / (3 * Real.pi) := by
        have hsum : x + y = Real.pi := by
          dsimp only [x, y]
          ring
        field_simp [Real.pi_ne_zero, hx0.ne', hy0.ne']
        nlinarith
  have henvelope :
      1 / x - y ^ 2 / (3 * Real.pi) ≤ 3 / 8 := by
    have h :=
      rightCorrectionEnvelope_le_three_eighths ht ht1
    dsimp only [x, y]
    convert h using 1
    field_simp [Real.pi_ne_zero]
  have hE :
      (1 - t) * d ≤ 3 / 8 :=
    hweighted.trans henvelope
  have hE0 : 0 ≤ (1 - t) * d :=
    mul_nonneg (sub_nonneg.mpr htOne) hd0
  have himag :
      (((1 - t) / 2) *
          (Real.cot (Real.pi * t) -
            1 / (Real.pi * t))) ^ 2 ≤
        (3 / 16 : ℝ) ^ 2 := by
    have hcot :
        Real.cot (Real.pi * t) -
            1 / (Real.pi * t) = -d := by
      dsimp only [d, x]
      ring
    rw [hcot]
    have hsquare :
        ((1 - t) * d) ^ 2 ≤ (3 / 8 : ℝ) ^ 2 :=
      (sq_le_sq₀ hE0 (by norm_num)).2 hE
    nlinarith
  have hpi2 : 9 < Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three, Real.pi_pos]
  have hbase :
      9 / 256 ≤
        (1 - t) * (Real.pi ^ 2 * t ^ 2) / 36 +
          (Real.pi ^ 2 * t ^ 2 / 36) ^ 2 := by
    have hnonneg1 : 0 ≤ t ^ 2 * (1 - t) :=
      mul_nonneg (sq_nonneg t) (sub_nonneg.mpr htOne)
    have hterm :
        t ^ 2 * (1 - t) / 4 + t ^ 4 / 16 ≤
          (1 - t) * (Real.pi ^ 2 * t ^ 2) / 36 +
            (Real.pi ^ 2 * t ^ 2 / 36) ^ 2 := by
      have hfirst :
          t ^ 2 * (1 - t) / 4 ≤
            (1 - t) * (Real.pi ^ 2 * t ^ 2) / 36 := by
        nlinarith
      have hsecond :
          t ^ 4 / 16 ≤
            (Real.pi ^ 2 * t ^ 2 / 36) ^ 2 := by
        nlinarith [sq_nonneg (Real.pi ^ 2 * t ^ 2 / 36 -
          t ^ 2 / 4)]
      linarith
    have hprod :
        3 / 4 ≤ t * (2 - t) := by
      have hnonneg :
          0 ≤ (t - 1 / 2) * (3 / 2 - t) :=
        mul_nonneg (sub_nonneg.mpr ht)
          (sub_nonneg.mpr (by linarith))
      nlinarith
    have hprod0 : 0 ≤ t * (2 - t) := by positivity
    have hsquare :
        (3 / 4 : ℝ) ^ 2 ≤ (t * (2 - t)) ^ 2 :=
      (sq_le_sq₀ (by norm_num) hprod0).2 hprod
    calc
      9 / 256 ≤ t ^ 2 * (1 - t) / 4 + t ^ 4 / 16 := by
        nlinarith
      _ ≤ _ := hterm
  have hA : 0 ≤ (1 - t) / 2 := by positivity
  have hC : 0 ≤ Real.pi ^ 2 * t ^ 2 / 36 := by positivity
  nlinarith [sq_nonneg
    ((1 - t) / 2 + Real.pi ^ 2 * t ^ 2 / 36)]

/--
Prawitz's I.30 kernel-correction inequality on the nonnegative half-band.
-/
private theorem norm_prawitzKernel_sub_principal_le_of_nonneg
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖prawitzKernel t - Complex.I / (2 * Real.pi * t)‖ ≤
      (1 - t + Real.pi ^ 2 * t ^ 2 / 18) / 2 := by
  rcases ht0.eq_or_lt with rfl | ht0
  · simp [prawitzKernel_zero]
  rcases ht1.eq_or_lt with rfl | ht1
  · rw [prawitzKernel_one, zero_sub, norm_neg, norm_div,
      Complex.norm_I]
    norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    have hpiCube : 18 ≤ Real.pi ^ 3 := by
      nlinarith [Real.pi_gt_three, Real.pi_pos,
        sq_nonneg (Real.pi - 3)]
    rw [show Real.pi⁻¹ * (1 / 2 : ℝ) =
        1 / (2 * Real.pi) by
      field_simp [Real.pi_ne_zero]]
    rw [div_le_iff₀ (mul_pos (by norm_num) Real.pi_pos)]
    nlinarith
  · have hidentity :=
      prawitzKernel_sub_principal_pos ht0 ht1
    rw [hidentity]
    let a : ℝ := (1 - t) / 2
    let b : ℝ := (1 - t) / 2 *
      (Real.cot (Real.pi * t) - 1 / (Real.pi * t))
    have hcomponents :
        a ^ 2 + b ^ 2 ≤
          ((1 - t + Real.pi ^ 2 * t ^ 2 / 18) / 2) ^ 2 := by
      by_cases hhalf : t ≤ 1 / 2
      · simpa only [a, b] using
          prawitzCorrection_components_sq_le_left ht0 hhalf
      · simpa only [a, b] using
          prawitzCorrection_components_sq_le_right
            (le_of_not_ge hhalf) ht1
    have hsquare :
        norm ((a : ℂ) + (b : ℂ) * Complex.I) ^ 2 ≤
          ((1 - t + Real.pi ^ 2 * t ^ 2 / 18) / 2) ^ 2 := by
      rw [Complex.sq_norm]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_im,
        Complex.I_re, mul_zero, Complex.I_im, sub_zero,
        add_zero, zero_add, mul_one]
      simpa only [sq] using hcomponents
    have hright :
        0 ≤ (1 - t + Real.pi ^ 2 * t ^ 2 / 18) / 2 := by
      positivity
    simpa only [a, b] using
      (sq_le_sq₀ (norm_nonneg _) hright).1 hsquare

/--
Prawitz's kernel-correction inequality I.30, with exact rational
coefficients and the closed support band made explicit.
-/
theorem norm_prawitzKernel_sub_principal_le
    {t : ℝ} (ht : |t| ≤ 1) :
    ‖prawitzKernel t - Complex.I / (2 * Real.pi * t)‖ ≤
      (1 - |t| + Real.pi ^ 2 * t ^ 2 / 18) / 2 := by
  by_cases ht0 : 0 ≤ t
  · simpa [abs_of_nonneg ht0] using
      norm_prawitzKernel_sub_principal_le_of_nonneg
        ht0 (by simpa [abs_of_nonneg ht0] using ht)
  · have hneg : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht0)
    have hband : -t ≤ 1 := by
      simpa [abs_of_neg (lt_of_not_ge ht0)] using ht
    have h :=
      norm_prawitzKernel_sub_principal_le_of_nonneg hneg hband
    have hkernel :
        prawitzKernel (-t) -
            Complex.I /
              ((2 : ℂ) * (Real.pi : ℂ) * ((-t : ℝ) : ℂ)) =
          conj (prawitzKernel t -
            Complex.I / (2 * Real.pi * t)) := by
      rw [prawitzKernel_neg]
      push_cast
      simp only [map_sub, map_div₀, map_mul, Complex.conj_I,
        Complex.conj_ofReal, map_ofNat]
      field_simp [Real.pi_ne_zero, (lt_of_not_ge ht0).ne]
    rw [hkernel, Complex.norm_conj] at h
    simpa [abs_of_neg (lt_of_not_ge ht0), neg_sq] using h

end Probability
end CertifiedJL
