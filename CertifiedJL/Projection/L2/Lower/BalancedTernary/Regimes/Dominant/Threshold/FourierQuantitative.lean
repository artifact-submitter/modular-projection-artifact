/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.WrappedFourier
import CertifiedJL.Analysis.Fourier.ElementaryCosineSmallBall

/-!
# Quantitative retained modes for the public-threshold dominant branch

The second cyclic mode can leave the central cosine lobe when `q/A` is close
to two.  On the compact medium-residual profile, however, every normalized
coordinate is at most `13/16`.  The elementary bound below controls the whole
enlarged lobe, including the portion past `π/2`, without a numerical oracle.
-/

open scoped BigOperators
open Set

namespace CertifiedJL

/-- A deliberately slack elementary envelope for the enlarged second-mode
lobe.  It combines the standard Gaussian cosine estimate on `[0,π/2]` with
monotonicity of cosine on the reflected interval `[3π/16,π/2]`. -/
theorem cos_sq_le_exp_neg_seven_two_hundredths_sq
    {x : ℝ} (hx : |x| ≤ 13 * Real.pi / 16) :
    Real.cos x ^ 2 ≤ Real.exp (-(7 / 200 : ℝ) * x ^ 2) := by
  wlog hxnonneg : 0 ≤ x generalizing x
  · have hneg : 0 ≤ -x := neg_nonneg.mpr (le_of_not_ge hxnonneg)
    have hband : |-x| ≤ 13 * Real.pi / 16 := by simpa using hx
    simpa [Real.cos_neg] using this hband hneg
  have hxupper : x ≤ 13 * Real.pi / 16 := by
    simpa [abs_of_nonneg hxnonneg] using hx
  by_cases hcentral : x < Real.pi / 2
  · have hcos := cos_sq_le_exp_neg_sq
      (show |x| < Real.pi / 2 by simpa [abs_of_nonneg hxnonneg])
    apply hcos.trans
    apply Real.exp_le_exp.mpr
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    nlinarith
  · have hhalf : Real.pi / 2 ≤ x := le_of_not_gt hcentral
    let y : ℝ := Real.pi - x
    have hy0 : 0 ≤ y := by
      dsimp [y]
      have hpi : 13 * Real.pi / 16 ≤ Real.pi := by
        nlinarith [Real.pi_pos]
      linarith
    have hypi : y ≤ Real.pi := by dsimp [y]; linarith [Real.pi_pos]
    have hyLower : Real.pi / 6 ≤ y := by
      dsimp [y]
      nlinarith [Real.pi_pos]
    have hyUpper : y ≤ Real.pi / 2 := by dsimp [y]; linarith
    have hcosyNonneg : 0 ≤ Real.cos y :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hyUpper⟩
    have hcosy : Real.cos y ≤ Real.cos (Real.pi / 6) := by
      exact Real.antitoneOn_cos
        ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
        ⟨hy0, hypi⟩
        hyLower
    have hcosSquare : Real.cos x ^ 2 ≤ 3 / 4 := by
      have hsquare := pow_le_pow_left₀ hcosyNonneg hcosy 2
      rw [Real.sq_cos_pi_div_six] at hsquare
      have hcosx : Real.cos x = -Real.cos y := by
        rw [show x = Real.pi - y by simp [y], Real.cos_pi_sub]
      rw [hcosx]
      simpa only [neg_sq] using hsquare
    have hxSquare : x ^ 2 ≤ (13 * Real.pi / 16) ^ 2 := by
      exact (sq_le_sq₀ hxnonneg
        (by positivity : 0 ≤ 13 * Real.pi / 16)).2 hxupper
    have hpi := Real.pi_lt_d2
    have hquarter :
        (7 / 200 : ℝ) * (13 * Real.pi / 16) ^ 2 ≤ 1 / 4 := by
      nlinarith [sq_nonneg (Real.pi - 22 / 7)]
    have hlinear : (3 / 4 : ℝ) ≤ 1 - (7 / 200 : ℝ) * x ^ 2 := by
      nlinarith
    have hexp :
        1 - (7 / 200 : ℝ) * x ^ 2 ≤
          Real.exp (-((7 / 200 : ℝ) * x ^ 2)) :=
      Real.one_sub_le_exp_neg _
    exact hcosSquare.trans (hlinear.trans (by simpa only [neg_mul] using hexp))

/-- Away from the `q/A = 2` resonance, the second mode has a uniform
Gaussian envelope on the entire unit coordinate range. -/
theorem cos_sq_le_exp_neg_one_twentieth_sq
    {x : ℝ} (hx : |x| ≤ 4 * Real.pi / 5) :
    Real.cos x ^ 2 ≤ Real.exp (-(1 / 20 : ℝ) * x ^ 2) := by
  wlog hxnonneg : 0 ≤ x generalizing x
  · have hneg : 0 ≤ -x := neg_nonneg.mpr (le_of_not_ge hxnonneg)
    have hband : |-x| ≤ 4 * Real.pi / 5 := by simpa using hx
    simpa [Real.cos_neg] using this hband hneg
  have hxupper : x ≤ 4 * Real.pi / 5 := by
    simpa [abs_of_nonneg hxnonneg] using hx
  by_cases hcentral : x < Real.pi / 2
  · have hcos := cos_sq_le_exp_neg_sq
      (show |x| < Real.pi / 2 by simpa [abs_of_nonneg hxnonneg])
    apply hcos.trans
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg x]
  · have hhalf : Real.pi / 2 ≤ x := le_of_not_gt hcentral
    let y : ℝ := Real.pi - x
    have hy0 : 0 ≤ y := by
      dsimp [y]
      have hpi : 4 * Real.pi / 5 ≤ Real.pi := by
        nlinarith [Real.pi_pos]
      linarith
    have hypi : y ≤ Real.pi := by dsimp [y]; linarith [Real.pi_pos]
    have hyLower : Real.pi / 5 ≤ y := by
      dsimp [y]
      nlinarith [Real.pi_pos]
    have hyUpper : y ≤ Real.pi / 2 := by dsimp [y]; linarith
    have hcosyNonneg : 0 ≤ Real.cos y :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hyUpper⟩
    have hcosy : Real.cos y ≤ Real.cos (Real.pi / 5) := by
      exact Real.antitoneOn_cos
        ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
        ⟨hy0, hypi⟩ hyLower
    have hsqrtFive : Real.sqrt 5 < 9 / 4 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have hcosSquare : Real.cos x ^ 2 ≤ 2 / 3 := by
      have hsquare := pow_le_pow_left₀ hcosyNonneg hcosy 2
      rw [Real.cos_pi_div_five] at hsquare
      have hsqrtSq : Real.sqrt 5 ^ 2 = 5 := by norm_num
      have hcosx : Real.cos x = -Real.cos y := by
        rw [show x = Real.pi - y by simp [y], Real.cos_pi_sub]
      rw [hcosx]
      have : ((1 + Real.sqrt 5) / 4) ^ 2 ≤ (2 / 3 : ℝ) := by
        nlinarith
      simpa only [neg_sq] using hsquare.trans this
    have hxSquare : x ^ 2 ≤ (4 * Real.pi / 5) ^ 2 := by
      exact (sq_le_sq₀ hxnonneg
        (by positivity : 0 ≤ 4 * Real.pi / 5)).2 hxupper
    have hpi := Real.pi_lt_d2
    have hthird :
        (1 / 20 : ℝ) * (4 * Real.pi / 5) ^ 2 ≤ 1 / 3 := by
      nlinarith [sq_nonneg (Real.pi - 22 / 7)]
    have hlinear : (2 / 3 : ℝ) ≤ 1 - (1 / 20 : ℝ) * x ^ 2 := by
      nlinarith
    have hexp :
        1 - (1 / 20 : ℝ) * x ^ 2 ≤
          Real.exp (-((1 / 20 : ℝ) * x ^ 2)) :=
      Real.one_sub_le_exp_neg _
    exact hcosSquare.trans (hlinear.trans (by simpa only [neg_mul] using hexp))

/-- Uniform second-mode attenuation for every normalized coordinate of a
maximal profile once `q/A ≥ 5/2`. -/
theorem full_secondModeProduct_le
    {d : ℕ} (v : Fin d → ℝ) {B u₀ : ℝ}
    (hB : 5 / 2 ≤ B)
    (hcoord : ∀ i, |v i| ≤ 1)
    (hmass : u₀ ≤ ∑ i, (v i) ^ 2) :
    (∏ i, Real.cos (2 * Real.pi * v i / B) ^ 2) ≤
      Real.exp (-(1 / 20 : ℝ) * (2 * Real.pi / B) ^ 2 * u₀) := by
  have hBpos : 0 < B := by linarith
  have hpoint (i : Fin d) :
      Real.cos (2 * Real.pi * v i / B) ^ 2 ≤
        Real.exp (-(1 / 20 : ℝ) * (2 * Real.pi * v i / B) ^ 2) := by
    apply cos_sq_le_exp_neg_one_twentieth_sq
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_pos Real.pi_pos, abs_of_pos hBpos]
    have hscale : 2 / B ≤ 4 / 5 := by
      rw [div_le_iff₀ hBpos]
      nlinarith
    calc
      2 * Real.pi * |v i| / B = (2 / B) * Real.pi * |v i| := by ring
      _ ≤ (4 / 5) * Real.pi * 1 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right hscale Real.pi_pos.le)
          (hcoord i) (abs_nonneg _) (by positivity)
      _ = 4 * Real.pi / 5 := by ring
  calc
    (∏ i, Real.cos (2 * Real.pi * v i / B) ^ 2) ≤
        ∏ i, Real.exp (-(1 / 20 : ℝ) *
          (2 * Real.pi * v i / B) ^ 2) := by
      apply Finset.prod_le_prod
      · intro i _
        exact sq_nonneg _
      · intro i _
        exact hpoint i
    _ = Real.exp (-(1 / 20 : ℝ) *
        (2 * Real.pi / B) ^ 2 * ∑ i, (v i) ^ 2) := by
      rw [← Real.exp_sum]
      congr 1
      calc
        ∑ i, -(1 / 20 : ℝ) * (2 * Real.pi * v i / B) ^ 2 =
            ∑ i, (-(1 / 20 : ℝ) * (2 * Real.pi / B) ^ 2) *
              v i ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = -(1 / 20 : ℝ) * (2 * Real.pi / B) ^ 2 *
            ∑ i, v i ^ 2 := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-(1 / 20 : ℝ) *
        (2 * Real.pi / B) ^ 2 * u₀) := by
      apply Real.exp_le_exp.mpr
      have hrate : 0 ≤ (1 / 20 : ℝ) * (2 * Real.pi / B) ^ 2 := by
        positivity
      nlinarith

/-- Tensorized second-mode attenuation on a compact residual profile.  This
is the quantitative reason the `q/A ≈ 2` resonance remains controllable: no
coordinate exceeds `13/16`, so the whole second-mode product still loses a
fixed exponential amount of squared mass. -/
theorem compact_secondModeProduct_le
    {d : ℕ} (v : Fin d → ℝ) {B u₀ : ℝ}
    (hB : 2 ≤ B)
    (hcoord : ∀ i, |v i| ≤ 13 / 16)
    (hmass : u₀ ≤ ∑ i, (v i) ^ 2) :
    (∏ i, Real.cos (2 * Real.pi * v i / B) ^ 2) ≤
      Real.exp (-(7 / 200 : ℝ) * (2 * Real.pi / B) ^ 2 * u₀) := by
  have hBpos : 0 < B := by linarith
  have hpoint (i : Fin d) :
      Real.cos (2 * Real.pi * v i / B) ^ 2 ≤
        Real.exp (-(7 / 200 : ℝ) * (2 * Real.pi * v i / B) ^ 2) := by
    apply cos_sq_le_exp_neg_seven_two_hundredths_sq
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_pos Real.pi_pos, abs_of_pos hBpos]
    have hscale : 2 / B ≤ 1 := (div_le_one hBpos).2 hB
    calc
      2 * Real.pi * |v i| / B = (2 / B) * Real.pi * |v i| := by ring
      _ ≤ 1 * Real.pi * (13 / 16) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right hscale Real.pi_pos.le)
          (hcoord i) (abs_nonneg _) (by positivity)
      _ = 13 * Real.pi / 16 := by ring
  calc
    (∏ i, Real.cos (2 * Real.pi * v i / B) ^ 2) ≤
        ∏ i, Real.exp (-(7 / 200 : ℝ) *
          (2 * Real.pi * v i / B) ^ 2) := by
      apply Finset.prod_le_prod
      · intro i _
        exact sq_nonneg _
      · intro i _
        exact hpoint i
    _ = Real.exp (-(7 / 200 : ℝ) *
        (2 * Real.pi / B) ^ 2 * ∑ i, (v i) ^ 2) := by
      rw [← Real.exp_sum]
      congr 1
      calc
        ∑ i, -(7 / 200 : ℝ) * (2 * Real.pi * v i / B) ^ 2 =
            ∑ i, (-(7 / 200 : ℝ) * (2 * Real.pi / B) ^ 2) *
              v i ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = -(7 / 200 : ℝ) * (2 * Real.pi / B) ^ 2 *
            ∑ i, v i ^ 2 := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-(7 / 200 : ℝ) *
        (2 * Real.pi / B) ^ 2 * u₀) := by
      apply Real.exp_le_exp.mpr
      have hrate : 0 ≤ (7 / 200 : ℝ) * (2 * Real.pi / B) ^ 2 := by
        positivity
      nlinarith

/-- First-mode attenuation for normalized coordinates of size at most one. -/
theorem compact_firstModeProduct_le
    {d : ℕ} (v : Fin d → ℝ) {B u₀ : ℝ}
    (hB : 2 < B)
    (hcoord : ∀ i, |v i| ≤ 1)
    (hmass : u₀ ≤ ∑ i, (v i) ^ 2) :
    (∏ i, Real.cos (Real.pi * v i / B) ^ 2) ≤
      Real.exp (-(Real.pi / B) ^ 2 * u₀) := by
  have hBpos : 0 < B := by linarith
  have hpoint (i : Fin d) :
      Real.cos (Real.pi * v i / B) ^ 2 ≤
        Real.exp (-((Real.pi * v i / B) ^ 2)) := by
    apply cos_sq_le_exp_neg_sq
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hBpos]
    have hscale : 1 / B < 1 / 2 := by
      exact one_div_lt_one_div_of_lt (by norm_num) hB
    calc
      Real.pi * |v i| / B = (1 / B) * Real.pi * |v i| := by ring
      _ ≤ (1 / B) * Real.pi * 1 := by
        exact mul_le_mul_of_nonneg_left (hcoord i) (by positivity)
      _ < (1 / 2) * Real.pi * 1 := by
        exact mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_right hscale Real.pi_pos) (by norm_num)
      _ = Real.pi / 2 := by ring
  calc
    (∏ i, Real.cos (Real.pi * v i / B) ^ 2) ≤
        ∏ i, Real.exp (-((Real.pi * v i / B) ^ 2)) := by
      apply Finset.prod_le_prod
      · intro i _
        exact sq_nonneg _
      · intro i _
        exact hpoint i
    _ = Real.exp (-(Real.pi / B) ^ 2 * ∑ i, (v i) ^ 2) := by
      rw [← Real.exp_sum]
      congr 1
      calc
        ∑ i, -((Real.pi * v i / B) ^ 2) =
            ∑ i, (-(Real.pi / B) ^ 2) * v i ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = -(Real.pi / B) ^ 2 * ∑ i, v i ^ 2 := by
          rw [Finset.mul_sum]
    _ ≤ Real.exp (-(Real.pi / B) ^ 2 * u₀) := by
      apply Real.exp_le_exp.mpr
      have hrate : 0 ≤ (Real.pi / B) ^ 2 := sq_nonneg _
      nlinarith

theorem sparseCyclicCosineModeInt_eq_normalizedCosProduct
    {d : ℕ} (q A : ℕ) (w : Fin d → ℤ) (k : ℤ)
    (hq : 0 < q) (hA : 0 < A) :
    sparseCyclicCosineModeInt q w k =
      ∏ i, Real.cos
        (Real.pi * (k : ℝ) * ((w i : ℝ) / (A : ℝ)) /
          ((q : ℝ) / (A : ℝ))) ^ 2 := by
  have hqReal : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hAReal : (A : ℝ) ≠ 0 := by exact_mod_cast hA.ne'
  unfold sparseCyclicCosineModeInt
  apply Finset.prod_congr rfl
  intro i hi
  rw [Real.cos_sq]
  field_simp [hqReal, hAReal]

theorem sparseCyclicCosineModeInt_one_le_compactMass
    {d : ℕ} (q A : ℕ) (w : Fin d → ℤ) (u₀ : ℝ)
    (hq : 0 < q) (hA : 0 < A)
    (hB : 2 < (q : ℝ) / (A : ℝ))
    (hcoord : ∀ i, |(w i : ℝ) / (A : ℝ)| ≤ 1)
    (hmass : u₀ ≤ ∑ i, ((w i : ℝ) / (A : ℝ)) ^ 2) :
    sparseCyclicCosineModeInt q w 1 ≤
      Real.exp (-(Real.pi / ((q : ℝ) / (A : ℝ))) ^ 2 * u₀) := by
  rw [sparseCyclicCosineModeInt_eq_normalizedCosProduct q A w 1 hq hA]
  norm_num only [Int.cast_one, mul_one]
  exact compact_firstModeProduct_le
    (fun i => (w i : ℝ) / (A : ℝ)) hB hcoord hmass

theorem sparseCyclicCosineModeInt_two_le_compactMass
    {d : ℕ} (q A : ℕ) (w : Fin d → ℤ) (u₀ : ℝ)
    (hq : 0 < q) (hA : 0 < A)
    (hB : 2 ≤ (q : ℝ) / (A : ℝ))
    (hcoord : ∀ i, |(w i : ℝ) / (A : ℝ)| ≤ 13 / 16)
    (hmass : u₀ ≤ ∑ i, ((w i : ℝ) / (A : ℝ)) ^ 2) :
    sparseCyclicCosineModeInt q w 2 ≤
      Real.exp (-(7 / 200 : ℝ) *
        (2 * Real.pi / ((q : ℝ) / (A : ℝ))) ^ 2 * u₀) := by
  rw [sparseCyclicCosineModeInt_eq_normalizedCosProduct q A w 2 hq hA]
  norm_num only [Int.cast_ofNat]
  calc
    (∏ i, Real.cos
        (Real.pi * 2 * ((w i : ℝ) / (A : ℝ)) /
          ((q : ℝ) / (A : ℝ))) ^ 2) =
        ∏ i, Real.cos
          (2 * Real.pi * ((w i : ℝ) / (A : ℝ)) /
            ((q : ℝ) / (A : ℝ))) ^ 2 := by
      apply Finset.prod_congr rfl
      intro i hi
      congr 2
      ring
    _ ≤ Real.exp (-(7 / 200 : ℝ) *
        (2 * Real.pi / ((q : ℝ) / (A : ℝ))) ^ 2 * u₀) :=
      compact_secondModeProduct_le
        (fun i => (w i : ℝ) / (A : ℝ)) hB hcoord hmass

theorem sparseCyclicCosineModeInt_two_le_fullMass
    {d : ℕ} (q A : ℕ) (w : Fin d → ℤ) (u₀ : ℝ)
    (hq : 0 < q) (hA : 0 < A)
    (hB : 5 / 2 ≤ (q : ℝ) / (A : ℝ))
    (hcoord : ∀ i, |(w i : ℝ) / (A : ℝ)| ≤ 1)
    (hmass : u₀ ≤ ∑ i, ((w i : ℝ) / (A : ℝ)) ^ 2) :
    sparseCyclicCosineModeInt q w 2 ≤
      Real.exp (-(1 / 20 : ℝ) *
        (2 * Real.pi / ((q : ℝ) / (A : ℝ))) ^ 2 * u₀) := by
  rw [sparseCyclicCosineModeInt_eq_normalizedCosProduct q A w 2 hq hA]
  norm_num only [Int.cast_ofNat]
  calc
    (∏ i, Real.cos
        (Real.pi * 2 * ((w i : ℝ) / (A : ℝ)) /
          ((q : ℝ) / (A : ℝ))) ^ 2) =
        ∏ i, Real.cos
          (2 * Real.pi * ((w i : ℝ) / (A : ℝ)) /
            ((q : ℝ) / (A : ℝ))) ^ 2 := by
      apply Finset.prod_congr rfl
      intro i hi
      congr 2
      ring
    _ ≤ Real.exp (-(1 / 20 : ℝ) *
        (2 * Real.pi / ((q : ℝ) / (A : ℝ))) ^ 2 * u₀) :=
      full_secondModeProduct_le
        (fun i => (w i : ℝ) / (A : ℝ)) hB hcoord hmass

theorem nonnegativeShiftedSparseCyclicCosineModeInt_le_unshifted
    (q : ℕ) (shift : ℤ) {d : ℕ} (w : Fin d → ℤ) (k : ℤ) :
    nonnegativeShiftedSparseCyclicCosineModeInt q shift w k ≤
      sparseCyclicCosineModeInt q w k := by
  unfold nonnegativeShiftedSparseCyclicCosineModeInt
  calc
    max 0 (Real.cos
        ((2 * Real.pi * (k : ℝ) / (q : ℝ)) * (shift : ℝ))) *
        sparseCyclicCosineModeInt q w k ≤
        1 * sparseCyclicCosineModeInt q w k := by
      exact mul_le_mul_of_nonneg_right
        (max_le (by norm_num) (Real.cos_le_one _))
        (sparseCyclicCosineModeInt_nonneg q w k)
    _ = sparseCyclicCosineModeInt q w k := one_mul _

/-- After positive-phase deletion, a shifted wrapped row is bounded by the
unshifted wrapped row on the same retained subprofile.  This is the scalable
large-modulus fallback: it keeps the full positive Fourier series rather
than truncating to a fixed number of modes. -/
theorem sparseRow_shiftedWrappedGaussianKernel_le_unshifted_restrict
    {q d : ℕ} (shift : ℤ) (w : Fin d → ℤ)
    (support : Finset (Fin d)) {s : ℝ}
    (hq : 0 < q) (hs : 0 < s) :
    (∫ row, wrappedGaussianKernel q s
        (shift + ∑ i, row i * w i)
        ∂(sparseRademacherRow d).toMeasure) ≤
      ∫ row, wrappedGaussianKernel q s
        (∑ i, row i * (if i ∈ support then w i else 0))
        ∂(sparseRademacherRow d).toMeasure := by
  let v : Fin d → ℤ := fun i => if i ∈ support then w i else 0
  let weight : ℤ → ℝ := fun k =>
    Real.exp
      (-Real.pi / (s * (q : ℝ) ^ 2 / Real.pi) * (k : ℝ) ^ 2)
  have hqReal : 0 < (q : ℝ) := by exact_mod_cast hq
  have hrate : 0 < Real.pi / (s * (q : ℝ) ^ 2 / Real.pi) := by
    positivity
  have hweight : Summable weight := by
    dsimp [weight]
    simpa only [neg_div] using summable_real_integer_exp_neg_sq hrate
  have hshiftSummable : Summable (fun k : ℤ =>
      weight k * nonnegativeShiftedSparseCyclicCosineModeInt q shift v k) := by
    apply hweight.of_norm_bounded
    intro k
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg]
    · exact mul_le_of_le_one_right (Real.exp_pos _).le
        ((nonnegativeShiftedSparseCyclicCosineModeInt_le_unshifted
          q shift v k).trans (sparseCyclicCosineModeInt_le_one q v k))
    · unfold nonnegativeShiftedSparseCyclicCosineModeInt
      exact mul_nonneg (le_max_left _ _)
        (sparseCyclicCosineModeInt_nonneg q v k)
  have hunshiftedSummable : Summable (fun k : ℤ =>
      weight k * sparseCyclicCosineModeInt q v k) := by
    apply hweight.of_norm_bounded
    intro k
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (sparseCyclicCosineModeInt_nonneg q v k)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le
      (sparseCyclicCosineModeInt_le_one q v k)
  have hseries :
      (∑' k : ℤ,
          weight k *
            nonnegativeShiftedSparseCyclicCosineModeInt q shift v k) ≤
        ∑' k : ℤ, weight k * sparseCyclicCosineModeInt q v k := by
    exact hshiftSummable.tsum_le_tsum
      (fun k => mul_le_mul_of_nonneg_left
        (nonnegativeShiftedSparseCyclicCosineModeInt_le_unshifted
          q shift v k) (Real.exp_nonneg _))
      hunshiftedSummable
  have hshift :=
    sparseRow_shiftedWrappedGaussianKernel_le_nonnegative_restrict
      shift w support hq hs
  have hunshifted := sparseRow_wrappedGaussianKernel_integral_eq v hq hs
  calc
    (∫ row, wrappedGaussianKernel q s
        (shift + ∑ i, row i * w i)
        ∂(sparseRademacherRow d).toMeasure) ≤
      1 / Real.sqrt (s * (q : ℝ) ^ 2 / Real.pi) *
        ∑' k : ℤ,
          weight k *
            nonnegativeShiftedSparseCyclicCosineModeInt q shift v k := by
      simpa only [v, weight] using hshift
    _ ≤ 1 / Real.sqrt (s * (q : ℝ) ^ 2 / Real.pi) *
        ∑' k : ℤ, weight k * sparseCyclicCosineModeInt q v k := by
      exact mul_le_mul_of_nonneg_left hseries (by positivity)
    _ = ∫ row, wrappedGaussianKernel q s
        (∑ i, row i * (if i ∈ support then w i else 0))
        ∂(sparseRademacherRow d).toMeasure := by
      simpa only [v, weight] using hunshifted.symm

/-- Gaussian integer-frequency tail beginning at frequency three. -/
theorem real_exp_neg_sq_nat_add_three_tsum_le {c : ℝ} (hc : 0 < c) :
    (∑' n : ℕ, Real.exp (-c * ((n + 3 : ℕ) : ℝ) ^ 2)) ≤
      Real.exp (-9 * c) / (1 - Real.exp (-7 * c)) := by
  let ρ : ℝ := Real.exp (-7 * c)
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom : Summable (fun n : ℕ => Real.exp (-9 * c) * ρ ^ n) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  have hterm (n : ℕ) :
      Real.exp (-c * ((n + 3 : ℕ) : ℝ) ^ 2) ≤
        Real.exp (-9 * c) * ρ ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    cases n with
    | zero => norm_num [pow_two, mul_comm]
    | succ n =>
        push_cast
        nlinarith [sq_nonneg (n : ℝ)]
  have hsum : Summable
      (fun n : ℕ => Real.exp (-c * ((n + 3 : ℕ) : ℝ) ^ 2)) :=
    hgeom.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hterm
  calc
    (∑' n : ℕ, Real.exp (-c * ((n + 3 : ℕ) : ℝ) ^ 2)) ≤
        ∑' n : ℕ, Real.exp (-9 * c) * ρ ^ n :=
      hsum.tsum_le_tsum hterm hgeom
    _ = Real.exp (-9 * c) * (1 - ρ)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]
    _ = Real.exp (-9 * c) / (1 - Real.exp (-7 * c)) := by rfl

/-- Abstract two-mode truncation for an even nonnegative Fourier mode. -/
theorem gaussianWeighted_evenMode_tsum_le_twoMode
    {c : ℝ} (hc : 0 < c) (mode low : ℤ → ℝ)
    (heven : mode.Even)
    (hmode0 : mode 0 ≤ 1)
    (hmode_nonneg : ∀ k, 0 ≤ mode k)
    (hmode_le_one : ∀ k, mode k ≤ 1)
    (hlow : ∀ n ∈ Finset.range 2,
      mode ((n + 1 : ℕ) : ℤ) ≤ low ((n + 1 : ℕ) : ℤ)) :
    (∑' k : ℤ, Real.exp (-c * (k : ℝ) ^ 2) * mode k) ≤
      1 + 2 * (∑ n ∈ Finset.range 2,
        Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2) *
          low ((n + 1 : ℕ) : ℤ)) +
        2 * (Real.exp (-9 * c) / (1 - Real.exp (-7 * c))) := by
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
        (∑ n ∈ Finset.range 2, f ((n + 1 : ℕ) : ℤ)) +
          ∑' n : ℕ, f ((n + 3 : ℕ) : ℤ) := by
    rw [← hgn.sum_add_tsum_nat_add 2]
  have hfinite :
      (∑ n ∈ Finset.range 2, f ((n + 1 : ℕ) : ℤ)) ≤
        ∑ n ∈ Finset.range 2,
          Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2) *
            low ((n + 1 : ℕ) : ℤ) := by
    apply Finset.sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_left (hlow n hn) (Real.exp_nonneg _)
  have htailTerm (n : ℕ) :
      f ((n + 3 : ℕ) : ℤ) ≤
        Real.exp (-c * ((n + 3 : ℕ) : ℝ) ^ 2) := by
    dsimp [f]
    exact mul_le_of_le_one_right (Real.exp_pos _).le
      (hmode_le_one ((n + 3 : ℕ) : ℤ))
  have hgauss : Summable
      (fun n : ℕ => Real.exp (-c * ((n + 3 : ℕ) : ℝ) ^ 2)) :=
    (summable_real_integer_exp_neg_sq hc).comp_injective
      (fun a b h => by
        have hab : a + 3 = b + 3 := by exact_mod_cast h
        omega)
  have htailSummable : Summable
      (fun n : ℕ => f ((n + 3 : ℕ) : ℤ)) :=
    hgauss.of_nonneg_of_le
      (fun n => mul_nonneg (Real.exp_nonneg _) (hmode_nonneg _)) htailTerm
  have htail :
      (∑' n : ℕ, f ((n + 3 : ℕ) : ℤ)) ≤
        Real.exp (-9 * c) / (1 - Real.exp (-7 * c)) := by
    exact (htailSummable.tsum_le_tsum htailTerm hgauss).trans
      (real_exp_neg_sq_nat_add_three_tsum_le hc)
  have hparts := add_le_add hfinite htail
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat hfeven hf, hpnat, hsplit]
  dsimp [f]
  norm_num only [Int.cast_zero, zero_pow, Real.exp_zero, one_mul,
    Nat.cast_add, Nat.cast_one, Int.cast_natCast, two_smul]
  have hzero : Real.exp (-c * 0) * mode 0 ≤ 1 := by simpa using hmode0
  have hdouble := mul_le_mul_of_nonneg_left hparts (by norm_num : (0 : ℝ) ≤ 2)
  norm_num only [Nat.cast_add, Nat.cast_one, Int.cast_natCast] at hdouble
  nlinarith

/-- Shifted wrapped sparse-row expectation reduced to two retained frequency
bounds.  Negative shift phases have already been discarded by the positive
Fourier transport. -/
theorem sparseRow_shiftedWrappedGaussianKernel_le_twoMode
    {q d : ℕ} (shift : ℤ) (w : Fin d → ℤ) {s L₁ L₂ : ℝ}
    (hq : 0 < q) (hs : 0 < s)
    (hmode₁ : nonnegativeShiftedSparseCyclicCosineModeInt q shift w 1 ≤ L₁)
    (hmode₂ : nonnegativeShiftedSparseCyclicCosineModeInt q shift w 2 ≤ L₂) :
    (∫ row, wrappedGaussianKernel q s
        (shift + ∑ i, row i * w i)
        ∂(sparseRademacherRow d).toMeasure) ≤
      1 / Real.sqrt (s * (q : ℝ) ^ 2 / Real.pi) *
        (1 + 2 *
          (Real.exp (-(Real.pi ^ 2 / (s * (q : ℝ) ^ 2))) * L₁ +
            Real.exp (-4 * (Real.pi ^ 2 / (s * (q : ℝ) ^ 2))) * L₂) +
          2 * (Real.exp
              (-9 * (Real.pi ^ 2 / (s * (q : ℝ) ^ 2))) /
            (1 - Real.exp
              (-7 * (Real.pi ^ 2 / (s * (q : ℝ) ^ 2)))))) := by
  let c : ℝ := Real.pi ^ 2 / (s * (q : ℝ) ^ 2)
  let mode : ℤ → ℝ :=
    nonnegativeShiftedSparseCyclicCosineModeInt q shift w
  let low : ℤ → ℝ := fun k => if k = 1 then L₁ else L₂
  have hqReal : 0 < (q : ℝ) := by exact_mod_cast hq
  have hc : 0 < c := by dsimp [c]; positivity
  have hmodeEven : mode.Even := by
    intro k
    unfold mode nonnegativeShiftedSparseCyclicCosineModeInt
    congr 1
    · push_cast
      rw [show (2 * Real.pi * (-(k : ℝ)) / (q : ℝ)) * (shift : ℝ) =
          -((2 * Real.pi * (k : ℝ) / (q : ℝ)) * (shift : ℝ)) by ring,
        Real.cos_neg]
    · unfold sparseCyclicCosineModeInt
      apply Finset.prod_congr rfl
      intro i hi
      congr 2
      push_cast
      rw [show (2 * Real.pi * (-(k : ℝ)) / (q : ℝ)) * (w i : ℝ) =
          -((2 * Real.pi * (k : ℝ) / (q : ℝ)) * (w i : ℝ)) by ring,
        Real.cos_neg]
  have hmode0 : mode 0 ≤ 1 := by
    unfold mode nonnegativeShiftedSparseCyclicCosineModeInt
    simp [sparseCyclicCosineModeInt]
  have hmode_nonneg : ∀ k, 0 ≤ mode k := by
    intro k
    unfold mode nonnegativeShiftedSparseCyclicCosineModeInt
    exact mul_nonneg (le_max_left _ _)
      (sparseCyclicCosineModeInt_nonneg q w k)
  have hmode_le_one : ∀ k, mode k ≤ 1 := by
    intro k
    unfold mode nonnegativeShiftedSparseCyclicCosineModeInt
    calc
      max 0 (Real.cos
          ((2 * Real.pi * (k : ℝ) / (q : ℝ)) * (shift : ℝ))) *
          sparseCyclicCosineModeInt q w k ≤
          1 * sparseCyclicCosineModeInt q w k := by
        exact mul_le_mul_of_nonneg_right
          (max_le (by norm_num) (Real.cos_le_one _))
          (sparseCyclicCosineModeInt_nonneg q w k)
      _ ≤ 1 := by simpa using sparseCyclicCosineModeInt_le_one q w k
  have hlow : ∀ n ∈ Finset.range 2,
      mode ((n + 1 : ℕ) : ℤ) ≤ low ((n + 1 : ℕ) : ℤ) := by
    intro n hn
    have hnCases : n = 0 ∨ n = 1 := by
      have := Finset.mem_range.mp hn
      omega
    rcases hnCases with rfl | rfl
    · simpa [mode, low] using hmode₁
    · simpa [mode, low] using hmode₂
  have hseries := gaussianWeighted_evenMode_tsum_le_twoMode
    hc mode low hmodeEven hmode0 hmode_nonneg hmode_le_one hlow
  have htransport :=
    sparseRow_shiftedWrappedGaussianKernel_le_nonnegative_restrict
      shift w Finset.univ hq hs
  calc
    _ ≤ 1 / Real.sqrt (s * (q : ℝ) ^ 2 / Real.pi) *
        ∑' k : ℤ,
          Real.exp
              (-Real.pi / (s * (q : ℝ) ^ 2 / Real.pi) * (k : ℝ) ^ 2) *
            mode k := by simpa [mode] using htransport
    _ ≤ 1 / Real.sqrt (s * (q : ℝ) ^ 2 / Real.pi) *
        (1 + 2 * (∑ n ∈ Finset.range 2,
          Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2) *
            low ((n + 1 : ℕ) : ℤ)) +
          2 * (Real.exp (-9 * c) / (1 - Real.exp (-7 * c)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [show (∑' k : ℤ,
          Real.exp
              (-Real.pi / (s * (q : ℝ) ^ 2 / Real.pi) * (k : ℝ) ^ 2) *
            mode k) =
          ∑' k : ℤ, Real.exp (-c * (k : ℝ) ^ 2) * mode k by
        apply tsum_congr
        intro k
        congr 2
        dsimp [c]
        field_simp [hqReal.ne', hs.ne']]
      exact hseries
    _ = _ := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        Nat.cast_zero, zero_add, Nat.cast_one, one_add_one_eq_two,
        Nat.cast_ofNat, Int.reduceOfNat, low, if_pos, if_false]
      dsimp [c]
      ring

end CertifiedJL
