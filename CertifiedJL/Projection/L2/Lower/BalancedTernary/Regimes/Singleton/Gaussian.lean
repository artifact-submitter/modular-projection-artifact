/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.WrappedFourier
import Mathlib.Analysis.Convex.Deriv

/-!
# Paired-image bounds for a wrapped Gaussian singleton

This module proves a dimensionless bound for the average of a centered
wrapped Gaussian and one translate.  Its key finite-dimensional step pairs
the two integer images adjacent to a point and uses convexity of the Gaussian
only outside a prescribed central interval.
-/

open scoped BigOperators

open Set

namespace CertifiedJL

/-- The dimensionless real wrapped Gaussian with image spacing `Q`. -/
noncomputable def realWrappedGaussianKernel (Q t x : ℝ) : ℝ :=
  ∑' n : ℤ, Real.exp (-t * (x - (n : ℝ) * Q) ^ 2)

/-- The dimensionless wrapped Gaussian is even in its translate. -/
theorem realWrappedGaussianKernel_neg (Q t x : ℝ) :
    realWrappedGaussianKernel Q t (-x) = realWrappedGaussianKernel Q t x := by
  unfold realWrappedGaussianKernel
  calc
    (∑' n : ℤ, Real.exp (-t * (-x - (n : ℝ) * Q) ^ 2)) =
        ∑' n : ℤ, Real.exp (-t * (-x - ((-n : ℤ) : ℝ) * Q) ^ 2) :=
      (Equiv.tsum_eq (Equiv.neg ℤ)
        (fun n : ℤ => Real.exp (-t * (-x - (n : ℝ) * Q) ^ 2))).symm
    _ = ∑' n : ℤ, Real.exp (-t * (x - (n : ℝ) * Q) ^ 2) := by
      apply tsum_congr
      intro n
      congr 2
      push_cast
      ring

private theorem summable_realWrappedGaussianKernel
    {Q t : ℝ} (hQ : 0 < Q) (ht : 0 < t) (x : ℝ) :
    Summable (fun n : ℤ => Real.exp (-t * (x - (n : ℝ) * Q) ^ 2)) := by
  have h := summable_exp_neg_mul_int_sub_sq
    (c := t * Q ^ 2) (x := x / Q) (by positivity)
  convert h using 1
  funext n
  congr 1
  field_simp [hQ.ne']
  ring

private theorem hasDerivAt_gaussian
    (t x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-t * y ^ 2))
      (-2 * t * x * Real.exp (-t * x ^ 2)) x := by
  have hinner : HasDerivAt (fun y : ℝ => -t * y ^ 2) (-2 * t * x) x := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (hasDerivAt_pow 2 x).const_mul (-t)
  simpa [mul_assoc, mul_comm, mul_left_comm] using hinner.exp

private theorem hasDerivAt_gaussian_deriv
    (t x : ℝ) :
    HasDerivAt
      ((fun y : ℝ => -2 * t * y) *
        fun y : ℝ => Real.exp (-t * y ^ 2))
      (-2 * t * Real.exp (-t * x ^ 2) +
        (-2 * t * x) * (-2 * t * x * Real.exp (-t * x ^ 2))) x := by
  have hlinear : HasDerivAt (fun y : ℝ => -2 * t * y) (-2 * t) x := by
    simpa [mul_assoc] using (hasDerivAt_id x).const_mul (-2 * t)
  exact hlinear.mul (hasDerivAt_gaussian t x)

/-- A Gaussian is convex once its argument is beyond its inflection point. -/
private theorem convexOn_gaussian_Ici
    {c t : ℝ} (hc : 0 < c) (ht : 0 < t) (hinflection : 1 ≤ 2 * t * c ^ 2) :
    ConvexOn ℝ (Ici c) (fun x : ℝ => Real.exp (-t * x ^ 2)) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici c)
  · exact (Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.pow 2))).continuousOn
  · intro x hx
    exact (hasDerivAt_gaussian t x).hasDerivWithinAt
  · intro x hx
    exact (hasDerivAt_gaussian_deriv t x).hasDerivWithinAt
  · intro x hx
    have hcx : c ≤ x := by
      rw [interior_Ici] at hx
      exact hx.le
    have hsq : c ^ 2 ≤ x ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2 * t)
    have hfactor : 0 ≤ 2 * t * x ^ 2 - 1 := by nlinarith
    have hexp : 0 < Real.exp (-t * x ^ 2) := Real.exp_pos _
    change 0 ≤ -2 * t * Real.exp (-t * x ^ 2) +
      (-2 * t * x) * (-2 * t * x * Real.exp (-t * x ^ 2))
    rw [show -2 * t * Real.exp (-t * x ^ 2) +
        (-2 * t * x) * (-2 * t * x * Real.exp (-t * x ^ 2)) =
      2 * t * (2 * t * x ^ 2 - 1) * Real.exp (-t * x ^ 2) by ring]
    positivity

/-- Pair the integer images indexed by `-n` and `n+1`. -/
private theorem realWrappedGaussianKernel_eq_pair_tsum
    {Q t : ℝ} (hQ : 0 < Q) (ht : 0 < t) (x : ℝ) :
    realWrappedGaussianKernel Q t x =
      ∑' n : ℕ,
        (Real.exp (-t * (n * Q + x) ^ 2) +
          Real.exp (-t * ((n + 1) * Q - x) ^ 2)) := by
  let f : ℤ → ℝ := fun n => Real.exp (-t * (x - (n : ℝ) * Q) ^ 2)
  have hf : Summable f := summable_realWrappedGaussianKernel hQ ht x
  have hpos : Summable (fun n : ℕ => f ((n + 1 : ℕ) : ℤ)) :=
    hf.comp_injective (fun _ _ h => by omega)
  have hneg : Summable (fun n : ℕ => f (-((n + 1 : ℕ) : ℤ))) :=
    hf.comp_injective (fun _ _ h => by omega)
  rw [realWrappedGaussianKernel, tsum_of_add_one_of_neg_add_one hpos hneg]
  have hnegZero : Summable (fun n : ℕ => f (-(n : ℤ))) :=
    hf.comp_injective (fun _ _ h => by omega)
  have hnegSplit :
      f 0 + ∑' n : ℕ, f (-((n + 1 : ℕ) : ℤ)) =
        ∑' n : ℕ, f (-(n : ℤ)) := by
    simpa using hnegZero.sum_add_tsum_nat_add 1
  calc
    (∑' n : ℕ, f ((n + 1 : ℕ) : ℤ)) + f 0 +
        ∑' n : ℕ, f (-((n + 1 : ℕ) : ℤ)) =
      (∑' n : ℕ, f (-(n : ℤ))) +
        ∑' n : ℕ, f ((n + 1 : ℕ) : ℤ) := by
      rw [← hnegSplit]
      ring
    _ = ∑' n : ℕ,
        (f (-(n : ℤ)) + f ((n + 1 : ℕ) : ℤ)) := by
      rw [hnegZero.tsum_add hpos]
  apply tsum_congr
  intro n
  dsimp [f]
  push_cast
  congr 1 <;> ring

/-- Each pair of images is largest at the endpoints of the admissible
translate interval. -/
private theorem pairedGaussian_le_left_endpoint
    {c Q t x : ℝ} (n : ℕ) (hc : 0 < c) (hQ : 2 * c ≤ Q)
    (ht : 0 < t) (hinflection : 1 ≤ 2 * t * c ^ 2)
    (hx : x ∈ Icc c (Q - c)) :
    Real.exp (-t * (n * Q + x) ^ 2) +
        Real.exp (-t * ((n + 1) * Q - x) ^ 2) ≤
      Real.exp (-t * (n * Q + c) ^ 2) +
        Real.exp (-t * ((n + 1) * Q - c) ^ 2) := by
  let g : ℝ → ℝ := fun y =>
    Real.exp (-t * (n * Q + y) ^ 2) +
      Real.exp (-t * ((n + 1) * Q - y) ^ 2)
  have hbase := convexOn_gaussian_Ici hc ht hinflection
  let leftMap : ℝ →ᵃ[ℝ] ℝ :=
    (1 : ℝ) • AffineMap.id ℝ ℝ + AffineMap.const ℝ ℝ (n * Q)
  let rightMap : ℝ →ᵃ[ℝ] ℝ :=
    (-1 : ℝ) • AffineMap.id ℝ ℝ + AffineMap.const ℝ ℝ ((n + 1) * Q)
  have hleft : ConvexOn ℝ (Icc c (Q - c))
      (fun y : ℝ => Real.exp (-t * (n * Q + y) ^ 2)) := by
    have hcomp := hbase.comp_affineMap leftMap
    have hsub : ConvexOn ℝ (Icc c (Q - c))
        ((fun x : ℝ => Real.exp (-t * x ^ 2)) ∘ leftMap) :=
      hcomp.subset (by
      intro y hy
      rcases hy with ⟨hyc, hyQ⟩
      change c ≤ leftMap y
      dsimp [leftMap]
      have hQ0 : 0 ≤ Q := by nlinarith
      have hn : (0 : ℝ) ≤ n := by positivity
      nlinarith [mul_nonneg hn hQ0]) (convex_Icc c (Q - c))
    simpa [leftMap, Function.comp_def, add_comm] using hsub
  have hright : ConvexOn ℝ (Icc c (Q - c))
      (fun y : ℝ => Real.exp (-t * ((n + 1) * Q - y) ^ 2)) := by
    have hcomp := hbase.comp_affineMap rightMap
    have hsub : ConvexOn ℝ (Icc c (Q - c))
        ((fun x : ℝ => Real.exp (-t * x ^ 2)) ∘ rightMap) :=
      hcomp.subset (by
      intro y hy
      rcases hy with ⟨hyc, hyQ⟩
      change c ≤ rightMap y
      dsimp [rightMap]
      have hQ0 : 0 ≤ Q := by nlinarith
      have hn : (0 : ℝ) ≤ n := by positivity
      nlinarith [mul_nonneg hn hQ0]) (convex_Icc c (Q - c))
    apply hsub.congr
    intro y hy
    dsimp [rightMap, Function.comp_def]
    congr 2
    ring
  have hconvex : ConvexOn ℝ (Icc c (Q - c)) g := by
    exact hleft.add hright
  have hend : g (Q - c) = g c := by
    dsimp [g]
    have hfirst : n * Q + (Q - c) = (n + 1) * Q - c := by ring
    have hsecond : (n + 1) * Q - (Q - c) = n * Q + c := by ring
    rw [hfirst, hsecond, add_comm]
  have hmax := hconvex.le_max_of_mem_Icc
    (show c ∈ Icc c (Q - c) by constructor <;> nlinarith)
    (show Q - c ∈ Icc c (Q - c) by constructor <;> nlinarith) hx
  rw [hend, max_self] at hmax
  exact hmax

/-- A Gaussian image at distance `n Q + d` is bounded by a geometric term
when the image spacing `Q` is at least `M`. -/
private theorem gaussian_image_le_geometric
    {M Q t d : ℝ} (hM : 0 ≤ M) (hMQ : M ≤ Q) (ht : 0 ≤ t) (hd : 0 ≤ d)
    (n : ℕ) :
    Real.exp (-t * (n * Q + d) ^ 2) ≤
      Real.exp (-t * d ^ 2) * (Real.exp (-t * M ^ 2)) ^ n := by
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hQ : 0 ≤ Q := hM.trans hMQ
  have hdist : n * M + d ≤ n * Q + d := by
    simpa [add_comm] using add_le_add_right (mul_le_mul_of_nonneg_left hMQ hn) d
  have hdist0 : 0 ≤ n * M + d := add_nonneg (mul_nonneg hn hM) hd
  have hdistQ0 : 0 ≤ n * Q + d := add_nonneg (mul_nonneg hn hQ) hd
  have hsquareQ : (n * M + d) ^ 2 ≤ (n * Q + d) ^ 2 :=
    pow_le_pow_left₀ hdist0 hdist 2
  have hnsquare : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    cases n with
    | zero => norm_num
    | succ n =>
        have hn1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        nlinarith
  have hcross : 0 ≤ 2 * n * M * d := by positivity
  have hsquareM : d ^ 2 + M ^ 2 * n ≤ (n * M + d) ^ 2 := by
    have hpow := mul_le_mul_of_nonneg_left hnsquare (sq_nonneg M)
    nlinarith
  have hexponent :
      -t * (n * Q + d) ^ 2 ≤ -t * d ^ 2 + (n : ℝ) * (-t * M ^ 2) := by
    have hsquare : d ^ 2 + M ^ 2 * n ≤ (n * Q + d) ^ 2 :=
      hsquareM.trans hsquareQ
    have hmul := mul_le_mul_of_nonpos_left hsquare (neg_nonpos.mpr ht)
    nlinarith
  calc
    Real.exp (-t * (n * Q + d) ^ 2) ≤
        Real.exp (-t * d ^ 2 + (n : ℝ) * (-t * M ^ 2)) :=
      Real.exp_le_exp.mpr hexponent
    _ = Real.exp (-t * d ^ 2) * (Real.exp (-t * M ^ 2)) ^ n := by
      rw [Real.exp_add, Real.exp_nat_mul]

private theorem geometric_ratio_data
    {M t : ℝ} (hM : 0 < M) (ht : 0 < t) :
    let r := Real.exp (-t * M ^ 2)
    0 ≤ r ∧ r < 1 ∧ 0 < 1 - r := by
  dsimp only
  have hpos : 0 < t * M ^ 2 := mul_pos ht (sq_pos_of_pos hM)
  have hneg : -t * M ^ 2 < 0 := by nlinarith
  have hrlt : Real.exp (-t * M ^ 2) < 1 := Real.exp_lt_one_iff.mpr hneg
  exact ⟨(Real.exp_pos _).le, hrlt, sub_pos.mpr hrlt⟩

/-- The centered wrapped Gaussian is bounded by the symmetric geometric
series generated by the minimum image spacing. -/
private theorem realWrappedGaussianKernel_zero_le_geometric
    {M Q t : ℝ} (hM : 0 < M) (hMQ : M ≤ Q) (ht : 0 < t) :
    realWrappedGaussianKernel Q t 0 ≤
      (1 + Real.exp (-M ^ 2 * t)) / (1 - Real.exp (-M ^ 2 * t)) := by
  have hQ : 0 < Q := hM.trans_le hMQ
  let r : ℝ := Real.exp (-t * M ^ 2)
  obtain ⟨hr0, hr1, hden⟩ := geometric_ratio_data hM ht
  have hrform : Real.exp (-M ^ 2 * t) = r := by
    dsimp [r]
    congr 1
    ring
  have hterm (n : ℕ) :
      Real.exp (-t * (n * Q + 0) ^ 2) +
          Real.exp (-t * ((n + 1) * Q - 0) ^ 2) ≤
        (1 + r) * r ^ n := by
    have hfirst := gaussian_image_le_geometric hM.le hMQ ht.le (le_refl 0) n
    have hsecond := gaussian_image_le_geometric hM.le hMQ ht.le (le_refl 0) (n + 1)
    dsimp [r] at hfirst hsecond ⊢
    norm_num only [Nat.cast_add, Nat.cast_one, zero_pow, mul_zero, Real.exp_zero,
      one_mul, add_zero, sub_zero] at hfirst hsecond ⊢
    calc
      _ ≤ (Real.exp (-t * M ^ 2)) ^ n +
          (Real.exp (-t * M ^ 2)) ^ (n + 1) := add_le_add hfirst hsecond
      _ = (1 + Real.exp (-t * M ^ 2)) *
          (Real.exp (-t * M ^ 2)) ^ n := by rw [pow_succ]; ring
  have htarget : Summable (fun n : ℕ => (1 + r) * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hsource : Summable (fun n : ℕ =>
      Real.exp (-t * (n * Q + 0) ^ 2) +
        Real.exp (-t * ((n + 1) * Q - 0) ^ 2)) :=
    htarget.of_nonneg_of_le (fun _ => by positivity) hterm
  rw [realWrappedGaussianKernel_eq_pair_tsum hQ ht 0]
  calc
    _ ≤ ∑' n : ℕ, (1 + r) * r ^ n :=
      hsource.tsum_le_tsum hterm htarget
    _ = (1 + r) * (1 - r)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    _ = (1 + Real.exp (-M ^ 2 * t)) /
        (1 - Real.exp (-M ^ 2 * t)) := by rw [hrform]; rfl

/-- Pairing adjacent images bounds every admissible translate by two
geometric tails whose initial distances are `c` and `M-c`. -/
private theorem realWrappedGaussianKernel_translate_le_geometric
    {c M Q t a : ℝ} (hc : 0 < c) (hcM : c ≤ M) (hMQ : M ≤ Q)
    (hQc : 2 * c ≤ Q) (ha : c ≤ a) (haQ : 2 * a ≤ Q)
    (ht : 0 < t) (hinflection : 1 ≤ 2 * t * c ^ 2) :
    realWrappedGaussianKernel Q t a ≤
      (Real.exp (-c ^ 2 * t) + Real.exp (-(M - c) ^ 2 * t)) /
        (1 - Real.exp (-M ^ 2 * t)) := by
  have hM : 0 < M := hc.trans_le hcM
  have hQ : 0 < Q := hM.trans_le hMQ
  have haIcc : a ∈ Icc c (Q - c) := by constructor <;> nlinarith
  let r : ℝ := Real.exp (-t * M ^ 2)
  let A : ℝ := Real.exp (-t * c ^ 2)
  let D : ℝ := Real.exp (-t * (M - c) ^ 2)
  obtain ⟨hr0, hr1, hden⟩ := geometric_ratio_data hM ht
  have hrform : Real.exp (-M ^ 2 * t) = r := by
    dsimp [r]
    congr 1
    ring
  have hAform : Real.exp (-c ^ 2 * t) = A := by
    dsimp [A]
    congr 1
    ring
  have hDform : Real.exp (-(M - c) ^ 2 * t) = D := by
    dsimp [D]
    congr 1
    ring
  have hterm (n : ℕ) :
      Real.exp (-t * (n * Q + a) ^ 2) +
          Real.exp (-t * ((n + 1) * Q - a) ^ 2) ≤
        (A + D) * r ^ n := by
    have hpair := pairedGaussian_le_left_endpoint n hc hQc ht hinflection haIcc
    have hfirst := gaussian_image_le_geometric hM.le hMQ ht.le hc.le n
    have hQrewrite : (n + 1 : ℝ) * Q - c = n * Q + (Q - c) := by ring
    have hdistance : M - c ≤ Q - c := sub_le_sub_right hMQ c
    have hsecondQ :
        Real.exp (-t * ((n + 1) * Q - c) ^ 2) ≤ D * r ^ n := by
      rw [hQrewrite]
      have hnQ0 : 0 ≤ (n : ℝ) * Q := mul_nonneg (by positivity) hQ.le
      have hsmall0 : 0 ≤ n * Q + (M - c) :=
        add_nonneg hnQ0 (sub_nonneg.mpr hcM)
      have hdist : n * Q + (M - c) ≤ n * Q + (Q - c) := by linarith
      have hsq : (n * Q + (M - c)) ^ 2 ≤ (n * Q + (Q - c)) ^ 2 :=
        pow_le_pow_left₀ hsmall0 hdist 2
      calc
        Real.exp (-t * (n * Q + (Q - c)) ^ 2) ≤
            Real.exp (-t * (n * Q + (M - c)) ^ 2) := by
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonpos_left hsq (by linarith)
        _ ≤ D * r ^ n := by
          simpa [D, r] using gaussian_image_le_geometric hM.le hMQ ht.le
            (sub_nonneg.mpr hcM) n
    calc
      _ ≤ Real.exp (-t * (n * Q + c) ^ 2) +
          Real.exp (-t * ((n + 1) * Q - c) ^ 2) := hpair
      _ ≤ A * r ^ n + D * r ^ n := by
        exact add_le_add (by simpa [A, r] using hfirst) hsecondQ
      _ = (A + D) * r ^ n := by ring
  have htarget : Summable (fun n : ℕ => (A + D) * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hsource : Summable (fun n : ℕ =>
      Real.exp (-t * (n * Q + a) ^ 2) +
        Real.exp (-t * ((n + 1) * Q - a) ^ 2)) :=
    htarget.of_nonneg_of_le (fun _ => by positivity) hterm
  rw [realWrappedGaussianKernel_eq_pair_tsum hQ ht a]
  calc
    _ ≤ ∑' n : ℕ, (A + D) * r ^ n :=
      hsource.tsum_le_tsum hterm htarget
    _ = (A + D) * (1 - r)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    _ = (Real.exp (-c ^ 2 * t) + Real.exp (-(M - c) ^ 2 * t)) /
        (1 - Real.exp (-M ^ 2 * t)) := by rw [hrform, hAform, hDform]; rfl

/-- The general paired-image bound.  `M` is a lower bound for the image
spacing, `c` is the convexity cutoff, and the translate may have either sign. -/
theorem realWrappedGaussianKernel_average_le_geometric
    {c M Q t a : ℝ} (hc : 0 < c) (hcM : c ≤ M) (hMQ : M ≤ Q)
    (hQc : 2 * c ≤ Q) (ha : c ≤ |a|) (haQ : 2 * |a| ≤ Q)
    (ht : 0 < t) (hinflection : 1 ≤ 2 * t * c ^ 2) :
    (realWrappedGaussianKernel Q t 0 + realWrappedGaussianKernel Q t a) / 2 ≤
      (1 + Real.exp (-M ^ 2 * t) + Real.exp (-c ^ 2 * t) +
          Real.exp (-(M - c) ^ 2 * t)) /
        (2 * (1 - Real.exp (-M ^ 2 * t))) := by
  have hM : 0 < M := hc.trans_le hcM
  have hzero := realWrappedGaussianKernel_zero_le_geometric hM hMQ ht
  have habs := realWrappedGaussianKernel_translate_le_geometric
    hc hcM hMQ hQc ha haQ ht hinflection
  have htranslate :
      realWrappedGaussianKernel Q t a ≤
        (Real.exp (-c ^ 2 * t) + Real.exp (-(M - c) ^ 2 * t)) /
          (1 - Real.exp (-M ^ 2 * t)) := by
    rcases le_total 0 a with ha0 | ha0
    · simpa [abs_of_nonneg ha0] using habs
    · rw [abs_of_nonpos ha0] at habs
      rw [← realWrappedGaussianKernel_neg Q t a]
      exact habs
  have hsum := add_le_add hzero htranslate
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  have havg := div_le_div_of_nonneg_right hsum htwo
  obtain ⟨hr0, hr1, hden⟩ := geometric_ratio_data hM ht
  have hden' : 1 - Real.exp (-M ^ 2 * t) ≠ 0 := by
    have hrform : Real.exp (-M ^ 2 * t) = Real.exp (-t * M ^ 2) := by
      congr 1
      ring
    rw [hrform]
    exact hden.ne'
  calc
    (realWrappedGaussianKernel Q t 0 + realWrappedGaussianKernel Q t a) / 2 ≤
        (((1 + Real.exp (-M ^ 2 * t)) /
            (1 - Real.exp (-M ^ 2 * t))) +
          ((Real.exp (-c ^ 2 * t) + Real.exp (-(M - c) ^ 2 * t)) /
            (1 - Real.exp (-M ^ 2 * t)))) / 2 := havg
    _ = (1 + Real.exp (-M ^ 2 * t) + Real.exp (-c ^ 2 * t) +
          Real.exp (-(M - c) ^ 2 * t)) /
        (2 * (1 - Real.exp (-M ^ 2 * t))) := by
      field_simp [hden']
      ring

/-- The explicit four-exponential singleton envelope at cutoff `49/50` and
minimum normalized modulus `3`. -/
noncomputable def singletonGaussianEnvelope (t : ℝ) : ℝ :=
  (1 + Real.exp (-9 * t) + Real.exp (-(49 / 50 : ℝ) ^ 2 * t) +
      Real.exp (-(3 - (49 / 50 : ℝ)) ^ 2 * t)) /
    (2 * (1 - Real.exp (-9 * t)))

/-- Dimensionless margin-three specialization of the paired-image bound. -/
theorem realWrappedGaussianKernel_average_le_marginThree
    {Q t a : ℝ} (hQ : 3 ≤ Q) (ha : (49 / 50 : ℝ) ≤ |a|)
    (haQ : 2 * |a| ≤ Q) (ht : (1250 / 2401 : ℝ) ≤ t) :
    (realWrappedGaussianKernel Q t 0 + realWrappedGaussianKernel Q t a) / 2 ≤
      singletonGaussianEnvelope t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hinflection : 1 ≤ 2 * t * (49 / 50 : ℝ) ^ 2 := by
    nlinarith
  have h := realWrappedGaussianKernel_average_le_geometric
      (c := (49 / 50 : ℝ)) (M := 3) (Q := Q) (t := t) (a := a)
      (by norm_num) (by norm_num) hQ (by nlinarith) ha haQ ht0 hinflection
  have h9 : -(3 : ℝ) ^ 2 * t = -9 * t := by ring
  rw [h9] at h
  simpa [singletonGaussianEnvelope] using h

/-- Scaling the integer wrapped kernel by a positive real reference size
produces the dimensionless wrapped kernel. -/
theorem wrappedGaussianKernel_eq_realWrappedGaussianKernel
    {q : ℕ} {B t : ℝ} (z : ℤ) (hB : 0 < B) :
    wrappedGaussianKernel q (t / B ^ 2) z =
      realWrappedGaussianKernel ((q : ℝ) / B) t ((z : ℝ) / B) := by
  unfold wrappedGaussianKernel realWrappedGaussianKernel
  apply tsum_congr
  intro n
  congr 1
  field_simp [hB.ne']

/-- Existing-kernel adapter for a retained singleton at margin three. -/
theorem wrappedGaussianKernel_singleton_le_envelope
    {q : ℕ} {B t : ℝ} (z : ℤ) (hB : 0 < B)
    (hmargin : 3 * B ≤ (q : ℝ))
    (ha : (49 / 50 : ℝ) * B ≤ |(z : ℝ)|)
    (hcentered : 2 * |(z : ℝ)| ≤ (q : ℝ))
    (ht : (1250 / 2401 : ℝ) ≤ t) :
    (wrappedGaussianKernel q (t / B ^ 2) 0 +
        wrappedGaussianKernel q (t / B ^ 2) z) / 2 ≤
      singletonGaussianEnvelope t := by
  have hQ : 3 ≤ (q : ℝ) / B := by
    exact (le_div_iff₀ hB).2 hmargin
  have hza : (49 / 50 : ℝ) ≤ |(z : ℝ) / B| := by
    rw [abs_div, abs_of_pos hB]
    exact (le_div_iff₀ hB).2 ha
  have hzQ : 2 * |(z : ℝ) / B| ≤ (q : ℝ) / B := by
    rw [abs_div, abs_of_pos hB]
    rw [show 2 * (|(z : ℝ)| / B) = (2 * |(z : ℝ)|) / B by ring]
    exact (div_le_div_iff_of_pos_right hB).2 hcentered
  rw [wrappedGaussianKernel_eq_realWrappedGaussianKernel (z := 0) hB,
    wrappedGaussianKernel_eq_realWrappedGaussianKernel z hB]
  norm_num only [Int.cast_zero, zero_div]
  exact realWrappedGaussianKernel_average_le_marginThree hQ hza hzQ ht

end CertifiedJL
