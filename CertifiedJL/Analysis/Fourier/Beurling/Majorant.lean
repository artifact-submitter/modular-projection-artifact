/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# The deterministic Beurling majorant

This file isolates the pointwise real-analysis input to the
Beurling--Prawitz smoothing inequality.  Following Vaaler's positive-half-line
formula, we define an odd function `beurlingH` and the squared-sinc correction
`beurlingK`, and prove

`|sign x - beurlingH x| ≤ beurlingK x`.

The proof is elementary.  Its only infinite sum is a reciprocal-square tail.
The two required bounds follow from the telescoping comparisons

`1 / (x+n+1)^2 ≤ 1 / (x+n) - 1 / (x+n+1)`

and

`2 / ((x+n)(x+n+1))
  ≤ 1 / (x+n)^2 + 1 / (x+n+1)^2`.

Fourier-transform and convolution facts are intentionally kept in the
smoothing module.
-/

open Filter MeasureTheory
open scoped BigOperators Topology

namespace CertifiedJL
namespace Probability

/-- The reciprocal-square tail in Vaaler's positive-half-line formula. -/
noncomputable def beurlingReciprocalSquareTail (x : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / (x + (n + 1 : ℕ)) ^ 2

/-- The nonnegative squared-sinc correction in Beurling's majorant. -/
noncomputable def beurlingK (x : ℝ) : ℝ :=
  Real.sinc (Real.pi * x) ^ 2

/--
Vaaler's formula for Beurling's odd band-limited approximation to `sign`.

For `x > 0`, this is equation (2.26) of Vaaler (1985).  The value on the
negative half-line is fixed by oddness, and the removable value at zero is
set to zero.
-/
noncomputable def beurlingH (x : ℝ) : ℝ :=
  if 0 < x then
    1 + (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
      (2 / x - 1 / x ^ 2 - 2 * beurlingReciprocalSquareTail x)
  else if x < 0 then
    -(1 + (Real.sin (Real.pi * (-x)) / Real.pi) ^ 2 *
      (2 / (-x) - 1 / (-x) ^ 2 -
        2 * beurlingReciprocalSquareTail (-x)))
  else 0

theorem beurlingK_nonneg (x : ℝ) :
    0 ≤ beurlingK x := by
  exact sq_nonneg _

theorem beurlingK_neg (x : ℝ) :
    beurlingK (-x) = beurlingK x := by
  simp [beurlingK, Real.sinc_neg]

theorem beurlingK_zero :
    beurlingK 0 = 1 := by
  simp [beurlingK]

@[fun_prop]
theorem continuous_beurlingK :
    Continuous beurlingK := by
  unfold beurlingK
  fun_prop

@[fun_prop]
theorem measurable_beurlingReciprocalSquareTail :
    Measurable beurlingReciprocalSquareTail := by
  unfold beurlingReciprocalSquareTail
  apply Measurable.tsum
  intro n
  fun_prop

theorem measurable_beurlingH :
    Measurable beurlingH := by
  unfold beurlingH
  apply Measurable.ite
    (measurableSet_lt measurable_const measurable_id)
  · fun_prop
  · apply Measurable.ite
      (measurableSet_lt measurable_id measurable_const)
    · fun_prop
    · fun_prop

theorem beurlingH_zero :
    beurlingH 0 = 0 := by
  simp [beurlingH]

theorem beurlingH_of_pos {x : ℝ} (hx : 0 < x) :
    beurlingH x =
      1 + (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
        (2 / x - 1 / x ^ 2 -
          2 * beurlingReciprocalSquareTail x) := by
  simp [beurlingH, hx]

theorem beurlingH_neg (x : ℝ) :
    beurlingH (-x) = -beurlingH x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hnx : 0 < -x := neg_pos.mpr hx
    simp [beurlingH, hx, hnx, hx.not_gt]
  · simp [beurlingH]
  · have hnx : -x < 0 := neg_lt_zero.mpr hx
    simp [beurlingH, hx, hnx, hx.not_gt]

/-- The reciprocal-square tail converges for every positive displacement. -/
theorem summable_beurlingReciprocalSquareTail {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => 1 / (x + (n + 1 : ℕ)) ^ 2) := by
  have hs :
      Summable (fun n : ℕ =>
        1 / |n + (x + 1)| ^ (2 : ℝ)) := by
    rw [Real.summable_one_div_nat_add_rpow]
    norm_num
  have hpoint (n : ℕ) :
      1 / (x + (n + 1 : ℕ)) ^ 2 =
        1 / |n + (x + 1)| ^ (2 : ℝ) := by
    have hpos : 0 < (n : ℝ) + (x + 1) := by positivity
    rw [abs_of_pos hpos, Real.rpow_two]
    congr 2
    push_cast
    ring
  exact hs.congr fun n => (hpoint n).symm

/--
The elementary upper telescoping bound
`∑_{n≥0} (x+n+1)⁻² ≤ x⁻¹`.
-/
theorem beurlingReciprocalSquareTail_le_inv
    {x : ℝ} (hx : 0 < x) :
    beurlingReciprocalSquareTail x ≤ 1 / x := by
  let f : ℕ → ℝ := fun n =>
    1 / (x + (n : ℝ)) - 1 / (x + (n + 1 : ℕ))
  have hf_nonneg (n : ℕ) : 0 ≤ f n := by
    dsimp only [f]
    have h₀ : 0 < x + (n : ℝ) := by positivity
    have h₁ : 0 < x + (n + 1 : ℕ) := by positivity
    exact sub_nonneg.mpr <|
      one_div_le_one_div_of_le h₀ (by push_cast; norm_num)
  have hsum (N : ℕ) :
      ∑ n ∈ Finset.range N, f n =
        1 / x - 1 / (x + (N : ℝ)) := by
    induction N with
    | zero => simp [f]
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        dsimp only [f]
        push_cast
        ring
  have hf_sum_le (s : Finset ℕ) :
      ∑ n ∈ s, f n ≤ 1 / x := by
    let N := if h : s.Nonempty then s.max' h + 1 else 0
    have hsubset : s ⊆ Finset.range N := by
      intro n hn
      simp only [Finset.mem_range]
      dsimp only [N]
      split_ifs with hs
      · exact Nat.lt_succ_of_le (Finset.le_max' s n hn)
      · exact (hs ⟨n, hn⟩).elim
    calc
      ∑ n ∈ s, f n ≤ ∑ n ∈ Finset.range N, f n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun n _ _ => hf_nonneg n)
      _ = 1 / x - 1 / (x + (N : ℝ)) := hsum N
      _ ≤ 1 / x := sub_le_self _ (by positivity)
  have hf_summable : Summable f :=
    summable_of_sum_le hf_nonneg hf_sum_le
  have hpoint (n : ℕ) :
      1 / (x + (n + 1 : ℕ)) ^ 2 ≤ f n := by
    dsimp only [f]
    have h₀ : 0 < x + (n : ℝ) := by positivity
    have h₁ : 0 < x + (n + 1 : ℕ) := by positivity
    have hdiff :
        1 / (x + (n : ℝ)) - 1 / (x + (n + 1 : ℕ)) =
          1 / ((x + (n : ℝ)) * (x + (n + 1 : ℕ))) := by
      field_simp
      push_cast
      ring
    rw [hdiff]
    exact one_div_le_one_div_of_le (mul_pos h₀ h₁) <| by
      have hab : x + (n : ℝ) ≤ x + (n + 1 : ℕ) := by
        push_cast
        norm_num
      nlinarith
  unfold beurlingReciprocalSquareTail
  exact (Summable.tsum_le_tsum hpoint
    (summable_beurlingReciprocalSquareTail hx) hf_summable).trans
      (hf_summable.tsum_le_of_sum_le hf_sum_le)

/--
The complementary reciprocal-square bound
`2/x ≤ x⁻² + 2∑_{n≥0}(x+n+1)⁻²`.
-/
theorem two_div_le_inv_sq_add_two_mul_beurlingTail
    {x : ℝ} (hx : 0 < x) :
    2 / x ≤
      1 / x ^ 2 + 2 * beurlingReciprocalSquareTail x := by
  let f : ℕ → ℝ := fun n =>
    2 / ((x + (n : ℝ)) * (x + (n + 1 : ℕ)))
  have hf_nonneg (n : ℕ) : 0 ≤ f n := by
    dsimp only [f]
    positivity
  have hf_eq (n : ℕ) :
      f n =
        2 * (1 / (x + (n : ℝ)) -
          1 / (x + (n + 1 : ℕ))) := by
    dsimp only [f]
    have h₀ : x + (n : ℝ) ≠ 0 := ne_of_gt (by positivity)
    have h₁ : x + (n + 1 : ℕ) ≠ 0 := ne_of_gt (by positivity)
    field_simp
    push_cast
    ring
  have hf_hasSum : HasSum f (2 / x) := by
    have htend :
        Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, f n)
          atTop (𝓝 (2 / x)) := by
      have hinv :
          Tendsto (fun N : ℕ => 1 / (x + (N : ℝ)))
            atTop (𝓝 0) := by
        have hbase :
            Tendsto (fun N : ℕ => x + (N : ℝ)) atTop atTop :=
          tendsto_atTop.2 fun b => by
            filter_upwards [eventually_ge_atTop (Nat.ceil (b - x))] with N hN
            have hceil : b - x ≤ (Nat.ceil (b - x) : ℝ) :=
              Nat.le_ceil _
            have hfirst : b ≤ x + (Nat.ceil (b - x) : ℝ) := by
              linarith
            have hsecond :
                x + (Nat.ceil (b - x) : ℝ) ≤ x + (N : ℝ) :=
              by simpa [add_comm] using
                add_le_add_left (Nat.cast_le.mpr hN) x
            exact hfirst.trans hsecond
        simp only [one_div]
        change Tendsto
          ((fun r : ℝ => r⁻¹) ∘ (fun N : ℕ => x + (N : ℝ)))
          atTop (𝓝 0)
        exact tendsto_inv_atTop_zero.comp hbase
      have heq (N : ℕ) :
          ∑ n ∈ Finset.range N, f n =
            2 * (1 / x - 1 / (x + (N : ℝ))) := by
        induction N with
        | zero => simp
        | succ N ih =>
            rw [Finset.sum_range_succ, ih, hf_eq]
            push_cast
            ring
      rw [show (2 / x : ℝ) = 2 * (1 / x - 0) by ring]
      exact ((tendsto_const_nhds.sub hinv).const_mul 2).congr'
        (Eventually.of_forall fun N => (heq N).symm)
    exact (hasSum_iff_tendsto_nat_of_nonneg hf_nonneg _).2 htend
  have hpair (n : ℕ) :
      f n ≤
        1 / (x + (n : ℝ)) ^ 2 +
          1 / (x + (n + 1 : ℕ)) ^ 2 := by
    dsimp only [f]
    have h₀ : 0 < x + (n : ℝ) := by positivity
    have h₁ : 0 < x + (n + 1 : ℕ) := by positivity
    field_simp
    nlinarith [sq_nonneg ((x + (n : ℝ)) -
      (x + (n + 1 : ℕ)))]
  have htail :
      Summable (fun n : ℕ =>
        1 / (x + (n + 1 : ℕ)) ^ 2) :=
    summable_beurlingReciprocalSquareTail hx
  have hhead :
      Summable (fun n : ℕ => 1 / (x + (n : ℝ)) ^ 2) := by
    have hs :
        Summable (fun n : ℕ =>
          1 / |n + x| ^ (2 : ℝ)) := by
      rw [Real.summable_one_div_nat_add_rpow]
      norm_num
    apply hs.congr
    intro n
    have hpos : 0 < (n : ℝ) + x := by positivity
    rw [abs_of_pos hpos, Real.rpow_two]
    congr 2
    ring
  have hright_summable :
      Summable (fun n : ℕ =>
        1 / (x + (n : ℝ)) ^ 2 +
          1 / (x + (n + 1 : ℕ)) ^ 2) := by
    exact hhead.add htail
  have htsum :=
    Summable.tsum_le_tsum hpair hf_hasSum.summable hright_summable
  rw [hf_hasSum.tsum_eq] at htsum
  have hright :
      (∑' n : ℕ,
          (1 / (x + (n : ℝ)) ^ 2 +
            1 / (x + (n + 1 : ℕ)) ^ 2)) =
        1 / x ^ 2 + 2 * beurlingReciprocalSquareTail x := by
    rw [Summable.tsum_add hhead htail]
    have hhead :
        (∑' n : ℕ, 1 / (x + (n : ℝ)) ^ 2) =
          1 / x ^ 2 + beurlingReciprocalSquareTail x := by
      let g : ℕ → ℝ := fun n => 1 / (x + (n : ℝ)) ^ 2
      have htail :
          HasSum (fun n => g (n + 1))
            (beurlingReciprocalSquareTail x) := by
        have hraw :
            HasSum (fun n : ℕ =>
              1 / (x + (n + 1 : ℕ)) ^ 2)
              (beurlingReciprocalSquareTail x) :=
          (summable_beurlingReciprocalSquareTail hx).hasSum
        simpa only [g, Nat.cast_add, Nat.cast_one] using hraw
      have hfull := htail.zero_add
      have hg :
          (fun n : ℕ => g n) =
            (fun n : ℕ => 1 / (x + (n : ℝ)) ^ 2) := rfl
      rw [← hg]
      simpa [g] using hfull.tsum_eq
    have htail_tsum :
        (∑' n : ℕ, 1 / (x + (n + 1 : ℕ)) ^ 2) =
          beurlingReciprocalSquareTail x := rfl
    rw [hhead, htail_tsum]
    ring
  rwa [hright] at htsum

theorem beurlingTailBracket_nonpos
    {x : ℝ} (hx : 0 < x) :
    2 / x - 1 / x ^ 2 -
        2 * beurlingReciprocalSquareTail x ≤ 0 := by
  linarith [two_div_le_inv_sq_add_two_mul_beurlingTail hx]

theorem neg_inv_sq_le_beurlingTailBracket
    {x : ℝ} (hx : 0 < x) :
    -(1 / x ^ 2) ≤
      2 / x - 1 / x ^ 2 -
        2 * beurlingReciprocalSquareTail x := by
  have h := beurlingReciprocalSquareTail_le_inv hx
  calc
    -(1 / x ^ 2) ≤
        -(1 / x ^ 2) + 2 * (1 / x -
          beurlingReciprocalSquareTail x) := by
      have hnonneg :
          0 ≤ 2 * (1 / x -
            beurlingReciprocalSquareTail x) :=
        mul_nonneg (by norm_num) (sub_nonneg.mpr h)
      exact le_add_of_nonneg_right hnonneg
    _ = 2 / x - 1 / x ^ 2 -
          2 * beurlingReciprocalSquareTail x := by ring

theorem beurlingK_eq_sine_factor_div_sq
    {x : ℝ} (hx : x ≠ 0) :
    beurlingK x =
      (Real.sin (Real.pi * x) / Real.pi) ^ 2 / x ^ 2 := by
  unfold beurlingK
  rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hx)]
  field_simp

theorem beurlingH_le_one_of_pos
    {x : ℝ} (hx : 0 < x) :
    beurlingH x ≤ 1 := by
  rw [beurlingH_of_pos hx]
  exact add_le_of_nonpos_right
    (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
      (beurlingTailBracket_nonpos hx))

theorem one_sub_beurlingK_le_beurlingH_of_pos
    {x : ℝ} (hx : 0 < x) :
    1 - beurlingK x ≤ beurlingH x := by
  rw [beurlingH_of_pos hx,
    beurlingK_eq_sine_factor_div_sq hx.ne']
  have hfactor : 0 ≤ (Real.sin (Real.pi * x) / Real.pi) ^ 2 :=
    sq_nonneg _
  have hbracket := neg_inv_sq_le_beurlingTailBracket hx
  have hmul := mul_le_mul_of_nonneg_left hbracket hfactor
  calc
    1 - (Real.sin (Real.pi * x) / Real.pi) ^ 2 / x ^ 2 =
        1 + (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
          (-(1 / x ^ 2)) := by ring
    _ ≤ 1 + (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
          (2 / x - 1 / x ^ 2 -
            2 * beurlingReciprocalSquareTail x) :=
      by simpa [add_comm] using add_le_add_left hmul 1

theorem abs_one_sub_beurlingH_le_beurlingK_of_pos
    {x : ℝ} (hx : 0 < x) :
    |1 - beurlingH x| ≤ beurlingK x := by
  rw [abs_le]
  constructor
  · calc
      -beurlingK x ≤ 0 := neg_nonpos.mpr (beurlingK_nonneg x)
      _ ≤ 1 - beurlingH x :=
        sub_nonneg.mpr (beurlingH_le_one_of_pos hx)
  · exact sub_le_iff_le_add.mpr <| by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        one_sub_beurlingK_le_beurlingH_of_pos hx

/-- Vaaler's deterministic Beurling inequality. -/
theorem abs_sign_sub_beurlingH_le_beurlingK (x : ℝ) :
    |Real.sign x - beurlingH x| ≤ beurlingK x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hpos : 0 < -x := neg_pos.mpr hx
    have h := abs_one_sub_beurlingH_le_beurlingK_of_pos hpos
    rw [Real.sign_of_neg hx, ← neg_neg x, beurlingH_neg,
      beurlingK_neg]
    convert h using 1
    rw [show -1 - -beurlingH (-x) =
      -(1 - beurlingH (-x)) by ring, abs_neg]
  · simp [beurlingH_zero, beurlingK_zero]
  · rw [Real.sign_of_pos hx]
    exact abs_one_sub_beurlingH_le_beurlingK_of_pos hx

theorem sign_sub_beurlingK_le_beurlingH (x : ℝ) :
    Real.sign x - beurlingK x ≤ beurlingH x := by
  have h := (abs_le.mp (abs_sign_sub_beurlingH_le_beurlingK x)).2
  linarith only [h]

theorem beurlingH_le_sign_add_beurlingK (x : ℝ) :
    beurlingH x ≤ Real.sign x + beurlingK x := by
  have h := (abs_le.mp (abs_sign_sub_beurlingH_le_beurlingK x)).1
  linarith only [h]

/-- Beurling's approximation at positive bandwidth `T`. -/
noncomputable def scaledBeurlingH (T x : ℝ) : ℝ :=
  beurlingH (T * x)

/-- Squared-sinc correction at positive bandwidth `T`. -/
noncomputable def scaledBeurlingK (T x : ℝ) : ℝ :=
  beurlingK (T * x)

theorem measurable_scaledBeurlingH (T : ℝ) :
    Measurable (scaledBeurlingH T) :=
  measurable_beurlingH.comp (measurable_const.mul measurable_id)

theorem continuous_scaledBeurlingK (T : ℝ) :
    Continuous (scaledBeurlingK T) := by
  unfold scaledBeurlingK
  exact continuous_beurlingK.comp
    (continuous_const.mul continuous_id)

theorem abs_sign_sub_scaledBeurlingH_le_scaledBeurlingK
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    |Real.sign x - scaledBeurlingH T x| ≤
      scaledBeurlingK T x := by
  have hsign : Real.sign (T * x) = Real.sign x := by
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · rw [Real.sign_of_neg hx,
        Real.sign_of_neg (mul_neg_of_pos_of_neg hT hx)]
    · simp [Real.sign_zero]
    · rw [Real.sign_of_pos hx,
        Real.sign_of_pos (mul_pos hT hx)]
  simpa only [scaledBeurlingH, scaledBeurlingK, hsign] using
    abs_sign_sub_beurlingH_le_beurlingK (T * x)

theorem sign_sub_scaledBeurlingK_le_scaledBeurlingH
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    Real.sign x - scaledBeurlingK T x ≤
      scaledBeurlingH T x := by
  have h := (abs_le.mp
    (abs_sign_sub_scaledBeurlingH_le_scaledBeurlingK hT x)).2
  linarith only [h]

theorem scaledBeurlingH_le_sign_add_scaledBeurlingK
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    scaledBeurlingH T x ≤
      Real.sign x + scaledBeurlingK T x := by
  have h := (abs_le.mp
    (abs_sign_sub_scaledBeurlingH_le_scaledBeurlingK hT x)).1
  linarith only [h]

end Probability
end CertifiedJL
