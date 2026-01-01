import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp

/-!
# Intermediate-profile modular images

This module formalizes the three geometric series in paper equation L14.
-/

open scoped BigOperators

namespace CertifiedJL

/-- The shifted-envelope exponent from L12 at dominant squared mass `r`. -/
noncomputable def intermediateAlpha (r : ℝ) : ℝ :=
  (23 / 10) / (1 + (23 / 10) * (1 - r))

/-- The three nonzero modular-image series in paper equation L13. -/
noncomputable def intermediateL13 (r D : ℝ) : ℝ :=
  let a := intermediateAlpha r
  let β := Real.sqrt r
  (∑' n : ℕ, Real.exp (-a * ((((n : ℝ) + 1) * D) ^ 2))) +
    (1 / 2 : ℝ) * (∑' n : ℕ, Real.exp
      (-a * ((((n : ℝ) + 1) * D - β) ^ 2))) +
    (1 / 2 : ℝ) * (∑' n : ℕ, Real.exp
      (-a * ((((n : ℝ) + 1) * D + β) ^ 2)))

/-- The endpoint shifted-envelope exponent `s/(1+s/3)` at `s=23/10`. -/
noncomputable def intermediateAlpha0 : ℝ := (23 / 10) / (1 + (23 / 10) / 3)

theorem intermediateAlpha0_eq : intermediateAlpha0 = (69 / 53 : ℝ) := by
  norm_num [intermediateAlpha0]

theorem intermediateAlpha_two_div_three :
    intermediateAlpha (2 / 3) = intermediateAlpha0 := by
  norm_num [intermediateAlpha, intermediateAlpha0]

/-- A Gaussian series whose squared arguments grow by at least `gap` is
bounded by the corresponding geometric series. -/
theorem gaussianShift_tsum_le_geometric {a first gap : ℝ} {z : ℕ → ℝ}
    (ha : 0 < a) (hgap : 0 < gap)
    (hz : ∀ n : ℕ, first + (n : ℝ) * gap ≤ z n) :
    (∑' n : ℕ, Real.exp (-a * z n)) ≤
      Real.exp (-a * first) / (1 - Real.exp (-a * gap)) := by
  let ρ : ℝ := Real.exp (-a * gap)
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := by
    dsimp [ρ]
    rw [Real.exp_lt_one_iff]
    nlinarith [mul_pos ha hgap]
  have hterm (n : ℕ) :
      Real.exp (-a * z n) ≤ Real.exp (-a * first) * ρ ^ n := by
    rw [show ρ ^ n = Real.exp (-(a * gap) * n) by
      rw [show -(a * gap) = -a * gap by ring, ← Real.exp_nat_mul]
      congr 1
      ring]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonpos_left (hz n) (neg_nonpos.mpr ha.le)
    calc
      -a * z n ≤ -a * (first + (n : ℝ) * gap) := hmul
      _ = -a * first + -(a * gap) * n := by ring
  have htarget : Summable (fun n : ℕ ↦ Real.exp (-a * first) * ρ ^ n) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  have hsource : Summable (fun n : ℕ ↦ Real.exp (-a * z n)) :=
    htarget.of_nonneg_of_le (fun _ ↦ Real.exp_nonneg _) hterm
  calc
    (∑' n : ℕ, Real.exp (-a * z n)) ≤
        ∑' n : ℕ, Real.exp (-a * first) * ρ ^ n :=
      hsource.tsum_le_tsum hterm htarget
    _ = Real.exp (-a * first) * (1 - ρ)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]
    _ = Real.exp (-a * first) / (1 - Real.exp (-a * gap)) := by
      simp [ρ, div_eq_mul_inv]

private theorem summable_gaussianShift_of_geometric {a first gap : ℝ}
    {z : ℕ → ℝ} (ha : 0 < a) (hgap : 0 < gap)
    (hz : ∀ n : ℕ, first + (n : ℝ) * gap ≤ z n) :
    Summable (fun n : ℕ ↦ Real.exp (-a * z n)) := by
  let ρ : ℝ := Real.exp (-a * gap)
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := by
    dsimp [ρ]
    rw [Real.exp_lt_one_iff]
    nlinarith [mul_pos ha hgap]
  have hterm (n : ℕ) :
      Real.exp (-a * z n) ≤ Real.exp (-a * first) * ρ ^ n := by
    rw [show ρ ^ n = Real.exp (-(a * gap) * n) by
      rw [show -(a * gap) = -a * gap by ring, ← Real.exp_nat_mul]
      congr 1
      ring]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonpos_left (hz n) (neg_nonpos.mpr ha.le)
    calc
      -a * z n ≤ -a * (first + (n : ℝ) * gap) := hmul
      _ = -a * first + -(a * gap) * n := by ring
  exact ((summable_geometric_of_lt_one hρ0 hρ1).mul_left _).of_nonneg_of_le
    (fun _ ↦ Real.exp_nonneg _) hterm

private theorem minus_gap {D β : ℝ} (n : ℕ) :
    (D - β) ^ 2 + (n : ℝ) * (3 * D ^ 2 - 2 * D * β) ≤
      (((n : ℝ) + 1) * D - β) ^ 2 := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    rw [show (((n : ℝ) + 1) * D - β) ^ 2 =
        (D - β) ^ 2 + (n : ℝ) * (3 * D ^ 2 - 2 * D * β) +
          (n : ℝ) * ((n : ℝ) - 1) * D ^ 2 by ring]
    exact le_add_of_nonneg_right (mul_nonneg
      (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hn1)) (sq_nonneg D))

private theorem plus_gap {D β : ℝ} (n : ℕ) :
    (D + β) ^ 2 + (n : ℝ) * (3 * D ^ 2 + 2 * D * β) ≤
      (((n : ℝ) + 1) * D + β) ^ 2 := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    rw [show (((n : ℝ) + 1) * D + β) ^ 2 =
        (D + β) ^ 2 + (n : ℝ) * (3 * D ^ 2 + 2 * D * β) +
          (n : ℝ) * ((n : ℝ) - 1) * D ^ 2 by ring]
    exact le_add_of_nonneg_right (mul_nonneg
      (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hn1)) (sq_nonneg D))

private theorem zero_gap {D : ℝ} (n : ℕ) :
    D ^ 2 + (n : ℝ) * (3 * D ^ 2) ≤ (((n : ℝ) + 1) * D) ^ 2 := by
  simpa using (minus_gap (D := D) (β := 0) n)

private theorem intermediate_den_pos_of_sq_le_one {y : ℝ} (hy : y ^ 2 ≤ 1) :
    0 < 1 + (23 / 10 : ℝ) * (1 - y ^ 2) := by
  nlinarith

private theorem intermediate_minus_exponent_mono_from_endpoint
    {A y β : ℝ} (hA : 3 ≤ A) (hβ0 : 0 ≤ β) (hβsq : β ^ 2 = 2 / 3)
    (hβy : β ≤ y) (hy1 : y ≤ 1) :
    (23 / 10 : ℝ) / (1 + (23 / 10) * (1 - β ^ 2)) * (A - β) ^ 2 ≤
      (23 / 10 : ℝ) / (1 + (23 / 10) * (1 - y ^ 2)) * (A - y) ^ 2 := by
  have hy0 : 0 ≤ y := hβ0.trans hβy
  have hySq : y ^ 2 ≤ 1 := by nlinarith
  have hdenβ : 0 < 1 + (23 / 10 : ℝ) * (1 - β ^ 2) :=
    intermediate_den_pos_of_sq_le_one (by nlinarith)
  have hdeny : 0 < 1 + (23 / 10 : ℝ) * (1 - y ^ 2) :=
    intermediate_den_pos_of_sq_le_one hySq
  have hAy : 0 ≤ A - y := by linarith
  have hAβ : 0 ≤ A - β := by linarith
  have hthreshold : 0 < (23 / 10 : ℝ) * A * β - (1 + 23 / 10) := by
    have hβpos : 0 < β := by nlinarith
    have hsq : (1 + (23 / 10 : ℝ)) ^ 2 <
        ((23 / 10 : ℝ) * A * β) ^ 2 := by
      nlinarith [sq_nonneg ((23 / 10 : ℝ) * β * (A - 3))]
    nlinarith [sq_nonneg ((23 / 10 : ℝ) * A * β + (1 + 23 / 10))]
  have hthresholdY : 0 < (23 / 10 : ℝ) * A * y - (1 + 23 / 10) := by
    nlinarith
  have hfactor : 0 ≤
      (A - β) * ((23 / 10 : ℝ) * A * y - (1 + 23 / 10)) +
        (A - y) * ((23 / 10 : ℝ) * A * β - (1 + 23 / 10)) := by
    positivity
  rw [show (23 / 10 : ℝ) / (1 + (23 / 10) * (1 - β ^ 2)) * (A - β) ^ 2 =
      ((23 / 10 : ℝ) * (A - β) ^ 2) /
        (1 + (23 / 10) * (1 - β ^ 2)) by ring,
    show (23 / 10 : ℝ) / (1 + (23 / 10) * (1 - y ^ 2)) * (A - y) ^ 2 =
      ((23 / 10 : ℝ) * (A - y) ^ 2) /
        (1 + (23 / 10) * (1 - y ^ 2)) by ring]
  apply (div_le_div_iff₀ hdenβ hdeny).2
  nlinarith

private theorem intermediate_plus_exponent_mono_from_endpoint
    {A y β : ℝ} (hA : 0 ≤ A) (hβ0 : 0 ≤ β) (hβy : β ≤ y)
    (hy1 : y ≤ 1) :
    (23 / 10 : ℝ) / (1 + (23 / 10) * (1 - β ^ 2)) * (A + β) ^ 2 ≤
      (23 / 10 : ℝ) / (1 + (23 / 10) * (1 - y ^ 2)) * (A + y) ^ 2 := by
  have hy0 : 0 ≤ y := hβ0.trans hβy
  have hySq : y ^ 2 ≤ 1 := by nlinarith
  have hβSq : β ^ 2 ≤ 1 := by nlinarith
  have hdenβ : 0 < 1 + (23 / 10 : ℝ) * (1 - β ^ 2) :=
    intermediate_den_pos_of_sq_le_one hβSq
  have hdeny : 0 < 1 + (23 / 10 : ℝ) * (1 - y ^ 2) :=
    intermediate_den_pos_of_sq_le_one hySq
  rw [show (23 / 10 : ℝ) / (1 + (23 / 10) * (1 - β ^ 2)) * (A + β) ^ 2 =
      ((23 / 10 : ℝ) * (A + β) ^ 2) /
        (1 + (23 / 10) * (1 - β ^ 2)) by ring,
    show (23 / 10 : ℝ) / (1 + (23 / 10) * (1 - y ^ 2)) * (A + y) ^ 2 =
      ((23 / 10 : ℝ) * (A + y) ^ 2) /
        (1 + (23 / 10) * (1 - y ^ 2)) by ring]
  apply (div_le_div_iff₀ hdenβ hdeny).2
  rw [← sub_nonneg]
  rw [show
    (23 / 10 : ℝ) * (A + y) ^ 2 * (1 + (23 / 10) * (1 - β ^ 2)) -
        (23 / 10 : ℝ) * (A + β) ^ 2 * (1 + (23 / 10) * (1 - y ^ 2)) =
      (23 / 10 : ℝ) * (y - β) *
        ((23 / 10 : ℝ) * A ^ 2 * (β + y) +
          2 * (23 / 10 : ℝ) * A * β * y +
          2 * A * (1 + 23 / 10) + (1 + 23 / 10) * (β + y)) by ring]
  positivity

private theorem intermediate_zero_exponent_mono_from_endpoint
    {A y β : ℝ} (_hA : 0 ≤ A) (hβ0 : 0 ≤ β) (hβy : β ≤ y)
    (hy1 : y ≤ 1) :
    (23 / 10 : ℝ) / (1 + (23 / 10) * (1 - β ^ 2)) * A ^ 2 ≤
      (23 / 10 : ℝ) / (1 + (23 / 10) * (1 - y ^ 2)) * A ^ 2 := by
  have hy0 : 0 ≤ y := hβ0.trans hβy
  have hySq : y ^ 2 ≤ 1 := by nlinarith
  have hβSq : β ^ 2 ≤ 1 := by nlinarith
  have hdenβ : 0 < 1 + (23 / 10 : ℝ) * (1 - β ^ 2) :=
    intermediate_den_pos_of_sq_le_one hβSq
  have hdeny : 0 < 1 + (23 / 10 : ℝ) * (1 - y ^ 2) :=
    intermediate_den_pos_of_sq_le_one hySq
  rw [show (23 / 10 : ℝ) / (1 + (23 / 10) * (1 - β ^ 2)) * A ^ 2 =
      ((23 / 10 : ℝ) * A ^ 2) /
        (1 + (23 / 10) * (1 - β ^ 2)) by ring,
    show (23 / 10 : ℝ) / (1 + (23 / 10) * (1 - y ^ 2)) * A ^ 2 =
      ((23 / 10 : ℝ) * A ^ 2) /
        (1 + (23 / 10) * (1 - y ^ 2)) by ring]
  apply (div_le_div_iff₀ hdenβ hdeny).2
  rw [← sub_nonneg]
  rw [show
    (23 / 10 : ℝ) * A ^ 2 * (1 + (23 / 10) * (1 - β ^ 2)) -
        (23 / 10 : ℝ) * A ^ 2 * (1 + (23 / 10) * (1 - y ^ 2)) =
      (23 / 10 : ℝ) ^ 2 * A ^ 2 * (y - β) * (β + y) by ring]
  positivity

/-- Exact L12 endpoint transfer for the inactive modular image. -/
theorem intermediate_inactive_image_le_two_div_three {r D : ℝ}
    (hr0 : 2 / 3 ≤ r) (hr1 : r ≤ 2000 / 2309) (hD : 3 ≤ D)
    (n : ℕ) :
    Real.exp (-intermediateAlpha r * ((((n : ℝ) + 1) * D) ^ 2)) ≤
      Real.exp (-intermediateAlpha0 * ((((n : ℝ) + 1) * D) ^ 2)) := by
  have hrNonneg : 0 ≤ r := le_trans (by norm_num) hr0
  let y := Real.sqrt r
  let β := Real.sqrt (2 / 3 : ℝ)
  have hβ0 : 0 ≤ β := Real.sqrt_nonneg _
  have hβsq : β ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  have hysq : y ^ 2 = r := Real.sq_sqrt hrNonneg
  have hβy : β ≤ y := Real.sqrt_le_sqrt hr0
  have hy1 : y ≤ 1 := by
    rw [← sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 1), hysq]
    exact hr1.trans (by norm_num)
  have hmono := intermediate_zero_exponent_mono_from_endpoint
    (A := ((n : ℝ) + 1) * D) (y := y) (β := β)
    (by positivity) hβ0 hβy hy1
  rw [hβsq, hysq] at hmono
  have hmono' :
      intermediateAlpha (2 / 3) * (((n : ℝ) + 1) * D) ^ 2 ≤
        intermediateAlpha r * (((n : ℝ) + 1) * D) ^ 2 := by
    simpa [intermediateAlpha, y, β] using hmono
  rw [intermediateAlpha_two_div_three] at hmono'
  apply Real.exp_le_exp.mpr
  linarith

/-- Exact L12 endpoint transfer for the active image shifted toward zero. -/
theorem intermediate_minus_image_le_two_div_three {r D : ℝ}
    (hr0 : 2 / 3 ≤ r) (hr1 : r ≤ 2000 / 2309) (hD : 3 ≤ D)
    (n : ℕ) :
    Real.exp (-intermediateAlpha r *
        ((((n : ℝ) + 1) * D - Real.sqrt r) ^ 2)) ≤
      Real.exp (-intermediateAlpha0 *
        ((((n : ℝ) + 1) * D - Real.sqrt (2 / 3)) ^ 2)) := by
  have hrNonneg : 0 ≤ r := le_trans (by norm_num) hr0
  let y := Real.sqrt r
  let β := Real.sqrt (2 / 3 : ℝ)
  have hβ0 : 0 ≤ β := Real.sqrt_nonneg _
  have hβsq : β ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  have hysq : y ^ 2 = r := Real.sq_sqrt hrNonneg
  have hβy : β ≤ y := Real.sqrt_le_sqrt hr0
  have hy1 : y ≤ 1 := by
    rw [← sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 1), hysq]
    exact hr1.trans (by norm_num)
  have hA : 3 ≤ ((n : ℝ) + 1) * D := by
    nlinarith [mul_nonneg (Nat.cast_nonneg n) (by linarith : 0 ≤ D)]
  have hmono := intermediate_minus_exponent_mono_from_endpoint
    (A := ((n : ℝ) + 1) * D) (y := y) (β := β)
    hA hβ0 hβsq hβy hy1
  rw [hβsq, hysq] at hmono
  have hmono' :
      intermediateAlpha (2 / 3) *
          (((n : ℝ) + 1) * D - Real.sqrt (2 / 3)) ^ 2 ≤
        intermediateAlpha r *
          (((n : ℝ) + 1) * D - Real.sqrt r) ^ 2 := by
    simpa [intermediateAlpha, y, β] using hmono
  rw [intermediateAlpha_two_div_three] at hmono'
  apply Real.exp_le_exp.mpr
  linarith

/-- Exact L12 endpoint transfer for the active image shifted away from zero. -/
theorem intermediate_plus_image_le_two_div_three {r D : ℝ}
    (hr0 : 2 / 3 ≤ r) (hr1 : r ≤ 2000 / 2309) (hD : 3 ≤ D)
    (n : ℕ) :
    Real.exp (-intermediateAlpha r *
        ((((n : ℝ) + 1) * D + Real.sqrt r) ^ 2)) ≤
      Real.exp (-intermediateAlpha0 *
        ((((n : ℝ) + 1) * D + Real.sqrt (2 / 3)) ^ 2)) := by
  have hrNonneg : 0 ≤ r := le_trans (by norm_num) hr0
  let y := Real.sqrt r
  let β := Real.sqrt (2 / 3 : ℝ)
  have hβ0 : 0 ≤ β := Real.sqrt_nonneg _
  have hβsq : β ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  have hysq : y ^ 2 = r := Real.sq_sqrt hrNonneg
  have hβy : β ≤ y := Real.sqrt_le_sqrt hr0
  have hy1 : y ≤ 1 := by
    rw [← sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 1), hysq]
    exact hr1.trans (by norm_num)
  have hmono := intermediate_plus_exponent_mono_from_endpoint
    (A := ((n : ℝ) + 1) * D) (y := y) (β := β)
    (by positivity) hβ0 hβy hy1
  rw [hβsq, hysq] at hmono
  have hmono' :
      intermediateAlpha (2 / 3) *
          (((n : ℝ) + 1) * D + Real.sqrt (2 / 3)) ^ 2 ≤
        intermediateAlpha r *
          (((n : ℝ) + 1) * D + Real.sqrt r) ^ 2 := by
    simpa [intermediateAlpha, y, β] using hmono
  rw [intermediateAlpha_two_div_three] at hmono'
  apply Real.exp_le_exp.mpr
  linarith

/-- Paper equation L13 is largest at the exact left endpoint `r=2/3`. -/
theorem intermediateL13_le_two_div_three {r D : ℝ}
    (hr0 : 2 / 3 ≤ r) (hr1 : r ≤ 2000 / 2309) (hD : 3 ≤ D) :
    intermediateL13 r D ≤ intermediateL13 (2 / 3) D := by
  have ha : 0 < intermediateAlpha0 := by norm_num [intermediateAlpha0]
  let β : ℝ := Real.sqrt (2 / 3)
  have hβ : 0 ≤ β := Real.sqrt_nonneg _
  have hβsq : β ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  have hminusGap : 0 < 3 * D ^ 2 - 2 * D * β := by nlinarith
  have hplusGap : 0 < 3 * D ^ 2 + 2 * D * β := by positivity
  have hzeroSummable := summable_gaussianShift_of_geometric
    (a := intermediateAlpha0) (first := D ^ 2) (gap := 3 * D ^ 2)
    (z := fun n : ℕ ↦ (((n : ℝ) + 1) * D) ^ 2)
    ha (by positivity) (fun n ↦ zero_gap n)
  have hminusSummable := summable_gaussianShift_of_geometric
    (a := intermediateAlpha0) (first := (D - β) ^ 2)
    (gap := 3 * D ^ 2 - 2 * D * β)
    (z := fun n : ℕ ↦ (((n : ℝ) + 1) * D - β) ^ 2)
    ha hminusGap (fun n ↦ minus_gap n)
  have hplusSummable := summable_gaussianShift_of_geometric
    (a := intermediateAlpha0) (first := (D + β) ^ 2)
    (gap := 3 * D ^ 2 + 2 * D * β)
    (z := fun n : ℕ ↦ (((n : ℝ) + 1) * D + β) ^ 2)
    ha hplusGap (fun n ↦ plus_gap n)
  have hzeroSource := hzeroSummable.of_nonneg_of_le
    (fun _ ↦ Real.exp_nonneg _)
    (fun n ↦ intermediate_inactive_image_le_two_div_three hr0 hr1 hD n)
  have hzero := hzeroSource.tsum_le_tsum
    (fun n ↦ intermediate_inactive_image_le_two_div_three hr0 hr1 hD n)
    hzeroSummable
  have hminusSource := hminusSummable.of_nonneg_of_le
    (fun _ ↦ Real.exp_nonneg _)
    (fun n ↦ intermediate_minus_image_le_two_div_three hr0 hr1 hD n)
  have hplusSource := hplusSummable.of_nonneg_of_le
    (fun _ ↦ Real.exp_nonneg _)
    (fun n ↦ intermediate_plus_image_le_two_div_three hr0 hr1 hD n)
  have hminus := hminusSource.tsum_le_tsum
    (fun n ↦ intermediate_minus_image_le_two_div_three hr0 hr1 hD n)
    hminusSummable
  have hplus := hplusSource.tsum_le_tsum
    (fun n ↦ intermediate_plus_image_le_two_div_three hr0 hr1 hD n)
    hplusSummable
  dsimp only [intermediateL13]
  rw [intermediateAlpha_two_div_three]
  linarith

/-- Each of the three L13 series is summable throughout the intermediate
parameter range. -/
theorem intermediateL13_terms_summable {r D : ℝ}
    (hr0 : 2 / 3 ≤ r) (hr1 : r ≤ 2000 / 2309) (hD : 3 ≤ D) :
    Summable (fun n : ℕ ↦ Real.exp
      (-intermediateAlpha r * (((n : ℝ) + 1) * D) ^ 2)) ∧
      Summable (fun n : ℕ ↦ Real.exp
        (-intermediateAlpha r *
          (((n : ℝ) + 1) * D - Real.sqrt r) ^ 2)) ∧
      Summable (fun n : ℕ ↦ Real.exp
        (-intermediateAlpha r *
          (((n : ℝ) + 1) * D + Real.sqrt r) ^ 2)) := by
  have ha : 0 < intermediateAlpha0 := by norm_num [intermediateAlpha0]
  let β : ℝ := Real.sqrt (2 / 3)
  have hβ : 0 ≤ β := Real.sqrt_nonneg _
  have hβsq : β ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  have hminusGap : 0 < 3 * D ^ 2 - 2 * D * β := by nlinarith
  have hplusGap : 0 < 3 * D ^ 2 + 2 * D * β := by positivity
  have hzeroTarget := summable_gaussianShift_of_geometric
    (a := intermediateAlpha0) (first := D ^ 2) (gap := 3 * D ^ 2)
    (z := fun n : ℕ ↦ (((n : ℝ) + 1) * D) ^ 2)
    ha (by positivity) (fun n ↦ zero_gap n)
  have hminusTarget := summable_gaussianShift_of_geometric
    (a := intermediateAlpha0) (first := (D - β) ^ 2)
    (gap := 3 * D ^ 2 - 2 * D * β)
    (z := fun n : ℕ ↦ (((n : ℝ) + 1) * D - β) ^ 2)
    ha hminusGap (fun n ↦ minus_gap n)
  have hplusTarget := summable_gaussianShift_of_geometric
    (a := intermediateAlpha0) (first := (D + β) ^ 2)
    (gap := 3 * D ^ 2 + 2 * D * β)
    (z := fun n : ℕ ↦ (((n : ℝ) + 1) * D + β) ^ 2)
    ha hplusGap (fun n ↦ plus_gap n)
  exact ⟨hzeroTarget.of_nonneg_of_le
      (fun _ ↦ Real.exp_nonneg _)
      (fun n ↦ intermediate_inactive_image_le_two_div_three hr0 hr1 hD n),
    hminusTarget.of_nonneg_of_le
      (fun _ ↦ Real.exp_nonneg _)
      (fun n ↦ intermediate_minus_image_le_two_div_three hr0 hr1 hD n),
    hplusTarget.of_nonneg_of_le
      (fun _ ↦ Real.exp_nonneg _)
      (fun n ↦ intermediate_plus_image_le_two_div_three hr0 hr1 hD n)⟩

/-- The exact right side of paper equation L14. -/
noncomputable def intermediateL14 (D : ℝ) : ℝ :=
  let a := intermediateAlpha0
  let β := Real.sqrt (2 / 3)
  Real.exp (-a * D ^ 2) / (1 - Real.exp (-a * (3 * D ^ 2))) +
    (1 / 2 : ℝ) *
      (Real.exp (-a * (D - β) ^ 2) /
        (1 - Real.exp (-a * (3 * D ^ 2 - 2 * D * β)))) +
    (1 / 2 : ℝ) *
      (Real.exp (-a * (D + β) ^ 2) /
        (1 - Real.exp (-a * (3 * D ^ 2 + 2 * D * β))))

/-- The three nonzero-image series at `r=2/3` satisfy L14 for every `D≥3`. -/
theorem intermediate_three_series_le_L14 {D : ℝ} (hD : 3 ≤ D) :
    (∑' n : ℕ, Real.exp (-intermediateAlpha0 * (((n : ℝ) + 1) * D) ^ 2)) +
      (1 / 2 : ℝ) * (∑' n : ℕ, Real.exp
        (-intermediateAlpha0 * (((n : ℝ) + 1) * D - Real.sqrt (2 / 3)) ^ 2)) +
      (1 / 2 : ℝ) * (∑' n : ℕ, Real.exp
        (-intermediateAlpha0 * (((n : ℝ) + 1) * D + Real.sqrt (2 / 3)) ^ 2)) ≤
      intermediateL14 D := by
  have ha : 0 < intermediateAlpha0 := by norm_num [intermediateAlpha0]
  let β : ℝ := Real.sqrt (2 / 3)
  have hβ : 0 ≤ β := Real.sqrt_nonneg _
  have hminusGap : 0 < 3 * D ^ 2 - 2 * D * β := by
    have hβsq : β ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
    nlinarith
  have hplusGap : 0 < 3 * D ^ 2 + 2 * D * β := by positivity
  have hzero := gaussianShift_tsum_le_geometric
    (a := intermediateAlpha0) (first := D ^ 2) (gap := 3 * D ^ 2)
    (z := fun n : ℕ ↦ (((n : ℝ) + 1) * D) ^ 2) ha (by positivity)
    (fun n : ℕ ↦ zero_gap n)
  have hminus := gaussianShift_tsum_le_geometric
    (a := intermediateAlpha0) (first := (D - β) ^ 2)
    (gap := 3 * D ^ 2 - 2 * D * β)
    (z := fun n : ℕ ↦ (((n : ℝ) + 1) * D - β) ^ 2) ha hminusGap
    (fun n ↦ minus_gap n)
  have hplus := gaussianShift_tsum_le_geometric
    (a := intermediateAlpha0) (first := (D + β) ^ 2)
    (gap := 3 * D ^ 2 + 2 * D * β)
    (z := fun n : ℕ ↦ (((n : ℝ) + 1) * D + β) ^ 2) ha hplusGap
    (fun n ↦ plus_gap n)
  dsimp only [intermediateL14]
  dsimp only [β] at hminus hplus ⊢
  linarith

/-- L12 through L14, with both intermediate-class endpoints explicit. -/
theorem intermediateL13_le_L14 {r D : ℝ}
    (hr0 : 2 / 3 ≤ r) (hr1 : r ≤ 2000 / 2309) (hD : 3 ≤ D) :
    intermediateL13 r D ≤ intermediateL14 D := by
  calc
    intermediateL13 r D ≤ intermediateL13 (2 / 3) D :=
      intermediateL13_le_two_div_three hr0 hr1 hD
    _ =
        (∑' n : ℕ, Real.exp
          (-intermediateAlpha0 * (((n : ℝ) + 1) * D) ^ 2)) +
          (1 / 2 : ℝ) * (∑' n : ℕ, Real.exp
            (-intermediateAlpha0 *
              (((n : ℝ) + 1) * D - Real.sqrt (2 / 3)) ^ 2)) +
          (1 / 2 : ℝ) * (∑' n : ℕ, Real.exp
            (-intermediateAlpha0 *
              (((n : ℝ) + 1) * D + Real.sqrt (2 / 3)) ^ 2)) := by
      simp only [intermediateL13, intermediateAlpha_two_div_three]
    _ ≤ intermediateL14 D := intermediate_three_series_le_L14 hD

end CertifiedJL
