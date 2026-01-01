/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Distributions.Entry
import CertifiedJL.Model.Modular.Centered
import Mathlib.Tactic

/-!
# Sparse three-atom bounds for centered modular arcs

After a sparse-row coordinate is isolated, its contribution has law
`{-1, 0, 1}` with masses `1/4, 1/2, 1/4`.  A centered modular arc shorter
than the separation between the middle atom and either outer atom therefore
has probability at most `1/2`.
-/

namespace CertifiedJL.Probability

/-- Membership in a centered modular arc, with division-free scaling. -/
def ScaledCenteredArcPass (q scale radius : ℕ) (z : ℤ) : Prop :=
  scale * (centeredMod q z).natAbs ≤ radius

/-- Centered modular distance satisfies the triangle inequality. -/
theorem centeredMod_natAbs_sub_le_add (q : ℕ) (x y : ℤ) :
    (centeredMod q (x - y)).natAbs ≤
      (centeredMod q x).natAbs + (centeredMod q y).natAbs := by
  have h := ZMod.natAbs_valMinAbs_add_le
    (n := q) (x : ZMod q) (-(y : ZMod q))
  unfold centeredMod
  calc
    (((x - y : ℤ) : ZMod q).valMinAbs).natAbs =
        (((x : ZMod q) + -(y : ZMod q)).valMinAbs).natAbs := by
      rw [Int.cast_sub, sub_eq_add_neg]
    _ ≤ ((x : ZMod q).valMinAbs +
          (-(y : ZMod q)).valMinAbs).natAbs := h
    _ ≤ (centeredMod q x).natAbs +
          (centeredMod q y).natAbs := by
      exact (Int.natAbs_add_le _ _).trans_eq (by
        rw [ZMod.natAbs_valMinAbs_neg]
        rfl)

/-- Negation does not change centered modular magnitude. -/
theorem centeredMod_neg_natAbs (q : ℕ) (z : ℤ) :
    (centeredMod q (-z)).natAbs = (centeredMod q z).natAbs := by
  unfold centeredMod
  simpa only [Int.cast_neg] using ZMod.natAbs_valMinAbs_neg (z : ZMod q)

/-- Centered reduction preserves magnitude when the input is at most half the
modulus. This includes the even-modulus tie, where the representative may
change sign. -/
theorem centeredMod_natAbs_eq_self_of_two_mul_natAbs_le
    {q : ℕ} {z : ℤ} (hz : 2 * z.natAbs ≤ q) :
    (centeredMod q z).natAbs = z.natAbs := by
  cases z with
  | ofNat n =>
      have hn : n ≤ q / 2 :=
        (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 (by
          simpa [Nat.mul_comm] using hz)
      rw [Int.ofNat_eq_natCast]
      unfold centeredMod
      have hcast : (((n : ℕ) : ℤ) : ZMod q) = (n : ZMod q) := by norm_num
      rw [hcast, ZMod.valMinAbs_natCast_of_le_half hn]
  | negSucc n =>
      have hn : n + 1 ≤ q / 2 :=
        (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 (by
          simpa [Nat.mul_comm] using hz)
      rw [show Int.negSucc n = -((n + 1 : ℕ) : ℤ) by omega]
      rw [centeredMod_neg_natAbs]
      unfold centeredMod
      have hcast : ((((n + 1 : ℕ) : ℤ)) : ZMod q) =
          ((n + 1 : ℕ) : ZMod q) := by norm_num
      rw [hcast, ZMod.valMinAbs_natCast_of_le_half hn, Int.natAbs_neg]

theorem scaledCenteredArcPass_not_zero_and_add
    {q scale radius : ℕ} {shift step : ℤ}
    (hsep : 2 * radius <
      scale * (centeredMod q step).natAbs) :
    ¬(ScaledCenteredArcPass q scale radius shift ∧
      ScaledCenteredArcPass q scale radius (shift + step)) := by
  rintro ⟨hzero, hpos⟩
  have hdist := centeredMod_natAbs_sub_le_add q (shift + step) shift
  have hdist' :
      (centeredMod q step).natAbs ≤
        (centeredMod q (shift + step)).natAbs +
          (centeredMod q shift).natAbs := by
    simpa using hdist
  have hscaled := Nat.mul_le_mul_left scale hdist'
  rw [Nat.mul_add] at hscaled
  unfold ScaledCenteredArcPass at hzero hpos
  omega

theorem scaledCenteredArcPass_not_sub_and_zero
    {q scale radius : ℕ} {shift step : ℤ}
    (hsep : 2 * radius <
      scale * (centeredMod q step).natAbs) :
    ¬(ScaledCenteredArcPass q scale radius (shift - step) ∧
      ScaledCenteredArcPass q scale radius shift) := by
  rintro ⟨hneg, hzero⟩
  have hdist := centeredMod_natAbs_sub_le_add q (shift - step) shift
  have hdist' :
      (centeredMod q step).natAbs ≤
        (centeredMod q (shift - step)).natAbs +
          (centeredMod q shift).natAbs := by
    rw [← centeredMod_neg_natAbs q step]
    simpa using hdist
  have hscaled := Nat.mul_le_mul_left scale hdist'
  rw [Nat.mul_add] at hscaled
  unfold ScaledCenteredArcPass at hneg hzero
  omega

/-- The sparse three-atom law puts mass at most `1/2` in a centered modular
arc whose doubled radius is smaller than the modular step. -/
theorem sparseEntry_scaledCenteredArcPass_toReal_le_half
    (q scale radius : ℕ) (shift step : ℤ)
    (hsep : 2 * radius <
      scale * (centeredMod q step).natAbs) :
    (eventProbability sparseEntryPMF
      (fun x ↦ ScaledCenteredArcPass q scale radius
        (shift + x * step))).toReal ≤ (1 / 2 : ℝ) := by
  classical
  have hzeroPos := scaledCenteredArcPass_not_zero_and_add
    (shift := shift) hsep
  have hnegZero := scaledCenteredArcPass_not_sub_and_zero
    (shift := shift) hsep
  have hpull :
      eventProbability sparseEntryPMF
          (fun x ↦ ScaledCenteredArcPass q scale radius
            (shift + x * step)) =
        eventProbability (PMF.uniformOfFintype (Bool × Bool))
          (fun bits ↦ ScaledCenteredArcPass q scale radius
            (shift + sparseBit bits * step)) := by
    unfold sparseEntryPMF eventProbability
    rw [PMF.map_comp]
    rfl
  rw [hpull, eventProbability_toReal_eq_sum,
    Fintype.sum_prod_type, Fintype.sum_bool]
  by_cases hzero : ScaledCenteredArcPass q scale radius shift
  · have hneg :
        ¬ ScaledCenteredArcPass q scale radius (shift - step) := by
      intro h
      exact hnegZero ⟨h, hzero⟩
    have hpos :
        ¬ ScaledCenteredArcPass q scale radius (shift + step) := by
      intro h
      exact hzeroPos ⟨hzero, h⟩
    rw [sub_eq_add_neg] at hneg
    simp [PMF.uniformOfFintype_apply, sparseBit, hzero, hneg, hpos]
    norm_num
  · by_cases hneg :
        ScaledCenteredArcPass q scale radius (shift + -step)
    · by_cases hpos :
          ScaledCenteredArcPass q scale radius (shift + step)
      · simp [PMF.uniformOfFintype_apply, sparseBit, hzero, hneg, hpos]
        norm_num
      · simp [PMF.uniformOfFintype_apply, sparseBit, hzero, hneg, hpos]
        norm_num
    · by_cases hpos :
          ScaledCenteredArcPass q scale radius (shift + step)
      · simp [PMF.uniformOfFintype_apply, sparseBit, hzero, hneg, hpos]
        norm_num
      · simp [PMF.uniformOfFintype_apply, sparseBit, hzero, hneg, hpos]

/-- A raw centered-input bound may replace the modular step magnitude in the
three-atom estimate. -/
theorem sparseEntry_scaledCenteredArcPass_toReal_le_half_of_centered
    {q scale radius : ℕ} (shift step : ℤ)
    (hcentered : 2 * step.natAbs ≤ q)
    (hsep : 2 * radius < scale * step.natAbs) :
    (eventProbability sparseEntryPMF
      (fun x ↦ ScaledCenteredArcPass q scale radius
        (shift + x * step))).toReal ≤ (1 / 2 : ℝ) := by
  apply sparseEntry_scaledCenteredArcPass_toReal_le_half
  rw [centeredMod_natAbs_eq_self_of_two_mul_natAbs_le hcentered]
  exact hsep

end CertifiedJL.Probability
