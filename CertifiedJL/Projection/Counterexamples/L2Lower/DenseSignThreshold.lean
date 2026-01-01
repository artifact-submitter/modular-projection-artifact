/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Distributions.Signs
import CertifiedJL.Model.Modular.Centered
import CertifiedJL.Model.Modular.Projection
import CertifiedJL.Model.Vectors.SquaredNorm
import CertifiedJL.Statements.Shared.Input
import Mathlib.Tactic

/-!
# Dense signs obstruct public-threshold modular lower tails

The two-coordinate vector `(1000, 1000)` modulo `2001` is a concrete
counterexample.  Every dense-sign row has integer dot product `0` or `±2000`,
so its centered modular representative has absolute value at most one.  Thus
an arbitrary `m`-row dense-sign projection has modular projection squared norm at most `m`.
The squared norm is recorded only to verify that the public threshold `667`
is admissible.

This is a deterministic obstruction: changing the failure probability or
adding rows cannot repair the threshold formulation without a corresponding
restriction on the public input threshold.
-/

open scoped BigOperators

namespace CertifiedJL.Counterexamples.DenseSignThreshold

/-- The modulus-growth witness with two equal centered coefficients. -/
def scaledWitness (a : ℕ) : Fin 2 → ℤ := fun _ => a

private theorem centeredMod_two_mul (a : ℕ) (ha : 0 < a) :
    centeredMod (2 * a + 1) (2 * (a : ℤ)) = -1 := by
  apply (centeredMod_eq_iff ⟨a, by omega⟩ _ _).2
  constructor
  · rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    use 1
    push_cast
    ring
  · simp only [centeredInterval, Set.mem_Icc]
    norm_num
    omega

private theorem centeredMod_neg_two_mul (a : ℕ) (ha : 0 < a) :
    centeredMod (2 * a + 1) (-(2 * (a : ℤ))) = 1 := by
  apply (centeredMod_eq_iff ⟨a, by omega⟩ _ _).2
  constructor
  · rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    use -1
    push_cast
    ring
  · simp only [centeredInterval, Set.mem_Icc]
    norm_num
    omega

/-- Every dense-sign row maps `(a,a)` modulo `2a+1` to magnitude at most one. -/
theorem centeredMod_rowDot_scaledWitness_natAbs_le_one
    (a : ℕ) (ha : 0 < a) (seed : SignRowSeed 2) :
    (centeredMod (2 * a + 1)
      (∑ i, signRow seed i * scaledWitness a i)).natAbs ≤ 1 := by
  rw [Fin.sum_univ_two]
  simp only [signRow, scaledWitness]
  cases h0 : seed 0 <;> cases h1 : seed 1 <;>
    simp only [signBit, neg_mul, one_mul]
  · rw [show -(a : ℤ) + -(a : ℤ) = -(2 * (a : ℤ)) by ring,
      centeredMod_neg_two_mul a ha]
    norm_num
  · rw [neg_add_cancel, centeredMod_eq_self ⟨a, by omega⟩]
    · norm_num
    · simp only [centeredInterval, Set.mem_Icc, neg_nonpos]
      constructor <;> positivity
  · rw [add_neg_cancel, centeredMod_eq_self ⟨a, by omega⟩]
    · norm_num
    · simp only [centeredInterval, Set.mem_Icc, neg_nonpos]
      constructor <;> positivity
  · rw [show (a : ℤ) + (a : ℤ) = 2 * (a : ℤ) by ring,
      centeredMod_two_mul a ha]
    norm_num

/-- Every `m`-row dense-sign matrix has modular projection squared norm at
most `m` on the modulus-growth witness. -/
theorem modularProjectionSqNorm_scaledWitness_le_rows
    (m a : ℕ) (ha : 0 < a) (seed : SignSeed m 2) :
    modularProjectionSqNorm (2 * a + 1) (signMatrix seed) (scaledWitness a) ≤ m := by
  unfold modularProjectionSqNorm rowDot signMatrix
  calc
    ∑ j, (centeredMod (2 * a + 1)
        (∑ i, signRow (seed j) i * scaledWitness a i)).natAbs ^ 2 ≤
        ∑ _j : Fin m, 1 := by
      apply Finset.sum_le_sum
      intro j _hj
      have h := centeredMod_rowDot_scaledWitness_natAbs_le_one a ha (seed j)
      exact Nat.pow_le_pow_left h 2
    _ = m := by simp

theorem scaledWitness_centered (a : ℕ) :
    CenteredInput (2 * a + 1) (scaledWitness a) := by
  intro i
  have hhalf : (2 * a + 1) / 2 = a := by omega
  simp [scaledWitness, centeredInterval, hhalf]

theorem scaledWitness_sqNorm (a : ℕ) :
    sqNorm (scaledWitness a) = 2 * a ^ 2 := by
  simp [sqNorm, scaledWitness]

/-- Universal dense-sign threshold obstruction, including zero rows.  For
every row count and positive real margin/lower constant, the construction
chooses natural `a,b`, modulus `q=2a+1`, and `w=(a,a)` so that the public
threshold is admissible while every dense-sign matrix lies in the strict bad
event `‖ctr_q(Jw)‖² < c b²`. -/
theorem universal_real_threshold_failure
    (m : ℕ) (M c : ℝ) (_hM : 0 < M) (hc : 0 < c) :
    ∃ a b : ℕ,
      0 < a ∧
      0 < b ∧
      Odd (2 * a + 1) ∧
      CenteredInput (2 * a + 1) (scaledWitness a) ∧
      InputThresholdAtMostNorm b (scaledWitness a) ∧
      M * (b : ℝ) ≤ (2 * a + 1 : ℕ) ∧
      (m : ℝ) < c * (b : ℝ) ^ 2 ∧
      ∀ seed : SignSeed m 2,
        modularProjectionSqNorm (2 * a + 1) (signMatrix seed)
            (scaledWitness a) ≤ m ∧
          (modularProjectionSqNorm (2 * a + 1) (signMatrix seed)
              (scaledWitness a) : ℝ) < c * (b : ℝ) ^ 2 := by
  obtain ⟨b, hb⟩ := exists_nat_gt (max 1 ((m : ℝ) / c))
  have hb1 : (1 : ℝ) < b := lt_of_le_of_lt (le_max_left 1 ((m : ℝ) / c)) hb
  have hbpos : 0 < b := by exact_mod_cast (zero_lt_one.trans hb1)
  have hbm : (m : ℝ) / c < b :=
    lt_of_le_of_lt (le_max_right 1 ((m : ℝ) / c)) hb
  have hmb : (m : ℝ) < c * (b : ℝ) := by
    simpa only [mul_comm] using (div_lt_iff₀ hc).mp hbm
  have hmb2 : (m : ℝ) < c * (b : ℝ) ^ 2 := by
    have hbReal : (1 : ℝ) ≤ b := hb1.le
    calc
      (m : ℝ) < c * b := hmb
      _ ≤ c * b ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hc.le
        nlinarith
  obtain ⟨a, ha⟩ := exists_nat_gt
    (max (b : ℝ) (M * (b : ℝ) / 2))
  have habReal : (b : ℝ) < a :=
    lt_of_le_of_lt (le_max_left (b : ℝ) (M * (b : ℝ) / 2)) ha
  have hab : b ≤ a := by exact_mod_cast habReal.le
  have hapos : 0 < a := hbpos.trans_le hab
  have haM : M * (b : ℝ) / 2 < a :=
    lt_of_le_of_lt (le_max_right (b : ℝ) (M * (b : ℝ) / 2)) ha
  have hmargin : M * (b : ℝ) ≤ (2 * a + 1 : ℕ) := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    linarith
  refine ⟨a, b, hapos, hbpos, ⟨a, by omega⟩, scaledWitness_centered a,
    ?_, hmargin, hmb2, ?_⟩
  · simp only [InputThresholdAtMostNorm, scaledWitness_sqNorm]
    nlinarith [Nat.mul_self_le_mul_self hab]
  · intro seed
    have hrows := modularProjectionSqNorm_scaledWitness_le_rows m a hapos seed
    have hrowsReal :
        (modularProjectionSqNorm (2 * a + 1) (signMatrix seed)
          (scaledWitness a) : ℝ) ≤ m := by
      exact_mod_cast hrows
    exact ⟨hrows, hrowsReal.trans_lt hmb2⟩

/-- The explicit two-coordinate input used by the dense-sign obstruction. -/
def witness : Fin 2 → ℤ := fun _ => 1000

/-- Every dense-sign row maps the witness to centered magnitude at most one. -/
theorem centeredMod_rowDot_witness_natAbs_le_one
    (seed : SignRowSeed 2) :
    (centeredMod 2001 (∑ i, signRow seed i * witness i)).natAbs ≤ 1 := by
  rw [Fin.sum_univ_two]
  simp only [signRow, witness]
  cases h0 : seed 0 <;> cases h1 : seed 1 <;>
    norm_num [signBit, centeredMod, ZMod.valMinAbs]
  all_goals decide +kernel

/-- Every `m`-row dense-sign matrix has modular projection squared norm at most
`m` on the witness. -/
theorem modularProjectionSqNorm_witness_le_rows (m : ℕ) (seed : SignSeed m 2) :
    modularProjectionSqNorm 2001 (signMatrix seed) witness ≤ m := by
  unfold modularProjectionSqNorm rowDot signMatrix
  calc
    ∑ j, (centeredMod 2001
        (∑ i, signRow (seed j) i * witness i)).natAbs ^ 2 ≤
        ∑ _j : Fin m, 1 := by
      apply Finset.sum_le_sum
      intro j _hj
      have h := centeredMod_rowDot_witness_natAbs_le_one (seed j)
      exact Nat.pow_le_pow_left h 2
    _ = m := by simp

/-- The witness has squared Euclidean norm exactly `2,000,000`. -/
theorem witness_sqNorm : sqNorm witness = 2000000 := by
  norm_num [sqNorm, witness, Fin.sum_univ_two]

end CertifiedJL.Counterexamples.DenseSignThreshold
