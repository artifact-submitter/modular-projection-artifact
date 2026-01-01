/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Finite.UniformPiBridge
import CertifiedJL.Probability.Finite.FailureBudget
import CertifiedJL.Model.Distributions.Signs

/-!
# Finite Rademacher sums

This module gives the finite uniform-bit model used by the one-row proof. In
particular, it records sign-complement symmetry at the level of the exact PMF,
so the final two-sided bound does not rely on an informal appeal to symmetry.
-/

open scoped BigOperators ENNReal

namespace CertifiedJL

/-- A real Rademacher sum driven by uniform Boolean sign bits. -/
def rademacherSum {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (bits : ι → Bool) : ℝ :=
  ∑ i, (signBit (bits i) : ℝ) * a i

/-- The uniform law of a finite family of Rademacher sign bits. -/
noncomputable def rademacherPMF (ι : Type*) [Fintype ι] :
    PMF (ι → Bool) :=
  uniformPiPMF (fun _ : ι => Bool)

/-- Complement every sign bit. -/
def complementBits {ι : Type*} (bits : ι → Bool) : ι → Bool :=
  fun i => !(bits i)

@[simp]
theorem complementBits_complementBits {ι : Type*} (bits : ι → Bool) :
    complementBits (complementBits bits) = bits := by
  funext i
  simp [complementBits]

/-- Bitwise complement is an involutive equivalence of sign seeds. -/
def complementBitsEquiv (ι : Type*) : (ι → Bool) ≃ (ι → Bool) where
  toFun := complementBits
  invFun := complementBits
  left_inv := complementBits_complementBits
  right_inv := complementBits_complementBits

@[simp]
theorem signBit_not (b : Bool) :
    (signBit (!b) : ℝ) = -(signBit b : ℝ) := by
  cases b <;> norm_num [signBit]

@[simp]
theorem rademacherSum_complement {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (bits : ι → Bool) :
    rademacherSum a (complementBits bits) = -rademacherSum a bits := by
  simp only [rademacherSum, complementBits, signBit_not, neg_mul,
    Finset.sum_neg_distrib]

/--
The strict lower and upper tails of a finite Rademacher sum have exactly the
same probability.
-/
theorem rademacherSum_strict_tail_symmetry
    {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (x : ℝ) :
    eventProbability (rademacherPMF ι)
        (fun bits => rademacherSum a bits < -x) =
      eventProbability (rademacherPMF ι)
        (fun bits => x < rademacherSum a bits) := by
  let : Fintype (ι → Bool) := Fintype.ofFinite (ι → Bool)
  unfold rademacherPMF
  rw [uniformPiPMF_eq_uniformOfFintype]
  rw [eventProbability_uniform_equiv (complementBitsEquiv ι)]
  apply congrArg
  funext bits
  apply propext
  change rademacherSum a (complementBits bits) < -x ↔
    x < rademacherSum a bits
  rw [rademacherSum_complement]
  exact neg_lt_neg_iff

/--
A strict one-sided Rademacher tail bound at `bits + 1` implies the strict
two-sided absolute tail bound at `bits`.
-/
theorem rademacherSum_abs_tail_lt
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (x : ℝ) (bits : ℕ)
    (hupper :
      eventProbability (rademacherPMF ι)
          (fun seed => x < rademacherSum a seed) <
        failureTarget (bits + 1)) :
    eventProbability (rademacherPMF ι)
        (fun seed => |rademacherSum a seed| > x) <
      failureTarget bits := by
  have habs :
      eventProbability (rademacherPMF ι)
          (fun seed => |rademacherSum a seed| > x) =
        eventProbability (rademacherPMF ι)
          (fun seed =>
            rademacherSum a seed < -x ∨ x < rademacherSum a seed) := by
    apply congrArg
    funext seed
    apply propext
    let s := rademacherSum a seed
    change |s| > x ↔ s < -x ∨ x < s
    constructor
    · intro hs
      by_cases hleft : s < -x
      · exact Or.inl hleft
      · right
        by_contra hright
        have hsLower : -x ≤ s := le_of_not_gt hleft
        have hsUpper : s ≤ x := le_of_not_gt hright
        exact (not_le_of_gt hs) ((abs_le).2 ⟨hsLower, hsUpper⟩)
    · rintro (hleft | hright)
      · simpa only [neg_neg] using
          (neg_lt_neg hleft).trans_le (neg_le_abs s)
      · exact hright.trans_le (le_abs_self s)
  have htwo0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have htwoTop : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  rw [habs]
  calc
    eventProbability (rademacherPMF ι)
        (fun seed =>
          rademacherSum a seed < -x ∨ x < rademacherSum a seed) ≤
      eventProbability (rademacherPMF ι)
          (fun seed => rademacherSum a seed < -x) +
        eventProbability (rademacherPMF ι)
          (fun seed => x < rademacherSum a seed) :=
      eventProbability_or_le _ _ _
    _ = 2 * eventProbability (rademacherPMF ι)
          (fun seed => x < rademacherSum a seed) := by
      rw [rademacherSum_strict_tail_symmetry]
      ring
    _ < 2 * failureTarget (bits + 1) :=
      ENNReal.mul_lt_mul_right htwo0 htwoTop hupper
    _ = failureTarget bits := by
      unfold failureTarget
      rw [show bits + 1 = Nat.succ bits by omega, pow_succ]
      calc
        2 * ((2 : ℝ≥0∞)⁻¹ ^ bits * (2 : ℝ≥0∞)⁻¹) =
            (2 : ℝ≥0∞)⁻¹ ^ bits *
              (2 * (2 : ℝ≥0∞)⁻¹) := by ring
        _ = (2 : ℝ≥0∞)⁻¹ ^ bits := by
          rw [two_mul, ENNReal.inv_two_add_inv_two, mul_one]

end CertifiedJL
