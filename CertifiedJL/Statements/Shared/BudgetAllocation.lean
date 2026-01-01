/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Finite.FailureBudget
import CertifiedJL.Probability.Product.RowTensorization
import Mathlib.Data.ENNReal.BigOperators

/-!
# Failure budgets

Probability statements accept arbitrary `ENNReal` budgets.  These helpers
construct common powers-of-two targets and explicit union-bound allocations.
-/

namespace CertifiedJL

open scoped BigOperators

/-- A power-of-two target with an arbitrary number of additional slack bits. -/
noncomputable def failureTargetWithSlack
    (bits slackBits : ℕ) : ENNReal :=
  failureTarget (bits + slackBits)

/-- An equal share of an arbitrary failure budget. -/
noncomputable def equalBudgetShare
    (budget : ENNReal) (shares : ℕ) (_ : 0 < shares) : ENNReal :=
  budget / shares

/-- An equal share of a power-of-two target with optional slack bits. -/
noncomputable def equalShareFailureTarget
    (shares bits slackBits : ℕ) (hshares : 0 < shares) : ENNReal :=
  equalBudgetShare (failureTargetWithSlack bits slackBits) shares hshares

/-- A finite union is strictly below a total budget when every branch is
strictly below its allocation and the allocations sum to at most the total. -/
theorem eventProbability_iUnion_lt_of_budgetAllocation
    {ι α : Type*} [Fintype ι] [Nonempty ι] [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) (event : ι → α → Prop)
    (allocation : ι → ENNReal) (total : ENNReal)
    (hbranch : ∀ i, eventProbability p (event i) < allocation i)
    (hallocation : ∑ i, allocation i ≤ total) :
    eventProbability p (fun x ↦ ∃ i, event i x) < total := by
  calc
    eventProbability p (fun x ↦ ∃ i, event i x) ≤
        ∑ i, eventProbability p (event i) :=
      eventProbability_exists_le_sum p event
    _ < ∑ i, allocation i :=
      ENNReal.sum_lt_sum_of_nonempty Finset.univ_nonempty
        (fun i _ ↦ hbranch i)
    _ ≤ total := hallocation

/-- At most `2^slackBits` equal allocations of
`2^-(bits + slackBits)` fit inside a `2^-bits` total budget. -/
theorem nsmul_failureTarget_add_le
    {shares bits slackBits : ℕ} (hshares : shares ≤ 2 ^ slackBits) :
    shares • failureTarget (bits + slackBits) ≤ failureTarget bits := by
  calc
    shares • failureTarget (bits + slackBits) =
        (shares : ENNReal) * failureTarget (bits + slackBits) := by
      rw [nsmul_eq_mul]
    _ ≤ (2 ^ slackBits : ℕ) * failureTarget (bits + slackBits) := by
      gcongr
    _ = failureTarget bits := by
      simp only [failureTarget, Nat.cast_pow, Nat.cast_ofNat, pow_add]
      calc
        (2 : ENNReal) ^ slackBits *
            ((2 : ENNReal)⁻¹ ^ bits * (2 : ENNReal)⁻¹ ^ slackBits) =
          (2 : ENNReal)⁻¹ ^ bits *
            ((2 : ENNReal) ^ slackBits *
              (2 : ENNReal)⁻¹ ^ slackBits) := by ac_rfl
        _ = (2 : ENNReal)⁻¹ ^ bits := by
          rw [← mul_pow]
          rw [ENNReal.mul_inv_cancel (by norm_num) (by finiteness)]
          simp

end CertifiedJL
