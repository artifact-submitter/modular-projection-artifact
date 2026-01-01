/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Statements.Shared.BudgetAllocation

/-!
# Failure-budget split for the 128-bit threshold lower tail

This small upstream module keeps the dominant analytic providers independent
of the final three-regime assembly.
-/

open scoped ENNReal

namespace CertifiedJL

noncomputable def sparseThreshold128LowActivityBudget : ENNReal :=
  (13 : ENNReal) / 200 * failureTarget 128

noncomputable def sparseThreshold128HighActivityBudget : ENNReal :=
  (187 : ENNReal) / 200 * failureTarget 128

theorem sparseThreshold128Budgets_add :
    sparseThreshold128LowActivityBudget +
        sparseThreshold128HighActivityBudget =
      failureTarget 128 := by
  unfold sparseThreshold128LowActivityBudget
    sparseThreshold128HighActivityBudget
  rw [← add_mul]
  rw [show (13 : ENNReal) / 200 + 187 / 200 = 1 by
    change (13 : ENNReal) * 200⁻¹ + (187 : ENNReal) * 200⁻¹ = 1
    rw [← add_mul]
    norm_num only [OfNat.ofNat, Nat.cast_ofNat]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  simp

end CertifiedJL
