/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Elementary logarithm bounds

This file collects the two explicit Taylor inequalities used in the local
binomial comparison.  They are intentionally stated independently of the
Johnson--Lindenstrauss parameters.
-/

namespace CertifiedJL
namespace Probability

/--
A third-order lower bound for `log (1 - u)`.

The remainder constant is slightly weaker than the paper's displayed
constant, but remains strong enough for the exact `336` counterexample and
follows directly from Mathlib's kernel-checked logarithm remainder theorem.
-/
theorem neg_add_sq_add_log_one_sub_le {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    -(u + u ^ 2 / 2 + u ^ 3 / (1 - u)) ≤ Real.log (1 - u) := by
  have habs := Real.abs_log_sub_add_sum_range_le
    (x := u) (by simpa [abs_of_nonneg hu0] using hu1) 2
  rw [abs_of_nonneg hu0] at habs
  have habs' :
      |u + u ^ 2 / 2 + Real.log (1 - u)| ≤
        u ^ 3 / (1 - u) := by
    norm_num [Finset.sum_range_succ] at habs ⊢
    exact habs
  have hlower :
      -(u ^ 3 / (1 - u)) ≤
        u + u ^ 2 / 2 + Real.log (1 - u) :=
    (neg_le_of_abs_le habs')
  linarith

/-- A cubic upper bound for `log (1 + v)` on the nonnegative axis. -/
theorem log_one_add_le_cubic {v : ℝ} (hv : 0 ≤ v) :
    Real.log (1 + v) ≤ v - v ^ 2 / 2 + v ^ 3 / 3 := by
  let f : ℝ → ℝ :=
    fun x => x - x ^ 2 / 2 + x ^ 3 / 3 - Real.log (1 + x)
  let f' : ℝ → ℝ := fun x => x ^ 3 / (1 + x)
  have hderiv :
      ∀ x ∈ Set.Icc (0 : ℝ) v, HasDerivAt f (f' x) x := by
    intro x hx
    have hxpos : 0 < 1 + x := by
      exact add_pos_of_pos_of_nonneg zero_lt_one hx.1
    have hbase :=
      (((hasDerivAt_id x).sub
        (((hasDerivAt_id x).pow 2).div_const 2)).add
          (((hasDerivAt_id x).pow 3).div_const 3)).sub
        (((hasDerivAt_const x 1).add (hasDerivAt_id x)).log
          hxpos.ne')
    have hvalue :
        1 - (2 : ℝ) * x ^ (2 - 1) * 1 / 2 +
            (3 : ℝ) * x ^ (3 - 1) * 1 / 3 -
              (0 + 1) / (1 + x) =
          x ^ 3 / (1 + x) := by
      field_simp
      ring
    have hbase' := hbase.congr_deriv hvalue
    apply hbase'.congr_of_eventuallyEq
    filter_upwards with y
    simp only [f, id_eq, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]
  have hderiv_nonneg :
      ∀ x ∈ interior (Set.Icc (0 : ℝ) v), 0 ≤ f' x := by
    intro x hx
    rw [interior_Icc, Set.mem_Ioo] at hx
    exact div_nonneg (pow_nonneg hx.1.le _) (by linarith)
  have hmono :=
    monotoneOn_of_hasDerivWithinAt_nonneg
      (convex_Icc 0 v)
      (fun x hx => (hderiv x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hderiv x (interior_subset hx)).hasDerivWithinAt)
      hderiv_nonneg
  have hzero : f 0 = 0 := by norm_num [f]
  have := hmono ⟨le_rfl, hv⟩ ⟨hv, le_rfl⟩ hv
  norm_num [f] at this
  linarith

end Probability
end CertifiedJL
