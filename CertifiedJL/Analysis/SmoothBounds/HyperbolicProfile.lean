/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Elementary hyperbolic calculus

This file supplies the small calculus interface for the hyperbolic profile
appearing in the sparse one-row tail bound.  The proofs deliberately expose
`tanh` as `sinh / cosh`; this keeps the dependency on special-function
calculus explicit and reduces the remaining inequalities to the identity
`cosh² - sinh² = 1`.
-/

namespace CertifiedJL
namespace Probability

/-- The derivative of `tanh`, in the reciprocal-`cosh` form used below. -/
theorem hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh ((Real.cosh x)⁻¹ ^ 2) x := by
  have h :=
    (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x)
      (Real.cosh_pos x).ne'
  have hfun :
      Real.sinh / Real.cosh = Real.tanh := by
    funext y
    simpa only [Pi.div_apply] using (Real.tanh_eq_sinh_div_cosh y).symm
  rw [hfun] at h
  apply h.congr_deriv
  rw [inv_pow]
  field_simp
  exact Real.cosh_sq_sub_sinh_sq x

/-- `tanh` is differentiable everywhere. -/
theorem differentiable_tanh : Differentiable ℝ Real.tanh :=
  fun x => (hasDerivAt_tanh x).differentiableAt

/-- `tanh` is continuous everywhere. -/
theorem continuous_tanh : Continuous Real.tanh :=
  differentiable_tanh.continuous

/-- The derivative of `x ↦ log (cosh x)` is `tanh x`. -/
theorem hasDerivAt_log_cosh (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.log (Real.cosh y)) (Real.tanh x) x := by
  convert (Real.hasDerivAt_cosh x).log (Real.cosh_pos x).ne' using 1
  rw [Real.tanh_eq_sinh_div_cosh]

/-- The fundamental identity `1 - tanh² = cosh⁻²`. -/
theorem one_sub_tanh_sq (x : ℝ) :
    1 - Real.tanh x ^ 2 = (Real.cosh x)⁻¹ ^ 2 := by
  rw [Real.tanh_eq_sinh_div_cosh, div_pow, inv_pow]
  field_simp
  exact Real.cosh_sq_sub_sinh_sq x

/-- `tanh` has the sign of its argument on the nonnegative half-line. -/
theorem tanh_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hx) (Real.cosh_pos x).le

/-- The elementary upper tangent bound `tanh x ≤ x` for `x ≥ 0`. -/
theorem tanh_le_self {x : ℝ} (hx : 0 ≤ x) :
    Real.tanh x ≤ x := by
  let f : ℝ → ℝ := id - Real.tanh
  have hf : Differentiable ℝ f :=
    differentiable_id.sub differentiable_tanh
  have hderiv : ∀ y, 0 ≤ deriv f y := by
    intro y
    have hd :
        HasDerivAt f (1 - (Real.cosh y)⁻¹ ^ 2) y := by
      simpa only [f] using (hasDerivAt_id y).sub (hasDerivAt_tanh y)
    rw [hd.deriv, ← one_sub_tanh_sq]
    exact sub_nonneg.mpr (sub_le_self 1 (sq_nonneg (Real.tanh y)))
  have hmono : Monotone f :=
    monotone_of_deriv_nonneg hf hderiv
  have hzero : f 0 = 0 := by simp [f]
  have := hmono hx
  simpa [f, hzero] using this

end Probability
end CertifiedJL
