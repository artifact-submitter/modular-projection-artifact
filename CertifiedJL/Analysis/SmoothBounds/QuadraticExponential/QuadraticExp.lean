/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.NormNum

/-!
# Smooth complex quadratic exponential

This is the smoothness boundary for the noncompact Peano consumer.
The actual derivative formula and exponential-integrability estimates remain
separate obligations.  This module records the exact complex-valued function,
its analytic `C^ω` regularity on a real argument, and the retained `C⁴`
compatibility specialization.
-/

namespace CertifiedJL

open scoped ContDiff

/-- The complex exponential of a real quadratic argument. -/
noncomputable def complexQuadraticExp (s : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (s * (x : ℂ) ^ 2)

/-- The real-variable complex quadratic exponential has Mathlib's analytic
regularity order `ω`, hence every finite derivative order used below. -/
theorem contDiff_omega_complexQuadraticExp (s : ℂ) :
    ContDiff ℝ ω (complexQuadraticExp s) := by
  have hx : ContDiff ℝ ω (fun x : ℝ => (x : ℂ)) :=
    Complex.ofRealCLM.contDiff.of_le le_rfl
  have hsq : ContDiff ℝ ω (fun x : ℝ => (x : ℂ) ^ 2) := hx.pow 2
  have harg : ContDiff ℝ ω (fun x : ℝ => s * (x : ℂ) ^ 2) := by
    simpa only using (contDiff_const.mul hsq)
  have hinst : (NormedSpace.complexToReal : NormedSpace ℝ ℂ) =
      (NormedAlgebra.toNormedSpace ℂ : NormedSpace ℝ ℂ) := by
    with_reducible_and_instances rfl
  rw [hinst]
  change ContDiff ℝ ω (fun x : ℝ => Complex.exp (s * (x : ℂ) ^ 2))
  exact harg.cexp

theorem contDiff_complexQuadraticExp (s : ℂ) :
    ContDiff ℝ 4 (complexQuadraticExp s) :=
  (contDiff_omega_complexQuadraticExp s).of_le
    (show (4 : ℕ∞ω) ≤ ω by simp)

end CertifiedJL
