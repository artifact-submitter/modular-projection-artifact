/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Interval.Reflection
import CertifiedJL.Certificates.Families.L2Lower.Shared.Spec
import Mathlib.Tactic.NormNum

/-! # Reflected numeric replay for the low-mass diffuse modular tail -/

namespace CertifiedJL.CertificateProviders.SparseThresholdDiffuse

private theorem exp_neg_lt {x u : ℚ} (hx : 0 ≤ x)
    (hcheck : Interval.upperLTCheck (Exp.negUpper 48 x 32) u = true) :
    Real.exp (-(x : ℝ)) < (u : ℝ) := by
  have hcontains := Exp.negUpper_contains (p := 48) (k := 32) (x := x) hx
  exact Interval.lt_of_contains_of_upperLTCheck hcontains hcheck

private theorem lowBand {c : ℝ} (hc : (7425 / 1108 : ℝ) ≤ c) :
    2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) < (13 / 5000 : ℝ) := by
  let y : ℝ := Real.exp (-c)
  have hy : y < (1 / 800 : ℝ) := by
    have hmono : y ≤ Real.exp (-(7425 / 1108 : ℝ)) := by
      dsimp [y]
      exact Real.exp_le_exp.mpr (by linarith)
    have hcert : Real.exp (-(7425 / 1108 : ℝ)) < (1 / 800 : ℝ) := by
      convert exp_neg_lt (x := (7425 / 1108 : ℚ))
        (u := (1 / 800 : ℚ)) (by norm_num) (by decide +kernel) using 1 <;> norm_num
    exact hmono.trans_lt hcert
  have hy0 : 0 ≤ y := (Real.exp_pos _).le
  have hy3 : y ^ 3 < (1 / 800 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hy hy0 (by norm_num)
  have hden : 0 < 1 - y ^ 3 := by nlinarith
  change 2 * y / (1 - y ^ 3) < (13 / 5000 : ℝ)
  rw [div_lt_iff₀ hden]
  nlinarith

private theorem fullBand {c : ℝ} (hc : (2970 / 463 : ℝ) ≤ c) :
    2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) < (1 / 200 : ℝ) := by
  let y : ℝ := Real.exp (-c)
  have hy : y < (1 / 600 : ℝ) := by
    have hmono : y ≤ Real.exp (-(2970 / 463 : ℝ)) := by
      dsimp [y]
      exact Real.exp_le_exp.mpr (by linarith)
    have hcert : Real.exp (-(2970 / 463 : ℝ)) < (1 / 600 : ℝ) := by
      convert exp_neg_lt (x := (2970 / 463 : ℚ))
        (u := (1 / 600 : ℚ)) (by norm_num) (by decide +kernel) using 1 <;> norm_num
    exact hmono.trans_lt hcert
  have hy0 : 0 ≤ y := (Real.exp_pos _).le
  have hy3 : y ^ 3 < (1 / 600 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hy hy0 (by norm_num)
  have hden : 0 < 1 - y ^ 3 := by nlinarith
  change 2 * y / (1 - y ^ 3) < (1 / 200 : ℝ)
  rw [div_lt_iff₀ hden]
  nlinarith

theorem verified :
    CertificateContracts.SparseL2ThresholdDiffuseLowModularTail128 where
  lowBand := lowBand
  fullBand := fullBand

end CertifiedJL.CertificateProviders.SparseThresholdDiffuse
