/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

/-!
# Rational brackets for nonnegative real cube roots

Numerical certificates provide rational lower and upper endpoints whose
cubes bracket a nonnegative real.  These lemmas turn those elementary
polynomial checks into bounds for the real one-third power.
-/

namespace CertifiedJL

theorem rpow_one_third_cube {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  simpa only [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num] using
    Real.rpow_inv_natCast_pow hx (by norm_num : (3 : ℕ) ≠ 0)

theorem le_rpow_one_third_of_cube_le
    {q x : ℝ} (hq : 0 ≤ q) (hx : 0 ≤ x)
    (hcube : q ^ 3 ≤ x) :
    q ≤ x ^ (1 / 3 : ℝ) := by
  apply (pow_le_pow_iff_left₀ hq (Real.rpow_nonneg hx _)
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  rwa [rpow_one_third_cube hx]

theorem rpow_one_third_le_of_le_cube
    {x q : ℝ} (hx : 0 ≤ x) (hq : 0 ≤ q)
    (hcube : x ≤ q ^ 3) :
    x ^ (1 / 3 : ℝ) ≤ q := by
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hx _) hq
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  rwa [rpow_one_third_cube hx]

theorem rpow_two_thirds_mem_sq_bracket
    {x q₀ q₁ : ℝ} (hx : 0 ≤ x)
    (hq₀ : 0 ≤ q₀) (hq₁ : 0 ≤ q₁)
    (hlower : q₀ ^ 3 ≤ x) (hupper : x ≤ q₁ ^ 3) :
    q₀ ^ 2 ≤ x ^ (2 / 3 : ℝ) ∧
      x ^ (2 / 3 : ℝ) ≤ q₁ ^ 2 := by
  have hrootLower :=
    le_rpow_one_third_of_cube_le hq₀ hx hlower
  have hrootUpper :=
    rpow_one_third_le_of_le_cube hx hq₁ hupper
  have hroot0 : 0 ≤ x ^ (1 / 3 : ℝ) :=
    Real.rpow_nonneg hx _
  have hpow :
      x ^ (2 / 3 : ℝ) = (x ^ (1 / 3 : ℝ)) ^ 2 := by
    simpa only [show (2 / 3 : ℝ) = (1 / 3 : ℝ) * (2 : ℕ) by norm_num] using
      Real.rpow_mul_natCast hx (1 / 3 : ℝ) 2
  rw [hpow]
  exact ⟨
    (sq_le_sq₀ hq₀ hroot0).2 hrootLower,
    (sq_le_sq₀ hroot0 hq₁).2 hrootUpper⟩

end CertifiedJL
