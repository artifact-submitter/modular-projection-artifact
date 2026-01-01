/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule

/-!
# Upper trapezoidal sums for convex integrands

The ordinary trapezoidal rule is an upper bound for a convex real function.
Mathlib contains the trapezoidal evaluator and an absolute-error theorem; the
short theorem below records the one-sided fact needed by exact certificates.
-/

open MeasureTheory Set
open scoped BigOperators

namespace CertifiedJL

/-- One chord bounds the integral of a convex function from above. -/
theorem intervalIntegral_le_oneTrapezoid_of_convexOn
    {f : ℝ → ℝ} {A B : ℝ} (hAB : A ≤ B)
    (hf : ConvexOn ℝ (Icc A B) f)
    (hint : IntervalIntegrable f volume A B) :
    (∫ x : ℝ in A..B, f x) ≤
      (B - A) / 2 * (f A + f B) := by
  rcases hAB.eq_or_lt with rfl | hABlt
  · simp
  let chord : ℝ → ℝ := fun x =>
    ((B - x) / (B - A)) * f A +
      ((x - A) / (B - A)) * f B
  have hchordContinuous : Continuous chord := by
    dsimp [chord]
    fun_prop
  have hpoint :
      ∀ x ∈ Icc A B, f x ≤ chord x := by
    intro x hx
    let a : ℝ := (B - x) / (B - A)
    let b : ℝ := (x - A) / (B - A)
    have ha : 0 ≤ a := by
      dsimp [a]
      exact div_nonneg (sub_nonneg.mpr hx.2)
        (sub_nonneg.mpr hAB)
    have hb : 0 ≤ b := by
      dsimp [b]
      exact div_nonneg (sub_nonneg.mpr hx.1)
        (sub_nonneg.mpr hAB)
    have hab : a + b = 1 := by
      dsimp [a, b]
      field_simp [sub_ne_zero.mpr hABlt.ne']
      ring
    have hcombo : a • A + b • B = x := by
      dsimp [a, b]
      field_simp [sub_ne_zero.mpr hABlt.ne']
      ring
    have h := hf.2
      (left_mem_Icc.mpr hAB) (right_mem_Icc.mpr hAB)
      ha hb hab
    rw [hcombo] at h
    simpa [chord, a, b, smul_eq_mul] using h
  have hmono :
      (∫ x : ℝ in A..B, f x) ≤
        ∫ x : ℝ in A..B, chord x := by
    exact intervalIntegral.integral_mono_on hAB hint
      (hchordContinuous.intervalIntegrable _ _) hpoint
  calc
    (∫ x : ℝ in A..B, f x)
        ≤ ∫ x : ℝ in A..B, chord x := hmono
    _ = (B - A) / 2 * (f A + f B) := by
      dsimp [chord]
      rw [intervalIntegral.integral_add
        ((by fun_prop : Continuous
          (fun x : ℝ => (B - x) / (B - A) * f A)).intervalIntegrable _ _)
        ((by fun_prop : Continuous
          (fun x : ℝ => (x - A) / (B - A) * f B)).intervalIntegrable _ _)]
      rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_mul_const]
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_div]
      have hleft :
          (∫ x : ℝ in A..B, B - x) =
            B * (B - A) - (B ^ 2 - A ^ 2) / 2 := by
        have hfun :
            (fun x : ℝ => B - x) =
              fun x : ℝ => B + (-1) * x := by
          funext x
          ring
        rw [hfun, intervalIntegral.integral_add
          (continuous_const.intervalIntegrable _ _)
          ((by fun_prop : Continuous
            (fun x : ℝ => (-1) * x)).intervalIntegrable _ _)]
        rw [intervalIntegral.integral_const,
          intervalIntegral.integral_const_mul, integral_id]
        simp only [smul_eq_mul]
        ring
      have hright :
          (∫ x : ℝ in A..B, x - A) =
            (B ^ 2 - A ^ 2) / 2 - A * (B - A) := by
        rw [intervalIntegral.integral_sub
          (f := fun x : ℝ => x) (g := fun _ : ℝ => A)
          (continuous_id.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _)]
        rw [integral_id, intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
      rw [hleft, hright]
      field_simp [sub_ne_zero.mpr hABlt.ne']
      ring

/--
The `n`-cell trapezoidal rule bounds a convex integrand from above.
-/
theorem intervalIntegral_le_trapezoidalIntegral_of_convexOn
    {f : ℝ → ℝ} {A B : ℝ} (n : ℕ)
    (hAB : A ≤ B) (hn : 0 < n)
    (hf : ConvexOn ℝ (Icc A B) f)
    (hcont : ContinuousOn f (Icc A B)) :
    (∫ x : ℝ in A..B, f x) ≤
      trapezoidal_integral f n A B := by
  let h : ℝ := (B - A) / n
  let grid : ℕ → ℝ := fun i => A + i * h
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hh : 0 ≤ h := by
    dsimp [h]
    positivity
  have hgrid (i : ℕ) (hi : i ≤ n) :
      grid i ∈ Icc A B := by
    constructor
    · dsimp [grid]
      exact le_add_of_nonneg_right (mul_nonneg (by positivity) hh)
    · dsimp [grid, h]
      calc
        A + (i : ℝ) * ((B - A) / n)
            ≤ A + (n : ℝ) * ((B - A) / n) := by
              gcongr
        _ = B := by
              field_simp
              ring
  have hgridMono (i : ℕ) :
      grid i ≤ grid (i + 1) := by
    dsimp [grid]
    gcongr
    exact_mod_cast Nat.le_succ i
  have hint (i : ℕ) (hi : i < n) :
      IntervalIntegrable f volume (grid i) (grid (i + 1)) := by
    apply (hcont.mono ?_).intervalIntegrable
    rw [uIcc_of_le (hgridMono i)]
    exact Icc_subset_Icc (hgrid i hi.le).1
      (hgrid (i + 1) hi).2
  have hpiece (i : ℕ) (hi : i < n) :
      (∫ x : ℝ in grid i..grid (i + 1), f x) ≤
        trapezoidal_integral
          f 1 (grid i) (grid (i + 1)) := by
    rw [trapezoidal_integral_one]
    apply intervalIntegral_le_oneTrapezoid_of_convexOn
      (by
        dsimp [grid]
        gcongr
        exact Nat.cast_le.mpr (Nat.le_succ i))
      (by
        have hsub := Icc_subset_Icc
          (hgrid i hi.le).1
          (hgrid (i + 1) hi).2
        refine ⟨convex_Icc _ _, ?_⟩
        intro x hx y hy a b ha hb hab
        exact hf.2 (hsub hx) (hsub hy) ha hb hab)
      (hint i hi)
  have hsum :
      (∑ i ∈ Finset.range n,
          ∫ x : ℝ in grid i..grid (i + 1), f x) ≤
        ∑ i ∈ Finset.range n,
          trapezoidal_integral
            f 1 (grid i) (grid (i + 1)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hpiece i (Finset.mem_range.mp hi)
  have hleft :
      (∑ i ∈ Finset.range n,
          ∫ x : ℝ in grid i..grid (i + 1), f x) =
        ∫ x : ℝ in A..B, f x := by
    rw [intervalIntegral.sum_integral_adjacent_intervals]
    · have hzero : grid 0 = A := by simp [grid]
      have hnend : grid n = B := by
        dsimp [grid, h]
        field_simp
        ring
      rw [hzero, hnend]
    · exact hint
  have hright :
      (∑ i ∈ Finset.range n,
          trapezoidal_integral
            f 1 (grid i) (grid (i + 1))) =
        trapezoidal_integral f n A B := by
    have hsumTrap :=
      sum_trapezoidal_integral_adjacent_intervals
        (f := f) (a := A) (h := h) hn
    have hend : A + (n : ℝ) * h = B := by
      dsimp [h]
      field_simp
      ring
    simpa [grid, hend] using hsumTrap
  rwa [hleft, hright] at hsum

end CertifiedJL
