/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib.Analysis.SumIntegralComparisons

/-!
# Certified endpoint Riemann sums

This file supplies the analytic soundness lemmas used by numerical integral
certificates.  They turn monotonicity or antitonicity on a compact interval
into a finite right- or left-endpoint sum with exact rational mesh.
-/

open MeasureTheory Set
open scoped BigOperators

namespace CertifiedJL

/--
The right-endpoint Riemann sum on an arbitrary nonempty compact interval.
-/
theorem intervalIntegral_le_rightRiemannSum_of_le
    {f : ℝ → ℝ} {A B : ℝ} (n : ℕ)
    (hAB : A ≤ B) (hn : 0 < n)
    (hf : MonotoneOn f (Icc A B)) :
    (∫ x : ℝ in A..B, f x) ≤
      ((B - A) / n) *
        ∑ i ∈ Finset.range n,
          f (A + ((B - A) / n) * (i + 1 : ℕ)) := by
  by_cases hEq : A = B
  · subst B
    simp
  have hABlt : A < B := hAB.lt_of_ne hEq
  let c : ℝ := (B - A) / n
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < c := div_pos (sub_pos.mpr hABlt) hnReal
  have hcn : c * (n : ℝ) = B - A := by
    dsimp [c]
    field_simp
  have hmono :
      MonotoneOn (fun x : ℝ => f (A + c * x))
        (Icc 0 (0 + n)) := by
    intro x hx y hy hxy
    apply hf
    · constructor
      · exact le_add_of_nonneg_right (mul_nonneg hc.le hx.1)
      · calc
          A + c * x ≤ A + c * (n : ℝ) := by
            gcongr
            simpa using hx.2
          _ = B := by rw [hcn]; ring
    · constructor
      · exact le_add_of_nonneg_right (mul_nonneg hc.le hy.1)
      · calc
          A + c * y ≤ A + c * (n : ℝ) := by
            gcongr
            simpa using hy.2
          _ = B := by rw [hcn]; ring
    · gcongr
  have hsum :
      (∫ x : ℝ in 0..(n : ℝ), f (A + c * x)) ≤
        ∑ i ∈ Finset.range n,
          f (A + c * (i + 1 : ℕ)) := by
    simpa using hmono.integral_le_sum
  have hscaled :=
    mul_le_mul_of_nonneg_left hsum hc.le
  have hIntegral :
      c * (∫ x : ℝ in 0..(n : ℝ), f (A + c * x)) =
        ∫ x : ℝ in A..B, f x := by
    have hchange :=
      intervalIntegral.smul_integral_comp_add_mul
        (f := f) (a := (0 : ℝ)) (b := (n : ℝ)) c A
    simpa [smul_eq_mul, hcn] using hchange
  rw [hIntegral] at hscaled
  simpa [c] using hscaled

/--
The right-endpoint Riemann sum of a monotone function bounds its integral
from above.
-/
theorem intervalIntegral_le_rightRiemannSum
    {f : ℝ → ℝ} {T : ℝ} (n : ℕ)
    (hT : 0 ≤ T) (hn : 0 < n)
    (hf : MonotoneOn f (Icc 0 T)) :
    (∫ x : ℝ in 0..T, f x) ≤
      (T / n) *
        ∑ i ∈ Finset.range n,
          f ((T / n) * (i + 1 : ℕ)) := by
  simpa using
    intervalIntegral_le_rightRiemannSum_of_le
      (f := f) (A := 0) (B := T) n hT hn hf

/--
The left-endpoint Riemann sum on an arbitrary nonempty compact interval bounds
the integral of an antitone function from above.
-/
theorem intervalIntegral_le_leftRiemannSum_of_le
    {f : ℝ → ℝ} {A B : ℝ} (n : ℕ)
    (hAB : A ≤ B) (hn : 0 < n)
    (hf : AntitoneOn f (Icc A B)) :
    (∫ x : ℝ in A..B, f x) ≤
      ((B - A) / n) *
        ∑ i ∈ Finset.range n,
          f (A + ((B - A) / n) * (i : ℕ)) := by
  by_cases hEq : A = B
  · subst B
    simp
  have hABlt : A < B := hAB.lt_of_ne hEq
  let c : ℝ := (B - A) / n
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < c := div_pos (sub_pos.mpr hABlt) hnReal
  have hcn : c * (n : ℝ) = B - A := by
    dsimp [c]
    field_simp
  have hanti :
      AntitoneOn (fun x : ℝ => f (A + c * x))
        (Icc 0 (0 + n)) := by
    intro x hx y hy hxy
    apply hf
    · constructor
      · exact le_add_of_nonneg_right (mul_nonneg hc.le hx.1)
      · calc
          A + c * x ≤ A + c * (n : ℝ) := by
            gcongr
            simpa using hx.2
          _ = B := by rw [hcn]; ring
    · constructor
      · exact le_add_of_nonneg_right (mul_nonneg hc.le hy.1)
      · calc
          A + c * y ≤ A + c * (n : ℝ) := by
            gcongr
            simpa using hy.2
          _ = B := by rw [hcn]; ring
    · gcongr
  have hsum :
      (∫ x : ℝ in 0..(n : ℝ), f (A + c * x)) ≤
        ∑ i ∈ Finset.range n,
          f (A + c * (i : ℕ)) := by
    simpa using hanti.integral_le_sum
  have hscaled :=
    mul_le_mul_of_nonneg_left hsum hc.le
  have hIntegral :
      c * (∫ x : ℝ in 0..(n : ℝ), f (A + c * x)) =
        ∫ x : ℝ in A..B, f x := by
    have hchange :=
      intervalIntegral.smul_integral_comp_add_mul
        (f := f) (a := (0 : ℝ)) (b := (n : ℝ)) c A
    simpa [smul_eq_mul, hcn] using hchange
  rw [hIntegral] at hscaled
  simpa [c] using hscaled

/--
The left-endpoint Riemann sum of an antitone function on `[0, T]` bounds its
integral from above.
-/
theorem intervalIntegral_le_leftRiemannSum
    {f : ℝ → ℝ} {T : ℝ} (n : ℕ)
    (hT : 0 ≤ T) (hn : 0 < n)
    (hf : AntitoneOn f (Icc 0 T)) :
    (∫ x : ℝ in 0..T, f x) ≤
      (T / n) *
        ∑ i ∈ Finset.range n,
          f ((T / n) * (i : ℕ)) := by
  simpa using
    intervalIntegral_le_leftRiemannSum_of_le
      (f := f) (A := 0) (B := T) n hT hn hf

/--
Soundness of a uniform-grid integral certificate.  Unlike
`intervalIntegral_le_rightRiemannSum_of_le`, the integrand need not be
monotone: the caller supplies one verified upper bound for each cell.
-/
theorem intervalIntegral_le_uniformCellSum
    {f : ℝ → ℝ} {A B : ℝ} {M : ℕ → ℝ} (n : ℕ)
    (hAB : A ≤ B) (hn : 0 < n)
    (hint : ∀ i < n,
      IntervalIntegrable f volume
        (A + ((B - A) / n) * i)
        (A + ((B - A) / n) * (i + 1)))
    (hcell : ∀ i < n, ∀ x ∈
      Icc
        (A + ((B - A) / n) * i)
        (A + ((B - A) / n) * (i + 1)),
      f x ≤ M i) :
    (∫ x : ℝ in A..B, f x) ≤
      ((B - A) / n) * ∑ i ∈ Finset.range n, M i := by
  let h : ℝ := (B - A) / n
  let grid : ℕ → ℝ := fun i => A + h * i
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hh : 0 ≤ h := by
    dsimp [h]
    positivity
  have hgridMono (i : ℕ) :
      grid i ≤ grid (i + 1) := by
    dsimp [grid]
    gcongr
    exact Nat.cast_le.mpr (Nat.le_succ i)
  have hpiece (i : ℕ) (hi : i < n) :
      (∫ x : ℝ in grid i..grid (i + 1), f x) ≤
        h * M i := by
    have hfi : IntervalIntegrable f volume (grid i) (grid (i + 1)) := by
      simpa [grid, h] using hint i hi
    have hconst :
        IntervalIntegrable (fun _ : ℝ => M i)
          volume (grid i) (grid (i + 1)) := by
      exact continuous_const.intervalIntegrable _ _
    calc
      (∫ x : ℝ in grid i..grid (i + 1), f x)
          ≤ ∫ _x : ℝ in grid i..grid (i + 1), M i := by
            apply intervalIntegral.integral_mono_on
              (hgridMono i) hfi hconst
            intro x hx
            exact hcell i hi x (by simpa [grid, h] using hx)
      _ = h * M i := by
            rw [intervalIntegral.integral_const]
            simp only [smul_eq_mul]
            dsimp [grid]
            push_cast
            ring
  have hsum :
      (∑ i ∈ Finset.range n,
          ∫ x : ℝ in grid i..grid (i + 1), f x) ≤
        ∑ i ∈ Finset.range n, h * M i := by
    apply Finset.sum_le_sum
    intro i hi
    exact hpiece i (Finset.mem_range.mp hi)
  have hsplit :
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
    · intro i hi
      simpa [grid, h] using hint i hi
  rw [hsplit, ← Finset.mul_sum] at hsum
  simpa [h] using hsum

end CertifiedJL
