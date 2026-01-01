/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib

/-!
# Kernel-checkable directed fixed-point convolution

This module implements compact, kernel-checkable fixed-point convolution.
A full coefficient vector is packed into one natural number, squared once,
and scanned in a large positional base while each coefficient is rounded down
by `scale`.  There is no generated certificate data or native evaluation hook.
-/

open scoped BigOperators

namespace CertifiedJL.FixedPointConvolution

noncomputable def polyOfList : List ℕ → Polynomial ℕ
  | [] => 0
  | x :: xs => Polynomial.C x + Polynomial.X * polyOfList xs

@[simp]
theorem coeff_polyOfList (xs : List ℕ) (n : ℕ) :
    (polyOfList xs).coeff n = xs.getD n 0 := by
  induction xs generalizing n with
  | nil => simp [polyOfList]
  | cons x xs ih =>
    cases n with
    | zero => simp [polyOfList]
    | succ n => simp [polyOfList, Polynomial.coeff_X_mul, ih]

theorem eval_polyOfList (xs : List ℕ) (b : ℕ) :
    (polyOfList xs).eval b = Nat.ofDigits b xs := by
  induction xs with
  | nil => simp [polyOfList, Nat.ofDigits]
  | cons x xs ih => simp [polyOfList, Nat.ofDigits, ih]

def convolutionCoeff (xs ys : List ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), xs.getD i 0 * ys.getD (n - i) 0

def convolutionList (length : ℕ) (xs ys : List ℕ) : List ℕ :=
  List.ofFn fun i : Fin length => convolutionCoeff xs ys i

theorem coeff_mul_polyOfList (xs ys : List ℕ) (n : ℕ) :
    (polyOfList xs * polyOfList ys).coeff n = convolutionCoeff xs ys n := by
  rw [Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_polyOfList, convolutionCoeff, Nat.succ_eq_add_one]

@[simp]
theorem length_convolutionList (length : ℕ) (xs ys : List ℕ) :
    (convolutionList length xs ys).length = length := by
  simp [convolutionList]

theorem getD_convolutionList_of_lt {length n : ℕ} (h : n < length)
    (xs ys : List ℕ) :
    (convolutionList length xs ys).getD n 0 = convolutionCoeff xs ys n := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp [convolutionList]

theorem convolutionCoeff_eq_zero_of_length_add_le
    (xs ys : List ℕ) {n : ℕ} (h : xs.length + ys.length ≤ n) :
    convolutionCoeff xs ys n = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_range] at hi
  by_cases hix : i < xs.length
  · have hiy : ys.length ≤ n - i := by omega
    have hz : ys.getD (n - i) 0 = 0 :=
      List.getD_eq_default _ _ hiy
    rw [hz, mul_zero]
  · have hz : xs.getD i 0 = 0 :=
      List.getD_eq_default _ _ (Nat.le_of_not_gt hix)
    rw [hz, zero_mul]

theorem polyOfList_fullConvolution (xs ys : List ℕ) :
    polyOfList (convolutionList (xs.length + ys.length) xs ys) =
      polyOfList xs * polyOfList ys := by
  ext n
  rw [coeff_mul_polyOfList]
  by_cases hn : n < xs.length + ys.length
  · rw [coeff_polyOfList, getD_convolutionList_of_lt hn]
  · rw [coeff_polyOfList, List.getD_eq_default]
    · exact (convolutionCoeff_eq_zero_of_length_add_le xs ys
        (Nat.le_of_not_gt hn)).symm
    · simpa using Nat.le_of_not_gt hn

theorem ofDigits_fullConvolution (b : ℕ) (xs ys : List ℕ) :
    Nat.ofDigits b (convolutionList (xs.length + ys.length) xs ys) =
      Nat.ofDigits b xs * Nat.ofDigits b ys := by
  rw [← eval_polyOfList, polyOfList_fullConvolution, Polynomial.eval_mul,
    eval_polyOfList, eval_polyOfList]

theorem take_fullConvolution (length : ℕ) (xs ys : List ℕ) :
    (convolutionList (length + length) xs ys).take length =
      convolutionList length xs ys := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp [convolutionList]

theorem getD_le_of_forall_mem {xs : List ℕ} {bound : ℕ}
    (h : ∀ x ∈ xs, x ≤ bound) (i : ℕ) :
    xs.getD i 0 ≤ bound := by
  by_cases hi : i < xs.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h xs[i] (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]
    exact Nat.zero_le _

theorem convolutionCoeff_le
    {length scale : ℕ} {xs ys : List ℕ}
    (hx : ∀ x ∈ xs, x ≤ scale) (hy : ∀ y ∈ ys, y ≤ scale)
    {n : ℕ} (hn : n < length + length) :
    convolutionCoeff xs ys n ≤ (length + length) * (scale * scale) := by
  calc
    convolutionCoeff xs ys n =
        ∑ i ∈ Finset.range (n + 1),
          xs.getD i 0 * ys.getD (n - i) 0 := rfl
    _ ≤ ∑ _i ∈ Finset.range (n + 1), scale * scale := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul
        (getD_le_of_forall_mem hx i)
        (getD_le_of_forall_mem hy (n - i))
    _ = (n + 1) * (scale * scale) := by simp
    _ ≤ (length + length) * (scale * scale) := by
      exact Nat.mul_le_mul_right _ (by omega)

theorem fullConvolution_digits_lt
    {length base scale : ℕ} {xs ys : List ℕ}
    (hx : ∀ x ∈ xs, x ≤ scale) (hy : ∀ y ∈ ys, y ≤ scale)
    (hbound : (length + length) * (scale * scale) < base) :
    ∀ x ∈ convolutionList (length + length) xs ys, x < base := by
  intro x hxmem
  rw [List.mem_iff_getElem] at hxmem
  obtain ⟨n, hn, rfl⟩ := hxmem
  have hn' : n < length + length := by simpa using hn
  simpa [convolutionList] using
    (convolutionCoeff_le hx hy hn').trans_lt hbound

/-- Read `length` base-`base` slots from `value`, divide each slot by
`scale`, and pack the rounded slots back into one natural number. -/
def scaledPackedDigits (length base scale value : ℕ) : ℕ :=
  match length with
  | 0 => 0
  | length + 1 =>
      value % base / scale +
        base * scaledPackedDigits length base scale (value / base)

@[simp]
theorem scaledPackedDigits_zero (base scale value : ℕ) :
    scaledPackedDigits 0 base scale value = 0 := rfl

@[simp]
theorem scaledPackedDigits_succ (length base scale value : ℕ) :
    scaledPackedDigits (length + 1) base scale value =
      value % base / scale +
        base * scaledPackedDigits length base scale (value / base) := rfl

theorem scaledPackedDigits_ofDigits
    {base scale : ℕ} (hbase : 0 < base) (xs : List ℕ)
    (hxs : ∀ x ∈ xs, x < base) :
    scaledPackedDigits xs.length base scale (Nat.ofDigits base xs) =
      Nat.ofDigits base (xs.map (· / scale)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.length_cons, scaledPackedDigits_succ, Nat.ofDigits_cons,
        List.map_cons]
      have hx : x < base := hxs x (by simp)
      have htail : ∀ y ∈ xs, y < base := by
        intro y hy
        exact hxs y (by simp [hy])
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx,
        Nat.add_mul_div_left _ _ hbase, Nat.div_eq_of_lt hx, zero_add,
        ih htail]

theorem scaledPackedDigits_ofDigits_take
    {length base scale : ℕ} (hbase : 0 < base) (xs : List ℕ)
    (hlen : length ≤ xs.length) (hxs : ∀ x ∈ xs, x < base) :
    scaledPackedDigits length base scale (Nat.ofDigits base xs) =
      Nat.ofDigits base ((xs.take length).map (· / scale)) := by
  induction length generalizing xs with
  | zero => simp
  | succ length ih =>
      cases xs with
      | nil => simp at hlen
      | cons x xs =>
          simp only [List.length_cons, Nat.succ_le_succ_iff] at hlen
          simp only [scaledPackedDigits_succ, Nat.ofDigits_cons, List.take_succ_cons,
            List.map_cons]
          have hx : x < base := hxs x (by simp)
          have htail : ∀ y ∈ xs, y < base := by
            intro y hy
            exact hxs y (by simp [hy])
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx,
            Nat.add_mul_div_left _ _ hbase, Nat.div_eq_of_lt hx, zero_add,
            ih xs hlen htail]

/-- Truncated convolution followed by coefficientwise downward rounding. -/
def roundedConvolution (length scale : ℕ) (input : List ℕ) : List ℕ :=
  (convolutionList length input input).map (· / scale)

@[simp]
theorem length_roundedConvolution (length scale : ℕ) (input : List ℕ) :
    (roundedConvolution length scale input).length = length := by
  simp [roundedConvolution]

theorem getD_roundedConvolution_of_lt {length scale n : ℕ}
    (hn : n < length) (input : List ℕ) :
    (roundedConvolution length scale input).getD n 0 =
      convolutionCoeff input input n / scale := by
  rw [List.getD_eq_getElem _ _ (by simpa using hn)]
  simp [roundedConvolution, convolutionList]

theorem sum_take_le (length : ℕ) (xs : List ℕ) :
    (xs.take length).sum ≤ xs.sum := by
  induction length generalizing xs with
  | zero => simp
  | succ length ih =>
      cases xs with
      | nil => simp
      | cons x xs =>
          simp only [List.take_succ_cons, List.sum_cons]
          exact Nat.add_le_add_left (ih xs) x

theorem sum_fullConvolution (xs ys : List ℕ) :
    (convolutionList (xs.length + ys.length) xs ys).sum = xs.sum * ys.sum := by
  rw [← Nat.ofDigits_one, ofDigits_fullConvolution, Nat.ofDigits_one,
    Nat.ofDigits_one]

theorem sum_convolutionList_le (length : ℕ) (xs ys : List ℕ)
    (hlenx : xs.length = length) (hleny : ys.length = length) :
    (convolutionList length xs ys).sum ≤ xs.sum * ys.sum := by
  rw [← sum_fullConvolution]
  rw [← take_fullConvolution length xs ys, hlenx, hleny]
  exact sum_take_le _ _

theorem roundedConvolution_sum_mul_scale_le
    (length scale : ℕ) (input : List ℕ) :
    (roundedConvolution length scale input).sum * scale ≤
      (convolutionList length input input).sum := by
  rw [roundedConvolution, ← List.sum_map_mul_right]
  have h := List.sum_le_sum (l := convolutionList length input input)
    (fun x _hx => Nat.div_mul_le_self x scale)
  rw [List.map_id'] at h
  exact h

theorem roundedConvolution_sum_le
    {length scale : ℕ} (hscale : 0 < scale) (input : List ℕ)
    (hlen : input.length = length) (hsum : input.sum ≤ scale) :
    (roundedConvolution length scale input).sum ≤ scale := by
  apply Nat.le_of_mul_le_mul_right (c := scale) _ hscale
  calc
    (roundedConvolution length scale input).sum * scale ≤
        (convolutionList length input input).sum :=
      roundedConvolution_sum_mul_scale_le length scale input
    _ ≤ input.sum * input.sum := sum_convolutionList_le length input input hlen hlen
    _ ≤ scale * scale := Nat.mul_le_mul hsum hsum

/-- One compact packed convolution-and-rounding step. -/
def packedSquareStep (length base scale state : ℕ) : ℕ :=
  scaledPackedDigits length base scale (state * state)

def packedSquareIterate (length base scale : ℕ) : ℕ → ℕ → ℕ
  | 0, state => state
  | stages + 1, state =>
      packedSquareStep length base scale
        (packedSquareIterate length base scale stages state)

/-- Sum the first `length` base-`base` slots of a packed value. -/
def packedDigitSum : ℕ → ℕ → ℕ → ℕ
  | 0, _base, _value => 0
  | length + 1, base, value =>
      value % base + packedDigitSum length base (value / base)

theorem packedDigitSum_ofDigits
    {base : ℕ} (hbase : 0 < base) (xs : List ℕ)
    (hxs : ∀ x ∈ xs, x < base) :
    packedDigitSum xs.length base (Nat.ofDigits base xs) = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.length_cons, packedDigitSum, Nat.ofDigits_cons, List.sum_cons]
      have hx : x < base := hxs x (by simp)
      have htail : ∀ y ∈ xs, y < base := by
        intro y hy
        exact hxs y (by simp [hy])
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx,
        Nat.add_mul_div_left _ _ hbase, Nat.div_eq_of_lt hx, zero_add,
        ih htail]

theorem packedSquareStep_ofDigits
    {length base scale : ℕ} (hbase : 0 < base) (input : List ℕ)
    (hlen : input.length = length)
    (hcoeff : ∀ x ∈ convolutionList (length + length) input input, x < base) :
    packedSquareStep length base scale (Nat.ofDigits base input) =
      Nat.ofDigits base (roundedConvolution length scale input) := by
  rw [packedSquareStep, ← ofDigits_fullConvolution]
  rw [hlen]
  rw [scaledPackedDigits_ofDigits_take hbase _ (by simp) hcoeff]
  congr 1
  simp [roundedConvolution, take_fullConvolution]

end CertifiedJL.FixedPointConvolution
