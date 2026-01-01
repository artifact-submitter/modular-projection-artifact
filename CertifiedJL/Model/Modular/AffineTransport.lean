/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Vectors.SquaredNorm
import CertifiedJL.Statements.Shared.Input
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum

/-!
# Deterministic transports for affine modular projections

This file contains the arithmetic used to transport lower tails between
scaled odd moduli and to absorb a fixed affine shift into upper bounds.  The
upper bounds deliberately make no oddness or centered-input assumptions.
-/

open scoped BigOperators

namespace CertifiedJL

/-- Scaling an integer in the centered interval by an odd natural factor
puts it in the centered interval for the scaled odd modulus. -/
private theorem mul_mem_centeredInterval_mul {k q : ℕ}
    (hk : Odd k) (hq : Odd q) {z : ℤ} (hz : z ∈ centeredInterval q) :
    (k : ℤ) * z ∈ centeredInterval (k * q) := by
  obtain ⟨a, rfl⟩ := hk
  obtain ⟨b, rfl⟩ := hq
  simp only [centeredInterval, Set.mem_Icc] at hz ⊢
  rw [show (2 * b + 1) / 2 = b by omega] at hz
  rw [show (2 * a + 1) * (2 * b + 1) =
    2 * (2 * a * b + a + b) + 1 by ring]
  rw [show (2 * (2 * a * b + a + b) + 1) / 2 =
    2 * a * b + a + b by omega]
  constructor
  · have hmul := mul_le_mul_of_nonneg_left hz.1
      (show (0 : ℤ) ≤ 2 * a + 1 by positivity)
    calc
      -(↑(2 * a * b + a + b) : ℤ) ≤
          (↑(2 * a + 1) : ℤ) * (-b) := by push_cast; ring_nf; omega
      _ ≤ (↑(2 * a + 1) : ℤ) * z := hmul
  · have hmul := mul_le_mul_of_nonneg_left hz.2
      (show (0 : ℤ) ≤ 2 * a + 1 by positivity)
    calc
      (↑(2 * a + 1) : ℤ) * z ≤
          (↑(2 * a + 1) : ℤ) * b := hmul
      _ ≤ (↑(2 * a * b + a + b) : ℤ) := by push_cast; ring_nf; omega

/-- Centered reduction commutes with multiplication of both the modulus and
the input by an odd natural factor. -/
theorem centeredMod_odd_mul (k q : ℕ) (hk : Odd k) (hq : Odd q) (z : ℤ) :
    centeredMod (k * q) ((k : ℤ) * z) =
      (k : ℤ) * centeredMod q z := by
  apply (centeredMod_eq_iff (hk.mul hq) _ _).2
  constructor
  · rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    have hc := centeredMod_intCast q z
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hc
    obtain ⟨a, ha⟩ := hc
    refine ⟨a, ?_⟩
    push_cast
    nlinarith
  · exact mul_mem_centeredInterval_mul hk hq
      (centeredMod_mem_centeredInterval hq z)

/-- The factor-three identity used by the margin-three to margin-two
transport. -/
theorem centeredMod_three_mul (q : ℕ) (hq : Odd q) (z : ℤ) :
    centeredMod (3 * q) (3 * z) = 3 * centeredMod q z := by
  simpa using centeredMod_odd_mul 3 q (by exact ⟨1, rfl⟩) hq z

/-- Natural absolute values scale exactly by a natural factor. -/
@[simp]
theorem natAbs_natCast_mul (k : ℕ) (z : ℤ) :
    ((k : ℤ) * z).natAbs = k * z.natAbs := by
  rw [Int.natAbs_mul]
  simp

/-- Squared integer norm scales by the square of a natural factor. -/
theorem sqNorm_natCast_mul {d : ℕ} (k : ℕ) (w : Fin d → ℤ) :
    sqNorm (fun i => (k : ℤ) * w i) = k ^ 2 * sqNorm w := by
  simp only [sqNorm, natAbs_natCast_mul, mul_pow, Finset.mul_sum]

/-- Row dot products commute with scaling the input vector. -/
theorem rowDot_natCast_mul {m d : ℕ} (k : ℕ)
    (J : Matrix (Fin m) (Fin d) ℤ) (w : Fin d → ℤ) (j : Fin m) :
    rowDot J (fun i => (k : ℤ) * w i) j = (k : ℤ) * rowDot J w j := by
  unfold rowDot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The shifted modular projected squared norm scales exactly when the modulus, shift, and input
are scaled by a common odd factor. -/
theorem shiftedModularProjectionSqNorm_odd_mul {m d : ℕ} (k q : ℕ)
    (hk : Odd k) (hq : Odd q) (shift : Fin m → ℤ)
    (J : Matrix (Fin m) (Fin d) ℤ) (w : Fin d → ℤ) :
    shiftedModularProjectionSqNorm (k * q) (fun j => (k : ℤ) * shift j) J
        (fun i => (k : ℤ) * w i) =
      k ^ 2 * shiftedModularProjectionSqNorm q shift J w := by
  simp only [shiftedModularProjectionSqNorm, rowDot_natCast_mul, ← mul_add,
    centeredMod_odd_mul k q hk hq, natAbs_natCast_mul, mul_pow,
    Finset.mul_sum]

/-- Multiplication by a positive odd factor preserves centered inputs at the
scaled modulus. -/
theorem CenteredInput.odd_mul {q d : ℕ} {w : Fin d → ℤ}
    (h : CenteredInput q w) (k : ℕ) (hk : Odd k) (hq : Odd q) :
    CenteredInput (k * q) (fun i => (k : ℤ) * w i) := by
  intro i
  exact mul_mem_centeredInterval_mul hk hq (h i)

/-- Centered modular reduction is subadditive in natural absolute value for
every modulus. -/
theorem centeredMod_natAbs_add_le (q : ℕ) (x y : ℤ) :
    (centeredMod q (x + y)).natAbs ≤
      (centeredMod q x).natAbs + (centeredMod q y).natAbs := by
  by_cases hq : q = 0
  · subst q
    change (x + y).natAbs ≤ x.natAbs + y.natAbs
    exact Int.natAbs_add_le x y
  · let _ : NeZero q := ⟨hq⟩
    have hleast := (centeredMod_natAbs_le_of_intCast_eq
      (q := q) (z := x + y)
      (y := centeredMod q x + centeredMod q y)) (by simp)
    exact hleast.trans (Int.natAbs_add_le _ _)

/-- The coordinatewise modular triangle inequality for an affine row. -/
theorem affineCenteredMod_natAbs_le (q : ℕ) (shift dot : ℤ) :
    (centeredMod q (shift + dot)).natAbs ≤
      (centeredMod q shift).natAbs + (centeredMod q dot).natAbs :=
  centeredMod_natAbs_add_le q shift dot

/-- Minkowski's inequality in exact natural squared-norm form. -/
theorem sum_sq_le_add_sq_of_pointwise_le {ι : Type*} [Fintype ι]
    (z x y : ι → ℕ) (hpoint : ∀ i, z i ≤ x i + y i)
    (A B : ℕ) (hx : ∑ i, x i ^ 2 ≤ A ^ 2)
    (hy : ∑ i, y i ^ 2 ≤ B ^ 2) :
    ∑ i, z i ^ 2 ≤ (A + B) ^ 2 := by
  have hpoint' : ∀ i, (z i : ℝ) ≤ x i + y i := fun i => by exact_mod_cast hpoint i
  have hx' : (∑ i, (x i : ℝ) ^ 2) ≤ (A : ℝ) ^ 2 := by exact_mod_cast hx
  have hy' : (∑ i, (y i : ℝ) ^ 2) ≤ (B : ℝ) ^ 2 := by exact_mod_cast hy
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ι)
    (fun i => (x i : ℝ)) (fun i => (y i : ℝ))
  have hsx0 : 0 ≤ ∑ i, (x i : ℝ) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsy0 : 0 ≤ ∑ i, (y i : ℝ) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsqrtx : Real.sqrt (∑ i, (x i : ℝ) ^ 2) ≤ A := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, hx'⟩
  have hsqrty : Real.sqrt (∑ i, (y i : ℝ) ^ 2) ≤ B := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, hy'⟩
  have hxy : (∑ i, (x i : ℝ) * y i) ≤ (A : ℝ) * B :=
    hcs.trans <| mul_le_mul hsqrtx hsqrty (Real.sqrt_nonneg _) (by positivity)
  have hz' : (∑ i, (z i : ℝ) ^ 2) ≤ ((A + B : ℕ) : ℝ) ^ 2 := by
    calc
      (∑ i, (z i : ℝ) ^ 2) ≤ ∑ i, ((x i : ℝ) + y i) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith [hpoint' i, Nat.cast_nonneg (α := ℝ) (z i),
          Nat.cast_nonneg (α := ℝ) (x i), Nat.cast_nonneg (α := ℝ) (y i)]
      _ = (∑ i, (x i : ℝ) ^ 2) + (∑ i, (y i : ℝ) ^ 2) +
          2 * ∑ i, (x i : ℝ) * y i := by
        simp_rw [add_sq]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.mul_sum]
        ring
      _ ≤ (A : ℝ) ^ 2 + (B : ℝ) ^ 2 + 2 * ((A : ℝ) * B) := by
        gcongr
      _ = ((A + B : ℕ) : ℝ) ^ 2 := by push_cast; ring
  exact_mod_cast hz'

/-- Exact natural squared-norm triangle bound for an affine modular
projection.  This theorem has no parity or modulus-margin assumptions. -/
theorem shiftedModularProjectionSqNorm_le_add_sq {q rows d : ℕ}
    (shift : Fin rows → ℤ) (J : Matrix (Fin rows) (Fin d) ℤ)
    (w : Fin d → ℤ) (projectedBound shiftBound : ℕ)
    (hprojected : modularProjectionSqNorm q J w ≤ projectedBound ^ 2)
    (hshift : ∑ j, (centeredMod q (shift j)).natAbs ^ 2 ≤ shiftBound ^ 2) :
    shiftedModularProjectionSqNorm q shift J w ≤ (projectedBound + shiftBound) ^ 2 := by
  exact sum_sq_le_add_sq_of_pointwise_le
    (fun j => (centeredMod q (shift j + rowDot J w j)).natAbs)
    (fun j => (centeredMod q (rowDot J w j)).natAbs)
    (fun j => (centeredMod q (shift j)).natAbs)
    (fun j => by simpa [add_comm] using
      centeredMod_natAbs_add_le q (shift j) (rowDot J w j))
    projectedBound shiftBound hprojected hshift

/-- Real Euclidean modular triangle inequality.  It is stated directly in
terms of the exact natural energies, so later probability wrappers introduce
no integer-radius rounding. -/
theorem sqrt_shiftedModularProjectionSqNorm_le {q rows d : ℕ}
    (shift : Fin rows → ℤ) (J : Matrix (Fin rows) (Fin d) ℤ)
    (w : Fin d → ℤ) :
    Real.sqrt (shiftedModularProjectionSqNorm q shift J w) ≤
      Real.sqrt (modularProjectionSqNorm q J w) +
        Real.sqrt (∑ j, (centeredMod q (shift j)).natAbs ^ 2) := by
  let x : Fin rows → ℝ := fun j =>
    (centeredMod q (rowDot J w j)).natAbs
  let y : Fin rows → ℝ := fun j =>
    (centeredMod q (shift j)).natAbs
  let z : Fin rows → ℝ := fun j =>
    (centeredMod q (shift j + rowDot J w j)).natAbs
  have hpoint : ∀ j, z j ≤ x j + y j := by
    intro j
    dsimp [z, x, y]
    have hnat := centeredMod_natAbs_add_le q (shift j) (rowDot J w j)
    norm_cast
    simpa [add_comm] using hnat
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin rows)) x y
  have hsum : (∑ j, z j ^ 2) ≤
      (Real.sqrt (∑ j, x j ^ 2) + Real.sqrt (∑ j, y j ^ 2)) ^ 2 := by
    calc
      (∑ j, z j ^ 2) ≤ ∑ j, (x j + y j) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        have hx0 : 0 ≤ x j := by simp [x]
        have hy0 : 0 ≤ y j := by simp [y]
        have hz0 : 0 ≤ z j := by simp [z]
        nlinarith [hpoint j]
      _ = (∑ j, x j ^ 2) + (∑ j, y j ^ 2) + 2 * ∑ j, x j * y j := by
        simp_rw [add_sq]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
        ring
      _ ≤ (∑ j, x j ^ 2) + (∑ j, y j ^ 2) +
          2 * (Real.sqrt (∑ j, x j ^ 2) * Real.sqrt (∑ j, y j ^ 2)) := by
        gcongr
      _ = (Real.sqrt (∑ j, x j ^ 2) +
          Real.sqrt (∑ j, y j ^ 2)) ^ 2 := by
        have hxroot : Real.sqrt (∑ j, x j ^ 2) ^ 2 = ∑ j, x j ^ 2 :=
          Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        have hyroot : Real.sqrt (∑ j, y j ^ 2) ^ 2 = ∑ j, y j ^ 2 :=
          Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        nlinarith
  have hroot := Real.sqrt_le_sqrt hsum
  rw [Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] at hroot
  simpa [z, x, y, shiftedModularProjectionSqNorm, modularProjectionSqNorm] using hroot

/-- The largest centered coordinate of a fixed shift. -/
def centeredShiftLInf {rows : ℕ} (q : ℕ) (shift : Fin rows → ℤ) : ℕ :=
  Finset.univ.sup fun j => (centeredMod q (shift j)).natAbs

/-- Every centered shift coordinate is bounded by `centeredShiftLInf`. -/
theorem centeredMod_shift_le_centeredShiftLInf {rows q : ℕ}
    (shift : Fin rows → ℤ) (j : Fin rows) :
    (centeredMod q (shift j)).natAbs ≤ centeredShiftLInf q shift := by
  exact Finset.le_sup (s := Finset.univ) (f := fun i =>
    (centeredMod q (shift i)).natAbs) (Finset.mem_univ j)

/-- Exact coordinatewise infinity-norm triangle bound for an affine modular
projection. -/
theorem affineModularCoordinate_le_add {q rows d : ℕ}
    (shift : Fin rows → ℤ) (J : Matrix (Fin rows) (Fin d) ℤ)
    (w : Fin d → ℤ) (projectedBound shiftBound : ℕ)
    (hprojected : ∀ j,
      (centeredMod q (rowDot J w j)).natAbs ≤ projectedBound)
    (hshift : ∀ j, (centeredMod q (shift j)).natAbs ≤ shiftBound) :
    ∀ j, (centeredMod q (shift j + rowDot J w j)).natAbs ≤
      projectedBound + shiftBound := by
  intro j
  exact (centeredMod_natAbs_add_le q _ _).trans
    (by simpa [add_comm] using Nat.add_le_add (hshift j) (hprojected j))

end CertifiedJL
