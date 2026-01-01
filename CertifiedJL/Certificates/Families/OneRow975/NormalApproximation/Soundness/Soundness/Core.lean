/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Numeric.Core
import CertifiedJL.Probability.NormalApproximation.Tyurin.CellEnvelope
import CertifiedJL.Probability.NormalApproximation.Tyurin.DStarCertificate

/-!
# Core analytic soundness of the moderate-Lyapunov certificate

This file connects the executable dyadic evaluator to the real Prawitz
functional.  The only reflected inputs are Boolean geometry, exponential
side-condition, and strict endpoint checks.
-/

open MeasureTheory Set
open scoped BigOperators

namespace CertifiedJL
namespace TyurinModerate

theorem contains_rat (q : ℚ) :
    (rat q).Contains (q : ℝ) :=
  Interval.contains_ofRat precision q

theorem lowerRat_le_of_contains
    {I : DInterval} {x : ℝ} (h : I.Contains x) :
    (I.lowerRat : ℝ) ≤ x := by
  simpa only [Interval.lowerRat, Dyadic.cast_toRat] using h.1

theorem le_upperRat_of_contains
    {I : DInterval} {x : ℝ} (h : I.Contains x) :
    x ≤ (I.upperRat : ℝ) := by
  simpa only [Interval.upperRat, Dyadic.cast_toRat] using h.2

theorem le_upperRat
    {I : DInterval} {x : ℝ} (h : I.Contains x) :
    x ≤ (I.upperRat : ℝ) :=
  le_upperRat_of_contains h

theorem contains_div
    {I J : DInterval} {x y : ℝ}
    (hJ : 0 < J.lo) (hx : I.Contains x) (hy : J.Contains y) :
    (div I J).Contains (x / y) := by
  unfold div
  simpa [div_eq_mul_inv] using
    Interval.contains_mul hx
      (Interval.contains_reciprocal_of_pos hJ hy)

theorem contains_hull_left
    {I J : DInterval} {x : ℝ} (hx : I.Contains x) :
    (hull I J).Contains x := by
  unfold hull Interval.Contains at *
  exact ⟨(Dyadic.toReal_mono (min_le_left _ _)).trans hx.1,
    hx.2.trans (Dyadic.toReal_mono (le_max_left _ _))⟩

theorem contains_hull_right
    {I J : DInterval} {x : ℝ} (hx : J.Contains x) :
    (hull I J).Contains x := by
  unfold hull Interval.Contains at *
  exact ⟨(Dyadic.toReal_mono (min_le_right _ _)).trans hx.1,
    hx.2.trans (Dyadic.toReal_mono (le_max_right _ _))⟩

private theorem toReal_min (p : ℕ) (a b : ℤ) :
    Dyadic.toReal p (min a b) =
      min (Dyadic.toReal p a) (Dyadic.toReal p b) := by
  unfold Dyadic.toReal
  rw [Int.cast_min, min_div_div_right]
  positivity

private theorem toRat_min (p : ℕ) (a b : ℤ) :
    Dyadic.toRat p (min a b) =
      min (Dyadic.toRat p a) (Dyadic.toRat p b) := by
  unfold Dyadic.toRat
  rw [Int.cast_min, min_div_div_right]
  positivity

theorem contains_minInterval
    {I J : DInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (minInterval I J).Contains (min x y) := by
  unfold minInterval Interval.Contains at *
  constructor
  · rw [toReal_min]
    exact min_le_min hx.1 hy.1
  · rw [toReal_min]
    exact min_le_min hx.2 hy.2

theorem contains_powNat
    {I : DInterval} {x : ℝ} (hx : I.Contains x) :
    ∀ n, (powNat I n).Contains (x ^ n)
  | 0 => by simpa [powNat] using contains_rat 1
  | n + 1 => by
      simpa [powNat, pow_succ] using
        Interval.contains_mul (contains_powNat hx n) hx

/--
An exponential safe check turns any enclosed exponent into an enclosure of
its exponential, using monotonicity before the certified endpoint call.
-/
theorem contains_expUpper
    {I : DInterval} {x : ℝ}
    (hx : I.Contains x) (h : expSafe I = true) :
    (expUpper I).Contains (Real.exp x) := by
  apply DyadicExp.ofIntervalUpper_contains_of_upperRat_le_one
  · norm_num [precision, Dyadic.scale]
  · norm_num [squarings]
  · exact hx
  · exact of_decide_eq_true (by simpa only [expSafe] using h)

private theorem contains_foldl_add
    {α : Type*} (xs : List α)
    (F : α → DInterval) (f : α → ℝ)
    (hF : ∀ i ∈ xs, (F i).Contains (f i))
    {I : DInterval} {x : ℝ} (hI : I.Contains x) :
    (xs.foldl (fun acc i => acc + F i) I).Contains
      (xs.foldl (fun acc i => acc + f i) x) := by
  induction xs generalizing I x with
  | nil => exact hI
  | cons i xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · intro j hj
        exact hF j (List.mem_cons_of_mem i hj)
      · exact Interval.contains_add hI (hF i (by simp))

private noncomputable def realWeightedSqExpSqTrapOn
    (indices : List ℕ) (n : ℚ) (c T : ℝ) : ℝ :=
  let nReal : ℝ := n
  let h := T / nReal
  let term := fun s : ℝ =>
    s ^ 2 / 2 * Real.exp ((c * s ^ 2 - T ^ 2) / 2)
  h * ((term 0 + term T) / 2 +
    indices.foldl
      (fun acc i => acc + term (h * ((i + 1 : ℕ) : ℝ))) 0)

private noncomputable def realWeightedSqExpSqTrap
    (c T : ℝ) : ℝ :=
  realWeightedSqExpSqTrapOn
    (List.range (innerTrapezoids - 1)) innerTrapezoids c T

private noncomputable def realWeightedSqExpCubeTrapOn
    (indices : List ℕ) (n : ℚ) (c A T : ℝ) : ℝ :=
  let nReal : ℝ := n
  let h := (T - A) / nReal
  let term := fun s : ℝ =>
    s ^ 2 / 2 * Real.exp (c * s ^ 3 / 5 - T ^ 2 / 2)
  h * ((term A + term T) / 2 +
    indices.foldl
      (fun acc i => acc + term (A + h * ((i + 1 : ℕ) : ℝ))) 0)

private noncomputable def realWeightedSqExpCubeTrap
    (c A T : ℝ) : ℝ :=
  realWeightedSqExpCubeTrapOn
    (List.range (innerTrapezoids - 1)) innerTrapezoids c A T

private theorem rat_innerTrapezoids_lo_pos :
    0 < (rat (innerTrapezoids : ℚ)).lo := by
  norm_num [rat, innerTrapezoids, Interval.ofRat,
    Interval.enclose, Dyadic.roundDown, Dyadic.scale,
    precision]

private theorem contains_weightedSqTerm
    {cI sI TI : DInterval} {c s T : ℝ}
    (hc : cI.Contains c) (hs : sI.Contains s)
    (hT : TI.Contains T)
    (hsafe :
      expSafe ((cI * sI.square - TI.square) * rat (1 / 2)) = true) :
    (sI.square * rat (1 / 2) *
        expUpper
          ((cI * sI.square - TI.square) * rat (1 / 2))).Contains
      (s ^ 2 / 2 * Real.exp ((c * s ^ 2 - T ^ 2) / 2)) := by
  have hsSq := Interval.contains_square hs
  have hTSq := Interval.contains_square hT
  have hexponent :
      ((cI * sI.square - TI.square) * rat (1 / 2)).Contains
        ((c * s ^ 2 - T ^ 2) / 2) := by
    have hmul := Interval.contains_mul hc hsSq
    have hsub := Interval.contains_sub hmul hTSq
    simpa [div_eq_mul_inv] using
      Interval.contains_mul hsub (contains_rat (1 / 2))
  have hfront :
      (sI.square * rat (1 / 2)).Contains (s ^ 2 / 2) := by
    simpa [div_eq_mul_inv] using
      Interval.contains_mul hsSq (contains_rat (1 / 2))
  exact Interval.contains_mul hfront
    (contains_expUpper hexponent hsafe)

private theorem contains_weightedCubeTerm
    {cI sI TI : DInterval} {c s T : ℝ}
    (hc : cI.Contains c) (hs : sI.Contains s)
    (hT : TI.Contains T)
    (hsafe :
      expSafe
        (cI * powNat sI 3 * rat (1 / 5) -
          TI.square * rat (1 / 2)) = true) :
    (sI.square * rat (1 / 2) *
        expUpper
          (cI * powNat sI 3 * rat (1 / 5) -
            TI.square * rat (1 / 2))).Contains
      (s ^ 2 / 2 * Real.exp (c * s ^ 3 / 5 - T ^ 2 / 2)) := by
  have hsSq := Interval.contains_square hs
  have hTSq := Interval.contains_square hT
  have hsCube := contains_powNat hs 3
  have hcubic :
      (cI * powNat sI 3 * rat (1 / 5)).Contains
        (c * s ^ 3 / 5) := by
    simpa [div_eq_mul_inv, mul_assoc] using
      Interval.contains_mul
        (Interval.contains_mul hc hsCube) (contains_rat (1 / 5))
  have hgaussian :
      (TI.square * rat (1 / 2)).Contains (T ^ 2 / 2) := by
    simpa [div_eq_mul_inv] using
      Interval.contains_mul hTSq (contains_rat (1 / 2))
  have hexponent :=
    Interval.contains_sub hcubic hgaussian
  have hfront :
      (sI.square * rat (1 / 2)).Contains (s ^ 2 / 2) := by
    simpa [div_eq_mul_inv] using
      Interval.contains_mul hsSq (contains_rat (1 / 2))
  exact Interval.contains_mul hfront
    (contains_expUpper hexponent hsafe)

private theorem contains_weightedSqExpSqTrapOn
    (indices : List ℕ) (n : ℚ)
    {cI TI : DInterval} {c T : ℝ}
    (hn : 0 < (rat n).lo)
    (hc : cI.Contains c) (hT : TI.Contains T)
    (hsafe : weightedSqExpSqTrapSafeOn indices n cI TI = true) :
    (weightedSqExpSqTrapOn indices n cI TI).Contains
      (realWeightedSqExpSqTrapOn indices n c T) := by
  let nI := rat n
  let hI := div TI nI
  let h : ℝ := T / (n : ℝ)
  let termI := fun sI : DInterval =>
    sI.square * rat (1 / 2) *
      expUpper ((cI * sI.square - TI.square) * rat (1 / 2))
  let term := fun s : ℝ =>
    s ^ 2 / 2 * Real.exp ((c * s ^ 2 - T ^ 2) / 2)
  have hnContains : nI.Contains (n : ℝ) := by
    simpa [nI] using contains_rat n
  have hh : hI.Contains h := by
    exact contains_div (by simpa [nI] using hn) hT hnContains
  unfold weightedSqExpSqTrapSafeOn at hsafe
  dsimp only at hsafe
  rw [Bool.and_eq_true, Bool.and_eq_true,
    List.all_eq_true] at hsafe
  have hterm (sI : DInterval) (s : ℝ)
      (hs : sI.Contains s)
      (hsafeTerm :
        expSafe ((cI * sI.square - TI.square) * rat (1 / 2)) = true) :
      (termI sI).Contains (term s) := by
    exact contains_weightedSqTerm hc hs hT hsafeTerm
  have hzero : (termI (rat 0)).Contains (term 0) :=
    hterm _ _ (by simpa using contains_rat (0 : ℚ)) hsafe.1.1
  have hend : (termI TI).Contains (term T) :=
    hterm _ _ hT hsafe.1.2
  have hstep (i : ℕ) :
      (hI * rat (((i + 1 : ℕ) : ℚ))).Contains
        (h * ((i + 1 : ℕ) : ℝ)) := by
    exact Interval.contains_mul hh
      (by simpa using contains_rat (((i + 1 : ℕ) : ℚ)))
  have hinterior :
      (indices.foldl
          (fun acc i =>
            acc + termI (hI * rat (((i + 1 : ℕ) : ℚ))))
          (rat 0)).Contains
        (indices.foldl
          (fun acc i =>
            acc + term (h * ((i + 1 : ℕ) : ℝ))) 0) := by
    apply contains_foldl_add
    · intro i hi
      exact contains_weightedSqTerm hc (hstep i) hT
        (by simpa [Nat.cast_add, Nat.cast_one] using hsafe.2 i hi)
    · simpa using contains_rat (0 : ℚ)
  have hendpoint :
      ((termI (rat 0) + termI TI) * rat (1 / 2)).Contains
        ((term 0 + term T) / 2) := by
    simpa [div_eq_mul_inv] using
      Interval.contains_mul (Interval.contains_add hzero hend)
        (contains_rat (1 / 2))
  have hsum :=
    Interval.contains_add hendpoint hinterior
  have htotal :=
    Interval.contains_mul hh hsum
  simpa only [weightedSqExpSqTrapOn, realWeightedSqExpSqTrapOn,
    nI, hI, h, termI, term] using htotal

private theorem contains_weightedSqExpSqTrap
    {cI TI : DInterval} {c T : ℝ}
    (hc : cI.Contains c) (hT : TI.Contains T)
    (hsafe : weightedSqExpSqTrapSafe cI TI = true) :
    (weightedSqExpSqTrap cI TI).Contains
      (realWeightedSqExpSqTrap c T) := by
  exact contains_weightedSqExpSqTrapOn
    (List.range (innerTrapezoids - 1)) innerTrapezoids
    rat_innerTrapezoids_lo_pos hc hT hsafe

private theorem contains_weightedSqExpCubeTrapOn
    (indices : List ℕ) (n : ℚ)
    {cI AI TI : DInterval} {c A T : ℝ}
    (hn : 0 < (rat n).lo)
    (hc : cI.Contains c) (hA : AI.Contains A) (hT : TI.Contains T)
    (hsafe : weightedSqExpCubeTrapSafeOn indices n cI AI TI = true) :
    (weightedSqExpCubeTrapOn indices n cI AI TI).Contains
      (realWeightedSqExpCubeTrapOn indices n c A T) := by
  let nI := rat n
  let hI := div (TI - AI) nI
  let h : ℝ := (T - A) / (n : ℝ)
  let termI := fun sI : DInterval =>
    sI.square * rat (1 / 2) *
      expUpper
        (cI * powNat sI 3 * rat (1 / 5) -
          TI.square * rat (1 / 2))
  let term := fun s : ℝ =>
    s ^ 2 / 2 * Real.exp (c * s ^ 3 / 5 - T ^ 2 / 2)
  have hnContains : nI.Contains (n : ℝ) := by
    simpa [nI] using contains_rat n
  have hh : hI.Contains h := by
    apply contains_div (by simpa [nI] using hn) _ hnContains
    exact Interval.contains_sub hT hA
  unfold weightedSqExpCubeTrapSafeOn at hsafe
  dsimp only at hsafe
  rw [Bool.and_eq_true, Bool.and_eq_true,
    List.all_eq_true] at hsafe
  have hterm (sI : DInterval) (s : ℝ)
      (hs : sI.Contains s)
      (hsafeTerm :
        expSafe
          (cI * powNat sI 3 * rat (1 / 5) -
            TI.square * rat (1 / 2)) = true) :
      (termI sI).Contains (term s) :=
    contains_weightedCubeTerm hc hs hT hsafeTerm
  have hleft : (termI AI).Contains (term A) :=
    hterm _ _ hA hsafe.1.1
  have hright : (termI TI).Contains (term T) :=
    hterm _ _ hT hsafe.1.2
  have hstep (i : ℕ) :
      (AI + hI * rat (((i + 1 : ℕ) : ℚ))).Contains
        (A + h * ((i + 1 : ℕ) : ℝ)) :=
    Interval.contains_add hA
      (Interval.contains_mul hh
        (by simpa using contains_rat (((i + 1 : ℕ) : ℚ))))
  have hinterior :
      (indices.foldl
          (fun acc i =>
            acc + termI
              (AI + hI * rat (((i + 1 : ℕ) : ℚ))))
          (rat 0)).Contains
        (indices.foldl
          (fun acc i =>
            acc + term (A + h * ((i + 1 : ℕ) : ℝ))) 0) := by
    apply contains_foldl_add
    · intro i hi
      exact contains_weightedCubeTerm hc (hstep i) hT
        (by simpa [Nat.cast_add, Nat.cast_one] using hsafe.2 i hi)
    · simpa using contains_rat (0 : ℚ)
  have hendpoint :
      ((termI AI + termI TI) * rat (1 / 2)).Contains
        ((term A + term T) / 2) := by
    simpa [div_eq_mul_inv] using
      Interval.contains_mul (Interval.contains_add hleft hright)
        (contains_rat (1 / 2))
  have htotal :=
    Interval.contains_mul hh
      (Interval.contains_add hendpoint hinterior)
  simpa only [weightedSqExpCubeTrapOn, realWeightedSqExpCubeTrapOn,
    nI, hI, h, termI, term] using htotal

private theorem contains_weightedSqExpCubeTrap
    {cI AI TI : DInterval} {c A T : ℝ}
    (hc : cI.Contains c) (hA : AI.Contains A) (hT : TI.Contains T)
    (hsafe : weightedSqExpCubeTrapSafe cI AI TI = true) :
    (weightedSqExpCubeTrap cI AI TI).Contains
      (realWeightedSqExpCubeTrap c A T) := by
  exact contains_weightedSqExpCubeTrapOn
    (List.range (innerTrapezoids - 1)) innerTrapezoids
    rat_innerTrapezoids_lo_pos hc hA hT hsafe

/-- The exact proposition reflected by the elementary cell-geometry check. -/
theorem geometryCheck_sound
    {C : Cell} (h : geometryCheck C = true) :
    0 < C.lo ∧ C.lo ≤ C.hi ∧
      C.hi / C.lo ≤ 471 / 400 ∧
      0 < C.cutoff ∧ C.cutoff ≤ C.bandwidth ∧
      0 < C.bandwidthInterval.lo ∧
      0 < C.rootLo ∧ C.rootLo ^ 3 ≤ C.hi ∧
      0 ≤ C.rootHi ∧ C.hi ≤ C.rootHi ^ 3 ∧
      0 < (rat 3 * C.rootInterval).lo ∧
      0 < (rat C.hi).lo ∧
      0 < (rat 2 * rat C.hi).lo ∧
      0 < (rat (2 * C.hi)).lo ∧
      0 < (rat 4 * C.lyapunovInterval.square).lo ∧
      0 < C.coreCells ∧ 0 < C.outerCells ∧
      2 * C.hi * C.bandwidth ≤ 157 / 25 := by
  unfold geometryCheck at h
  exact of_decide_eq_true h

/--
The recorded rational cube-root bracket encloses the one-third power of the
cell's upper Lyapunov endpoint.
-/
theorem rootInterval_contains_endpoint
    {C : Cell} (h : geometryCheck C = true) :
    C.rootInterval.Contains
      (Probability.lyapunovThirdRoot (C.hi : ℝ)) := by
  rcases geometryCheck_sound h with
    ⟨hlo, hlohi, _hratio, _hcutoff, _hcut, _hbandlo,
      hrootLo, hrootLoCube, hrootHi, hrootHiCube, _⟩
  apply Interval.contains_enclose
  constructor
  · unfold Probability.lyapunovThirdRoot
    exact le_rpow_one_third_of_cube_le
      (by exact_mod_cast hrootLo.le)
      (by exact_mod_cast hlo.le.trans hlohi)
      (by exact_mod_cast hrootLoCube)
  · unfold Probability.lyapunovThirdRoot
    exact rpow_one_third_le_of_le_cube
      (by exact_mod_cast hlo.le.trans hlohi)
      (by exact_mod_cast hrootHi)
      (by exact_mod_cast hrootHiCube)

theorem endpoint_root_bounds
    {C : Cell} (h : geometryCheck C = true) :
    (C.rootLo : ℝ) ≤
        Probability.lyapunovThirdRoot (C.hi : ℝ) ∧
      Probability.lyapunovThirdRoot (C.hi : ℝ) ≤
        (C.rootHi : ℝ) := by
  rcases geometryCheck_sound h with
    ⟨hlo, hlohi, _hratio, _hcutoff, _hcut, _hbandlo,
      hrootLo, hrootLoCube, hrootHi, hrootHiCube, _⟩
  constructor
  · unfold Probability.lyapunovThirdRoot
    exact le_rpow_one_third_of_cube_le
      (by exact_mod_cast hrootLo.le)
      (by exact_mod_cast hlo.le.trans hlohi)
      (by exact_mod_cast hrootLoCube)
  · unfold Probability.lyapunovThirdRoot
    exact rpow_one_third_le_of_le_cube
      (by exact_mod_cast hlo.le.trans hlohi)
      (by exact_mod_cast hrootHi)
      (by exact_mod_cast hrootHiCube)

/-- The squared root interval encloses the endpoint variance cap. -/
theorem varianceCapInterval_contains_endpoint
    {C : Cell} (h : geometryCheck C = true) :
    (varianceCapInterval C).Contains
      (Probability.lyapunovVarianceCap (C.hi : ℝ)) := by
  unfold varianceCapInterval
  have hroot := rootInterval_contains_endpoint h
  rw [← Probability.lyapunovThirdRoot_sq]
  · exact Interval.contains_square hroot
  · exact_mod_cast (geometryCheck_sound h).1.le.trans
      (geometryCheck_sound h).2.1

/-- The fixed cell parameters are positive and ordered. -/
theorem cell_parameters_sound
    {C : Cell} (h : geometryCheck C = true) :
    (0 : ℝ) < C.cutoff ∧
      (C.cutoff : ℝ) ≤ C.bandwidth ∧
      (0 : ℝ) < C.bandwidth := by
  rcases geometryCheck_sound h with
    ⟨_hlo, _hlohi, _hratio, hcutoff, hcut, _⟩
  exact ⟨by exact_mod_cast hcutoff,
    by exact_mod_cast hcut,
    by exact_mod_cast hcutoff.trans_le hcut⟩

private theorem foldl_range_add_eq_sum
    (f : ℕ → ℝ) (n : ℕ) :
    (List.range n).foldl (fun acc i => acc + f i) 0 =
      ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append,
        Finset.sum_range_succ, ih]
      simp

private theorem weighted_sq_term_eq
    (c T s : ℝ) :
    s ^ 2 / 2 * Real.exp ((c * s ^ 2 - T ^ 2) / 2) =
      Real.exp (-(T ^ 2) / 2) *
        (s ^ 2 / 2 * Real.exp (c * s ^ 2 / 2)) := by
  rw [show (c * s ^ 2 - T ^ 2) / 2 =
      -(T ^ 2) / 2 + c * s ^ 2 / 2 by ring,
    Real.exp_add]
  ring

private theorem weighted_cube_term_eq
    (c T s : ℝ) :
    s ^ 2 / 2 * Real.exp (c * s ^ 3 / 5 - T ^ 2 / 2) =
      Real.exp (-(T ^ 2) / 2) *
        (s ^ 2 / 2 * Real.exp (c * s ^ 3 / 5)) := by
  rw [show c * s ^ 3 / 5 - T ^ 2 / 2 =
      -(T ^ 2) / 2 + c * s ^ 3 / 5 by ring,
    Real.exp_add]
  ring

private theorem realWeightedSqExpSqTrap_eq
    (c T : ℝ) :
    realWeightedSqExpSqTrap c T =
      Real.exp (-(T ^ 2) / 2) *
        Probability.sqExpSqTrapezoid innerTrapezoids c T := by
  unfold realWeightedSqExpSqTrap realWeightedSqExpSqTrapOn
    Probability.sqExpSqTrapezoid trapezoidal_integral
  dsimp only
  rw [foldl_range_add_eq_sum]
  have hncast :
      (((innerTrapezoids : ℕ) : ℚ) : ℝ) =
        (innerTrapezoids : ℝ) := by
    norm_num [innerTrapezoids]
  rw [hncast]
  have hgrid (i : ℕ) :
      T / (innerTrapezoids : ℝ) * (i + 1 : ℕ) =
        0 + ((i : ℝ) + 1) * (T - 0) / (innerTrapezoids : ℝ) := by
    norm_num [innerTrapezoids]
    ring
  simp_rw [hgrid]
  simp_rw [weighted_sq_term_eq]
  rw [← Finset.mul_sum]
  ring

private theorem realWeightedSqExpCubeTrap_eq
    (c A T : ℝ) :
    realWeightedSqExpCubeTrap c A T =
      Real.exp (-(T ^ 2) / 2) *
        Probability.sqExpCubeTrapezoid
          innerTrapezoids c A T := by
  unfold realWeightedSqExpCubeTrap realWeightedSqExpCubeTrapOn
    Probability.sqExpCubeTrapezoid trapezoidal_integral
  dsimp only
  rw [foldl_range_add_eq_sum]
  have hncast :
      (((innerTrapezoids : ℕ) : ℚ) : ℝ) =
        (innerTrapezoids : ℝ) := by
    norm_num [innerTrapezoids]
  rw [hncast]
  have hgrid (i : ℕ) :
      A + (T - A) / (innerTrapezoids : ℝ) *
          (i + 1 : ℕ) =
        A + ((i : ℝ) + 1) * (T - A) /
          (innerTrapezoids : ℝ) := by
    norm_num [innerTrapezoids]
    ring
  simp_rw [hgrid]
  simp_rw [weighted_cube_term_eq]
  rw [← Finset.mul_sum]
  ring

private theorem weightedSq_then_gaussian_eq
    (c A T : ℝ) :
    realWeightedSqExpSqTrap c A *
        Real.exp ((A ^ 2 - T ^ 2) / 2) =
      Real.exp (-(T ^ 2) / 2) *
        Probability.sqExpSqTrapezoid
          innerTrapezoids c A := by
  rw [realWeightedSqExpSqTrap_eq]
  calc
    Real.exp (-A ^ 2 / 2) *
          Probability.sqExpSqTrapezoid innerTrapezoids c A *
          Real.exp ((A ^ 2 - T ^ 2) / 2) =
        (Real.exp (-A ^ 2 / 2) *
          Real.exp ((A ^ 2 - T ^ 2) / 2)) *
          Probability.sqExpSqTrapezoid innerTrapezoids c A := by ring
    _ = Real.exp (-(T ^ 2) / 2) *
          Probability.sqExpSqTrapezoid innerTrapezoids c A := by
      rw [← Real.exp_add]
      congr 2
      ring

private theorem inverse_tyurinRationalEll_eq :
    1 / Probability.tyurinRationalEll =
      Real.exp (25 / 54 : ℝ) := by
  unfold Probability.tyurinRationalEll
  rw [one_div, ← Real.exp_neg]
  congr 1
  ring

/--
The executable first-discrepancy interval encloses the exact eight-trapezoid
upper envelope at the cell's upper Lyapunov endpoint.
-/
theorem deltaOne_contains_endpointTrapezoid
    {C : Cell} {TI : DInterval} {t : ℝ}
    (ht : TI.Contains t) (ht0 : 0 ≤ t)
    (hsafe : deltaOneSafe C TI = true) :
    (deltaOne C TI).Contains
      (Probability.tyurinDeltaOneTrapezoidUpper
        innerTrapezoids (C.hi : ℝ) t) := by
  have hc : (rat 1).Contains (1 : ℝ) := by
    simpa using contains_rat (1 : ℚ)
  have hweighted :=
    contains_weightedSqExpSqTrap hc ht hsafe
  rw [realWeightedSqExpSqTrap_eq] at hweighted
  have hL :
      C.lyapunovInterval.Contains (C.hi : ℝ) := by
    simpa [Cell.lyapunovInterval] using contains_rat C.hi
  unfold deltaOne Probability.tyurinDeltaOneTrapezoidUpper
  rw [abs_of_nonneg ht0]
  simpa only [mul_assoc] using
    Interval.contains_mul hL hweighted

/-- The executable switching-point interval encloses `5/(3 L^(1/3))`. -/
theorem switchInterval_contains_endpoint
    {C : Cell} (hgeometry : geometryCheck C = true) :
    (switchInterval C).Contains
      (5 /
        (3 * Probability.lyapunovThirdRoot (C.hi : ℝ))) := by
  rcases geometryCheck_sound hgeometry with
    ⟨_hlo, _hlohi, _hratio, _hcutoff, _hcut,
      _hbandlo, _hrootLo, _hrootLoCube, _hrootHi, _hrootHiCube,
      hdenom, _hhiLo, _htwoHi, _htwoExact, _hfourL,
      _hcore, _houter, _hband⟩
  have hthree : (rat 3).Contains (3 : ℝ) := by
    simpa using contains_rat (3 : ℚ)
  have hden :
      (rat 3 * C.rootInterval).Contains
        (3 * Probability.lyapunovThirdRoot (C.hi : ℝ)) :=
    Interval.contains_mul hthree
      (rootInterval_contains_endpoint hgeometry)
  unfold switchInterval
  exact contains_div hdenom
    (by simpa using contains_rat (5 : ℚ)) hden

/-- Soundness of the quadratic branch of the second discrepancy envelope. -/
theorem deltaTwoFirst_contains_endpointBranch
    {C : Cell} {TI : DInterval} {t : ℝ}
    (ht : TI.Contains t)
    (hgeometry : geometryCheck C = true)
    (hsafe : deltaTwoFirstSafe C TI = true) :
    (deltaTwoFirst C TI).Contains
      ((C.hi : ℝ) * Real.exp (-(t ^ 2) / 2) *
        Probability.sqExpSqTrapezoid innerTrapezoids
          (Probability.lyapunovVarianceCap (C.hi : ℝ)) t) := by
  have hweighted :=
    contains_weightedSqExpSqTrap
      (varianceCapInterval_contains_endpoint hgeometry) ht hsafe
  rw [realWeightedSqExpSqTrap_eq] at hweighted
  have hL :
      C.lyapunovInterval.Contains (C.hi : ℝ) := by
    simpa [Cell.lyapunovInterval] using contains_rat C.hi
  unfold deltaTwoFirst
  simpa only [mul_assoc] using
    Interval.contains_mul hL hweighted

/-- Soundness of the post-switch branch of the second discrepancy envelope. -/
theorem deltaTwoSecond_contains_endpointBranch
    {C : Cell} {TI : DInterval} {t : ℝ}
    (ht : TI.Contains t)
    (hgeometry : geometryCheck C = true)
    (hsafe : deltaTwoSecondSafe C TI = true) :
    (deltaTwoSecond C TI).Contains
      ((C.hi : ℝ) * Real.exp (-(t ^ 2) / 2) *
        (Probability.sqExpSqTrapezoid innerTrapezoids
            (Probability.lyapunovVarianceCap (C.hi : ℝ))
            (5 / (3 *
              Probability.lyapunovThirdRoot (C.hi : ℝ))) +
          (1 / Probability.tyurinRationalEll) *
            Probability.sqExpCubeTrapezoid innerTrapezoids
              (C.hi : ℝ)
              (5 / (3 *
                Probability.lyapunovThirdRoot (C.hi : ℝ))) t)) := by
  let A : ℝ :=
    5 / (3 * Probability.lyapunovThirdRoot (C.hi : ℝ))
  have hA : (switchInterval C).Contains A := by
    simpa [A] using switchInterval_contains_endpoint hgeometry
  unfold deltaTwoSecondSafe at hsafe
  dsimp only at hsafe
  simp only [Bool.and_eq_true] at hsafe
  have hfirstWeighted :=
    contains_weightedSqExpSqTrap
      (varianceCapInterval_contains_endpoint hgeometry)
      hA hsafe.1.1.2
  have hASq := Interval.contains_square hA
  have htSq := Interval.contains_square ht
  have hbridgeExponent :
      ((switchInterval C).square - TI.square) *
          rat (1 / 2) |>.Contains
        ((A ^ 2 - t ^ 2) / 2) := by
    simpa [div_eq_mul_inv] using
      Interval.contains_mul
        (Interval.contains_sub hASq htSq)
        (contains_rat (1 / 2))
  have hbridge :=
    contains_expUpper hbridgeExponent hsafe.1.2
  have hfirstProduct :=
    Interval.contains_mul hfirstWeighted hbridge
  rw [weightedSq_then_gaussian_eq] at hfirstProduct
  have hL :
      C.lyapunovInterval.Contains (C.hi : ℝ) := by
    simpa [Cell.lyapunovInterval] using contains_rat C.hi
  have hinvEll :
      (expUpper (rat (25 / 54))).Contains
        (1 / Probability.tyurinRationalEll) := by
    rw [inverse_tyurinRationalEll_eq]
    exact contains_expUpper
      (by simpa using contains_rat (25 / 54))
      hsafe.1.1.1
  have hcubeWeighted :=
    contains_weightedSqExpCubeTrap hL hA ht hsafe.2
  rw [realWeightedSqExpCubeTrap_eq] at hcubeWeighted
  have hsecondProduct :=
    Interval.contains_mul hinvEll hcubeWeighted
  have hinside :=
    Interval.contains_add hfirstProduct hsecondProduct
  have htotal := Interval.contains_mul hL hinside
  unfold deltaTwoSecond
  dsimp only
  change
    (C.lyapunovInterval *
        (weightedSqExpSqTrap (varianceCapInterval C)
              (switchInterval C) *
            expUpper
              (((switchInterval C).square - TI.square) *
                rat (1 / 2)) +
          expUpper (rat (25 / 54)) *
            weightedSqExpCubeTrap C.lyapunovInterval
              (switchInterval C) TI)).Contains _
  convert htotal using 1
  all_goals
    dsimp only [A]
    ring

/--
The branch-independent executable interval encloses the exact
eight-trapezoid second-discrepancy envelope at the cell endpoint.
-/
theorem deltaTwo_contains_endpointTrapezoid
    {C : Cell} {TI : DInterval} {t : ℝ}
    (ht : TI.Contains t) (ht0 : 0 ≤ t)
    (hgeometry : geometryCheck C = true)
    (hsafe : deltaTwoSafe C TI = true) :
    (deltaTwo C TI).Contains
      (Probability.tyurinDeltaTwoTrapezoidUpper
        innerTrapezoids (C.hi : ℝ) t) := by
  let R : ℝ :=
    Probability.lyapunovThirdRoot (C.hi : ℝ)
  have hroot :=
    endpoint_root_bounds hgeometry
  have hrootLo0 : (0 : ℝ) ≤ C.rootLo := by
    rcases geometryCheck_sound hgeometry with
      ⟨_hlo, _hlohi, _hratio, _hcutoff, _hcut, _hbandlo,
        hrootLo, _⟩
    exact_mod_cast hrootLo.le
  have hR0 : 0 ≤ R := by
    dsimp only [R]
    have hhi0 : 0 ≤ C.hi :=
      (geometryCheck_sound hgeometry).1.le.trans
        (geometryCheck_sound hgeometry).2.1
    exact Probability.lyapunovThirdRoot_nonneg
      (by exact_mod_cast hhi0)
  have hupper : t ≤ (TI.upperRat : ℝ) :=
    le_upperRat_of_contains ht
  have hlower : (TI.lowerRat : ℝ) ≤ t :=
    lowerRat_le_of_contains ht
  by_cases hfirst :
      TI.upperRat * C.rootHi ≤ 5 / 3
  · have hbranch : t * R ≤ 5 / 3 := by
      have hproduct :
          t * R ≤
            (TI.upperRat : ℝ) * (C.rootHi : ℝ) :=
        mul_le_mul hupper (by simpa [R] using hroot.2)
          hR0 (by
            exact ht0.trans hupper)
      have hfirstReal :
          ((TI.upperRat * C.rootHi : ℚ) : ℝ) ≤
            (((5 / 3 : ℚ) : ℝ)) := by
        exact_mod_cast hfirst
      exact hproduct.trans (by simpa using hfirstReal)
    unfold deltaTwoSafe at hsafe
    unfold deltaTwo
    rw [if_pos hfirst] at hsafe ⊢
    unfold Probability.tyurinDeltaTwoTrapezoidUpper
    dsimp only
    rw [abs_of_nonneg ht0, if_pos (by simpa [R] using hbranch)]
    exact deltaTwoFirst_contains_endpointBranch
      ht hgeometry hsafe
  · by_cases hsecond :
        5 / 3 < TI.lowerRat * C.rootLo
    · have hbranch : 5 / 3 < t * R := by
        have hproduct :
            (TI.lowerRat : ℝ) * (C.rootLo : ℝ) ≤ t * R :=
          mul_le_mul hlower (by simpa [R] using hroot.1)
            hrootLo0
            ht0
        have hsecondReal :
            (((5 / 3 : ℚ) : ℝ)) <
              ((TI.lowerRat * C.rootLo : ℚ) : ℝ) := by
          exact_mod_cast hsecond
        have hsecondReal' :
            (5 / 3 : ℝ) <
              (TI.lowerRat : ℝ) * (C.rootLo : ℝ) := by
          simpa using hsecondReal
        exact hsecondReal'.trans_le hproduct
      unfold deltaTwoSafe at hsafe
      unfold deltaTwo
      rw [if_neg hfirst, if_pos hsecond] at hsafe ⊢
      unfold Probability.tyurinDeltaTwoTrapezoidUpper
      dsimp only
      rw [abs_of_nonneg ht0,
        if_neg (by simpa [R] using not_le.mpr hbranch)]
      exact deltaTwoSecond_contains_endpointBranch
        ht hgeometry hsafe
    · unfold deltaTwoSafe at hsafe
      unfold deltaTwo
      rw [if_neg hfirst, if_neg hsecond] at hsafe ⊢
      simp only [Bool.and_eq_true] at hsafe
      unfold Probability.tyurinDeltaTwoTrapezoidUpper
      dsimp only
      rw [abs_of_nonneg ht0]
      by_cases hbranch : t * R ≤ 5 / 3
      · rw [if_pos (by simpa [R] using hbranch)]
        exact contains_hull_left
          (deltaTwoFirst_contains_endpointBranch
            ht hgeometry hsafe.1)
      · rw [if_neg (by simpa [R] using hbranch)]
        exact contains_hull_right
          (deltaTwoSecond_contains_endpointBranch
            ht hgeometry hsafe.2)

/-- The reflected minimum encloses the minimum of both endpoint envelopes. -/
theorem deltaMin_contains_endpointTrapezoids
    {C : Cell} {TI : DInterval} {t : ℝ}
    (ht : TI.Contains t) (ht0 : 0 ≤ t)
    (hgeometry : geometryCheck C = true)
    (hsafeOne : deltaOneSafe C TI = true)
    (hsafeTwo : deltaTwoSafe C TI = true) :
    (deltaMin C TI).Contains
      (min
        (Probability.tyurinDeltaOneTrapezoidUpper
          innerTrapezoids (C.hi : ℝ) t)
        (Probability.tyurinDeltaTwoTrapezoidUpper
          innerTrapezoids (C.hi : ℝ) t)) := by
  unfold deltaMin
  exact contains_minInterval
    (deltaOne_contains_endpointTrapezoid ht ht0 hsafeOne)
    (deltaTwo_contains_endpointTrapezoid
      ht ht0 hgeometry hsafeTwo)

private theorem scaledI29_le_rational
    {t : ℝ} (ht : 0 < t) :
    Probability.scaledPrawitzI29Envelope t ≤
      (513 / 500 : ℝ) /
        (2 * (piLower : ℝ) * t) := by
  have hpi :
      (piLower : ℝ) < Real.pi := by
    simpa [piLower] using pi_gt_3141592_div_1000000
  unfold Probability.scaledPrawitzI29Envelope
  rw [abs_of_pos ht]
  apply div_le_div_of_nonneg_left
  · norm_num
  · unfold piLower
    positivity
  · nlinarith

theorem kernelI29_upper
    {TI : DInterval} {t : ℝ}
    (ht : TI.Contains t) (ht0 : 0 < t)
    (hsafe : 0 < (rat (2 * piLower) * TI).lo) :
    Probability.scaledPrawitzI29Envelope t ≤
      ((kernelI29 TI).upperRat : ℝ) := by
  have hden :
      (rat (2 * piLower) * TI).Contains
        (2 * (piLower : ℝ) * t) := by
    exact Interval.contains_mul
      (by
        simpa [piLower] using
          contains_rat (2 * piLower))
      ht
  have hrat :
      (kernelI29 TI).Contains
        ((513 / 500 : ℝ) /
          (2 * (piLower : ℝ) * t)) := by
    unfold kernelI29
    exact contains_div hsafe
      (by simpa using contains_rat (513 / 500)) hden
  exact (scaledI29_le_rational ht0).trans
    (le_upperRat hrat)

private theorem scaledEndpoint_le_rational
    {U t : ℝ} (hU : 0 < U) (ht0 : 0 ≤ t) (htU : t ≤ U) :
    Probability.scaledPrawitzEndpointEnvelope U t ≤
      (1 / U) *
        ((1 - t / U) / 2 +
          (piUpper : ℝ) * (1 - t / U) ^ 2 / 4) := by
  have hpi :
      Real.pi ≤ (piUpper : ℝ) := by
    exact (by
      simpa [piUpper] using
        pi_lt_3141593_div_1000000.le)
  have hgap : 0 ≤ 1 - t / U := by
    rw [sub_nonneg, div_le_one hU]
    exact htU
  unfold Probability.scaledPrawitzEndpointEnvelope
  rw [abs_of_nonneg ht0]
  gcongr

theorem kernelEndpoint_upper
    {C : Cell} {TI : DInterval} {t : ℝ}
    (ht : TI.Contains t) (ht0 : 0 ≤ t)
    (hgeometry : geometryCheck C = true)
    (htU : t ≤ (C.bandwidth : ℝ)) :
    Probability.scaledPrawitzEndpointEnvelope
        (C.bandwidth : ℝ) t ≤
      ((kernelEndpoint C TI).upperRat : ℝ) := by
  rcases geometryCheck_sound hgeometry with
    ⟨_hlo, _hlohi, _hratio, hcutoff, hcut, hUlo, _⟩
  have hU : (0 : ℝ) < C.bandwidth := by
    exact_mod_cast hcutoff.trans_le hcut
  have hUI :
      C.bandwidthInterval.Contains (C.bandwidth : ℝ) := by
    simpa [Cell.bandwidthInterval] using
      contains_rat C.bandwidth
  have htDiv :
      (div TI C.bandwidthInterval).Contains
        (t / (C.bandwidth : ℝ)) :=
    contains_div hUlo ht hUI
  have hgap :
      (rat 1 - div TI C.bandwidthInterval).Contains
        (1 - t / (C.bandwidth : ℝ)) :=
    Interval.contains_sub
      (by simpa using contains_rat (1 : ℚ)) htDiv
  have hgapSq := Interval.contains_square hgap
  have hhalf :
      ((rat 1 - div TI C.bandwidthInterval) *
          rat (1 / 2)).Contains
        ((1 - t / (C.bandwidth : ℝ)) / 2) := by
    simpa [div_eq_mul_inv] using
      Interval.contains_mul hgap (contains_rat (1 / 2))
  have hquarter :
      (rat piUpper *
          (rat 1 - div TI C.bandwidthInterval).square *
          rat (1 / 4)).Contains
        ((piUpper : ℝ) *
          (1 - t / (C.bandwidth : ℝ)) ^ 2 / 4) := by
    simpa [div_eq_mul_inv, mul_assoc] using
      Interval.contains_mul
        (Interval.contains_mul (contains_rat piUpper) hgapSq)
        (contains_rat (1 / 4))
  have hInvU :
      (div (rat 1) C.bandwidthInterval).Contains
        (1 / (C.bandwidth : ℝ)) :=
    contains_div hUlo
      (by simpa using contains_rat (1 : ℚ)) hUI
  have hrational :
      (kernelEndpoint C TI).Contains
        ((1 / (C.bandwidth : ℝ)) *
          ((1 - t / (C.bandwidth : ℝ)) / 2 +
            (piUpper : ℝ) *
              (1 - t / (C.bandwidth : ℝ)) ^ 2 / 4)) := by
    unfold kernelEndpoint
    exact Interval.contains_mul hInvU
      (Interval.contains_add hhalf hquarter)
  exact
    (scaledEndpoint_le_rational hU ht0 htU).trans
      (le_upperRat hrational)

/--
The executable kernel interval's upper endpoint dominates the analytic
certificate kernel at every enclosed positive frequency.
-/
theorem kernel_upper
    {C : Cell} {TI : DInterval} {t : ℝ}
    (ht : TI.Contains t) (ht0 : 0 < t)
    (htU : t ≤ (C.bandwidth : ℝ))
    (hgeometry : geometryCheck C = true)
    (hsafe : kernelSafe C TI = true) :
    Probability.scaledPrawitzCertificateEnvelope
        (C.bandwidth : ℝ) t ≤
      ((kernel C TI).upperRat : ℝ) := by
  unfold kernelSafe at hsafe
  rw [Bool.and_eq_true] at hsafe
  have hi29 := kernelI29_upper ht ht0
    (of_decide_eq_true hsafe.1)
  by_cases hhalfCheck :
      C.bandwidth / 2 ≤ TI.lowerRat
  · have hhalf :
        (C.bandwidth : ℝ) / 2 ≤ t := by
      have hcast :
          ((C.bandwidth / 2 : ℚ) : ℝ) ≤
            (TI.lowerRat : ℝ) := by
        exact_mod_cast hhalfCheck
      have hcast' :
          (C.bandwidth : ℝ) / 2 ≤
            (TI.lowerRat : ℝ) := by
        simpa using hcast
      exact hcast'.trans (lowerRat_le_of_contains ht)
    have hendpoint :=
      kernelEndpoint_upper ht ht0.le hgeometry htU
    unfold kernel
    rw [if_pos hhalfCheck]
    unfold Probability.scaledPrawitzCertificateEnvelope
    rw [abs_of_pos ht0, if_pos hhalf]
    unfold minInterval Interval.upperRat
    rw [toRat_min]
    unfold Interval.upperRat at hi29 hendpoint
    simpa using min_le_min hi29 hendpoint
  · have henvelope :
        Probability.scaledPrawitzCertificateEnvelope
            (C.bandwidth : ℝ) t ≤
          Probability.scaledPrawitzI29Envelope t := by
      unfold Probability.scaledPrawitzCertificateEnvelope
      by_cases hhalf :
          (C.bandwidth : ℝ) / 2 ≤ |t|
      · rw [if_pos hhalf]
        exact min_le_left _ _
      · rw [if_neg hhalf]
    unfold kernel
    rw [if_neg hhalfCheck]
    exact henvelope.trans hi29

private theorem rationalCosineLower_nonneg
    {x : ℝ} (hx0 : 4 ≤ x) (hx1 : x ≤ 157 / 25) :
    0 ≤ Probability.tyurinRationalCosineLower x := by
  unfold Probability.tyurinRationalCosineLower
  split_ifs with hleft hmiddle
  · have hgap0 : 0 ≤ x - 157 / 50 := by nlinarith
    have hgap1 : x - 157 / 50 ≤ 157 / 50 := by nlinarith
    nlinarith [sq_nonneg (x - 157 / 50),
      sq_le_sq₀ hgap0 (by norm_num : (0 : ℝ) ≤ 157 / 50) |>.2 hgap1]
  · norm_num
  · have hr0 : 0 ≤ 157 / 25 - x := by linarith
    have hr1 : 157 / 25 - x ≤ 313 / 200 := by
      have : 189 / 40 ≤ x := le_of_not_gt hmiddle
      linarith
    have hrsq :
        (157 / 25 - x) ^ 2 ≤ (313 / 200 : ℝ) ^ 2 :=
      (sq_le_sq₀ hr0 (by norm_num)).2 hr1
    have hfactor :
        (157 / 25 - x) ^ 2 / 2 -
            (157 / 25 - x) ^ 4 / 24 =
          (157 / 25 - x) ^ 2 *
            (1 / 2 - (157 / 25 - x) ^ 2 / 24) := by
      ring
    rw [hfactor]
    apply mul_nonneg (sq_nonneg _)
    nlinarith

private theorem rationalCosineLower_ge_two_fifths
    {x : ℝ} (hx0 : 4 ≤ x) (hx1 : x ≤ 189 / 40) :
    (2 / 5 : ℝ) ≤
      Probability.tyurinRationalCosineLower x := by
  unfold Probability.tyurinRationalCosineLower
  split_ifs with hleft hmiddle
  · have hgap0 : 0 ≤ x - 157 / 50 := by nlinarith
    have hgap1 : x - 157 / 50 ≤ 317 / 200 := by
      linarith
    have hrsq :
        (x - 157 / 50) ^ 2 ≤ (317 / 200 : ℝ) ^ 2 :=
      (sq_le_sq₀ hgap0 (by norm_num)).2 hgap1
    nlinarith
  · exact le_rfl
  · have hx : x = 189 / 40 := by
      exact le_antisymm hx1 (le_of_not_gt hmiddle)
    subst x
    norm_num

/--
The executable piecewise cosine evaluator contains a rational surrogate no
larger than the analytic rational cosine envelope.
-/
theorem rationalCosineLower_surrogate
    {XI : DInterval} {x : ℝ}
    (hx : XI.Contains x) (hx0 : 4 ≤ x)
    (hx1 : x ≤ 157 / 25) :
    ∃ q : ℝ,
      (rationalCosineLower XI).Contains q ∧
        q ≤ Probability.tyurinRationalCosineLower x := by
  unfold rationalCosineLower
  by_cases hleft : XI.upperRat ≤ 471 / 100
  · rw [if_pos hleft]
    let q : ℝ := 2 - (x - 157 / 50) ^ 2 / 2
    have hq :
        (rat 2 - (XI - rat (157 / 50)).square *
            rat (1 / 2)).Contains q := by
      dsimp only [q]
      have hshift :=
        Interval.contains_sub hx
          (by simpa using contains_rat (157 / 50))
      have hsq := Interval.contains_square hshift
      simpa [div_eq_mul_inv] using
        Interval.contains_sub (by simpa using contains_rat (2 : ℚ))
          (Interval.contains_mul hsq
            (by simpa using contains_rat (1 / 2)))
    refine ⟨q, hq, ?_⟩
    unfold Probability.tyurinRationalCosineLower
    have hxleft : x ≤ (471 / 100 : ℝ) := by
      have hleftReal :
          (XI.upperRat : ℝ) ≤ (471 / 100 : ℝ) := by
        have hcast :
            ((XI.upperRat : ℚ) : ℝ) ≤
              (((471 / 100 : ℚ) : ℝ)) := by
          exact_mod_cast hleft
        simpa using hcast
      exact (le_upperRat_of_contains hx).trans hleftReal
    rw [if_pos hxleft]
  · rw [if_neg hleft]
    by_cases hright : 189 / 40 ≤ XI.lowerRat
    · rw [if_pos hright]
      let r : ℝ := 157 / 25 - x
      let q : ℝ := r ^ 2 / 2 - r ^ 4 / 24
      have hr :
          (rat (157 / 25) - XI).Contains r := by
        dsimp only [r]
        exact Interval.contains_sub
          (by simpa using contains_rat (157 / 25)) hx
      have hq :
          ((rat (157 / 25) - XI).square * rat (1 / 2) -
            powNat (rat (157 / 25) - XI) 4 *
              rat (1 / 24)).Contains q := by
        dsimp only [q]
        have hhalf :
            ((rat (157 / 25) - XI).square *
                rat (1 / 2)).Contains (r ^ 2 / 2) := by
          simpa [div_eq_mul_inv] using
            Interval.contains_mul (Interval.contains_square hr)
              (by simpa using contains_rat (1 / 2))
        have htwentyFour :
            (powNat (rat (157 / 25) - XI) 4 *
                rat (1 / 24)).Contains (r ^ 4 / 24) := by
          simpa [div_eq_mul_inv] using
            Interval.contains_mul (contains_powNat hr 4)
              (by simpa using contains_rat (1 / 24))
        exact Interval.contains_sub
          hhalf htwentyFour
      refine ⟨q, hq, ?_⟩
      unfold Probability.tyurinRationalCosineLower
      have hrightReal :
          (189 / 40 : ℝ) ≤ (XI.lowerRat : ℝ) := by
        have hcast :
            (((189 / 40 : ℚ) : ℝ)) ≤
              ((XI.lowerRat : ℚ) : ℝ) := by
          exact_mod_cast hright
        simpa using hcast
      have hxRight :
          (189 / 40 : ℝ) ≤ x :=
        hrightReal.trans (lowerRat_le_of_contains hx)
      have hxNotLeft : ¬x ≤ (471 / 100 : ℝ) := by
        linarith
      have hxNotMiddle : ¬x < (189 / 40 : ℝ) :=
        not_lt.mpr hxRight
      rw [if_neg hxNotLeft, if_neg hxNotMiddle]
    · rw [if_neg hright]
      by_cases hmiddle : XI.upperRat ≤ 189 / 40
      · rw [if_pos hmiddle]
        refine ⟨2 / 5,
          by simpa using contains_rat (2 / 5), ?_⟩
        apply rationalCosineLower_ge_two_fifths hx0
        have hmiddleReal :
            (XI.upperRat : ℝ) ≤ (189 / 40 : ℝ) := by
          have hcast :
              ((XI.upperRat : ℚ) : ℝ) ≤
                (((189 / 40 : ℚ) : ℝ)) := by
            exact_mod_cast hmiddle
          simpa using hcast
        exact (le_upperRat_of_contains hx).trans hmiddleReal
      · rw [if_neg hmiddle]
        exact ⟨0, by simpa using contains_rat (0 : ℚ),
          rationalCosineLower_nonneg hx0 hx1⟩

end TyurinModerate
end CertifiedJL
