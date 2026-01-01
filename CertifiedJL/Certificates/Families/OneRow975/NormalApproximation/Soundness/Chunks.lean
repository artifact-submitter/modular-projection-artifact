/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Soundness.Coverage

/-!
# Granular reflected claims for moderate-Lyapunov cells

Large cells contain hundreds of core rectangles and thousands of outer
rectangles.  Reducing their entire Boolean checker in one kernel expression
creates an avoidable normalization bottleneck.  This module exposes small
independent claims: every node in a chunk is safe, and its rectangle endpoint
is at most a supplied rational bound.
-/

open scoped BigOperators

namespace CertifiedJL
namespace TyurinModerate

/-- Grouped core rectangle budget carried by a list of chunk maxima. -/
def coreGroupedUpper (C : Cell) (q : ℕ) (bounds : List ℚ) : ℚ :=
  (C.cutoff / C.coreCells) * (q * bounds.sum)

/-- Grouped outer rectangle budget carried by a list of chunk maxima. -/
def outerGroupedUpper (C : Cell) (q : ℕ) (bounds : List ℚ) : ℚ :=
  ((2 * C.hi * C.bandwidth - 2 * C.hi * C.cutoff) /
    C.outerCells) * (q * bounds.sum)

/-- Executable core-node safety and upper-bound check on one index chunk. -/
def coreChunkCheck
    (C : Cell) (start length : ℕ) (upper : ℚ) : Bool :=
  decide (start + length ≤ C.coreCells) &&
    (List.range length).all fun k =>
      let i := start + k
      (if i = 0 then true else coreIntegrandSafe C i) &&
        decide (coreCellUpper C i ≤ upper)

/-- Executable outer-node safety and upper-bound check on one index chunk. -/
def outerChunkCheck
    (C : Cell) (start length : ℕ) (upper : ℚ) : Bool :=
  decide (start + length ≤ C.outerCells) &&
    (List.range length).all fun k =>
      let i := start + k
      outerScaledIntegrandSafe C i &&
        decide (outerCellUpper C i ≤ upper)

/-- Exact reflected sum of the core rectangle endpoints in one chunk. -/
def coreChunkSum (C : Cell) (start length : ℕ) : ℚ :=
  (List.range length).foldl
    (fun acc k => acc + coreCellUpper C (start + k)) 0

/-- Exact sum of selected core rectangle endpoints in one chunk. -/
def chosenCoreChunkSum
    (C : Cell) (choices : ℕ → CoreChoice)
    (start length : ℕ) : ℚ :=
  (List.range length).foldl
    (fun acc k =>
      let i := start + k
      acc + chosenCoreCellUpper C (choices i) i) 0

/-- Exact reflected sum of the outer rectangle endpoints in one chunk. -/
def outerChunkSum (C : Cell) (start length : ℕ) : ℚ :=
  (List.range length).foldl
    (fun acc k => acc + outerCellUpper C (start + k)) 0

/--
Executable core safety and exact-sum claim on one small chunk.  Exact chunk
sums preserve the original quadrature budget when grouped maxima are too
coarse.
-/
def coreExactChunkCheck
    (C : Cell) (start length : ℕ) (total : ℚ) : Bool :=
  decide (start + length ≤ C.coreCells) &&
    ((List.range length).all fun k =>
      let i := start + k
      if i = 0 then true else coreIntegrandSafe C i) &&
    decide (coreChunkSum C start length = total)

/--
Executable selected-core safety and exact-sum claim on one small chunk.
Only the stored discrepancy and kernel alternatives are reduced.
-/
def chosenCoreExactChunkCheck
    (C : Cell) (choices : ℕ → CoreChoice)
    (start length : ℕ) (total : ℚ) : Bool :=
  decide (start + length ≤ C.coreCells) &&
    ((List.range length).all fun k =>
      let i := start + k
      if i = 0 then true
      else chosenCoreIntegrandSafe C (choices i) i) &&
    decide (chosenCoreChunkSum C choices start length = total)

/-- Executable outer safety and exact-sum claim on one small chunk. -/
def outerExactChunkCheck
    (C : Cell) (start length : ℕ) (total : ℚ) : Bool :=
  decide (start + length ≤ C.outerCells) &&
    ((List.range length).all fun k =>
      outerScaledIntegrandSafe C (start + k)) &&
    decide (outerChunkSum C start length = total)

/-- Exact proposition certified by one successful core chunk check. -/
theorem coreChunkCheck_sound
    {C : Cell} {start length : ℕ} {upper : ℚ}
    (hcheck : coreChunkCheck C start length upper = true) :
    start + length ≤ C.coreCells ∧
      ∀ k < length,
        (if start + k = 0 then true
          else coreIntegrandSafe C (start + k)) = true ∧
        coreCellUpper C (start + k) ≤ upper := by
  unfold coreChunkCheck at hcheck
  rw [Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨hbound, hnodes⟩
  have hbound' : start + length ≤ C.coreCells :=
    of_decide_eq_true hbound
  rw [List.all_eq_true] at hnodes
  refine ⟨hbound', ?_⟩
  intro k hk
  have hnode := hnodes k (by simpa using hk)
  rw [Bool.and_eq_true] at hnode
  exact ⟨hnode.1, of_decide_eq_true hnode.2⟩

/-- Exact proposition certified by one successful outer chunk check. -/
theorem outerChunkCheck_sound
    {C : Cell} {start length : ℕ} {upper : ℚ}
    (hcheck : outerChunkCheck C start length upper = true) :
    start + length ≤ C.outerCells ∧
      ∀ k < length,
        outerScaledIntegrandSafe C (start + k) = true ∧
        outerCellUpper C (start + k) ≤ upper := by
  unfold outerChunkCheck at hcheck
  rw [Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨hbound, hnodes⟩
  have hbound' : start + length ≤ C.outerCells :=
    of_decide_eq_true hbound
  rw [List.all_eq_true] at hnodes
  refine ⟨hbound', ?_⟩
  intro k hk
  have hnode := hnodes k (by simpa using hk)
  rw [Bool.and_eq_true] at hnode
  exact ⟨hnode.1, of_decide_eq_true hnode.2⟩

/-- Exact proposition certified by one successful core exact-sum chunk. -/
theorem coreExactChunkCheck_sound
    {C : Cell} {start length : ℕ} {total : ℚ}
    (hcheck : coreExactChunkCheck C start length total = true) :
    start + length ≤ C.coreCells ∧
      (∀ k < length,
        (if start + k = 0 then true
          else coreIntegrandSafe C (start + k)) = true) ∧
      coreChunkSum C start length = total := by
  unfold coreExactChunkCheck at hcheck
  rw [Bool.and_eq_true, Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨⟨hbound, hnodes⟩, hsum⟩
  refine ⟨of_decide_eq_true hbound, ?_,
    of_decide_eq_true hsum⟩
  rw [List.all_eq_true] at hnodes
  intro k hk
  exact hnodes k (by simpa using hk)

/-- Exact proposition certified by one selected-core exact-sum chunk. -/
theorem chosenCoreExactChunkCheck_sound
    {C : Cell} {choices : ℕ → CoreChoice}
    {start length : ℕ} {total : ℚ}
    (hcheck :
      chosenCoreExactChunkCheck C choices start length total = true) :
    start + length ≤ C.coreCells ∧
      (∀ k < length,
        (if start + k = 0 then true
          else chosenCoreIntegrandSafe C
            (choices (start + k)) (start + k)) = true) ∧
      chosenCoreChunkSum C choices start length = total := by
  unfold chosenCoreExactChunkCheck at hcheck
  rw [Bool.and_eq_true, Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨⟨hbound, hnodes⟩, hsum⟩
  refine ⟨of_decide_eq_true hbound, ?_,
    of_decide_eq_true hsum⟩
  rw [List.all_eq_true] at hnodes
  intro k hk
  exact hnodes k (by simpa using hk)

/-- Exact proposition certified by one successful outer exact-sum chunk. -/
theorem outerExactChunkCheck_sound
    {C : Cell} {start length : ℕ} {total : ℚ}
    (hcheck : outerExactChunkCheck C start length total = true) :
    start + length ≤ C.outerCells ∧
      (∀ k < length,
        outerScaledIntegrandSafe C (start + k) = true) ∧
      outerChunkSum C start length = total := by
  unfold outerExactChunkCheck at hcheck
  rw [Bool.and_eq_true, Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨⟨hbound, hnodes⟩, hsum⟩
  refine ⟨of_decide_eq_true hbound, ?_,
    of_decide_eq_true hsum⟩
  rw [List.all_eq_true] at hnodes
  intro k hk
  exact hnodes k (by simpa using hk)

private theorem foldl_range_add_eq_finsetSum
    {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (n : ℕ) :
    (List.range n).foldl (fun acc i => acc + f i) 0 =
      ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append,
        Finset.sum_range_succ, ih]
      simp

/--
Split a range sum into equally sized consecutive blocks.  This is the
structural aggregation lemma behind grouped rectangle bounds.
-/
theorem sum_range_mul_eq_sum_blocks
    {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (q m : ℕ) :
    (∑ i ∈ Finset.range (q * m), f i) =
      ∑ j ∈ Finset.range m,
        ∑ k ∈ Finset.range q, f (j * q + k) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ← ih]
      have hsplit :=
        Finset.sum_range_add_sum_Ico f
          (Nat.mul_le_mul_left q (Nat.le_succ m))
      rw [← hsplit]
      congr 1
      rw [Finset.sum_Ico_eq_sum_range]
      have hdiff : q * (m + 1) - q * m = q := by
        simp [Nat.mul_add]
      rw [hdiff]
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      simp [Nat.mul_comm]

private theorem sum_range_getD_eq_sum (l : List ℚ) :
    (∑ j ∈ Finset.range l.length, l.getD j 0) = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.length_cons]
      rw [Finset.sum_range_succ']
      simp only [List.getD_cons_zero, List.getD_cons_succ,
        List.sum_cons, ih]
      ring

/--
Uniform core chunks bound the exact reflected core rectangle sum.  The
supplied list contains one upper bound per chunk.
-/
theorem coreIntegralUpper_le_grouped
    {C : Cell} {q : ℕ} {bounds : List ℚ}
    (hcutoff : 0 ≤ C.cutoff)
    (hcount : C.coreCells = q * bounds.length)
    (hchunks : ∀ j (hj : j < bounds.length),
      coreChunkCheck C (j * q) q bounds[j] = true) :
    coreIntegralUpper C ≤
      coreGroupedUpper C q bounds := by
  unfold coreGroupedUpper
  have hpoint :
      ∀ j (hj : j < bounds.length) k (hk : k < q),
        coreCellUpper C (j * q + k) ≤ bounds[j] := by
    intro j hj k hk
    exact (coreChunkCheck_sound (hchunks j hj)).2 k hk |>.2
  unfold coreIntegralUpper
  rw [foldl_range_add_eq_finsetSum, hcount,
    sum_range_mul_eq_sum_blocks]
  apply mul_le_mul_of_nonneg_left
  · calc
      (∑ j ∈ Finset.range bounds.length,
          ∑ k ∈ Finset.range q,
            coreCellUpper C (j * q + k)) ≤
          ∑ j ∈ Finset.range bounds.length,
            ∑ _k ∈ Finset.range q, bounds.getD j 0 := by
              apply Finset.sum_le_sum
              intro j hj
              apply Finset.sum_le_sum
              intro k hk
              have hj' : j < bounds.length := by simpa using hj
              simpa only [List.getD_eq_getElem bounds 0 hj'] using
                hpoint j hj' k (by simpa using hk)
      _ = q * bounds.sum := by
        simp only [Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        rw [← Finset.mul_sum, sum_range_getD_eq_sum]
  · positivity

/-- Uniform checked core chunks supply every local core safety premise. -/
theorem coreSafe_of_uniformChunks
    {C : Cell} {q : ℕ} {bounds : List ℚ}
    (hq : 0 < q)
    (hcount : C.coreCells = q * bounds.length)
    (hchunks : ∀ j (hj : j < bounds.length),
      coreChunkCheck C (j * q) q bounds[j] = true) :
    ∀ i < C.coreCells,
      (if i = 0 then true else coreIntegrandSafe C i) = true := by
  intro i hi
  let j := i / q
  let k := i % q
  have hk : k < q := Nat.mod_lt i hq
  have hj : j < bounds.length := by
    apply (Nat.div_lt_iff_lt_mul hq).2
    rw [← Nat.mul_comm q bounds.length, ← hcount]
    exact hi
  have hs :=
    (coreChunkCheck_sound (hchunks j hj)).2 k hk |>.1
  have hindex : j * q + k = i := by
    dsimp only [j, k]
    simpa [Nat.mul_comm] using Nat.div_add_mod i q
  simpa only [hindex] using hs

/--
Uniform outer chunks bound the exact reflected outer rectangle sum.
-/
theorem outerIntegralUpper_le_grouped
    {C : Cell} {q : ℕ} {bounds : List ℚ}
    (hhi : 0 ≤ C.hi)
    (hband : C.cutoff ≤ C.bandwidth)
    (hcount : C.outerCells = q * bounds.length)
    (hchunks : ∀ j (hj : j < bounds.length),
      outerChunkCheck C (j * q) q bounds[j] = true) :
    outerIntegralUpper C ≤
      outerGroupedUpper C q bounds := by
  unfold outerGroupedUpper
  have hpoint :
      ∀ j (hj : j < bounds.length) k (hk : k < q),
        outerCellUpper C (j * q + k) ≤ bounds[j] := by
    intro j hj k hk
    exact (outerChunkCheck_sound (hchunks j hj)).2 k hk |>.2
  unfold outerIntegralUpper
  dsimp only
  rw [foldl_range_add_eq_finsetSum, hcount,
    sum_range_mul_eq_sum_blocks]
  apply mul_le_mul_of_nonneg_left
  · calc
      (∑ j ∈ Finset.range bounds.length,
          ∑ k ∈ Finset.range q,
            outerCellUpper C (j * q + k)) ≤
          ∑ j ∈ Finset.range bounds.length,
            ∑ _k ∈ Finset.range q, bounds.getD j 0 := by
              apply Finset.sum_le_sum
              intro j hj
              apply Finset.sum_le_sum
              intro k hk
              have hj' : j < bounds.length := by simpa using hj
              simpa only [List.getD_eq_getElem bounds 0 hj'] using
                hpoint j hj' k (by simpa using hk)
      _ = q * bounds.sum := by
        simp only [Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        rw [← Finset.mul_sum, sum_range_getD_eq_sum]
  · have hwidth : 0 ≤
        2 * C.hi * C.bandwidth - 2 * C.hi * C.cutoff := by
      nlinarith
    positivity

/-- Uniform checked outer chunks supply every local outer safety premise. -/
theorem outerSafe_of_uniformChunks
    {C : Cell} {q : ℕ} {bounds : List ℚ}
    (hq : 0 < q)
    (hcount : C.outerCells = q * bounds.length)
    (hchunks : ∀ j (hj : j < bounds.length),
      outerChunkCheck C (j * q) q bounds[j] = true) :
    ∀ i < C.outerCells,
      outerScaledIntegrandSafe C i = true := by
  intro i hi
  let j := i / q
  let k := i % q
  have hk : k < q := Nat.mod_lt i hq
  have hj : j < bounds.length := by
    apply (Nat.div_lt_iff_lt_mul hq).2
    rw [← Nat.mul_comm q bounds.length, ← hcount]
    exact hi
  have hs :=
    (outerChunkCheck_sound (hchunks j hj)).2 k hk |>.1
  have hindex : j * q + k = i := by
    dsimp only [j, k]
    simpa [Nat.mul_comm] using Nat.div_add_mod i q
  simpa only [hindex] using hs

/-- Exact core chunks reconstruct the original reflected core quadrature. -/
theorem coreIntegralUpper_eq_exactChunks
    {C : Cell} {q : ℕ} {totals : List ℚ}
    (hcount : C.coreCells = q * totals.length)
    (hchunks : ∀ j (hj : j < totals.length),
      coreExactChunkCheck C (j * q) q totals[j] = true) :
    coreIntegralUpper C =
      (C.cutoff / C.coreCells) * totals.sum := by
  have hblock :
      ∀ j (hj : j < totals.length),
        (∑ k ∈ Finset.range q,
          coreCellUpper C (j * q + k)) = totals[j] := by
    intro j hj
    have hsum :=
      (coreExactChunkCheck_sound (hchunks j hj)).2.2
    unfold coreChunkSum at hsum
    rw [foldl_range_add_eq_finsetSum] at hsum
    exact hsum
  unfold coreIntegralUpper
  rw [foldl_range_add_eq_finsetSum, hcount,
    sum_range_mul_eq_sum_blocks]
  congr 1
  calc
    (∑ j ∈ Finset.range totals.length,
        ∑ k ∈ Finset.range q,
          coreCellUpper C (j * q + k)) =
        ∑ j ∈ Finset.range totals.length,
          totals.getD j 0 := by
            apply Finset.sum_congr rfl
            intro j hj
            have hj' : j < totals.length := by simpa using hj
            rw [List.getD_eq_getElem totals 0 hj']
            exact hblock j hj'
    _ = totals.sum := sum_range_getD_eq_sum totals

/--
Selected exact core chunks reconstruct the granular reflected core
quadrature.
-/
theorem chosenCoreIntegralUpper_eq_exactChunks
    {C : Cell} {choices : ℕ → CoreChoice}
    {q : ℕ} {totals : List ℚ}
    (hcount : C.coreCells = q * totals.length)
    (hchunks : ∀ j (hj : j < totals.length),
      chosenCoreExactChunkCheck C choices
        (j * q) q totals[j] = true) :
    chosenCoreIntegralUpper C choices =
      (C.cutoff / C.coreCells) * totals.sum := by
  have hblock :
      ∀ j (hj : j < totals.length),
        (∑ k ∈ Finset.range q,
          chosenCoreCellUpper C
            (choices (j * q + k)) (j * q + k)) = totals[j] := by
    intro j hj
    have hsum :=
      (chosenCoreExactChunkCheck_sound
        (hchunks j hj)).2.2
    unfold chosenCoreChunkSum at hsum
    rw [foldl_range_add_eq_finsetSum] at hsum
    exact hsum
  unfold chosenCoreIntegralUpper
  rw [foldl_range_add_eq_finsetSum, hcount,
    sum_range_mul_eq_sum_blocks]
  congr 1
  calc
    (∑ j ∈ Finset.range totals.length,
        ∑ k ∈ Finset.range q,
          chosenCoreCellUpper C
            (choices (j * q + k)) (j * q + k)) =
        ∑ j ∈ Finset.range totals.length,
          totals.getD j 0 := by
            apply Finset.sum_congr rfl
            intro j hj
            have hj' : j < totals.length := by simpa using hj
            rw [List.getD_eq_getElem totals 0 hj']
            exact hblock j hj'
    _ = totals.sum := sum_range_getD_eq_sum totals

/-- Exact outer chunks reconstruct the original reflected outer quadrature. -/
theorem outerIntegralUpper_eq_exactChunks
    {C : Cell} {q : ℕ} {totals : List ℚ}
    (hcount : C.outerCells = q * totals.length)
    (hchunks : ∀ j (hj : j < totals.length),
      outerExactChunkCheck C (j * q) q totals[j] = true) :
    outerIntegralUpper C =
      ((2 * C.hi * C.bandwidth - 2 * C.hi * C.cutoff) /
        C.outerCells) * totals.sum := by
  have hblock :
      ∀ j (hj : j < totals.length),
        (∑ k ∈ Finset.range q,
          outerCellUpper C (j * q + k)) = totals[j] := by
    intro j hj
    have hsum :=
      (outerExactChunkCheck_sound (hchunks j hj)).2.2
    unfold outerChunkSum at hsum
    rw [foldl_range_add_eq_finsetSum] at hsum
    exact hsum
  unfold outerIntegralUpper
  dsimp only
  rw [foldl_range_add_eq_finsetSum, hcount,
    sum_range_mul_eq_sum_blocks]
  congr 1
  calc
    (∑ j ∈ Finset.range totals.length,
        ∑ k ∈ Finset.range q,
          outerCellUpper C (j * q + k)) =
        ∑ j ∈ Finset.range totals.length,
          totals.getD j 0 := by
            apply Finset.sum_congr rfl
            intro j hj
            have hj' : j < totals.length := by simpa using hj
            rw [List.getD_eq_getElem totals 0 hj']
            exact hblock j hj'
    _ = totals.sum := sum_range_getD_eq_sum totals

/-- Exact checked core chunks supply every local core safety premise. -/
theorem coreSafe_of_exactChunks
    {C : Cell} {q : ℕ} {totals : List ℚ}
    (hq : 0 < q)
    (hcount : C.coreCells = q * totals.length)
    (hchunks : ∀ j (hj : j < totals.length),
      coreExactChunkCheck C (j * q) q totals[j] = true) :
    ∀ i < C.coreCells,
      (if i = 0 then true else coreIntegrandSafe C i) = true := by
  intro i hi
  let j := i / q
  let k := i % q
  have hk : k < q := Nat.mod_lt i hq
  have hj : j < totals.length := by
    apply (Nat.div_lt_iff_lt_mul hq).2
    rw [← Nat.mul_comm q totals.length, ← hcount]
    exact hi
  have hs :=
    (coreExactChunkCheck_sound (hchunks j hj)).2.1 k hk
  have hindex : j * q + k = i := by
    dsimp only [j, k]
    simpa [Nat.mul_comm] using Nat.div_add_mod i q
  simpa only [hindex] using hs

/-- Selected exact core chunks supply every local core safety premise. -/
theorem chosenCoreSafe_of_exactChunks
    {C : Cell} {choices : ℕ → CoreChoice}
    {q : ℕ} {totals : List ℚ}
    (hq : 0 < q)
    (hcount : C.coreCells = q * totals.length)
    (hchunks : ∀ j (hj : j < totals.length),
      chosenCoreExactChunkCheck C choices
        (j * q) q totals[j] = true) :
    ∀ i < C.coreCells,
      (if i = 0 then true
        else chosenCoreIntegrandSafe C (choices i) i) = true := by
  intro i hi
  let j := i / q
  let k := i % q
  have hk : k < q := Nat.mod_lt i hq
  have hj : j < totals.length := by
    apply (Nat.div_lt_iff_lt_mul hq).2
    rw [← Nat.mul_comm q totals.length, ← hcount]
    exact hi
  have hs :=
    (chosenCoreExactChunkCheck_sound
      (hchunks j hj)).2.1 k hk
  have hindex : j * q + k = i := by
    dsimp only [j, k]
    simpa [Nat.mul_comm] using Nat.div_add_mod i q
  simpa only [hindex] using hs

/-- Exact checked outer chunks supply every local outer safety premise. -/
theorem outerSafe_of_exactChunks
    {C : Cell} {q : ℕ} {totals : List ℚ}
    (hq : 0 < q)
    (hcount : C.outerCells = q * totals.length)
    (hchunks : ∀ j (hj : j < totals.length),
      outerExactChunkCheck C (j * q) q totals[j] = true) :
    ∀ i < C.outerCells,
      outerScaledIntegrandSafe C i = true := by
  intro i hi
  let j := i / q
  let k := i % q
  have hk : k < q := Nat.mod_lt i hq
  have hj : j < totals.length := by
    apply (Nat.div_lt_iff_lt_mul hq).2
    rw [← Nat.mul_comm q totals.length, ← hcount]
    exact hi
  have hs :=
    (outerExactChunkCheck_sound (hchunks j hj)).2.1 k hk
  have hindex : j * q + k = i := by
    dsimp only [j, k]
    simpa [Nat.mul_comm] using Nat.div_add_mod i q
  simpa only [hindex] using hs

/--
Uniform grouped-max chunks are a complete semantic cell certificate.  The
only final arithmetic claim is over the short lists of chunk maxima.
-/
theorem cellCertified_of_uniformChunks
    {C : Cell}
    {coreQ outerQ : ℕ}
    {coreBounds outerBounds : List ℚ}
    (hgeometry : geometryCheck C = true)
    (hcoreQ : 0 < coreQ) (houterQ : 0 < outerQ)
    (hcoreCount :
      C.coreCells = coreQ * coreBounds.length)
    (houterCount :
      C.outerCells = outerQ * outerBounds.length)
    (hcoreChunks : ∀ j (hj : j < coreBounds.length),
      coreChunkCheck C (j * coreQ) coreQ
        coreBounds[j] = true)
    (houterChunks : ∀ j (hj : j < outerBounds.length),
      outerChunkCheck C (j * outerQ) outerQ
        outerBounds[j] = true)
    (hfinal :
      2 * coreGroupedUpper C coreQ coreBounds +
          2 * outerGroupedUpper C outerQ outerBounds +
          gaussianBudgetUpper C <
        cellTarget C) :
    CellCertified C := by
  rcases geometryCheck_sound hgeometry with
    ⟨hlo, hlohi, _hratio, hcutoff, hcut, _⟩
  refine ⟨by exact_mod_cast hcutoff,
    by exact_mod_cast hcut, ?_⟩
  intro L hL hLb
  have hcoreEval :
      coreIntegralUpper C ≤
        coreGroupedUpper C coreQ coreBounds :=
    coreIntegralUpper_le_grouped hcutoff.le
      hcoreCount hcoreChunks
  have houterEval :
      outerIntegralUpper C ≤
        outerGroupedUpper C outerQ outerBounds :=
    outerIntegralUpper_le_grouped
      (hlo.le.trans hlohi) hcut
      houterCount houterChunks
  exact
    tyurinRationalDStar_lt_three_fifths_of_reflectedBounds
      hgeometry
      (coreSafe_of_uniformChunks hcoreQ
        hcoreCount hcoreChunks)
      (outerSafe_of_uniformChunks houterQ
        houterCount houterChunks)
      hcoreEval houterEval le_rfl hfinal hL hLb

/--
Exact-sum chunks preserve the original rectangle budget while keeping every
kernel replay bounded by one small chunk.
-/
theorem cellCertified_of_exactChunks
    {C : Cell}
    {coreQ outerQ : ℕ}
    {coreTotals outerTotals : List ℚ}
    (hgeometry : geometryCheck C = true)
    (hcoreQ : 0 < coreQ) (houterQ : 0 < outerQ)
    (hcoreCount :
      C.coreCells = coreQ * coreTotals.length)
    (houterCount :
      C.outerCells = outerQ * outerTotals.length)
    (hcoreChunks : ∀ j (hj : j < coreTotals.length),
      coreExactChunkCheck C (j * coreQ) coreQ
        coreTotals[j] = true)
    (houterChunks : ∀ j (hj : j < outerTotals.length),
      outerExactChunkCheck C (j * outerQ) outerQ
        outerTotals[j] = true)
    (hfinal :
      2 * ((C.cutoff / C.coreCells) * coreTotals.sum) +
          2 * (((2 * C.hi * C.bandwidth -
              2 * C.hi * C.cutoff) / C.outerCells) *
            outerTotals.sum) +
          gaussianBudgetUpper C <
        cellTarget C) :
    CellCertified C := by
  rcases geometryCheck_sound hgeometry with
    ⟨_hlo, _hlohi, _hratio, hcutoff, hcut, _⟩
  refine ⟨by exact_mod_cast hcutoff,
    by exact_mod_cast hcut, ?_⟩
  intro L hL hLb
  have hcoreEval :=
    coreIntegralUpper_eq_exactChunks
      hcoreCount hcoreChunks
  have houterEval :=
    outerIntegralUpper_eq_exactChunks
      houterCount houterChunks
  exact
    tyurinRationalDStar_lt_three_fifths_of_reflectedBounds
      hgeometry
      (coreSafe_of_exactChunks hcoreQ
        hcoreCount hcoreChunks)
      (outerSafe_of_exactChunks houterQ
        houterCount houterChunks)
      hcoreEval.le houterEval.le le_rfl hfinal hL hLb

/--
Selected exact core chunks and ordinary exact outer chunks form a complete
semantic cell certificate while avoiding all discarded core envelopes.
-/
theorem cellCertified_of_chosenExactChunks
    {C : Cell} {choices : ℕ → CoreChoice}
    {coreQ outerQ : ℕ}
    {coreTotals outerTotals : List ℚ}
    (hgeometry : geometryCheck C = true)
    (hcoreQ : 0 < coreQ) (houterQ : 0 < outerQ)
    (hcoreCount :
      C.coreCells = coreQ * coreTotals.length)
    (houterCount :
      C.outerCells = outerQ * outerTotals.length)
    (hcoreChunks : ∀ j (hj : j < coreTotals.length),
      chosenCoreExactChunkCheck C choices
        (j * coreQ) coreQ coreTotals[j] = true)
    (houterChunks : ∀ j (hj : j < outerTotals.length),
      outerExactChunkCheck C (j * outerQ) outerQ
        outerTotals[j] = true)
    (hfinal :
      2 * ((C.cutoff / C.coreCells) * coreTotals.sum) +
          2 * (((2 * C.hi * C.bandwidth -
              2 * C.hi * C.cutoff) / C.outerCells) *
            outerTotals.sum) +
          gaussianBudgetUpper C <
        cellTarget C) :
    CellCertified C := by
  rcases geometryCheck_sound hgeometry with
    ⟨_hlo, _hlohi, _hratio, hcutoff, hcut, _⟩
  refine ⟨by exact_mod_cast hcutoff,
    by exact_mod_cast hcut, ?_⟩
  intro L hL hLb
  have hcoreEval :=
    chosenCoreIntegralUpper_eq_exactChunks
      hcoreCount hcoreChunks
  have houterEval :=
    outerIntegralUpper_eq_exactChunks
      houterCount houterChunks
  exact
    tyurinRationalDStar_lt_three_fifths_of_chosenReflectedBounds
      choices hgeometry
      (chosenCoreSafe_of_exactChunks hcoreQ
        hcoreCount hcoreChunks)
      (outerSafe_of_exactChunks houterQ
        houterCount houterChunks)
      hcoreEval.le houterEval.le le_rfl hfinal hL hLb

end TyurinModerate
end CertifiedJL
