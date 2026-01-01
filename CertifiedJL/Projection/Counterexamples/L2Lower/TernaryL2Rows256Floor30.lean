/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Finite.Counting
import CertifiedJL.Projection.Counterexamples.Shared.SparseAllOnesRow
import CertifiedJL.Statements.L2.Lower
import Mathlib.Tactic

/-!
# The 256-row threshold-floor-30 obstruction

The explicit input `w = (1000, 1)`, public threshold `b = 1000`, and modulus
`q = 2^32 - 99` satisfy both modulus margins `3` and `125`.  A finite seed
event forces the strict projected-energy inequality `energy < 30 * b^2` and
has probability greater than `2^-127` (hence greater than `2^-128`).
-/

open scoped BigOperators ENNReal

namespace CertifiedJL.Counterexamples.TernaryL2Rows256Floor30

open Probability

def modulus : ℕ := 2 ^ 32 - 99

def inputThreshold : ℕ := 1000

def witness : Fin 2 → ℤ := ![1000, 1]

def parametersMarginThree : L2ThresholdLowerParameters :=
  { distribution := .balancedTernary
    rows := 256
    squaredNormFloor := NonnegativeRatio.ofNat 30
    modulusMargin := NonnegativeRatio.ofNat 3 }

def parametersMargin125 : L2ThresholdLowerParameters :=
  { distribution := .balancedTernary
    rows := 256
    squaredNormFloor := NonnegativeRatio.ofNat 30
    modulusMargin := NonnegativeRatio.ofNat 125 }

/-! ## Exact seed count -/

/-- A row-wise seed decomposition adapted to the vector `(1000, 1)`. -/
@[ext]
structure LowerSeedView (rows : ℕ) where
  activity : Fin rows → Bool
  leadingSign : Fin rows → Bool
  tailSigns : Fin rows × Fin 2 → Bool
  deriving Fintype

def signTwist (sign bit : Bool) : Bool :=
  if sign then bit else !bit

@[simp]
theorem signTwist_self (sign bit : Bool) :
    signTwist sign (signTwist sign bit) = bit := by
  cases sign <;> cases bit <;> decide

@[simp]
theorem signBit_signTwist (sign bit : Bool) :
    signBit (signTwist sign bit) = signBit sign * signBit bit := by
  cases sign <;> cases bit <;> decide

def lowerSeedView (rows : ℕ) (seed : SparseSeed rows 2) : LowerSeedView rows where
  activity row := decide ((seed row 0).1 = (seed row 0).2)
  leadingSign row := (seed row 0).1
  tailSigns rowBit := signTwist (seed rowBit.1 0).1
    (pairBit (seed rowBit.1 1) rowBit.2)

def lowerSeedOfView (rows : ℕ) (view : LowerSeedView rows) : SparseSeed rows 2 :=
  fun row => ![
    (view.leadingSign row,
      if view.activity row then view.leadingSign row else !view.leadingSign row),
    bitPair (fun bit =>
      signTwist (view.leadingSign row) (view.tailSigns (row, bit)))]

theorem lowerSeedOfView_view (rows : ℕ) (seed : SparseSeed rows 2) :
    lowerSeedOfView rows (lowerSeedView rows seed) = seed := by
  funext row coordinate
  fin_cases coordinate
  · dsimp [lowerSeedOfView, lowerSeedView]
    have h (pair : Bool × Bool) :
        (pair.1, if decide (pair.1 = pair.2) then pair.1 else !pair.1) = pair := by
      rcases pair with ⟨left, right⟩
      cases left <;> cases right <;> decide
    exact h (seed row 0)
  · dsimp [lowerSeedOfView, lowerSeedView, bitPair, pairBit]
    simp

theorem lowerSeedView_ofView (rows : ℕ) (view : LowerSeedView rows) :
    lowerSeedView rows (lowerSeedOfView rows view) = view := by
  rcases view with ⟨activity, leadingSign, tailSigns⟩
  have hActivity :
      (lowerSeedView rows
        (lowerSeedOfView rows ⟨activity, leadingSign, tailSigns⟩)).activity =
        activity := by
    funext row
    dsimp [lowerSeedView, lowerSeedOfView]
    have h (active sign : Bool) :
        decide (sign = if active then sign else !sign) = active := by
      cases active <;> cases sign <;> decide
    exact h (activity row) (leadingSign row)
  have hLeading :
      (lowerSeedView rows
        (lowerSeedOfView rows ⟨activity, leadingSign, tailSigns⟩)).leadingSign =
        leadingSign := rfl
  have hTail :
      (lowerSeedView rows
        (lowerSeedOfView rows ⟨activity, leadingSign, tailSigns⟩)).tailSigns =
        tailSigns := by
    funext rowBit
    rcases rowBit with ⟨row, bit⟩
    fin_cases bit <;>
      simp [lowerSeedView, lowerSeedOfView, bitPair, pairBit]
  apply LowerSeedView.ext <;> assumption

def lowerSeedEquiv (rows : ℕ) : SparseSeed rows 2 ≃ LowerSeedView rows where
  toFun := lowerSeedView rows
  invFun := lowerSeedOfView rows
  left_inv := lowerSeedOfView_view rows
  right_inv := lowerSeedView_ofView rows

def activityCount {rows : ℕ} (view : LowerSeedView rows) : ℕ :=
  (boolSupport view.activity).card

def activeTailTrueCount {rows : ℕ} (view : LowerSeedView rows) : ℕ :=
  trueCountOn (fun rowBit : Fin rows × Fin 2 =>
    view.activity rowBit.1 = true) view.tailSigns

def countedWitness {rows : ℕ} (view : LowerSeedView rows) : Prop :=
  activityCount view < 30 ∨
    activityCount view = 30 ∧ activeTailTrueCount view < 30

instance countedWitnessDecidable {rows : ℕ} :
    DecidablePred (@countedWitness rows) := by
  intro view
  unfold countedWitness
  infer_instance

def lowerSeedViewProdEquiv (rows : ℕ) :
    LowerSeedView rows ≃
      (Fin rows → Bool) ×
        ((Fin rows → Bool) × (Fin rows × Fin 2 → Bool)) where
  toFun view := (view.activity, view.leadingSign, view.tailSigns)
  invFun value := ⟨value.1, value.2.1, value.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def activeIndexEquiv {rows : ℕ} (activity : Fin rows → Bool) :
    {rowBit : Fin rows × Fin 2 // activity rowBit.1 = true} ≃
      {row : Fin rows // activity row = true} × Fin 2 where
  toFun rowBit := (⟨rowBit.1.1, rowBit.2⟩, rowBit.1.2)
  invFun rowBit := ⟨(rowBit.1.1, rowBit.2), rowBit.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_activeIndex {rows : ℕ} (activity : Fin rows → Bool) :
    Fintype.card {rowBit : Fin rows × Fin 2 // activity rowBit.1 = true} =
      2 * (boolSupport activity).card := by
  rw [Fintype.card_congr (activeIndexEquiv activity),
    Fintype.card_prod, Fintype.card_fin, mul_comm]
  rw [Fintype.card_subtype]
  rfl

theorem card_inactiveIndex {rows : ℕ} (activity : Fin rows → Bool) :
    Fintype.card {rowBit : Fin rows × Fin 2 // ¬ activity rowBit.1 = true} =
      2 * rows - 2 * (boolSupport activity).card := by
  rw [Fintype.card_subtype_compl, card_activeIndex,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  rw [Nat.mul_comm rows 2]

theorem card_tailSigns_lt_of_activityCount
    {rows k : ℕ} (activity : Fin rows → Bool)
    (hactivity : (boolSupport activity).card = k) :
    Fintype.card
        {tail : Fin rows × Fin 2 → Bool //
          trueCountOn (fun rowBit : Fin rows × Fin 2 =>
            activity rowBit.1 = true) tail < k} =
      (∑ t ∈ Finset.range k, (2 * k).choose t) *
        2 ^ (2 * rows - 2 * k) := by
  rw [card_trueCountOn_lt, card_activeIndex, card_inactiveIndex, hactivity]

def boolCountLtEquiv {α : Type*} [Fintype α] (k : ℕ) :
    {f : α → Bool // (boolSupport f).card < k} ≃
      (t : Fin k) × {f : α → Bool // (boolSupport f).card = t} :=
  (Equiv.sigmaSubtypeFiberEquivSubtype
      (f := fun f : α → Bool => (boolSupport f).card)
      (p := fun f => (boolSupport f).card < k)
      (q := fun t : ℕ => t < k)
      (fun _ => Iff.rfl)).symm |>.trans
    (Equiv.sigmaCongrLeft Fin.equivSubtype).symm

theorem card_bool_true_count_lt
    (α : Type*) [Fintype α] [DecidableEq α] (k : ℕ) :
    Fintype.card {f : α → Bool // (boolSupport f).card < k} =
      ∑ t ∈ Finset.range k, (Fintype.card α).choose t := by
  rw [Fintype.card_congr (boolCountLtEquiv k), Fintype.card_sigma]
  simp_rw [card_bool_true_count]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro t ht
  rw [dif_pos (Finset.mem_range.mp ht)]

def lowerActivityLtEquiv (rows k : ℕ) :
    {view : LowerSeedView rows // activityCount view < k} ≃
      {activity : Fin rows → Bool // (boolSupport activity).card < k} ×
        ((Fin rows → Bool) × (Fin rows × Fin 2 → Bool)) :=
  (Equiv.subtypeEquiv (lowerSeedViewProdEquiv rows)
    fun _ => Iff.rfl).trans
      (subtypeProdLeftEquiv
        (fun activity : Fin rows → Bool =>
          (boolSupport activity).card < k))

theorem card_lowerActivityLt (rows k : ℕ) :
    Fintype.card {view : LowerSeedView rows // activityCount view < k} =
      (∑ t ∈ Finset.range k, rows.choose t) * 2 ^ (3 * rows) := by
  rw [Fintype.card_congr (lowerActivityLtEquiv rows k),
    Fintype.card_prod, card_bool_true_count_lt,
    Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin, Fintype.card_bool]
  ring

def lowerBoundaryEquiv (rows k : ℕ) :
    {view : LowerSeedView rows //
      activityCount view = k ∧ activeTailTrueCount view < k} ≃
      (activity : {activity : Fin rows → Bool //
          (boolSupport activity).card = k}) ×
        ((Fin rows → Bool) ×
          {tail : Fin rows × Fin 2 → Bool //
            trueCountOn (fun rowBit : Fin rows × Fin 2 =>
              activity.1 rowBit.1 = true) tail < k}) where
  toFun view :=
    ⟨⟨view.1.activity, view.2.1⟩, view.1.leadingSign,
      ⟨view.1.tailSigns, view.2.2⟩⟩
  invFun value :=
    ⟨⟨value.1.1, value.2.1, value.2.2.1⟩, value.1.2, value.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_lowerBoundary (rows k : ℕ) :
    Fintype.card {view : LowerSeedView rows //
      activityCount view = k ∧ activeTailTrueCount view < k} =
      rows.choose k * 2 ^ rows *
        ((∑ t ∈ Finset.range k, (2 * k).choose t) *
          2 ^ (2 * rows - 2 * k)) := by
  rw [Fintype.card_congr (lowerBoundaryEquiv rows k), Fintype.card_sigma]
  calc
    (∑ activity :
        {activity : Fin rows → Bool // (boolSupport activity).card = k},
        Fintype.card
          ((Fin rows → Bool) ×
            {tail : Fin rows × Fin 2 → Bool //
              trueCountOn (fun rowBit : Fin rows × Fin 2 =>
                activity.1 rowBit.1 = true) tail < k})) =
        ∑ _activity :
          {activity : Fin rows → Bool // (boolSupport activity).card = k},
          2 ^ rows *
            ((∑ t ∈ Finset.range k, (2 * k).choose t) *
              2 ^ (2 * rows - 2 * k)) := by
      apply Finset.sum_congr rfl
      intro activity _
      rw [Fintype.card_prod, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin,
        card_tailSigns_lt_of_activityCount activity.1 activity.2]
    _ = Fintype.card
          {activity : Fin rows → Bool // (boolSupport activity).card = k} *
          (2 ^ rows *
            ((∑ t ∈ Finset.range k, (2 * k).choose t) *
              2 ^ (2 * rows - 2 * k))) := by simp
    _ = _ := by
      rw [card_bool_true_count, Fintype.card_fin]
      ac_rfl

theorem card_countedWitness (rows : ℕ) :
    Fintype.card {view : LowerSeedView rows // countedWitness view} =
      (∑ k ∈ Finset.range 30, rows.choose k) * 2 ^ (3 * rows) +
        rows.choose 30 * 2 ^ rows *
          ((∑ t ∈ Finset.range 30, Nat.choose 60 t) *
            2 ^ (2 * rows - 60)) := by
  classical
  unfold countedWitness
  rw [Fintype.card_subtype_or_disjoint
    (fun view : LowerSeedView rows => activityCount view < 30)
    (fun view : LowerSeedView rows =>
      activityCount view = 30 ∧ activeTailTrueCount view < 30)]
  · rw [card_lowerActivityLt, card_lowerBoundary]
  · intro predicate hleft hright view hview
    exact (Nat.ne_of_lt (hleft view hview)) (hright view hview).1

theorem card_countedWitness_seed (rows : ℕ) :
    Fintype.card
        {seed : SparseSeed rows 2 // countedWitness (lowerSeedView rows seed)} =
      (∑ k ∈ Finset.range 30, rows.choose k) * 2 ^ (3 * rows) +
        rows.choose 30 * 2 ^ rows *
          ((∑ t ∈ Finset.range 30, Nat.choose 60 t) *
            2 ^ (2 * rows - 60)) := by
  let equivalence :
      {seed : SparseSeed rows 2 // countedWitness (lowerSeedView rows seed)} ≃
        {view : LowerSeedView rows // countedWitness view} :=
    Equiv.subtypeEquiv (lowerSeedEquiv rows) fun _ => Iff.rfl
  exact (Fintype.card_congr equivalence).trans (card_countedWitness rows)

/-! ## The counted event implies strict floor-30 failure -/

theorem witness_sqNorm : sqNorm witness = 1_000_001 := by
  norm_num [sqNorm, witness, Fin.sum_univ_two]

theorem witness_centered : CenteredInput modulus witness := by
  intro coordinate
  fin_cases coordinate <;>
    norm_num [witness, modulus, centeredInterval]

theorem rowDot_witness (seed : SparseSeed 256 2) (row : Fin 256) :
    rowDot (sparseMatrix seed) witness row =
      1000 * sparseBit (seed row 0) + sparseBit (seed row 1) := by
  simp [rowDot, sparseMatrix, sparseRow, witness, Fin.sum_univ_two]
  ring

theorem centered_rowDot_witness (seed : SparseSeed 256 2) (row : Fin 256) :
    centeredMod modulus (rowDot (sparseMatrix seed) witness row) =
      rowDot (sparseMatrix seed) witness row := by
  apply centeredMod_eq_self (by norm_num [modulus])
  rw [rowDot_witness]
  rcases hdominant : seed row 0 with ⟨dleft, dright⟩
  rcases htail : seed row 1 with ⟨tleft, tright⟩
  cases dleft <;> cases dright <;> cases tleft <;> cases tright <;>
    norm_num [sparseBit, modulus, centeredInterval]

theorem row_sq_le_activity (seed : SparseSeed 256 2) (row : Fin 256) :
    (rowDot (sparseMatrix seed) witness row).natAbs ^ 2 ≤
      if (lowerSeedView 256 seed).activity row = true then 1_002_001 else 1 := by
  rw [rowDot_witness]
  rcases hdominant : seed row 0 with ⟨dleft, dright⟩
  rcases htail : seed row 1 with ⟨tleft, tright⟩
  cases dleft <;> cases dright <;> cases tleft <;> cases tright <;>
    norm_num [hdominant, htail, sparseBit, lowerSeedView]

theorem projectionSqNorm_le_activity (seed : SparseSeed 256 2) :
    modularProjectionSqNorm modulus (sparseMatrix seed) witness ≤
      activityCount (lowerSeedView 256 seed) * 1_002_001 +
        (256 - activityCount (lowerSeedView 256 seed)) := by
  unfold modularProjectionSqNorm
  simp_rw [centered_rowDot_witness]
  calc
    (∑ row, (rowDot (sparseMatrix seed) witness row).natAbs ^ 2) ≤
        ∑ row, if (lowerSeedView 256 seed).activity row = true
          then 1_002_001 else 1 := by
      apply Finset.sum_le_sum
      intro row _
      exact row_sq_le_activity seed row
    _ = _ := by
      unfold activityCount boolSupport
      rw [Finset.sum_ite]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      have hpartition := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin 256)))
        (fun row => (lowerSeedView 256 seed).activity row = true)
      rw [Finset.card_univ, Fintype.card_fin] at hpartition
      have hcomplement :
          (Finset.univ.filter fun row : Fin 256 =>
            ¬(lowerSeedView 256 seed).activity row = true).card =
          256 - (Finset.univ.filter fun row : Fin 256 =>
            (lowerSeedView 256 seed).activity row = true).card := by omega
      rw [hcomplement]
      norm_cast

def activeTailSignSum {rows : ℕ} (view : LowerSeedView rows) : ℤ :=
  ∑ rowBit, if view.activity rowBit.1 = true
    then signBit (view.tailSigns rowBit) else 0

theorem signBit_eq_indicator (bit : Bool) :
    signBit bit = 2 * (if bit = true then (1 : ℤ) else 0) - 1 := by
  cases bit <;> decide

theorem sum_signBit_on
    {α : Type*} [Fintype α]
    (predicate : α → Prop) [DecidablePred predicate] (bits : α → Bool) :
    ∑ i, (if predicate i then signBit (bits i) else 0) =
      2 * (trueCountOn predicate bits : ℤ) -
        Fintype.card {i // predicate i} := by
  classical
  calc
    (∑ i, if predicate i then signBit (bits i) else 0) =
        ∑ i ∈ Finset.univ.filter predicate, signBit (bits i) := by
      rw [Finset.sum_filter]
    _ = ∑ i ∈ Finset.univ.filter predicate,
          (2 * (if bits i = true then (1 : ℤ) else 0) - 1) := by
      apply Finset.sum_congr rfl
      intro i _
      exact signBit_eq_indicator (bits i)
    _ = 2 * (∑ i ∈ Finset.univ.filter predicate,
          (if bits i = true then (1 : ℤ) else 0)) -
          (Finset.univ.filter predicate).card := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp
    _ = 2 * (trueCountOn predicate bits : ℤ) -
          Fintype.card {i // predicate i} := by
      rw [Fintype.card_subtype]
      unfold trueCountOn
      congr 1
      rw [← Finset.sum_filter]
      have hfilter :
          (Finset.univ.filter predicate).filter (fun i => bits i = true) =
            Finset.univ.filter (fun i => predicate i ∧ bits i = true) := by
        ext i
        simp
      rw [hfilter]
      simp

theorem activeTailSignSum_eq {rows : ℕ} (view : LowerSeedView rows) :
    activeTailSignSum view =
      2 * (activeTailTrueCount view : ℤ) - 2 * activityCount view := by
  unfold activeTailSignSum activeTailTrueCount
  rw [sum_signBit_on, card_activeIndex]
  norm_cast

theorem row_sq_le_cross (seed : SparseSeed 256 2) (row : Fin 256) :
    (rowDot (sparseMatrix seed) witness row) ^ 2 ≤
      1_000_000 *
          (if (lowerSeedView 256 seed).activity row = true then (1 : ℤ) else 0) +
        1000 * (∑ bit : Fin 2,
          if (lowerSeedView 256 seed).activity row = true
          then signBit ((lowerSeedView 256 seed).tailSigns (row, bit))
          else 0) + 1 := by
  rw [rowDot_witness]
  rcases hdominant : seed row 0 with ⟨dleft, dright⟩
  rcases htail : seed row 1 with ⟨tleft, tright⟩
  cases dleft <;> cases dright <;> cases tleft <;> cases tright <;>
    norm_num [hdominant, htail, sparseBit, lowerSeedView,
      signTwist, pairBit, Fin.sum_univ_two, signBit]

theorem sum_activity_indicator {rows : ℕ} (view : LowerSeedView rows) :
    ∑ row, (if view.activity row = true then (1 : ℤ) else 0) =
      activityCount view := by
  unfold activityCount boolSupport
  rw [← Finset.sum_filter]
  simp

theorem projectionSqNorm_le_cross (seed : SparseSeed 256 2) :
    (modularProjectionSqNorm modulus (sparseMatrix seed) witness : ℤ) ≤
      1_000_000 * activityCount (lowerSeedView 256 seed) +
        1000 * activeTailSignSum (lowerSeedView 256 seed) + 256 := by
  unfold modularProjectionSqNorm
  simp_rw [centered_rowDot_witness]
  calc
    (↑(∑ row, (rowDot (sparseMatrix seed) witness row).natAbs ^ 2) : ℤ) =
        ∑ row, (rowDot (sparseMatrix seed) witness row) ^ 2 := by
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro row _
      rw [Nat.cast_pow, Int.natCast_natAbs, sq_abs]
    _ ≤ ∑ row,
        (1_000_000 *
            (if (lowerSeedView 256 seed).activity row = true then (1 : ℤ) else 0) +
          1000 * (∑ bit : Fin 2,
            if (lowerSeedView 256 seed).activity row = true
            then signBit ((lowerSeedView 256 seed).tailSigns (row, bit))
            else 0) + 1) := by
      apply Finset.sum_le_sum
      intro row _
      exact row_sq_le_cross seed row
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
      rw [sum_activity_indicator]
      have htail :
          (∑ row, ∑ bit : Fin 2,
            if (lowerSeedView 256 seed).activity row = true
            then signBit ((lowerSeedView 256 seed).tailSigns (row, bit))
            else 0) = activeTailSignSum (lowerSeedView 256 seed) := by
        unfold activeTailSignSum
        rw [Fintype.sum_prod_type]
      rw [htail, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      norm_num

theorem failure_of_countedWitness (seed : SparseSeed 256 2)
    (hcounted : countedWitness (lowerSeedView 256 seed)) :
    L2ThresholdLowerFailure (NonnegativeRatio.ofNat 30) inputThreshold modulus witness
      (sparseMatrix seed) := by
  unfold L2ThresholdLowerFailure
  simp only [NonnegativeRatio.ofNat, one_mul, inputThreshold]
  rcases hcounted with hsmall | hboundary
  · have henergy := projectionSqNorm_le_activity seed
    omega
  · have henergy := projectionSqNorm_le_cross seed
    have hcross := activeTailSignSum_eq (lowerSeedView 256 seed)
    omega

/-! ## Probability and public obstruction -/

set_option maxRecDepth 10000 in
def countedWitnessNumerator : ℕ :=
  (∑ k ∈ Finset.range 30, Nat.choose 256 k) * 2 ^ 60 +
    Nat.choose 256 30 * (∑ t ∈ Finset.range 30, Nat.choose 60 t)

def chooseRec (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => chooseRec n k * (n - k) / (k + 1)

def choosePrefixSum (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => choosePrefixSum n k + chooseRec n k

theorem chooseRec_eq_choose (n k : ℕ) : chooseRec n k = Nat.choose n k := by
  induction k with
  | zero => simp [chooseRec]
  | succ k ih =>
      rw [chooseRec, ih]
      apply Nat.div_eq_of_eq_mul_right (by omega)
      simpa [Nat.mul_comm] using (Nat.choose_succ_right_eq n k).symm

theorem choosePrefixSum_eq_sum (n k : ℕ) :
    choosePrefixSum n k = ∑ i ∈ Finset.range k, Nat.choose n i := by
  induction k with
  | zero => simp [choosePrefixSum]
  | succ k ih =>
      rw [choosePrefixSum, ih, Finset.sum_range_succ, chooseRec_eq_choose]

set_option maxRecDepth 10000 in
theorem countedWitnessNumerator_gt :
    2 ^ 189 < countedWitnessNumerator := by
  have hchoose27 :
      Nat.choose 256 27 = 2335379345202966215744864529558086400 := by
    rw [Nat.choose_eq_fast_choose]
    decide +kernel
  have hchoose28 :
      Nat.choose 256 28 = 19100066787552830835913356331028635200 := by
    rw [Nat.choose_eq_fast_choose]
    decide +kernel
  have hchoose29 :
      Nat.choose 256 29 = 150166042329725704503042939430156166400 := by
    rw [Nat.choose_eq_fast_choose]
    decide +kernel
  have hchoose30 :
      Nat.choose 256 30 = 1136256386961591164073024908354848325760 := by
    rw [Nat.choose_eq_fast_choose]
    decide +kernel
  have hsum256 :
      171601488462481501554701160290742888000 ≤
        ∑ k ∈ Finset.range 30, Nat.choose 256 k := by
    rw [show (30 : ℕ) = 29 + 1 by norm_num, Finset.sum_range_succ,
      show (29 : ℕ) = 28 + 1 by norm_num, Finset.sum_range_succ,
      show (28 : ℕ) = 27 + 1 by norm_num, Finset.sum_range_succ,
      hchoose27, hchoose28, hchoose29]
    omega
  have hsum60 :
      7 * 2 ^ 56 + 11 * 2 ^ 50 ≤
        ∑ t ∈ Finset.range 30, Nat.choose 60 t := by
    simp_rw [Nat.choose_eq_fast_choose]
    decide +kernel
  unfold countedWitnessNumerator
  calc
    2 ^ 189 <
        171601488462481501554701160290742888000 * 2 ^ 60 +
          1136256386961591164073024908354848325760 *
            (7 * 2 ^ 56 + 11 * 2 ^ 50) := by norm_num
    _ ≤ _ := by
      rw [hchoose30]
      gcongr

set_option exponentiation.threshold 2048 in
theorem countedWitnessCard_eq :
    Fintype.card
        {seed : SparseSeed 256 2 // countedWitness (lowerSeedView 256 seed)} =
      countedWitnessNumerator * 2 ^ 708 := by
  rw [card_countedWitness_seed]
  have hpow768 : (2 : ℕ) ^ 768 = 2 ^ 60 * 2 ^ 708 := by
    rw [← pow_add]
  rw [hpow768]
  have hsecond :
      Nat.choose 256 30 * 2 ^ 256 *
          ((∑ t ∈ Finset.range 30, Nat.choose 60 t) * 2 ^ 452) =
        Nat.choose 256 30 *
          (∑ t ∈ Finset.range 30, Nat.choose 60 t) * 2 ^ 708 := by
    rw [show (708 : ℕ) = 256 + 452 by norm_num, pow_add]
    ring
  rw [hsecond]
  unfold countedWitnessNumerator
  ring

set_option exponentiation.threshold 2048 in
theorem sparseSeedCard : Fintype.card (SparseSeed 256 2) = 2 ^ 1024 := by
  rw [Probability.SparseAllOnes.card_sparseSeed]
  norm_num

set_option exponentiation.threshold 2048 in
set_option maxRecDepth 10000 in
theorem countedWitnessProbability_gt_127 :
    (Fintype.card
        {seed : SparseSeed 256 2 // countedWitness (lowerSeedView 256 seed)} : ℝ≥0∞) *
        (Fintype.card (SparseSeed 256 2) : ℝ≥0∞)⁻¹ > failureTarget 127 := by
  rw [countedWitnessCard_eq, sparseSeedCard]
  have hnumerator := countedWitnessNumerator_gt
  have hscaled :
      2 ^ 1024 < 2 ^ 127 * (countedWitnessNumerator * 2 ^ 708) := by
    calc
      2 ^ 1024 = 2 ^ 189 * 2 ^ 835 := by rw [show (1024 : ℕ) = 189 + 835 by norm_num, pow_add]
      _ < countedWitnessNumerator * 2 ^ 835 :=
        Nat.mul_lt_mul_of_pos_right hnumerator (pow_pos (by norm_num) _)
      _ = 2 ^ 127 * (countedWitnessNumerator * 2 ^ 708) := by
        rw [show (835 : ℕ) = 127 + 708 by norm_num, pow_add]
        ring
  change (2 : ℝ≥0∞)⁻¹ ^ 127 <
    (countedWitnessNumerator * 2 ^ 708 : ℕ) * ((2 ^ 1024 : ℕ) : ℝ≥0∞)⁻¹
  rw [← ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  field_simp
  exact_mod_cast hscaled

theorem failureProbability_gt_127 :
    eventProbability (sparseRademacherMatrix 256 2)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 30)
          inputThreshold modulus witness) > failureTarget 127 := by
  classical
  rw [sparseRademacherMatrix_eq_map_uniformSeed,
    eventProbability_map_uniform_eq_card]
  let countedSubtype :=
    {seed : SparseSeed 256 2 // countedWitness (lowerSeedView 256 seed)}
  let failureSubtype :=
    {seed : SparseSeed 256 2 //
      L2ThresholdLowerFailure (NonnegativeRatio.ofNat 30)
        inputThreshold modulus witness (sparseMatrix seed)}
  let embed : countedSubtype → failureSubtype :=
    fun seed => ⟨seed.1, failure_of_countedWitness seed.1 seed.2⟩
  have hinjective : Function.Injective embed := by
    intro left right heq
    apply Subtype.ext
    exact congrArg (fun value : failureSubtype => value.1) heq
  have hcard : Fintype.card countedSubtype ≤ Fintype.card failureSubtype :=
    Fintype.card_le_of_injective embed hinjective
  have hprobability :
      (Fintype.card countedSubtype : ℝ≥0∞) *
          (Fintype.card (SparseSeed 256 2) : ℝ≥0∞)⁻¹ ≤
        (Fintype.card failureSubtype : ℝ≥0∞) *
          (Fintype.card (SparseSeed 256 2) : ℝ≥0∞)⁻¹ := by gcongr
  exact countedWitnessProbability_gt_127.trans_le hprobability

theorem failureProbability_gt_128 :
    eventProbability (sparseRademacherMatrix 256 2)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 30)
          inputThreshold modulus witness) > failureTarget 128 := by
  exact (show failureTarget 128 < failureTarget 127 by
    rw [← ENNReal.toReal_lt_toReal
      (by simp [failureTarget]) (by simp [failureTarget])]
    norm_num [failureTarget]).trans failureProbability_gt_127

/-- The fixed witness meets the threshold-relative hypotheses for both the
new margin `3` and LaBRADOR's stronger historical margin `125`, and its strict
floor-30 failure probability is already greater than `2^-127`. -/
theorem admissible_witness :
    Odd modulus ∧
      CenteredInput modulus witness ∧
      0 < inputThreshold ∧
      InputThresholdAtMostNorm inputThreshold witness ∧
      InputThresholdWithinModulus (NonnegativeRatio.ofNat 3) modulus inputThreshold ∧
      InputThresholdWithinModulus (NonnegativeRatio.ofNat 125) modulus inputThreshold ∧
      eventProbability (sparseRademacherMatrix 256 2)
          (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 30)
            inputThreshold modulus witness) > failureTarget 127 := by
  refine ⟨by norm_num [modulus], witness_centered, by norm_num [inputThreshold], ?_,
    by norm_num [InputThresholdWithinModulus, NonnegativeRatio.ofNat,
      modulus, inputThreshold],
    by norm_num [InputThresholdWithinModulus, NonnegativeRatio.ofNat,
      modulus, inputThreshold], failureProbability_gt_127⟩
  norm_num [InputThresholdAtMostNorm, inputThreshold, witness_sqNorm]

theorem bits128_marginThree_false :
    ¬ L2ThresholdLowerTailAt parametersMarginThree (failureTarget 128) := by
  intro hclaimed
  have hbad := hclaimed modulus 2 witness inputThreshold
    admissible_witness.1 admissible_witness.2.1 admissible_witness.2.2.1
    admissible_witness.2.2.2.1 admissible_witness.2.2.2.2.1
  simp only [parametersMarginThree,
    ProjectionDistribution.matrixPMF_balancedTernary] at hbad
  exact (not_lt_of_ge failureProbability_gt_128.le) hbad

theorem bits128_margin125_false :
    ¬ L2ThresholdLowerTailAt parametersMargin125 (failureTarget 128) := by
  intro hclaimed
  have hbad := hclaimed modulus 2 witness inputThreshold
    admissible_witness.1 admissible_witness.2.1 admissible_witness.2.2.1
    admissible_witness.2.2.2.1 admissible_witness.2.2.2.2.2.1
  simp only [parametersMargin125,
    ProjectionDistribution.matrixPMF_balancedTernary] at hbad
  exact (not_lt_of_ge failureProbability_gt_128.le) hbad

end CertifiedJL.Counterexamples.TernaryL2Rows256Floor30
