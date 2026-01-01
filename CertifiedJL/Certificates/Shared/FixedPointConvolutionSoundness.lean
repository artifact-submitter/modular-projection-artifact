/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Shared.FixedPointConvolution

/-!
# Semantic soundness of directed convolution certificates

Fibers of an arbitrary finite statistic convolve under products. Combining
that counting fact with downward-rounded convolution yields a reusable
lower-approximation invariant for repeatedly doubled blocks of independent
finite samples. The statistic need not be a norm or squared norm.
-/

open scoped BigOperators

namespace CertifiedJL.FixedPointConvolution

universe u

def statisticMultiplicity {α : Type*} [Fintype α] (statistic : α → ℕ) (e : ℕ) : ℕ :=
  Fintype.card {x : α // statistic x = e}

def addStatistic {α β : Type*} (left : α → ℕ) (right : β → ℕ) : α × β → ℕ :=
  fun x => left x.1 + right x.2

def addStatisticFiberEquiv {α β : Type*} (left : α → ℕ) (right : β → ℕ)
    (e : ℕ) :
    {x : α × β // addStatistic left right x = e} ≃
      (i : Fin (e + 1)) ×
        ({x : α // left x = i} × {y : β // right y = e - i}) where
  toFun x :=
    ⟨⟨left x.1.1, by
        have := x.2
        simp only [addStatistic] at this
        omega⟩,
      ⟨⟨x.1.1, rfl⟩, ⟨x.1.2, by
        have := x.2
        simp only [addStatistic] at this
        exact Nat.eq_sub_of_add_eq' this⟩⟩⟩
  invFun x :=
    ⟨(x.2.1.1, x.2.2.1), by
      simp only [addStatistic]
      have hx := x.2.1.2
      have hy := x.2.2.2
      omega⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    rcases x with ⟨i, x, y⟩
    rcases i with ⟨i, hi⟩
    rcases x with ⟨x, hx⟩
    rcases y with ⟨y, hy⟩
    dsimp at hx hy ⊢
    subst i
    rfl

theorem statisticMultiplicity_addStatistic {α β : Type*} [Fintype α] [Fintype β]
    (left : α → ℕ) (right : β → ℕ) (e : ℕ) :
    statisticMultiplicity (addStatistic left right) e =
      ∑ i ∈ Finset.range (e + 1),
        statisticMultiplicity left i * statisticMultiplicity right (e - i) := by
  rw [statisticMultiplicity, Fintype.card_congr (addStatisticFiberEquiv left right e),
    Fintype.card_sigma, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dif_pos (Finset.mem_range.mp hi), Fintype.card_prod]
  rfl

theorem statisticMultiplicity_congr
    {α β : Type*} [Fintype α] [Fintype β]
    {left : α → ℕ} {right : β → ℕ} (equiv : α ≃ β)
    (hStatistic : ∀ x, right (equiv x) = left x) (e : ℕ) :
    statisticMultiplicity left e = statisticMultiplicity right e := by
  exact Fintype.card_congr
    (Equiv.subtypeEquiv equiv fun x => by rw [hStatistic])

abbrev Block (α : Type u) (n : ℕ) := Fin n → α

def blockStatisticSum {α : Type*} (statistic : α → ℕ) {n : ℕ}
    (block : Block α n) : ℕ :=
  ∑ i, statistic (block i)

def splitBlockEquiv (α : Type u) (n : ℕ) :
    Block α (n + n) ≃ Block α n × Block α n where
  toFun block :=
    (fun i => block (Fin.castAdd n i), fun i => block (Fin.natAdd n i))
  invFun blocks := Fin.addCases blocks.1 blocks.2
  left_inv block := by
    funext i
    apply Fin.addCases (motive := fun i =>
      Fin.addCases
        (fun j => block (Fin.castAdd n j))
        (fun j => block (Fin.natAdd n j)) i = block i)
    · intro j
      rw [Fin.addCases_left]
    · intro j
      rw [Fin.addCases_right]
  right_inv blocks := by
    rcases blocks with ⟨left, right⟩
    apply Prod.ext <;> funext i
    · change Fin.addCases left right (Fin.castAdd n i) = left i
      exact Fin.addCases_left i
    · change Fin.addCases left right (Fin.natAdd n i) = right i
      exact Fin.addCases_right i

theorem blockStatisticSum_splitBlockEquiv
    {α : Type*} (statistic : α → ℕ) (n : ℕ) (block : Block α (n + n)) :
    addStatistic (@blockStatisticSum α statistic n) (@blockStatisticSum α statistic n)
        (splitBlockEquiv α n block) =
      blockStatisticSum statistic block := by
  rw [blockStatisticSum, Fin.sum_univ_add]
  rfl

theorem statisticMultiplicity_blockStatisticSum_double
    {α : Type*} [Fintype α] (statistic : α → ℕ) (n e : ℕ) :
    statisticMultiplicity (@blockStatisticSum α statistic (n + n)) e =
      ∑ i ∈ Finset.range (e + 1),
        statisticMultiplicity (@blockStatisticSum α statistic n) i *
          statisticMultiplicity (@blockStatisticSum α statistic n) (e - i) := by
  rw [statisticMultiplicity_congr (splitBlockEquiv α n)
    (blockStatisticSum_splitBlockEquiv statistic n) e]
  exact statisticMultiplicity_addStatistic
    (@blockStatisticSum α statistic n) (@blockStatisticSum α statistic n) e

def LowerApproximation {α : Type*} [Fintype α]
    (cutoff denominator scale : ℕ) (statistic : α → ℕ)
    (values : List ℕ) : Prop :=
  values.length = cutoff ∧
    ∀ e < cutoff,
      values.getD e 0 * denominator ≤ statisticMultiplicity statistic e * scale

/-- Downward-rounded convolution preserves a directed lower approximation. -/
theorem LowerApproximation.squareRounded
    {α : Type*} [Fintype α]
    {cutoff denominator scale : ℕ}
    {statistic : α → ℕ} {input : List ℕ}
    (hscale : 0 < scale)
    (hinput : LowerApproximation cutoff denominator scale statistic input) :
    LowerApproximation cutoff (denominator * denominator) scale
      (addStatistic statistic statistic) (roundedConvolution cutoff scale input) := by
  constructor
  · exact length_roundedConvolution cutoff scale input
  · intro e he
    have hround :
        (roundedConvolution cutoff scale input).getD e 0 * scale ≤
          convolutionCoeff input input e := by
      rw [getD_roundedConvolution_of_lt he]
      exact Nat.div_mul_le_self _ _
    have hterm : ∀ i ∈ Finset.range (e + 1),
        input.getD i 0 * input.getD (e - i) 0 *
            (denominator * denominator) ≤
          (statisticMultiplicity statistic i * statisticMultiplicity statistic (e - i)) *
            (scale * scale) := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hiCutoff : i < cutoff := by omega
      have heiCutoff : e - i < cutoff := by omega
      have hleft := hinput.2 i hiCutoff
      have hright := hinput.2 (e - i) heiCutoff
      have hmul := Nat.mul_le_mul hleft hright
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul
    apply Nat.le_of_mul_le_mul_right (c := scale) _ hscale
    calc
      (roundedConvolution cutoff scale input).getD e 0 *
            (denominator * denominator) * scale =
          ((roundedConvolution cutoff scale input).getD e 0 * scale) *
            (denominator * denominator) := by ring
      _ ≤ convolutionCoeff input input e * (denominator * denominator) :=
        Nat.mul_le_mul_right _ hround
      _ = ∑ i ∈ Finset.range (e + 1),
          input.getD i 0 * input.getD (e - i) 0 *
            (denominator * denominator) := by
        rw [convolutionCoeff, Finset.sum_mul]
      _ ≤ ∑ i ∈ Finset.range (e + 1),
          (statisticMultiplicity statistic i * statisticMultiplicity statistic (e - i)) *
            (scale * scale) := Finset.sum_le_sum hterm
      _ = statisticMultiplicity (addStatistic statistic statistic) e * (scale * scale) := by
        rw [statisticMultiplicity_addStatistic, Finset.sum_mul]
      _ = (statisticMultiplicity (addStatistic statistic statistic) e * scale) * scale := by ring

theorem LowerApproximation.congr_statistic
    {α β : Type*} [Fintype α] [Fintype β]
    {cutoff denominator scale : ℕ} {left : α → ℕ} {right : β → ℕ}
    {values : List ℕ}
    (h : ∀ e, statisticMultiplicity left e = statisticMultiplicity right e)
    (happrox : LowerApproximation cutoff denominator scale left values) :
    LowerApproximation cutoff denominator scale right values := by
  refine ⟨happrox.1, ?_⟩
  intro e he
  rw [← h e]
  exact happrox.2 e he

/-- Block form of `LowerApproximation.squareRounded`. -/
theorem LowerApproximation.squareBlockRounded
    {α : Type*} [Fintype α]
    {cutoff denominator scale n : ℕ}
    {statistic : α → ℕ} {input : List ℕ}
    (hscale : 0 < scale)
    (hinput : LowerApproximation cutoff denominator scale
      (@blockStatisticSum α statistic n) input) :
    LowerApproximation cutoff (denominator * denominator) scale
      (@blockStatisticSum α statistic (n + n))
      (roundedConvolution cutoff scale input) := by
  apply LowerApproximation.congr_statistic
    (left := addStatistic (@blockStatisticSum α statistic n) (@blockStatisticSum α statistic n))
  · intro e
    exact (statisticMultiplicity_congr (splitBlockEquiv α n)
      (blockStatisticSum_splitBlockEquiv statistic n) e).symm
  · exact hinput.squareRounded hscale

def statisticLtEquivSigma {α : Type*} (statistic : α → ℕ) (cutoff : ℕ) :
    {x : α // statistic x < cutoff} ≃
      (e : Fin cutoff) × {x : α // statistic x = e} :=
  (Equiv.sigmaSubtypeFiberEquivSubtype
      (f := statistic)
      (p := fun x => statistic x < cutoff)
      (q := fun e : ℕ => e < cutoff)
      (fun _ => Iff.rfl)).symm |>.trans
    (Equiv.sigmaCongrLeft Fin.equivSubtype).symm

theorem card_statistic_lt {α : Type*} [Fintype α]
    (statistic : α → ℕ) (cutoff : ℕ) :
    Fintype.card {x : α // statistic x < cutoff} =
      ∑ e ∈ Finset.range cutoff, statisticMultiplicity statistic e := by
  rw [Fintype.card_congr (statisticLtEquivSigma statistic cutoff),
    Fintype.card_sigma, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro e he
  rw [dif_pos (Finset.mem_range.mp he)]
  rfl

theorem LowerApproximation.sum_le_card_statistic_lt_mul_scale
    {α : Type*} [Fintype α]
    {cutoff denominator scale : ℕ} {statistic : α → ℕ} {values : List ℕ}
    (h : LowerApproximation cutoff denominator scale statistic values) :
    values.sum * denominator ≤
      Fintype.card {x : α // statistic x < cutoff} * scale := by
  rw [card_statistic_lt]
  rw [Finset.sum_mul]
  have hvalues : values = List.ofFn fun e : Fin cutoff => values.getD e 0 := by
    calc
      values = List.ofFn values.get := (List.ofFn_get values).symm
      _ = List.ofFn fun e : Fin cutoff => values.getD e 0 := by
        apply List.ext_getElem
        · simp [h.1]
        · intro i hi₁ hi₂
          simp only [List.getElem_ofFn]
          have hi : i < values.length := by simpa using hi₁
          rw [List.getD_eq_getElem values 0 hi]
          exact List.get_eq_getElem
  rw [hvalues, List.sum_ofFn, Finset.sum_fin_eq_sum_range,
    Finset.sum_mul]
  apply Finset.sum_le_sum
  intro e he
  rw [dif_pos (Finset.mem_range.mp he)]
  exact h.2 e (Finset.mem_range.mp he)

/-- Cancel a common positive factor from a scaled counting lower bound. -/
theorem count_mul_pow_gt_of_scaled_lower
    {count mass denominator pivot bits scale : ℕ}
    (hpivot : 0 < pivot)
    (hdenominator : 0 < denominator)
    (hmass : pivot < mass)
    (hscaled : mass * denominator ≤ count * scale)
    (hscale : scale = pivot * 2 ^ bits) :
    denominator < count * 2 ^ bits := by
  have hstrict : pivot * denominator < count * scale := by
    exact lt_of_lt_of_le ((Nat.mul_lt_mul_right hdenominator).2 hmass) hscaled
  rw [hscale] at hstrict
  have hstrict' : pivot * denominator < pivot * (count * 2 ^ bits) := by
    calc
      pivot * denominator < count * (pivot * 2 ^ bits) := hstrict
      _ = pivot * (count * 2 ^ bits) := by
        rw [← mul_assoc, Nat.mul_comm count pivot, mul_assoc]
  exact (Nat.mul_lt_mul_left hpivot).mp hstrict'

end CertifiedJL.FixedPointConvolution
