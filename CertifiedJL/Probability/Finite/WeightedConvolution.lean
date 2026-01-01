/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Finite.Counting
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic

/-!
# Exact truncated convolution for finite iid experiments

This module counts strict lower-tail events for independent rows after the
one-row sample space has been partitioned into finitely many weighted energy
classes.  The recurrence truncates only at the requested strict cutoff;
nonnegative discarded energies cannot re-enter the event.
-/

open scoped BigOperators Nat

namespace CertifiedJL.Probability

/-- Exact numerator of an iid strict lower-tail event.  `weights outcome` is
the number of one-row seeds in the class and `energies outcome` is its
nonnegative energy. -/
def strictWeightedCount {Outcome : Type*} [Fintype Outcome]
    (weights energies : Outcome → ℕ) : ℕ → ℕ → ℕ
  | 0, cutoff => if 0 < cutoff then 1 else 0
  | rows + 1, cutoff =>
      ∑ outcome, weights outcome *
        strictWeightedCount weights energies rows (cutoff - energies outcome)

/-- Pascal recurrence for a finite multinomial coefficient, expressed by
removing one occurrence of every class that occurs. -/
theorem multinomial_eq_sum_update_sub_one
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (counts : Outcome → ℕ) (hcounts : 0 < ∑ outcome, counts outcome) :
    Nat.multinomial Finset.univ counts =
      ∑ outcome,
        if 0 < counts outcome then
          Nat.multinomial Finset.univ
            (Function.update counts outcome (counts outcome - 1))
        else 0 := by
  classical
  let total := ∑ outcome, counts outcome
  let denominator := ∏ outcome, (counts outcome)!
  have hdenominator : 0 < denominator := by
    exact Finset.prod_pos fun _ _ => Nat.factorial_pos _
  apply Nat.eq_of_mul_eq_mul_left hdenominator
  rw [Finset.mul_sum]
  have hleft :
      denominator * Nat.multinomial Finset.univ counts = total ! := by
    exact Nat.multinomial_spec Finset.univ counts
  rw [hleft]
  have hterm (outcome : Outcome) (houtcome : 0 < counts outcome) :
      denominator * Nat.multinomial Finset.univ
          (Function.update counts outcome (counts outcome - 1)) =
        counts outcome * (total - 1)! := by
    let counts' := Function.update counts outcome (counts outcome - 1)
    let denominator' := ∏ value, (counts' value)!
    have htotalSplit :
        total = counts outcome +
          ∑ value ∈ ({outcome} : Finset Outcome)ᶜ, counts value := by
      exact Fintype.sum_eq_add_sum_compl outcome counts
    have hsum : (∑ value, counts' value) = total - 1 := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ outcome)]
      change counts outcome - 1 +
          ∑ value ∈ Finset.univ \ {outcome}, counts value = total - 1
      rw [show Finset.univ \ {outcome} =
          ({outcome} : Finset Outcome)ᶜ by ext; simp]
      rw [htotalSplit]
      omega
    have hdenominator_eq : denominator = counts outcome * denominator' := by
      rw [show denominator =
          (counts outcome)! * ∏ value ∈ ({outcome} : Finset Outcome)ᶜ,
            (counts value)! by
        exact Fintype.prod_eq_mul_prod_compl outcome _]
      rw [show denominator' =
          (counts outcome - 1)! *
            ∏ value ∈ ({outcome} : Finset Outcome)ᶜ, (counts value)! by
        change (∏ value, (counts' value)!) = _
        rw [Fintype.prod_eq_mul_prod_compl outcome]
        congr 1
        · change (Function.update counts outcome (counts outcome - 1) outcome)! = _
          rw [Function.update_self]
        · apply Finset.prod_congr rfl
          intro value hvalue
          change (Function.update counts outcome (counts outcome - 1) value)! = _
          rw [Function.update_of_ne]
          simpa using hvalue]
      obtain ⟨count, hcount⟩ : ∃ count, counts outcome = count + 1 := by
        exact ⟨counts outcome - 1, by omega⟩
      rw [hcount, Nat.factorial_succ]
      rw [show count + 1 - 1 = count by omega]
      ring
    calc
      denominator * Nat.multinomial Finset.univ counts' =
          counts outcome *
            (denominator' * Nat.multinomial Finset.univ counts') := by
        rw [hdenominator_eq]
        simp only [Nat.mul_assoc]
      _ = counts outcome * (∑ value, counts' value)! := by
        rw [Nat.multinomial_spec]
      _ = counts outcome * (total - 1)! := by rw [hsum]
  obtain ⟨previous, htotal⟩ : ∃ previous, total = previous + 1 := by
    exact ⟨total - 1, by simpa [total] using (Nat.sub_add_cancel hcounts).symm⟩
  calc
    total ! = total * (total - 1)! := by
      rw [htotal, Nat.factorial_succ]
      simp
    _ = (∑ outcome, counts outcome) * (total - 1)! := by rfl
    _ = ∑ outcome, counts outcome * (total - 1)! := by
      rw [Finset.sum_mul]
    _ = ∑ outcome, denominator *
        (if 0 < counts outcome then
          Nat.multinomial Finset.univ
            (Function.update counts outcome (counts outcome - 1))
        else 0) := by
      apply Finset.sum_congr rfl
      intro outcome _
      by_cases houtcome : 0 < counts outcome
      · simp [houtcome, hterm outcome houtcome]
      · have hzero : counts outcome = 0 := by omega
        simp [hzero]

/-- The weighted multinomial mass of a fixed class-count vector. -/
def multinomialWeightedTerm {Outcome : Type*} [Fintype Outcome]
    (weights counts : Outcome → ℕ) : ℕ :=
  Nat.multinomial Finset.univ counts *
    ∏ outcome, weights outcome ^ counts outcome

/-- Weighted Pascal recurrence for a fixed class-count vector. -/
theorem multinomialWeightedTerm_eq_sum_update_sub_one
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (weights counts : Outcome → ℕ)
    (hcounts : 0 < ∑ outcome, counts outcome) :
    multinomialWeightedTerm weights counts =
      ∑ outcome,
        if 0 < counts outcome then
          weights outcome * multinomialWeightedTerm weights
            (Function.update counts outcome (counts outcome - 1))
        else 0 := by
  classical
  rw [multinomialWeightedTerm,
    multinomial_eq_sum_update_sub_one counts hcounts, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases houtcome : 0 < counts outcome
  · have hproduct :
        weights outcome *
            ∏ value,
              weights value ^
                Function.update counts outcome (counts outcome - 1) value =
          ∏ value, weights value ^ counts value := by
      obtain ⟨count, hcount⟩ : ∃ count, counts outcome = count + 1 := by
        exact ⟨counts outcome - 1, by omega⟩
      have hcompl :
          (∏ value ∈ ({outcome} : Finset Outcome)ᶜ,
              weights value ^
                Function.update counts outcome (counts outcome - 1) value) =
            ∏ value ∈ ({outcome} : Finset Outcome)ᶜ,
              weights value ^ counts value := by
        apply Finset.prod_congr rfl
        intro value hvalue
        rw [Function.update_of_ne]
        simpa using hvalue
      calc
        weights outcome *
              ∏ value,
                weights value ^
                  Function.update counts outcome (counts outcome - 1) value =
            weights outcome *
              (weights outcome ^ (counts outcome - 1) *
                ∏ value ∈ ({outcome} : Finset Outcome)ᶜ,
                  weights value ^ counts value) := by
          rw [Fintype.prod_eq_mul_prod_compl outcome,
            Function.update_self, hcompl]
        _ = weights outcome ^ counts outcome *
              ∏ value ∈ ({outcome} : Finset Outcome)ᶜ,
                weights value ^ counts value := by
          rw [hcount]
          simp only [Nat.add_sub_cancel]
          rw [pow_succ']
          ring
        _ = ∏ value, weights value ^ counts value := by
          rw [Fintype.prod_eq_mul_prod_compl outcome]
    simp only [houtcome, if_true, multinomialWeightedTerm]
    rw [← hproduct]
    ring
  · simp [houtcome]

/-- Every fixed class-count vector whose total energy is strictly below the
cutoff contributes its full weighted multinomial mass to the truncated
convolution. -/
theorem multinomialWeightedTerm_le_strictWeightedCount
    {Outcome : Type*} [Fintype Outcome]
    (weights energies : Outcome → ℕ) :
    ∀ rows counts cutoff,
      (∑ outcome, counts outcome) = rows →
      (∑ outcome, counts outcome * energies outcome) < cutoff →
      multinomialWeightedTerm weights counts ≤
        strictWeightedCount weights energies rows cutoff := by
  classical
  intro rows
  induction rows with
  | zero =>
      intro counts cutoff hcounts henergy
      have hzero (outcome : Outcome) : counts outcome = 0 := by
        have hle : counts outcome ≤ ∑ value, counts value :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ outcome)
        omega
      have hcountsZero : counts = fun _ => 0 := by
        funext outcome
        exact hzero outcome
      subst counts
      simp only [Finset.sum_const_zero, zero_mul] at henergy
      simp [multinomialWeightedTerm, Nat.multinomial,
        strictWeightedCount, henergy]
  | succ rows ih =>
      intro counts cutoff hcounts henergy
      have hcountsPos : 0 < ∑ outcome, counts outcome := by omega
      rw [multinomialWeightedTerm_eq_sum_update_sub_one
        weights counts hcountsPos, strictWeightedCount]
      apply Finset.sum_le_sum
      intro outcome _
      by_cases houtcome : 0 < counts outcome
      · let counts' := Function.update counts outcome (counts outcome - 1)
        have hsumSplit :
            (∑ value, counts value) = counts outcome +
              ∑ value ∈ ({outcome} : Finset Outcome)ᶜ, counts value :=
          Fintype.sum_eq_add_sum_compl outcome counts
        have hcounts' : (∑ value, counts' value) = rows := by
          rw [Finset.sum_update_of_mem (Finset.mem_univ outcome)]
          change counts outcome - 1 +
              ∑ value ∈ Finset.univ \ {outcome}, counts value = rows
          rw [show Finset.univ \ {outcome} =
              ({outcome} : Finset Outcome)ᶜ by ext; simp]
          omega
        have henergyEq :
            energies outcome +
                ∑ value, counts' value * energies value =
              ∑ value, counts value * energies value := by
          rw [Fintype.sum_eq_add_sum_compl outcome,
            Fintype.sum_eq_add_sum_compl outcome]
          simp only [counts', Function.update_self]
          have hcompl :
              (∑ value ∈ ({outcome} : Finset Outcome)ᶜ,
                  Function.update counts outcome (counts outcome - 1) value *
                    energies value) =
                ∑ value ∈ ({outcome} : Finset Outcome)ᶜ,
                  counts value * energies value := by
            apply Finset.sum_congr rfl
            intro value hvalue
            rw [Function.update_of_ne]
            simpa using hvalue
          rw [hcompl]
          obtain ⟨count, hcount⟩ : ∃ count, counts outcome = count + 1 := by
            exact ⟨counts outcome - 1, by omega⟩
          rw [hcount]
          simp only [Nat.add_sub_cancel, Nat.add_mul, one_mul]
          omega
        have henergy' :
            (∑ value, counts' value * energies value) <
              cutoff - energies outcome := by
          omega
        have hle := ih counts' (cutoff - energies outcome)
          hcounts' henergy'
        simp only [houtcome, if_true]
        exact Nat.mul_le_mul_left (weights outcome) hle
      · simp [houtcome]

/-- A finite set of distinct class-count vectors contributes the sum of its
weighted multinomial masses.  Distinctness is preserved after removing one
occurrence inside each fixed leading-class branch. -/
theorem sum_multinomialWeightedTerm_le_strictWeightedCount
    {Outcome : Type*} [Fintype Outcome]
    (weights energies : Outcome → ℕ) :
    ∀ rows (vectors : Finset (Outcome → ℕ)) cutoff,
      (∀ counts ∈ vectors, (∑ outcome, counts outcome) = rows) →
      (∀ counts ∈ vectors,
        (∑ outcome, counts outcome * energies outcome) < cutoff) →
      (∑ counts ∈ vectors, multinomialWeightedTerm weights counts) ≤
        strictWeightedCount weights energies rows cutoff := by
  classical
  intro rows
  induction rows with
  | zero =>
      intro vectors cutoff hrows henergy
      by_cases hvectors : vectors = ∅
      · simp [hvectors, strictWeightedCount]
      · obtain ⟨counts, hcounts⟩ := Finset.nonempty_iff_ne_empty.mpr hvectors
        have hzero (values : Outcome → ℕ) (hvalues : values ∈ vectors) :
            values = fun _ => 0 := by
          funext outcome
          have hle : values outcome ≤ ∑ value, values value :=
            Finset.single_le_sum (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ outcome)
          have := hrows values hvalues
          omega
        have hvectorsEq : vectors = {fun _ => 0} := by
          apply Finset.Subset.antisymm
          · intro values hvalues
            simp [hzero values hvalues]
          · rw [Finset.singleton_subset_iff]
            simpa [hzero counts hcounts] using hcounts
        have hcutoff : 0 < cutoff := by
          simpa [hzero counts hcounts] using henergy counts hcounts
        simp [hvectorsEq, multinomialWeightedTerm, Nat.multinomial,
          strictWeightedCount, hcutoff]
  | succ rows ih =>
      intro vectors cutoff hrows henergy
      rw [strictWeightedCount]
      calc
        (∑ counts ∈ vectors, multinomialWeightedTerm weights counts) =
            ∑ counts ∈ vectors,
              ∑ outcome,
                if 0 < counts outcome then
                  weights outcome * multinomialWeightedTerm weights
                    (Function.update counts outcome (counts outcome - 1))
                else 0 := by
          apply Finset.sum_congr rfl
          intro counts hcounts
          rw [multinomialWeightedTerm_eq_sum_update_sub_one]
          have := hrows counts hcounts
          omega
        _ = ∑ outcome,
            ∑ counts ∈ vectors,
              if 0 < counts outcome then
                weights outcome * multinomialWeightedTerm weights
                  (Function.update counts outcome (counts outcome - 1))
              else 0 := by
          rw [Finset.sum_comm]
        _ ≤ ∑ outcome, weights outcome *
            strictWeightedCount weights energies rows
              (cutoff - energies outcome) := by
          apply Finset.sum_le_sum
          intro outcome _
          let source := vectors.filter fun counts => 0 < counts outcome
          let pred (counts : Outcome → ℕ) :=
            Function.update counts outcome (counts outcome - 1)
          let target := source.image pred
          have hinjective : Set.InjOn pred source := by
            intro left hleft right hright heq
            have hleftPos : 0 < left outcome :=
              (Finset.mem_filter.mp hleft).2
            have hrightPos : 0 < right outcome :=
              (Finset.mem_filter.mp hright).2
            funext value
            by_cases hvalue : value = outcome
            · subst value
              have := congrFun heq outcome
              simp only [pred, Function.update_self] at this
              omega
            · have := congrFun heq value
              simpa [pred, Function.update_of_ne hvalue] using this
          have hrowsTarget (counts' : Outcome → ℕ)
              (hcounts' : counts' ∈ target) :
              (∑ value, counts' value) = rows := by
            obtain ⟨counts, hsource, rfl⟩ := Finset.mem_image.mp hcounts'
            have hcountsMem := (Finset.mem_filter.mp hsource).1
            have hcountsPos := (Finset.mem_filter.mp hsource).2
            have hsumSplit :
                (∑ value, counts value) = counts outcome +
                  ∑ value ∈ ({outcome} : Finset Outcome)ᶜ, counts value :=
              Fintype.sum_eq_add_sum_compl outcome counts
            rw [Finset.sum_update_of_mem (Finset.mem_univ outcome)]
            change counts outcome - 1 +
                ∑ value ∈ Finset.univ \ {outcome}, counts value = rows
            rw [show Finset.univ \ {outcome} =
                ({outcome} : Finset Outcome)ᶜ by ext; simp]
            have := hrows counts hcountsMem
            omega
          have henergyTarget (counts' : Outcome → ℕ)
              (hcounts' : counts' ∈ target) :
              (∑ value, counts' value * energies value) <
                cutoff - energies outcome := by
            obtain ⟨counts, hsource, rfl⟩ := Finset.mem_image.mp hcounts'
            have hcountsMem := (Finset.mem_filter.mp hsource).1
            have hcountsPos := (Finset.mem_filter.mp hsource).2
            have henergyEq :
                energies outcome +
                    ∑ value,
                      Function.update counts outcome (counts outcome - 1) value *
                        energies value =
                  ∑ value, counts value * energies value := by
              rw [Fintype.sum_eq_add_sum_compl outcome,
                Fintype.sum_eq_add_sum_compl outcome]
              simp only [Function.update_self]
              have hcompl :
                  (∑ value ∈ ({outcome} : Finset Outcome)ᶜ,
                      Function.update counts outcome (counts outcome - 1) value *
                        energies value) =
                    ∑ value ∈ ({outcome} : Finset Outcome)ᶜ,
                      counts value * energies value := by
                apply Finset.sum_congr rfl
                intro value hvalue
                rw [Function.update_of_ne]
                simpa using hvalue
              rw [hcompl]
              obtain ⟨count, hcount⟩ :
                  ∃ count, counts outcome = count + 1 := by
                exact ⟨counts outcome - 1, by omega⟩
              rw [hcount]
              simp only [Nat.add_sub_cancel, Nat.add_mul, one_mul]
              omega
            have := henergy counts hcountsMem
            change (∑ value,
                Function.update counts outcome (counts outcome - 1) value *
                  energies value) < cutoff - energies outcome
            rw [Nat.lt_sub_iff_add_lt, add_comm, henergyEq]
            exact this
          have htarget := ih target (cutoff - energies outcome)
            hrowsTarget henergyTarget
          calc
            (∑ counts ∈ vectors,
                if 0 < counts outcome then
                  weights outcome * multinomialWeightedTerm weights (pred counts)
                else 0) =
                ∑ counts ∈ source,
                  weights outcome * multinomialWeightedTerm weights (pred counts) := by
              rw [Finset.sum_filter]
            _ = ∑ counts' ∈ target,
                  weights outcome * multinomialWeightedTerm weights counts' := by
              rw [Finset.sum_image]
              exact hinjective
            _ = weights outcome *
                ∑ counts' ∈ target,
                  multinomialWeightedTerm weights counts' := by
              rw [Finset.mul_sum]
            _ ≤ weights outcome *
                strictWeightedCount weights energies rows
                  (cutoff - energies outcome) :=
              Nat.mul_le_mul_left _ htarget

/-- Sum a class-dependent value over a finite sample space by multiplying
each value by the cardinality of its fiber. -/
theorem sum_comp_eq_sum_card_fiber_mul
    {Seed Outcome : Type*} [Fintype Seed] [Fintype Outcome]
    [DecidableEq Outcome]
    (classify : Seed → Outcome) (value : Outcome → ℕ) :
    (∑ seed, value (classify seed)) =
      ∑ outcome,
        Fintype.card {seed : Seed // classify seed = outcome} * value outcome := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ) classify
    (fun seed => value (classify seed))]
  apply Finset.sum_congr rfl
  intro outcome _
  calc
    (∑ seed ∈ Finset.univ with classify seed = outcome,
        value (classify seed)) =
        ∑ _seed ∈ Finset.univ.filter
          (fun seed => classify seed = outcome), value outcome := by
      apply Finset.sum_congr rfl
      intro seed hseed
      rw [(Finset.mem_filter.mp hseed).2]
    _ = (Finset.univ.filter
          (fun seed => classify seed = outcome)).card * value outcome := by
      simp
    _ = Fintype.card {seed : Seed // classify seed = outcome} *
        value outcome := by
      have hcard :
          Fintype.card {seed : Seed // classify seed = outcome} =
            (Finset.univ.filter
              (fun seed => classify seed = outcome)).card := by
        rw [Fintype.card_subtype]
      rw [hcard]

set_option maxRecDepth 10000 in
/-- Cardinality of a fiber after a finite classification, expanded over the
fibers of an intermediate classification. -/
theorem card_composite_fiber_eq_sum
    {Seed Middle Outcome : Type*}
    [Fintype Seed] [Fintype Middle]
    [DecidableEq Middle] [DecidableEq Outcome]
    (middle : Seed → Middle) (classify : Middle → Outcome)
    (outcome : Outcome) :
    Fintype.card {seed : Seed // classify (middle seed) = outcome} =
      ∑ value : Middle,
        if classify value = outcome then
          Fintype.card {seed : Seed // middle seed = value}
        else 0 := by
  classical
  have hsum := sum_comp_eq_sum_card_fiber_mul middle
    (fun value => if classify value = outcome then 1 else 0)
  rw [Fintype.card_subtype]
  calc
    (Finset.univ.filter
      (fun seed => classify (middle seed) = outcome)).card =
        ∑ seed, if classify (middle seed) = outcome then 1 else 0 := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ value,
        Fintype.card {seed : Seed // middle seed = value} *
          (if classify value = outcome then 1 else 0) := hsum
    _ = ∑ value,
        if classify value = outcome then
          Fintype.card {seed : Seed // middle seed = value}
        else 0 := by
      apply Finset.sum_congr rfl
      intro value _
      split <;> simp

/-- Split a function on `Fin (rows + 1)` into its first row and remaining
rows, retaining a strict bound on the total energy. -/
def strictEnergySuccEquiv
    {Seed : Type*} [Fintype Seed] (energy : Seed → ℕ)
    (rows cutoff : ℕ) :
    {seeds : Fin (rows + 1) → Seed //
      (∑ row, energy (seeds row)) < cutoff} ≃
      (first : Seed) ×
        {rest : Fin rows → Seed //
          energy first + ∑ row, energy (rest row) < cutoff} where
  toFun seeds :=
    ⟨seeds.1 0, ⟨fun row => seeds.1 row.succ, by
      simpa only [Fin.sum_univ_succ] using seeds.2⟩⟩
  invFun split :=
    ⟨Fin.cons split.1 split.2.1, by
      simpa [Fin.sum_univ_succ] using split.2.2⟩
  left_inv seeds := by
    apply Subtype.ext
    funext row
    exact Fin.cases rfl (fun _ => rfl) row
  right_inv split := rfl

/-- The weighted convolution recurrence is exactly the cardinality of the
strict-energy event on the original row-seed space. -/
theorem card_strictEnergy_eq_strictWeightedCount
    {Seed Outcome : Type*} [Fintype Seed] [Fintype Outcome]
    [DecidableEq Outcome]
    (classify : Seed → Outcome) (energy : Seed → ℕ)
    (weights energies : Outcome → ℕ)
    (henergy : ∀ seed, energy seed = energies (classify seed))
    (hweights : ∀ outcome,
      Fintype.card {seed : Seed // classify seed = outcome} = weights outcome) :
    ∀ rows cutoff,
      Fintype.card {seeds : Fin rows → Seed //
        (∑ row, energy (seeds row)) < cutoff} =
      strictWeightedCount weights energies rows cutoff := by
  classical
  intro rows
  induction rows with
  | zero =>
      intro cutoff
      rw [Fintype.card_subtype]
      by_cases hcutoff : 0 < cutoff <;>
        simp [strictWeightedCount, hcutoff]
  | succ rows ih =>
      intro cutoff
      rw [Fintype.card_congr (strictEnergySuccEquiv energy rows cutoff),
        Fintype.card_sigma]
      have hbound (first : Seed) :
          Fintype.card {rest : Fin rows → Seed //
              energy first + ∑ row, energy (rest row) < cutoff} =
            strictWeightedCount weights energies rows
              (cutoff - energy first) := by
        have hequiv :
            {rest : Fin rows → Seed //
                energy first + ∑ row, energy (rest row) < cutoff} ≃
              {rest : Fin rows → Seed //
                (∑ row, energy (rest row)) < cutoff - energy first} :=
          Equiv.subtypeEquiv (Equiv.refl _) fun rest => by
            change energy first + ∑ row, energy (rest row) < cutoff ↔
              (∑ row, energy (rest row)) < cutoff - energy first
            omega
        rw [Fintype.card_congr hequiv, ih]
      simp_rw [hbound]
      simp_rw [henergy]
      rw [sum_comp_eq_sum_card_fiber_mul classify
        (fun outcome => strictWeightedCount weights energies rows
          (cutoff - energies outcome))]
      simp_rw [hweights]
      rw [strictWeightedCount]

end CertifiedJL.Probability
