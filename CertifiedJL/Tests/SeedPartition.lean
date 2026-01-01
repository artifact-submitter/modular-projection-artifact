/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Distributions.BalancedTernary.SeedPartition
import Mathlib.Tactic

/-!
# Coordinate-partition producer canaries

The asymmetric two-coordinate examples pin both sides of the partition, the
join orientation, and the integer dot-product decomposition.
-/

namespace CertifiedJL

private def firstOfTwo (i : Fin 2) : Prop := i = 0

private instance : DecidablePred firstOfTwo :=
  fun i => inferInstanceAs (Decidable (i = 0))

private def firstOfThree (i : Fin 3) : Prop := i = 0

private instance : DecidablePred firstOfThree :=
  fun i => inferInstanceAs (Decidable (i = 0))

example : Fintype.card (SparseRowSeedPart firstOfThree) = 4 := by decide

example : Fintype.card (SparseRowSeedCompl firstOfThree) = 16 := by decide

private def selectedSeed : SparseRowSeedPart firstOfTwo :=
  fun _ => (true, true)

private def complementarySeed : SparseRowSeedCompl firstOfTwo :=
  fun _ => (false, false)

/-- Equal bits have conditional probability `1/2` in each asymmetric fiber. -/
example :
    (eventProbability
      ((PMF.uniformOfFintype (Bool × Bool)).map id)
      (fun x => x.1 = x.2)).toReal ≤ (1 / 2 : ℝ) := by
  apply Probability.eventProbability_map_uniform_prod_toReal_le
    (fun a b => (a, b)) (fun x => x.1 = x.2) (1 / 2 : ℝ)
  intro a
  rw [show eventProbability
      ((PMF.uniformOfFintype Bool).map (fun b => (a, b)))
        (fun x => x.1 = x.2) =
      eventProbability (PMF.uniformOfFintype Bool) (fun b => a = b) by
    unfold eventProbability
    rw [PMF.map_comp]
    rfl]
  rw [eventProbability_toReal_eq_sum, Fintype.sum_bool]
  cases a <;> norm_num [PMF.uniformOfFintype_apply]

/-- The selected coordinate is reconstructed from the selected fiber. -/
example :
    joinSparseRowSeed firstOfTwo selectedSeed complementarySeed 0 =
      (true, true) := by
  exact joinSparseRowSeed_selected firstOfTwo selectedSeed complementarySeed
    (⟨0, rfl⟩ : {i : Fin 2 // firstOfTwo i})

/-- The other coordinate is reconstructed from the complementary fiber. -/
example :
    joinSparseRowSeed firstOfTwo selectedSeed complementarySeed 1 =
      (false, false) := by
  exact joinSparseRowSeed_compl firstOfTwo selectedSeed complementarySeed
    (⟨1, by decide⟩ : {i : Fin 2 // ¬ firstOfTwo i})

/-- Unequal weights and opposite sparse signs pin both summands and their order. -/
example :
    (∑ i, sparseRow
      (joinSparseRowSeed firstOfTwo selectedSeed complementarySeed) i *
        ![(3 : ℤ), 5] i) = -2 := by
  rw [sparseRow_join_dot_eq_add]
  decide

/-- The exact conditional-average bridge is usable on a nontrivial mask. -/
example (event : (Fin 2 → ℤ) → Prop) :
    (eventProbability (sparseRademacherRow 2) event).toReal =
      ∑ selected : SparseRowSeedPart firstOfTwo,
        (Fintype.card (SparseRowSeedPart firstOfTwo) : ℝ)⁻¹ *
          (eventProbability
            ((PMF.uniformOfFintype
              (SparseRowSeedCompl firstOfTwo)).map
              (fun other => sparseRow
                (joinSparseRowSeed firstOfTwo selected other))) event).toReal :=
  sparseRademacherRow_eventProbability_toReal_eq_partitionAverage
    firstOfTwo event

/--
The complement-first average has 16 outer seeds and 4 inner seeds for a
one-coordinate mask in dimension three, pinning the conditioning direction.
-/
example (event : (Fin 3 → ℤ) → Prop) :
    (eventProbability (sparseRademacherRow 3) event).toReal =
      ∑ other : SparseRowSeedCompl firstOfThree,
        (Fintype.card (SparseRowSeedCompl firstOfThree) : ℝ)⁻¹ *
          (eventProbability
            ((PMF.uniformOfFintype
              (SparseRowSeedPart firstOfThree)).map
              (fun selected => sparseRow
                (joinSparseRowSeed firstOfThree selected other))) event).toReal :=
  sparseRademacherRow_eventProbability_toReal_eq_complFirstAverage
    firstOfThree event

/-- The complement-first common-bound API quantifies over the fixed block. -/
example (event : (Fin 3 → ℤ) → Prop) (c : ℝ)
    (hbound : ∀ other : SparseRowSeedCompl firstOfThree,
      (eventProbability
        ((PMF.uniformOfFintype (SparseRowSeedPart firstOfThree)).map
          (fun selected => sparseRow
            (joinSparseRowSeed firstOfThree selected other))) event).toReal ≤ c) :
    (eventProbability (sparseRademacherRow 3) event).toReal ≤ c :=
  sparseRademacherRow_eventProbability_toReal_le_of_complFirst
    firstOfThree event c hbound

#print axioms CertifiedJL.Probability.eventProbability_map_uniform_prod_toReal_le_average
#print axioms CertifiedJL.Probability.eventProbability_map_uniform_prod_toReal_le
#print axioms CertifiedJL.sparseRow_join_dot_eq_add
#print axioms CertifiedJL.sparseRademacherRow_eq_map_uniformPartition
#print axioms CertifiedJL.sparseRademacherRow_eventProbability_toReal_eq_partitionAverage
#print axioms CertifiedJL.sparseRademacherRow_eventProbability_toReal_le_of_partition
#print axioms CertifiedJL.sparseRademacherRow_eq_map_uniformPartitionComplFirst
#print axioms CertifiedJL.sparseRademacherRow_eventProbability_toReal_eq_complFirstAverage
#print axioms CertifiedJL.sparseRademacherRow_eventProbability_toReal_le_of_complFirst

end CertifiedJL
