/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperPeanoConcrete

/-! # Concrete mixed product distributions for the sparse upper Peano telescope -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CertifiedJL

/-- At stage `k`, coordinates below `k` are Rademacher and the remaining
coordinates are standard Gaussian. -/
noncomputable def upperPeanoHybridCoordinateLaw {n : ℕ} (k : ℕ)
    (i : Fin n) : Measure ℝ :=
  if i.val < k then standardRademacherMeasure else gaussianReal 0 1

/-- The coordinate being replaced is Gaussian immediately before its step. -/
@[simp] theorem upperPeanoHybridCoordinateLaw_self {n : ℕ} (i : Fin n) :
    upperPeanoHybridCoordinateLaw i.val i = gaussianReal 0 1 := by
  simp [upperPeanoHybridCoordinateLaw]

/-- The coordinate being replaced is Rademacher immediately after its step. -/
@[simp] theorem upperPeanoHybridCoordinateLaw_self_succ {n : ℕ} (i : Fin n) :
    upperPeanoHybridCoordinateLaw (i.val + 1) i =
      standardRademacherMeasure := by
  simp [upperPeanoHybridCoordinateLaw]

/-- Every other coordinate has the same law on the two sides of a replacement
step.  This is the exact rest-product equality needed by coordinate Fubini. -/
theorem upperPeanoHybridCoordinateLaw_succAbove_eq {m : ℕ}
    (i : Fin (m + 1)) (j : Fin m) :
    upperPeanoHybridCoordinateLaw i.val (i.succAbove j) =
      upperPeanoHybridCoordinateLaw (i.val + 1) (i.succAbove j) := by
  have hne : (i.succAbove j).val ≠ i.val := by
    intro h
    apply Fin.succAbove_ne i j
    exact Fin.ext h
  unfold upperPeanoHybridCoordinateLaw
  split_ifs with hleft hright
  · rfl
  · omega
  · omega
  · rfl

/-- The unchanged product distribution after removing the coordinate replaced at this
step. -/
noncomputable def upperPeanoHybridRestCoordinateLaw {m : ℕ}
    (i : Fin (m + 1)) (j : Fin m) : Measure ℝ :=
  upperPeanoHybridCoordinateLaw i.val (i.succAbove j)

/-- Reindexing the product immediately before a step exposes a Gaussian first
coordinate and the unchanged rest product. -/
theorem upperPeanoHybridMeasure_before_map_piFinSuccAbove {m : ℕ}
    (i : Fin (m + 1)) :
    Measure.map (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i)
        (Measure.pi (upperPeanoHybridCoordinateLaw i.val)) =
      (gaussianReal 0 1).prod
        (Measure.pi (upperPeanoHybridRestCoordinateLaw i)) := by
  let (j : Fin (m + 1)) : IsProbabilityMeasure
      (upperPeanoHybridCoordinateLaw i.val j) := by
    unfold upperPeanoHybridCoordinateLaw
    split <;> infer_instance
  have hmap := (measurePreserving_piFinSuccAbove
    (upperPeanoHybridCoordinateLaw (n := m + 1) i.val) i).map_eq
  rw [hmap, upperPeanoHybridCoordinateLaw_self]
  congr 1

/-- Reindexing the product immediately after a step exposes a Rademacher first
coordinate and exactly the same rest product. -/
theorem upperPeanoHybridMeasure_after_map_piFinSuccAbove {m : ℕ}
    (i : Fin (m + 1)) :
    Measure.map (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i)
        (Measure.pi (upperPeanoHybridCoordinateLaw (i.val + 1))) =
      standardRademacherMeasure.prod
        (Measure.pi (upperPeanoHybridRestCoordinateLaw i)) := by
  let (j : Fin (m + 1)) : IsProbabilityMeasure
      (upperPeanoHybridCoordinateLaw (i.val + 1) j) := by
    unfold upperPeanoHybridCoordinateLaw
    split <;> infer_instance
  have hmap := (measurePreserving_piFinSuccAbove
    (upperPeanoHybridCoordinateLaw (n := m + 1) (i.val + 1)) i).map_eq
  rw [hmap, upperPeanoHybridCoordinateLaw_self_succ]
  congr 1
  congr 1
  funext j
  exact (upperPeanoHybridCoordinateLaw_succAbove_eq i j).symm

/-- The quadratic-exponential expectation at stage `k` of the concrete
Gaussian-to-Rademacher coordinate telescope. -/
noncomputable def upperPeanoHybridValue {n : ℕ} (b : Fin n → ℝ)
    (s : ℂ) (k : ℕ) : ℂ :=
  ∫ x : Fin n → ℝ, complexQuadraticExp s (∑ i, b i * x i)
    ∂Measure.pi (upperPeanoHybridCoordinateLaw k)

/-- Stage zero is the all-Gaussian endpoint. -/
theorem upperPeanoHybridValue_zero {n : ℕ} (b : Fin n → ℝ) (s : ℂ) :
    upperPeanoHybridValue b s 0 =
      ∫ x : Fin n → ℝ, complexQuadraticExp s (∑ i, b i * x i)
        ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  have hlaw : upperPeanoHybridCoordinateLaw (n := n) 0 =
      fun _ : Fin n => gaussianReal 0 1 := by
    funext i
    simp [upperPeanoHybridCoordinateLaw]
  rw [upperPeanoHybridValue, hlaw]

/-- Stage `n` is the all-Rademacher endpoint. -/
theorem upperPeanoHybridValue_card {n : ℕ} (b : Fin n → ℝ) (s : ℂ) :
    upperPeanoHybridValue b s n =
      ∫ x : Fin n → ℝ, complexQuadraticExp s (∑ i, b i * x i)
        ∂Measure.pi (fun _ : Fin n => standardRademacherMeasure) := by
  have hlaw : upperPeanoHybridCoordinateLaw (n := n) n =
      fun _ : Fin n => standardRademacherMeasure := by
    funext i
    simp [upperPeanoHybridCoordinateLaw, i.isLt]
  rw [upperPeanoHybridValue, hlaw]

/-- The concrete mixed-product stages telescope to their adjacent coordinate
replacements. -/
theorem upperPeanoHybridValue_zero_sub_card_eq_sum {n : ℕ}
    (b : Fin n → ℝ) (s : ℂ) :
    upperPeanoHybridValue b s 0 - upperPeanoHybridValue b s n =
      ∑ i : Fin n, (upperPeanoHybridValue b s i.val -
        upperPeanoHybridValue b s (i.val + 1)) := by
  let H : ℕ → ℂ := upperPeanoHybridValue b s
  have htel := Finset.sum_range_sub H n
  change H 0 - H n = ∑ i : Fin n, (H i.val - H (i.val + 1))
  calc
    H 0 - H n = -(H n - H 0) := by ring
    _ = -(∑ i ∈ Finset.range n, (H (i + 1) - H i)) := by rw [htel]
    _ = ∑ i ∈ Finset.range n, (H i - H (i + 1)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ i : Fin n, (H i.val - H (i.val + 1)) :=
      (Fin.sum_univ_eq_sum_range (fun i => H i - H (i + 1)) n).symm

/-- If every adjacent concrete product replacement has its fourth-Peano
identity, the exact `hfirst` premise of `norm_fourthPeanoHybridRemainder_le`
follows with no further measure algebra. -/
theorem upperPeanoHybridValue_sub_eq_sum_fourthPeano {n : ℕ}
    (b : Fin n → ℝ) (s : ℂ) (K4 : Fin n → ℂ)
    (hstep : ∀ i : Fin n,
      upperPeanoHybridValue b s i.val -
          upperPeanoHybridValue b s (i.val + 1) =
        (b i ^ 4 / 12 : ℝ) • K4 i) :
    upperPeanoHybridValue b s 0 - upperPeanoHybridValue b s n =
      ∑ i, (b i ^ 4 / 12 : ℝ) • K4 i := by
  rw [upperPeanoHybridValue_zero_sub_card_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact hstep i

end CertifiedJL
