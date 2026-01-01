/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Distributions.Entry
import CertifiedJL.Model.Vectors.Real
import CertifiedJL.Probability.Distributions.Rademacher.NormalizedRademacherProfile
import CertifiedJL.Probability.Distributions.Rademacher.Rademacher
import Mathlib.Tactic.FinCases

/-!
# Sparse rows as duplicated Rademacher signs

Each sparse-Rademacher entry is the average of two independent signs. This
module records the corresponding whole-seed equivalence and the exact dot
product identity used by the coefficient-uniform one-row theorem.
-/

open scoped BigOperators

namespace CertifiedJL

/-- Expose the two independent sign bits underlying each sparse-row entry. -/
def sparseRowSeedSigns {d : ℕ} (seed : SparseRowSeed d) :
    Fin d × Fin 2 → Bool
  | (i, j) => if j = 0 then (seed i).1 else (seed i).2

/-- Reassemble a sparse-row seed from its two sign bits per coordinate. -/
def sparseRowSeedOfSigns {d : ℕ} (bits : Fin d × Fin 2 → Bool) :
    SparseRowSeed d :=
  fun i => (bits (i, 0), bits (i, 1))

@[simp]
theorem sparseRowSeedOfSigns_signs {d : ℕ} (seed : SparseRowSeed d) :
    sparseRowSeedOfSigns (sparseRowSeedSigns seed) = seed := by
  funext i
  simp [sparseRowSeedOfSigns, sparseRowSeedSigns]

@[simp]
theorem sparseRowSeedSigns_ofSigns {d : ℕ}
    (bits : Fin d × Fin 2 → Bool) :
    sparseRowSeedSigns (sparseRowSeedOfSigns bits) = bits := by
  funext p
  rcases p with ⟨i, j⟩
  fin_cases j <;> simp [sparseRowSeedSigns, sparseRowSeedOfSigns]

/--
Sparse-row seeds are canonically equivalent to two independent sign bits at
each coordinate.
-/
def sparseRowSeedEquivSigns (d : ℕ) :
    SparseRowSeed d ≃ (Fin d × Fin 2 → Bool) where
  toFun := sparseRowSeedSigns
  invFun := sparseRowSeedOfSigns
  left_inv := sparseRowSeedOfSigns_signs
  right_inv := sparseRowSeedSigns_ofSigns

/-- The duplicated sign view of a uniform sparse seed is itself uniform. -/
theorem map_uniformSparseSeed_signs (d : ℕ) :
    (PMF.uniformOfFintype (SparseRowSeed d)).map sparseRowSeedSigns =
      PMF.uniformOfFintype (Fin d × Fin 2 → Bool) := by
  change
    (PMF.uniformOfFintype (SparseRowSeed d)).map
        (sparseRowSeedEquivSigns d) =
      PMF.uniformOfFintype (Fin d × Fin 2 → Bool)
  exact map_uniformOfFintype_equiv (sparseRowSeedEquivSigns d)

/-- The duplicated-sign linear form corresponding to a sparse row. -/
def duplicatedSparseSignSum {d : ℕ} (seed : SparseRowSeed d)
    (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ p : Fin d × Fin 2,
    (signBit (sparseRowSeedSigns seed p) : ℝ) * w p.1

/-- The one-sided Rademacher threshold corresponding to sparse constant `39/4`. -/
noncomputable def sparseOneRowRademacherThreshold : ℝ :=
  (39 / 4 : ℝ) * Real.sqrt 2

/--
The normalized coefficient of either sign copy underlying sparse coordinate
`i`. The zero-vector branch is intentionally total; normalization lemmas state
the necessary nonzero hypothesis explicitly.
-/
noncomputable def normalizedDuplicatedCoefficient {d : ℕ}
    (w : EuclideanSpace ℝ (Fin d)) (p : Fin d × Fin 2) : ℝ :=
  w p.1 / (Real.sqrt 2 * ‖w‖)

/-- A nonzero coefficient vector yields a normalized duplicated profile. -/
theorem sum_sq_normalizedDuplicatedCoefficient {d : ℕ}
    (w : EuclideanSpace ℝ (Fin d)) (hw : w ≠ 0) :
    ∑ p : Fin d × Fin 2,
        normalizedDuplicatedCoefficient w p ^ 2 = 1 := by
  have hnorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, normalizedDuplicatedCoefficient]
  rw [show
      (∑ i, ((w i / (Real.sqrt 2 * ‖w‖)) ^ 2 +
        (w i / (Real.sqrt 2 * ‖w‖)) ^ 2)) =
        2 * ∑ i, (w i / (Real.sqrt 2 * ‖w‖)) ^ 2 by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]
  simp_rw [div_pow]
  rw [← Finset.sum_div]
  rw [← EuclideanSpace.real_norm_sq_eq w]
  rw [mul_pow]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp

/--
In the diffuse regime, every normalized duplicated coefficient is at most
`1 / (6 * sqrt 2)` in absolute value.
-/
theorem abs_normalizedDuplicatedCoefficient_le_inv_six_sqrt_two
    {d : ℕ} (w : EuclideanSpace ℝ (Fin d)) (hw : w ≠ 0)
    (hdiffuse : ∀ i, 6 * |w i| ≤ ‖w‖)
    (p : Fin d × Fin 2) :
    |normalizedDuplicatedCoefficient w p| ≤
      1 / (6 * Real.sqrt 2) := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  unfold normalizedDuplicatedCoefficient
  rw [abs_div, abs_of_pos (mul_pos hs hn)]
  apply (div_le_div_iff₀ (mul_pos hs hn) (mul_pos (by norm_num) hs)).2
  have h := mul_le_mul_of_nonneg_right (hdiffuse p.1) hs.le
  nlinarith

/--
The absolute-cube sum of a diffuse normalized duplicated profile is at most
`1 / (6 * sqrt 2)`.
-/
theorem sum_abs_cube_normalizedDuplicatedCoefficient_le_inv_six_sqrt_two
    {d : ℕ} (w : EuclideanSpace ℝ (Fin d)) (hw : w ≠ 0)
    (hdiffuse : ∀ i, 6 * |w i| ≤ ‖w‖) :
    ∑ p : Fin d × Fin 2,
        |normalizedDuplicatedCoefficient w p| ^ 3 ≤
      1 / (6 * Real.sqrt 2) :=
  Probability.sum_abs_cube_le_of_sum_sq_eq_one_of_abs_le
    (normalizedDuplicatedCoefficient w)
    (sum_sq_normalizedDuplicatedCoefficient w hw)
    (abs_normalizedDuplicatedCoefficient_le_inv_six_sqrt_two w hw hdiffuse)

/--
The duplicated-sign sum is exactly twice the sparse-row dot product.
-/
theorem duplicatedSparseSignSum_eq_two_mul {d : ℕ}
    (seed : SparseRowSeed d) (w : EuclideanSpace ℝ (Fin d)) :
    duplicatedSparseSignSum seed w =
      2 * euclideanRowDot (sparseRow seed) w := by
  rw [duplicatedSparseSignSum, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, sparseRowSeedSigns]
  rw [euclideanRowDot, realRowDot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hs := sparseBit_eq_average (seed i)
  have hsReal := congrArg (fun z : ℤ => (z : ℝ)) hs
  norm_num only [Int.cast_mul, Int.cast_add, Int.cast_ofNat] at hsReal
  simp only [sparseRow]
  calc
    (signBit (seed i).1 : ℝ) * w i +
          (signBit (seed i).2 : ℝ) * w i =
        ((signBit (seed i).1 : ℝ) +
          (signBit (seed i).2 : ℝ)) * w i := by ring
    _ = (2 * (sparseBit (seed i) : ℝ)) * w i := by rw [hsReal]
    _ = 2 * ((sparseBit (seed i) : ℝ) * w i) := by ring

/--
The normalized duplicated Rademacher sum is the normalized sparse dot product
scaled by `sqrt 2`.
-/
theorem rademacherSum_normalizedDuplicatedCoefficient {d : ℕ}
    (seed : SparseRowSeed d) (w : EuclideanSpace ℝ (Fin d))
    (hw : w ≠ 0) :
    rademacherSum (normalizedDuplicatedCoefficient w)
        (sparseRowSeedSigns seed) =
      Real.sqrt 2 * euclideanRowDot (sparseRow seed) w / ‖w‖ := by
  have hnorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  simp only [rademacherSum, normalizedDuplicatedCoefficient]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  change duplicatedSparseSignSum seed w / (Real.sqrt 2 * ‖w‖) =
    Real.sqrt 2 * euclideanRowDot (sparseRow seed) w / ‖w‖
  rw [duplicatedSparseSignSum_eq_two_mul]
  field_simp [hnorm, hsqrt]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/--
For a nonzero coefficient vector, the strict sparse one-row event is exactly
the strict normalized duplicated-Rademacher event.
-/
theorem sparseOneRow975Event_iff_rademacher {d : ℕ}
    (seed : SparseRowSeed d) (w : EuclideanSpace ℝ (Fin d))
    (hw : w ≠ 0) :
    |euclideanRowDot (sparseRow seed) w| > (39 / 4 : ℝ) * ‖w‖ ↔
      |rademacherSum (normalizedDuplicatedCoefficient w)
          (sparseRowSeedSigns seed)| >
        sparseOneRowRademacherThreshold := by
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [rademacherSum_normalizedDuplicatedCoefficient seed w hw]
  rw [abs_div, abs_mul, abs_of_pos hsqrt, abs_norm]
  constructor
  · intro h
    change sparseOneRowRademacherThreshold <
      Real.sqrt 2 * |euclideanRowDot (sparseRow seed) w| / ‖w‖
    apply (lt_div_iff₀ hnorm).2
    have hscaled := mul_lt_mul_of_pos_left h hsqrt
    unfold sparseOneRowRademacherThreshold
    nlinarith
  · intro h
    change sparseOneRowRademacherThreshold <
      Real.sqrt 2 * |euclideanRowDot (sparseRow seed) w| / ‖w‖ at h
    have hscaled :
        sparseOneRowRademacherThreshold * ‖w‖ <
          Real.sqrt 2 * |euclideanRowDot (sparseRow seed) w| :=
      (lt_div_iff₀ hnorm).mp h
    unfold sparseOneRowRademacherThreshold at hscaled
    have hcancel :
        Real.sqrt 2 * ((39 / 4 : ℝ) * ‖w‖) <
          Real.sqrt 2 * |euclideanRowDot (sparseRow seed) w| := by
      nlinarith
    exact lt_of_mul_lt_mul_left hcancel hsqrt.le

/--
Under a uniform sparse-row seed, the strict `9.75` event has exactly the same
probability as its normalized duplicated-Rademacher formulation.
-/
theorem sparseOneRow975_probability_eq_rademacher {d : ℕ}
    (w : EuclideanSpace ℝ (Fin d)) (hw : w ≠ 0) :
    eventProbability (sparseRademacherRow d)
        (fun row =>
          |euclideanRowDot row w| > (39 / 4 : ℝ) * ‖w‖) =
      eventProbability (rademacherPMF (Fin d × Fin 2))
        (fun bits =>
          |rademacherSum (normalizedDuplicatedCoefficient w) bits| >
            sparseOneRowRademacherThreshold) := by
  rw [sparseRademacherRow_eq_map_uniformRowSeed]
  calc
    eventProbability
        ((PMF.uniformOfFintype (SparseRowSeed d)).map sparseRow)
        (fun row =>
          |euclideanRowDot row w| > (39 / 4 : ℝ) * ‖w‖) =
      eventProbability
        ((PMF.uniformOfFintype (SparseRowSeed d)).map sparseRowSeedSigns)
        (fun bits =>
          |rademacherSum (normalizedDuplicatedCoefficient w) bits| >
            sparseOneRowRademacherThreshold) := by
      apply eventProbability_map_congr
      intro seed
      exact sparseOneRow975Event_iff_rademacher seed w hw
    _ = eventProbability (rademacherPMF (Fin d × Fin 2))
        (fun bits =>
          |rademacherSum (normalizedDuplicatedCoefficient w) bits| >
            sparseOneRowRademacherThreshold) := by
      rw [map_uniformSparseSeed_signs]
      unfold rademacherPMF
      rw [uniformPiPMF_eq_uniformOfFintype]

end CertifiedJL
