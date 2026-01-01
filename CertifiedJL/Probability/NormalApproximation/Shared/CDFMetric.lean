/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib.Probability.CDF

/-!
# CDF discrepancies and Kolmogorov distance

This file fixes the half-line conventions used by the quantitative normal
approximation argument.  Mathlib's `cdf` uses the closed lower half-line
`Set.Iic x`; the lemmas below make every passage to a strict lower half-line
or an upper tail explicit, including the atom at the endpoint.

The Kolmogorov distance is defined as the supremum of the pointwise absolute
CDF discrepancy.  Its elementary metric estimates are proved directly from
the universal bounds `0 ≤ cdf μ x ≤ 1`.
-/

open MeasureTheory ProbabilityTheory Set

namespace CertifiedJL
namespace Probability

/-- Signed pointwise CDF discrepancy, in the order `μ - ν`. -/
noncomputable def cdfDiscrepancy
    (μ ν : Measure ℝ) (x : ℝ) : ℝ :=
  cdf μ x - cdf ν x

/-- Absolute pointwise CDF discrepancy. -/
noncomputable def cdfAbsoluteDiscrepancy
    (μ ν : Measure ℝ) (x : ℝ) : ℝ :=
  |cdfDiscrepancy μ ν x|

/-- One-sided positive CDF discrepancy, in the order `μ - ν`. -/
noncomputable def cdfPositiveDiscrepancy
    (μ ν : Measure ℝ) (x : ℝ) : ℝ :=
  max (cdfDiscrepancy μ ν x) 0

/-- Kolmogorov distance between two real measures. -/
noncomputable def kolmogorovDistance
    (μ ν : Measure ℝ) : ℝ :=
  sSup (Set.range (cdfAbsoluteDiscrepancy μ ν))

theorem cdfAbsoluteDiscrepancy_nonneg
    (μ ν : Measure ℝ) (x : ℝ) :
    0 ≤ cdfAbsoluteDiscrepancy μ ν x :=
  abs_nonneg _

theorem cdfPositiveDiscrepancy_nonneg
    (μ ν : Measure ℝ) (x : ℝ) :
    0 ≤ cdfPositiveDiscrepancy μ ν x := by
  simp [cdfPositiveDiscrepancy]

theorem cdfDiscrepancy_le_positiveDiscrepancy
    (μ ν : Measure ℝ) (x : ℝ) :
    cdfDiscrepancy μ ν x ≤ cdfPositiveDiscrepancy μ ν x := by
  simp [cdfPositiveDiscrepancy]

theorem cdfPositiveDiscrepancy_le_absoluteDiscrepancy
    (μ ν : Measure ℝ) (x : ℝ) :
    cdfPositiveDiscrepancy μ ν x ≤
      cdfAbsoluteDiscrepancy μ ν x := by
  unfold cdfPositiveDiscrepancy cdfAbsoluteDiscrepancy
  exact max_le (le_abs_self _) (abs_nonneg _)

theorem cdfAbsoluteDiscrepancy_le_one
    (μ ν : Measure ℝ) (x : ℝ) :
    cdfAbsoluteDiscrepancy μ ν x ≤ 1 := by
  rw [cdfAbsoluteDiscrepancy, cdfDiscrepancy, abs_le]
  constructor
  · linarith [cdf_nonneg μ x, cdf_le_one ν x]
  · linarith [cdf_nonneg ν x, cdf_le_one μ x]

theorem cdfPositiveDiscrepancy_le_one
    (μ ν : Measure ℝ) (x : ℝ) :
    cdfPositiveDiscrepancy μ ν x ≤ 1 :=
  (cdfPositiveDiscrepancy_le_absoluteDiscrepancy μ ν x).trans
    (cdfAbsoluteDiscrepancy_le_one μ ν x)

private theorem cdfAbsoluteDiscrepancy_range_bddAbove
    (μ ν : Measure ℝ) :
    BddAbove (Set.range (cdfAbsoluteDiscrepancy μ ν)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact cdfAbsoluteDiscrepancy_le_one μ ν x

theorem cdfAbsoluteDiscrepancy_le_kolmogorovDistance
    (μ ν : Measure ℝ) (x : ℝ) :
    cdfAbsoluteDiscrepancy μ ν x ≤ kolmogorovDistance μ ν := by
  exact le_csSup (cdfAbsoluteDiscrepancy_range_bddAbove μ ν)
    (Set.mem_range_self x)

theorem cdfPositiveDiscrepancy_le_kolmogorovDistance
    (μ ν : Measure ℝ) (x : ℝ) :
    cdfPositiveDiscrepancy μ ν x ≤ kolmogorovDistance μ ν :=
  (cdfPositiveDiscrepancy_le_absoluteDiscrepancy μ ν x).trans
    (cdfAbsoluteDiscrepancy_le_kolmogorovDistance μ ν x)

theorem kolmogorovDistance_nonneg
    (μ ν : Measure ℝ) :
    0 ≤ kolmogorovDistance μ ν :=
  (cdfAbsoluteDiscrepancy_nonneg μ ν 0).trans
    (cdfAbsoluteDiscrepancy_le_kolmogorovDistance μ ν 0)

theorem kolmogorovDistance_le_one
    (μ ν : Measure ℝ) :
    kolmogorovDistance μ ν ≤ 1 := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  exact cdfAbsoluteDiscrepancy_le_one μ ν x

@[simp]
theorem cdfDiscrepancy_self
    (μ : Measure ℝ) (x : ℝ) :
    cdfDiscrepancy μ μ x = 0 := by
  simp [cdfDiscrepancy]

@[simp]
theorem cdfAbsoluteDiscrepancy_self
    (μ : Measure ℝ) (x : ℝ) :
    cdfAbsoluteDiscrepancy μ μ x = 0 := by
  simp [cdfAbsoluteDiscrepancy]

@[simp]
theorem kolmogorovDistance_self
    (μ : Measure ℝ) :
    kolmogorovDistance μ μ = 0 := by
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨x, rfl⟩
    simp
  · exact kolmogorovDistance_nonneg μ μ

theorem cdfAbsoluteDiscrepancy_comm
    (μ ν : Measure ℝ) (x : ℝ) :
    cdfAbsoluteDiscrepancy μ ν x =
      cdfAbsoluteDiscrepancy ν μ x := by
  simp only [cdfAbsoluteDiscrepancy, cdfDiscrepancy]
  exact abs_sub_comm _ _

theorem kolmogorovDistance_comm
    (μ ν : Measure ℝ) :
    kolmogorovDistance μ ν = kolmogorovDistance ν μ := by
  unfold kolmogorovDistance
  congr 1
  ext y
  simp only [Set.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, (cdfAbsoluteDiscrepancy_comm μ ν x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, (cdfAbsoluteDiscrepancy_comm ν μ x).symm⟩

theorem cdfAbsoluteDiscrepancy_triangle
    (μ ν κ : Measure ℝ) (x : ℝ) :
    cdfAbsoluteDiscrepancy μ κ x ≤
      cdfAbsoluteDiscrepancy μ ν x +
        cdfAbsoluteDiscrepancy ν κ x := by
  unfold cdfAbsoluteDiscrepancy cdfDiscrepancy
  exact abs_sub_le _ _ _

theorem cdfPositiveDiscrepancy_triangle
    (μ ν κ : Measure ℝ) (x : ℝ) :
    cdfPositiveDiscrepancy μ κ x ≤
      cdfPositiveDiscrepancy μ ν x +
        cdfPositiveDiscrepancy ν κ x := by
  unfold cdfPositiveDiscrepancy cdfDiscrepancy
  rw [max_le_iff]
  constructor
  · have hμν :
        cdf μ x - cdf ν x ≤ max (cdf μ x - cdf ν x) 0 :=
      le_max_left _ _
    have hνκ :
        cdf ν x - cdf κ x ≤ max (cdf ν x - cdf κ x) 0 :=
      le_max_left _ _
    linarith
  · exact add_nonneg (le_max_right _ _) (le_max_right _ _)

theorem kolmogorovDistance_triangle
    (μ ν κ : Measure ℝ) :
    kolmogorovDistance μ κ ≤
      kolmogorovDistance μ ν + kolmogorovDistance ν κ := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  exact (cdfAbsoluteDiscrepancy_triangle μ ν κ x).trans
    (add_le_add
      (cdfAbsoluteDiscrepancy_le_kolmogorovDistance μ ν x)
      (cdfAbsoluteDiscrepancy_le_kolmogorovDistance ν κ x))

theorem kolmogorovDistance_eq_zero_iff
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    kolmogorovDistance μ ν = 0 ↔ μ = ν := by
  constructor
  · intro h
    refine Measure.eq_of_cdf μ ν ?_
    ext x
    have hpoint :=
      cdfAbsoluteDiscrepancy_le_kolmogorovDistance μ ν x
    rw [h] at hpoint
    have hzero : cdf μ x - cdf ν x = 0 :=
      abs_eq_zero.mp (le_antisymm hpoint (abs_nonneg _))
    exact sub_eq_zero.mp hzero
  · rintro rfl
    exact kolmogorovDistance_self μ

/-! ## Closed and strict half-line conventions -/

theorem cdf_eq_probability_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    cdf μ x = μ.real (Iic x) :=
  cdf_eq_real μ x

theorem probability_le_eq_probability_lt_add_atom
    (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    μ.real (Iic x) = μ.real (Iio x) + μ.real {x} := by
  rw [show Iic x = Iio x ∪ {x} by ext y; simp [le_iff_lt_or_eq]]
  exact measureReal_union (by simp) (measurableSet_singleton x)

theorem cdf_eq_probability_lt_add_atom
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    cdf μ x = μ.real (Iio x) + μ.real {x} := by
  rw [cdf_eq_probability_le,
    probability_le_eq_probability_lt_add_atom]

theorem cdf_sub_probability_lt_eq_atom
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    cdf μ x - μ.real (Iio x) = μ.real {x} := by
  rw [cdf_eq_probability_lt_add_atom]
  ring

theorem cdf_eq_probability_lt_of_noAtom
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {x : ℝ}
    (hx : μ {x} = 0) :
    cdf μ x = μ.real (Iio x) := by
  have hxReal : μ.real {x} = 0 := by
    simp [measureReal_def, hx]
  rw [cdf_eq_probability_lt_add_atom, hxReal, add_zero]

theorem one_sub_cdf_eq_probability_gt
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    1 - cdf μ x = μ.real (Ioi x) := by
  rw [cdf_eq_probability_le,
    ← probReal_compl_eq_one_sub measurableSet_Iic]
  congr 2
  simp

theorem one_sub_probability_lt_eq_probability_ge
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    1 - μ.real (Iio x) = μ.real (Ici x) := by
  rw [← probReal_compl_eq_one_sub measurableSet_Iio]
  congr 2
  simp

theorem probability_ge_eq_one_sub_cdf_add_atom
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    μ.real (Ici x) = 1 - cdf μ x + μ.real {x} := by
  rw [← one_sub_probability_lt_eq_probability_ge,
    cdf_eq_probability_lt_add_atom]
  ring

theorem probability_ge_eq_one_sub_cdf_of_noAtom
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {x : ℝ}
    (hx : μ {x} = 0) :
    μ.real (Ici x) = 1 - cdf μ x := by
  rw [probability_ge_eq_one_sub_cdf_add_atom, measureReal_def, hx]
  simp

/-! ## Affine pushforwards -/

theorem cdf_map_add_const
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (b x : ℝ) :
    cdf (μ.map fun y : ℝ => y + b) x = cdf μ (x - b) := by
  let : IsProbabilityMeasure (μ.map fun y : ℝ => y + b) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic,
    cdf_eq_real]
  congr 2
  ext y
  simp

theorem cdf_map_const_add
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (b x : ℝ) :
    cdf (μ.map fun y : ℝ => b + y) x = cdf μ (x - b) := by
  simpa [add_comm] using cdf_map_add_const μ b x

theorem cdf_map_mul_pos
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a : ℝ} (ha : 0 < a) (x : ℝ) :
    cdf (μ.map fun y : ℝ => a * y) x = cdf μ (x / a) := by
  let : IsProbabilityMeasure (μ.map fun y : ℝ => a * y) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic,
    cdf_eq_real]
  congr 2
  ext y
  simp only [Set.mem_preimage, Set.mem_Iic]
  rw [mul_comm]
  exact (le_div_iff₀ ha).symm

theorem cdf_map_affine_pos
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a : ℝ} (ha : 0 < a) (b x : ℝ) :
    cdf (μ.map fun y : ℝ => a * y + b) x =
      cdf μ ((x - b) / a) := by
  let : IsProbabilityMeasure (μ.map fun y : ℝ => a * y + b) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic,
    cdf_eq_real]
  congr 2
  ext y
  simp only [Set.mem_preimage, Set.mem_Iic]
  constructor <;> intro h
  · apply (le_div_iff₀ ha).2
    nlinarith
  · have h' := (le_div_iff₀ ha).1 h
    nlinarith

theorem kolmogorovDistance_map_add_const
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (b : ℝ) :
    kolmogorovDistance (μ.map fun y : ℝ => y + b)
      (ν.map fun y : ℝ => y + b) =
        kolmogorovDistance μ ν := by
  let : IsProbabilityMeasure (μ.map fun y : ℝ => y + b) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let : IsProbabilityMeasure (ν.map fun y : ℝ => y + b) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  unfold kolmogorovDistance
  congr 1
  ext z
  simp only [Set.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x - b, ?_⟩
    simp only [cdfAbsoluteDiscrepancy, cdfDiscrepancy,
      cdf_map_add_const]
  · rintro ⟨x, rfl⟩
    refine ⟨x + b, ?_⟩
    simp only [cdfAbsoluteDiscrepancy, cdfDiscrepancy,
      cdf_map_add_const]
    ring_nf

theorem kolmogorovDistance_map_affine_pos
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {a : ℝ} (ha : 0 < a) (b : ℝ) :
    kolmogorovDistance (μ.map fun y : ℝ => a * y + b)
      (ν.map fun y : ℝ => a * y + b) =
        kolmogorovDistance μ ν := by
  let : IsProbabilityMeasure (μ.map fun y : ℝ => a * y + b) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let : IsProbabilityMeasure (ν.map fun y : ℝ => a * y + b) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  unfold kolmogorovDistance
  congr 1
  ext z
  simp only [Set.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(x - b) / a, ?_⟩
    simp only [cdfAbsoluteDiscrepancy, cdfDiscrepancy,
      cdf_map_affine_pos _ ha]
  · rintro ⟨x, rfl⟩
    refine ⟨a * x + b, ?_⟩
    simp only [cdfAbsoluteDiscrepancy, cdfDiscrepancy,
      cdf_map_affine_pos _ ha]
    have ha0 : a ≠ 0 := ne_of_gt ha
    have hx : (a * x + b - b) / a = x := by
      field_simp
      ring
    rw [hx]

end Probability
end CertifiedJL
