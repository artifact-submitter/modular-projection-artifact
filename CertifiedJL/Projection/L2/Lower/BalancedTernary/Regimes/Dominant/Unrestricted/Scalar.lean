/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Unrestricted.Kernel
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Shared.CosineLaplace
import CertifiedJL.Analysis.Fourier.LowerPeriodization

/-!
# Scalar adapters for dominant remainder rows

This module reindexes the dependent remainder-coordinate type by a canonical
finite type, preserving its natural norm, uniform sparse seed law, and dot
product. The existing scalar Fourier and periodization theorems can therefore
be applied without changing the dominant-coordinate semantics.
-/

namespace CertifiedJL

/-- Canonical finite enumeration of coordinates other than `i`. -/
noncomputable def dominantRemainderEquivFin {d : ℕ} (i : Fin d) :
    DominantRemainderIndex i ≃ Fin (Fintype.card (DominantRemainderIndex i)) :=
  Fintype.equivFin _

/-- Remainder coefficients in the canonical finite enumeration. -/
noncomputable def dominantRemainderFinWeights {d : ℕ}
    (w : Fin d → ℤ) (i : Fin d) :
    Fin (Fintype.card (DominantRemainderIndex i)) → ℤ :=
  fun j => w ((dominantRemainderEquivFin i).symm j).1

/-- Reindex one row-local remainder seed by the canonical finite enumeration. -/
noncomputable def dominantRemainderRowSeedEquivFin {d : ℕ} (i : Fin d) :
    (DominantRemainderIndex i → Bool × Bool) ≃
      SparseRowSeed (Fintype.card (DominantRemainderIndex i)) where
  toFun seed j := seed ((dominantRemainderEquivFin i).symm j)
  invFun seed j := seed (dominantRemainderEquivFin i j)
  left_inv seed := by
    funext j
    simp
  right_inv seed := by
    funext j
    simp

/-- Reindexing preserves the natural squared remainder norm exactly. -/
theorem sqNorm_dominantRemainderFinWeights {d : ℕ}
    (w : Fin d → ℤ) (i : Fin d) :
    sqNorm (dominantRemainderFinWeights w i) =
      dominantRemainderSqNorm w i := by
  unfold sqNorm dominantRemainderFinWeights dominantRemainderSqNorm
  exact (dominantRemainderEquivFin i).symm.sum_comp
    (fun j : DominantRemainderIndex i => (w j.1).natAbs ^ 2)

/-- Reindexing preserves every remainder dot product exactly. -/
theorem dominantRemainderRowSeedDot_eq_fin {d : ℕ}
    (i : Fin d) (seed : DominantRemainderIndex i → Bool × Bool)
    (w : Fin d → ℤ) :
    dominantRemainderRowSeedDot seed w =
      ∑ j, sparseBit (dominantRemainderRowSeedEquivFin i seed j) *
        dominantRemainderFinWeights w i j := by
  unfold dominantRemainderRowSeedDot dominantRemainderRowSeedEquivFin
    dominantRemainderFinWeights
  exact ((dominantRemainderEquivFin i).symm.sum_comp
    (fun j : DominantRemainderIndex i => sparseBit (seed j) * w j.1)).symm

/-- The reindexed uniform remainder seed produces the ordinary sparse-row PMF. -/
theorem map_uniformDominantRemainderRowSeed_reindex {d : ℕ} (i : Fin d) :
    (PMF.uniformOfFintype
      (DominantRemainderIndex i → Bool × Bool)).map
        (fun seed => sparseRow (dominantRemainderRowSeedEquivFin i seed)) =
      sparseRademacherRow (Fintype.card (DominantRemainderIndex i)) := by
  calc
    _ = ((PMF.uniformOfFintype
          (DominantRemainderIndex i → Bool × Bool)).map
            (dominantRemainderRowSeedEquivFin i)).map sparseRow := by
      rw [PMF.map_comp]
      rfl
    _ = _ := by
      rw [map_uniformOfFintype_equiv]
      exact (sparseRademacherRow_eq_map_uniformRowSeed _).symm

/--
The nonzero modular images of the canonically reindexed dominant remainder
obey the quantitative periodization bound at its natural squared norm.
-/
theorem dominantRemainderFin_normalizedPeriodization_nonzeroImageBound
    {d : ℕ} (w : Fin d → ℤ) (i : Fin d) (q : ℕ) (s : ℝ)
    (hq : Odd q) (hU : 0 < dominantRemainderSqNorm w i) (hs : 0 < s) :
    ENNReal.ofReal
        (∫ row, Real.exp
          (-s * ((centeredMod q
            (∑ j, row j * dominantRemainderFinWeights w i j : ℤ) : ℝ) /
              Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2)
          ∂(sparseRademacherRow
            (Fintype.card (DominantRemainderIndex i))).toMeasure) ≤
      ENNReal.ofReal
        (∫ row, Real.exp
          (-s * (((∑ j, row j * dominantRemainderFinWeights w i j : ℤ) : ℝ) /
              Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2)
          ∂(sparseRademacherRow
            (Fintype.card (DominantRemainderIndex i))).toMeasure) +
      ENNReal.ofReal
        (2 * Real.exp
          (-s * ((q : ℝ) /
            Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 / (1 + s)) /
          (1 - (Real.exp
            (-s * ((q : ℝ) /
              Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 /
                (1 + s))) ^ 3)) := by
  have hU' : 0 < (dominantRemainderSqNorm w i : ℝ) := by
    exact_mod_cast hU
  have hnorm :
      ∑ j, (dominantRemainderFinWeights w i j : ℝ) ^ 2 =
        (dominantRemainderSqNorm w i : ℝ) := by
    rw [← realCast_sqNorm, sqNorm_dominantRemainderFinWeights]
  exact sparseRow_normalizedPeriodization_nonzeroImageBound
    (dominantRemainderFinWeights w i) q
      (dominantRemainderSqNorm w i : ℝ) s hq hU' hnorm hs

/--
The zero modular image of a nonzero dominant remainder is bounded by the
existing scalar Fourier/Hölder product after canonical reindexing. Zero
coefficients are removed before reciprocal Hölder exponents are formed.
-/
theorem dominantRemainderFin_scalarReduction
    {d : ℕ} (w : Fin d → ℤ) (i : Fin d) (s : ℝ)
    (hU : 0 < dominantRemainderSqNorm w i) (hs : 0 ≤ s) :
    let a : Fin (Fintype.card (DominantRemainderIndex i)) → ℝ :=
      fun j => (dominantRemainderFinWeights w i j : ℝ) /
        Real.sqrt (dominantRemainderSqNorm w i : ℝ)
    let S := Finset.univ.filter fun j => a j ≠ 0
    ENNReal.ofReal
        (∫ row, Real.exp (-s * (realRowDot row a) ^ 2)
          ∂(sparseRademacherRow
            (Fintype.card (DominantRemainderIndex i))).toMeasure) ≤
      ∏ j ∈ S, gaussianCosineMoment s (2 / (a j ^ 2)) ^ (a j ^ 2) := by
  dsimp only
  let a : Fin (Fintype.card (DominantRemainderIndex i)) → ℝ :=
    fun j => (dominantRemainderFinWeights w i j : ℝ) /
      Real.sqrt (dominantRemainderSqNorm w i : ℝ)
  let S := Finset.univ.filter fun j => a j ≠ 0
  have hU' : 0 < (dominantRemainderSqNorm w i : ℝ) := by
    exact_mod_cast hU
  have hsqrt_sq :
      Real.sqrt (dominantRemainderSqNorm w i : ℝ) ^ 2 =
        (dominantRemainderSqNorm w i : ℝ) := Real.sq_sqrt hU'.le
  have hnorm :
      ∑ j, (dominantRemainderFinWeights w i j : ℝ) ^ 2 =
        (dominantRemainderSqNorm w i : ℝ) := by
    rw [← realCast_sqNorm, sqNorm_dominantRemainderFinWeights]
  have hS : ∀ j, j ∈ S ↔ a j ≠ 0 := by
    intro j
    simp [S]
  have ha : ∑ j, a j ^ 2 = 1 := by
    calc
      ∑ j, a j ^ 2 =
          ∑ j, (dominantRemainderFinWeights w i j : ℝ) ^ 2 /
            (dominantRemainderSqNorm w i : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [a]
        rw [div_pow, hsqrt_sq]
      _ = (∑ j, (dominantRemainderFinWeights w i j : ℝ) ^ 2) /
          (dominantRemainderSqNorm w i : ℝ) := by
        rw [Finset.sum_div]
      _ = 1 := by
        rw [hnorm, div_self hU'.ne']
  exact sparseScalarReduction s a S hS hs ha

/--
The complete inactive-remainder scalar estimate available before the local
L17 numeric comparison: the modular kernel is bounded by the exact
Fourier/Hölder product plus the explicit nonzero-image error.
-/
theorem dominantRemainderFin_modular_le_scalarProduct_add_wrap
    {d : ℕ} (w : Fin d → ℤ) (i : Fin d) (q : ℕ) (s : ℝ)
    (hq : Odd q) (hU : 0 < dominantRemainderSqNorm w i) (hs : 0 < s) :
    let a : Fin (Fintype.card (DominantRemainderIndex i)) → ℝ :=
      fun j => (dominantRemainderFinWeights w i j : ℝ) /
        Real.sqrt (dominantRemainderSqNorm w i : ℝ)
    let S := Finset.univ.filter fun j => a j ≠ 0
    ENNReal.ofReal
        (∫ row, Real.exp
          (-s * ((centeredMod q
            (∑ j, row j * dominantRemainderFinWeights w i j : ℤ) : ℝ) /
              Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2)
          ∂(sparseRademacherRow
            (Fintype.card (DominantRemainderIndex i))).toMeasure) ≤
      (∏ j ∈ S,
          gaussianCosineMoment s (2 / (a j ^ 2)) ^ (a j ^ 2)) +
        ENNReal.ofReal
          (2 * Real.exp
            (-s * ((q : ℝ) /
              Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 / (1 + s)) /
            (1 - (Real.exp
              (-s * ((q : ℝ) /
                Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2 /
                  (1 + s))) ^ 3)) := by
  dsimp only
  let a : Fin (Fintype.card (DominantRemainderIndex i)) → ℝ :=
    fun j => (dominantRemainderFinWeights w i j : ℝ) /
      Real.sqrt (dominantRemainderSqNorm w i : ℝ)
  let S := Finset.univ.filter fun j => a j ≠ 0
  have hzero := dominantRemainderFin_scalarReduction w i s hU hs.le
  have hdot (row : Fin (Fintype.card (DominantRemainderIndex i)) → ℤ) :
      realRowDot row a =
        ((∑ j, row j * dominantRemainderFinWeights w i j : ℤ) : ℝ) /
          Real.sqrt (dominantRemainderSqNorm w i : ℝ) := by
    simp only [realRowDot, a, Int.cast_sum, Int.cast_mul]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hzero' :
      ENNReal.ofReal
          (∫ row, Real.exp
            (-s * (((∑ j,
                row j * dominantRemainderFinWeights w i j : ℤ) : ℝ) /
              Real.sqrt (dominantRemainderSqNorm w i : ℝ)) ^ 2)
            ∂(sparseRademacherRow
              (Fintype.card (DominantRemainderIndex i))).toMeasure) ≤
        ∏ j ∈ S,
          gaussianCosineMoment s (2 / (a j ^ 2)) ^ (a j ^ 2) := by
    dsimp [S, a] at hzero ⊢
    convert hzero using 1
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with row
    rw [hdot]
  exact (dominantRemainderFin_normalizedPeriodization_nonzeroImageBound
    w i q s hq hU hs).trans (add_le_add hzero' le_rfl)

end CertifiedJL
