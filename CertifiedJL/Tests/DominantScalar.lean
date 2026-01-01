/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Unrestricted.Scalar

/-! # Producer canaries for dominant scalar reindexing -/

namespace CertifiedJL.Tests

private def weights : Fin 3 → ℤ := ![2, -3, 5]

private def remainderSeed :
    DominantRemainderIndex (1 : Fin 3) → Bool × Bool :=
  fun j => if j.1 = 0 then (false, false) else (true, true)

private noncomputable def normalizedRemainderWeights :
    Fin (Fintype.card (DominantRemainderIndex (1 : Fin 3))) → ℝ :=
  fun j => (dominantRemainderFinWeights weights (1 : Fin 3) j : ℝ) /
    Real.sqrt (dominantRemainderSqNorm weights (1 : Fin 3) : ℝ)

private noncomputable def normalizedRemainderSupport :=
  Finset.univ.filter fun j => normalizedRemainderWeights j ≠ 0

private def weightsWithZero : Fin 3 → ℤ := ![0, -3, 5]

private noncomputable def zeroNormalizedRemainderWeights :
    Fin (Fintype.card (DominantRemainderIndex (1 : Fin 3))) → ℝ :=
  fun j => (dominantRemainderFinWeights weightsWithZero (1 : Fin 3) j : ℝ) /
    Real.sqrt (dominantRemainderSqNorm weightsWithZero (1 : Fin 3) : ℝ)

private noncomputable def zeroNormalizedRemainderSupport :=
  Finset.univ.filter fun j => zeroNormalizedRemainderWeights j ≠ 0

example : sqNorm (dominantRemainderFinWeights weights (1 : Fin 3)) = 29 := by
  rw [sqNorm_dominantRemainderFinWeights]
  decide

example :
    dominantRemainderRowSeedDot remainderSeed weights =
      ∑ j, sparseBit
          (dominantRemainderRowSeedEquivFin (1 : Fin 3) remainderSeed j) *
        dominantRemainderFinWeights weights (1 : Fin 3) j := by
  exact dominantRemainderRowSeedDot_eq_fin
    (1 : Fin 3) remainderSeed weights

example :
    (PMF.uniformOfFintype
      (DominantRemainderIndex (1 : Fin 3) → Bool × Bool)).map
        (fun seed => sparseRow
          (dominantRemainderRowSeedEquivFin (1 : Fin 3) seed)) =
      sparseRademacherRow
        (Fintype.card (DominantRemainderIndex (1 : Fin 3))) := by
  exact map_uniformDominantRemainderRowSeed_reindex (1 : Fin 3)

example : Fintype.card (DominantRemainderIndex (1 : Fin 3)) = 2 := by
  decide

example (q : ℕ) (hq : Odd q) :
    ENNReal.ofReal
        (∫ row, Real.exp
          (-2 * ((centeredMod q
            (∑ j, row j * dominantRemainderFinWeights weights (1 : Fin 3) j : ℤ) : ℝ) /
              Real.sqrt (dominantRemainderSqNorm weights (1 : Fin 3) : ℝ)) ^ 2)
          ∂(sparseRademacherRow
            (Fintype.card (DominantRemainderIndex (1 : Fin 3)))).toMeasure) ≤
      ENNReal.ofReal
        (∫ row, Real.exp
          (-2 * (((∑ j,
              row j * dominantRemainderFinWeights weights (1 : Fin 3) j : ℤ) : ℝ) /
              Real.sqrt (dominantRemainderSqNorm weights (1 : Fin 3) : ℝ)) ^ 2)
          ∂(sparseRademacherRow
            (Fintype.card (DominantRemainderIndex (1 : Fin 3)))).toMeasure) +
      ENNReal.ofReal
        (2 * Real.exp
          (-2 * ((q : ℝ) /
            Real.sqrt (dominantRemainderSqNorm weights (1 : Fin 3) : ℝ)) ^ 2 /
              (1 + 2)) /
          (1 - (Real.exp
            (-2 * ((q : ℝ) /
              Real.sqrt (dominantRemainderSqNorm weights (1 : Fin 3) : ℝ)) ^ 2 /
                (1 + 2))) ^ 3)) := by
  exact dominantRemainderFin_normalizedPeriodization_nonzeroImageBound
    weights (1 : Fin 3) q 2 hq (by decide) (by norm_num)

example :
    ENNReal.ofReal
        (∫ row, Real.exp
          (-1 * (realRowDot row normalizedRemainderWeights) ^ 2)
          ∂(sparseRademacherRow
            (Fintype.card (DominantRemainderIndex (1 : Fin 3)))).toMeasure) ≤
      ∏ j ∈ normalizedRemainderSupport,
        gaussianCosineMoment 1 (2 / (normalizedRemainderWeights j ^ 2)) ^
          (normalizedRemainderWeights j ^ 2) := by
  exact dominantRemainderFin_scalarReduction
    weights (1 : Fin 3) 1 (by decide) (by norm_num)

example :
    ENNReal.ofReal
        (∫ row, Real.exp
          (-0 * (realRowDot row zeroNormalizedRemainderWeights) ^ 2)
          ∂(sparseRademacherRow
            (Fintype.card (DominantRemainderIndex (1 : Fin 3)))).toMeasure) ≤
      ∏ j ∈ zeroNormalizedRemainderSupport,
        gaussianCosineMoment 0 (2 / (zeroNormalizedRemainderWeights j ^ 2)) ^
          (zeroNormalizedRemainderWeights j ^ 2) := by
  exact dominantRemainderFin_scalarReduction
    weightsWithZero (1 : Fin 3) 0 (by decide) (by norm_num)

example (q : ℕ) (hq : Odd q) (s : ℝ) (hs : 0 < s) :
    ENNReal.ofReal
        (∫ row, Real.exp
          (-s * ((centeredMod q
            (∑ j, row j * dominantRemainderFinWeights weights (1 : Fin 3) j : ℤ) : ℝ) /
              Real.sqrt (dominantRemainderSqNorm weights (1 : Fin 3) : ℝ)) ^ 2)
          ∂(sparseRademacherRow
            (Fintype.card (DominantRemainderIndex (1 : Fin 3)))).toMeasure) ≤
      (∏ j ∈ normalizedRemainderSupport,
          gaussianCosineMoment s (2 / (normalizedRemainderWeights j ^ 2)) ^
            (normalizedRemainderWeights j ^ 2)) +
        ENNReal.ofReal
          (2 * Real.exp
            (-s * ((q : ℝ) /
              Real.sqrt (dominantRemainderSqNorm weights (1 : Fin 3) : ℝ)) ^ 2 /
                (1 + s)) /
            (1 - (Real.exp
              (-s * ((q : ℝ) /
                Real.sqrt (dominantRemainderSqNorm weights (1 : Fin 3) : ℝ)) ^ 2 /
                  (1 + s))) ^ 3)) := by
  exact dominantRemainderFin_modular_le_scalarProduct_add_wrap
    weights (1 : Fin 3) q s hq (by decide) hs

end CertifiedJL.Tests
