/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Unrestricted.Normalization
import Mathlib.Tactic.NormNum

/-!
# Producer canaries for dominant normalization and symmetry
-/

namespace CertifiedJL.Tests

private def coefficients : Fin 3 → ℤ := ![3, -4, 0]

/-- Natural norm decomposition pins `A²=16`, `U=9`, and `V=25`. -/
example :
    sqNorm coefficients =
      (coefficients 1).natAbs ^ 2 +
        dominantRemainderSqNorm coefficients 1 := by
  exact sqNorm_eq_dominant_add_remainder coefficients 1

example : dominantAmplitude coefficients 1 = 4 := by
  decide

example : dominantRemainderSqNorm coefficients 1 = 9 := by
  decide

example : sqNorm coefficients = 25 := by
  decide

/-- The real normalization is exactly `u=9/16`. -/
example : dominantResidualRatio coefficients 1 = (9 : ℝ) / 16 := by
  rw [dominantResidualRatio]
  rw [show dominantRemainderSqNorm coefficients 1 = 9 by decide]
  norm_num [dominantAmplitude, coefficients]

/-- The bridge retains the total natural norm: `1+u=25/16`. -/
example : 1 + dominantResidualRatio coefficients 1 = (25 : ℝ) / 16 := by
  rw [one_add_dominantResidualRatio coefficients 1 (by decide)]
  rw [show sqNorm coefficients = 25 by decide]
  norm_num [dominantAmplitude, coefficients]

private def rowSeed : SparseSeed 2 3
  | 0, 0 => (false, false)
  | 0, 1 => (true, true)
  | 0, 2 => (false, true)
  | 1, 0 => (true, true)
  | 1, 1 => (true, false)
  | 1, 2 => (false, false)

/-- Row zero is active: `(+1)(-4) + (-1)(3) = -7`. -/
example : rowDot (sparseMatrix rowSeed) coefficients 0 = -7 := by
  decide

/-- Row one is inactive at the dominant coordinate, hence equals `R=3`. -/
example : rowDot (sparseMatrix rowSeed) coefficients 1 = 3 := by
  decide

private def oppositeActiveSignRowSeed : SparseSeed 1 3
  | 0, 0 => (false, false)
  | 0, 1 => (false, false)
  | 0, 2 => (false, true)

/-- The opposite active sign is observed on an actual reconstructed row. -/
example :
    rowDot (sparseMatrix oppositeActiveSignRowSeed) coefficients 0 = 1 := by
  decide

/-- The pointwise row decomposition selects its active branch. -/
example :
    rowDot (sparseMatrix rowSeed) coefficients 0 =
      signBit ((dominantSeedView (1 : Fin 3) rowSeed).2.1 0) *
          coefficients 1 +
        dominantRemainderDot (sparseMatrix rowSeed 0) coefficients 1 := by
  simpa [dominantSeedView, sparsePairActivity, rowSeed] using
    sparseMatrix_rowDot_dominantView rowSeed coefficients 0 (1 : Fin 3)

/-- The pointwise row decomposition also selects its inactive branch. -/
example :
    rowDot (sparseMatrix rowSeed) coefficients 1 =
      dominantRemainderDot (sparseMatrix rowSeed 1) coefficients 1 := by
  simpa [dominantSeedView, sparsePairActivity, rowSeed] using
    sparseMatrix_rowDot_dominantView rowSeed coefficients 1 (1 : Fin 3)

/-- Negating both underlying bits flips active signs and preserves zeros. -/
example :
    (sparseBit (negateSparsePairSeed (false, false)),
      sparseBit (negateSparsePairSeed (false, true)),
      sparseBit (negateSparsePairSeed (true, false)),
      sparseBit (negateSparsePairSeed (true, true))) = (1, 0, 0, -1) := by
  decide

private def asymmetricCoefficients : Fin 3 → ℤ := ![2, -3, 5]

private def asymmetricRemainderSeed :
    DominantRemainderSeeds (m := 1) (1 : Fin 3) :=
  fun _ j => if j.1 = 0 then (false, false) else (true, true)

private def asymmetricView : DominantSeedView (m := 1) (1 : Fin 3) :=
  (![true], (![false], asymmetricRemainderSeed))

/-- Reconstruction identifies the actual row remainder with the seed remainder. -/
example :
    dominantRemainderDot
        (sparseMatrixOfDominantView (1 : Fin 3) asymmetricView 0)
        asymmetricCoefficients 1 = 3 := by
  rw [dominantRemainderDot_sparseMatrixOfDominantView]
  decide

/-- The reconstructed active row is `(-1)(-3) + R = 6`. -/
example :
    rowDot (sparseMatrixOfDominantView (1 : Fin 3) asymmetricView)
        asymmetricCoefficients 0 = 6 := by
  rw [sparseMatrixOfDominantView_rowDot]
  decide

/-- Both nonzero asymmetric remainder coordinates are negated. -/
example :
    dominantRemainderSeedDot
        (negateDominantRemainderSeeds asymmetricRemainderSeed)
        asymmetricCoefficients 0 = -3 := by
  rw [dominantRemainderSeedDot_negate]
  decide

example :
    negateDominantRemainderSeeds
        (negateDominantRemainderSeeds asymmetricRemainderSeed) =
      asymmetricRemainderSeed := by
  exact negateDominantRemainderSeeds_involutive asymmetricRemainderSeed

example :
    (negateDominantRemainderSeedsEquiv (m := 1) (1 : Fin 3)).symm
        ((negateDominantRemainderSeedsEquiv (m := 1) (1 : Fin 3))
          asymmetricRemainderSeed) = asymmetricRemainderSeed := by
  exact (negateDominantRemainderSeedsEquiv (m := 1) (1 : Fin 3)).left_inv _

example :
    (PMF.uniformOfFintype
        (DominantRemainderSeeds (m := 1) (1 : Fin 3))).map
        negateDominantRemainderSeeds =
      PMF.uniformOfFintype
        (DominantRemainderSeeds (m := 1) (1 : Fin 3)) := by
  exact map_uniformDominantRemainderSeeds_negate (m := 1) (1 : Fin 3)

/-- The finite remainder law identifies the two active shifted-square laws. -/
example :
    (PMF.uniformOfFintype
      (DominantRemainderSeeds (m := 2) (1 : Fin 3))).map
        (fun seed =>
          (-coefficients 1 +
            dominantRemainderSeedDot seed coefficients 0) ^ 2) =
      (PMF.uniformOfFintype
        (DominantRemainderSeeds (m := 2) (1 : Fin 3))).map
          (fun seed =>
            (coefficients 1 +
              dominantRemainderSeedDot seed coefficients 0) ^ 2) := by
  exact activeShiftSquarePMF_symm (1 : Fin 3) coefficients 0

/-- A negative dominant coefficient and either sign reduce to `A + R`. -/
example (sign : Bool) :
    (PMF.uniformOfFintype
      (DominantRemainderSeeds (m := 1) (1 : Fin 3))).map
        (fun seed =>
          (signBit sign * asymmetricCoefficients 1 +
            dominantRemainderSeedDot seed asymmetricCoefficients 0) ^ 2) =
      (PMF.uniformOfFintype
        (DominantRemainderSeeds (m := 1) (1 : Fin 3))).map
          (fun seed =>
            (((dominantAmplitude asymmetricCoefficients 1 : ℕ) : ℤ) +
              dominantRemainderSeedDot seed asymmetricCoefficients 0) ^ 2) := by
  exact activeSignedShiftSquarePMF_eq_amplitude
    (1 : Fin 3) asymmetricCoefficients 0 sign

end CertifiedJL.Tests
