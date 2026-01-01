/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Unrestricted.Conditioning
import Mathlib.Tactic.NormNum

/-!
# Producer canaries for dominant-coordinate conditioning

The examples distinguish active and inactive pairs, both active signs, a
nontrivial row set, the conditional product law, and boundary/interior
binomial masses.
-/

namespace CertifiedJL.Tests

/-- Equal false bits are active with negative sign. -/
example :
    (sparsePairActivity (false, false), sparsePairSign (false, false),
      sparseBit (false, false)) = (true, false, -1) := by
  decide

/-- Equal true bits are active with positive sign. -/
example :
    (sparsePairActivity (true, true), sparsePairSign (true, true),
      sparseBit (true, true)) = (true, true, 1) := by
  decide

/-- The first unequal orientation is inactive. -/
example :
    (sparsePairActivity (false, true), sparsePairSign (false, true),
      sparseBit (false, true)) = (false, false, 0) := by
  decide

/-- The other unequal orientation is also inactive but retains its sign bit. -/
example :
    (sparsePairActivity (true, false), sparsePairSign (true, false),
      sparseBit (true, false)) = (false, true, 0) := by
  decide

/-- Inactive/negative view input reassembles the first unequal pair. -/
example : sparsePairOfActivitySign false false = (false, true) := by decide

/-- Inactive/positive view input reassembles the other unequal pair. -/
example : sparsePairOfActivitySign false true = (true, false) := by decide

/-- Active/negative view input reassembles the negative sparse entry. -/
example : sparsePairOfActivitySign true false = (false, false) := by decide

/-- Active/positive view input reassembles the positive sparse entry. -/
example : sparsePairOfActivitySign true true = (true, true) := by decide

private def seedCanary : SparseSeed 2 2
  | 0, 0 => (false, false)
  | 0, 1 => (false, true)
  | 1, 0 => (true, false)
  | 1, 1 => (true, true)

/-- The view selects only the distinguished coordinate for activity. -/
example : (dominantSeedView (0 : Fin 2) seedCanary).1 = ![true, false] := by
  decide

/-- The dominant signs remain visible even on an inactive row. -/
example : (dominantSeedView (0 : Fin 2) seedCanary).2.1 = ![false, true] := by
  decide

/-- The other coordinate has the asymmetric complementary activity pattern. -/
example : (dominantSeedView (1 : Fin 2) seedCanary).1 = ![false, true] := by
  decide

/-- Actual matrices recover activity at coordinate one as well. -/
example :
    matrixDominantActivity (1 : Fin 2) (sparseMatrix seedCanary) =
      ![false, true] := by
  decide

private def asymmetricView : DominantSeedView (m := 2) (1 : Fin 2) :=
  (![true, false],
    (![false, true], fun row _ => if row = 0 then (true, true) else (false, true)))

/-- A view assembled independently from any seed survives view-seed-view. -/
example :
    dominantSeedView (1 : Fin 2)
        (sparseSeedOfDominantView (1 : Fin 2) asymmetricView) =
      asymmetricView := by
  exact dominantSeedView_ofView (1 : Fin 2) asymmetricView

/-- Reassembly preserves all four distinguishable seed entries. -/
example : sparseSeedOfDominantView (0 : Fin 2)
    (dominantSeedView (0 : Fin 2) seedCanary) = seedCanary := by
  exact sparseSeedOfDominantView_view (0 : Fin 2) seedCanary

/-- The concrete conditioning law samples activity before uniform residual data. -/
example :
    PMF.uniformOfFintype (DominantSeedView (m := 2) (0 : Fin 2)) =
      (PMF.uniformOfFintype (DominantActivity 2)).bind fun activity =>
        (PMF.uniformOfFintype
          (DominantConditionalSeeds (m := 2) (0 : Fin 2))).map
            fun conditional => (activity, conditional) := by
  exact uniformDominantSeedView_eq_bind (0 : Fin 2)

/-- The mapped sparse-seed view itself has the activity-first bind law. -/
example :
    (PMF.uniformOfFintype (SparseSeed 2 2)).map
        (dominantSeedView (1 : Fin 2)) =
      (PMF.uniformOfFintype (DominantActivity 2)).bind fun activity =>
        (PMF.uniformOfFintype
          (DominantConditionalSeeds (m := 2) (1 : Fin 2))).map
            fun conditional => (activity, conditional) := by
  exact map_uniformSparseSeed_dominantView_eq_bind (1 : Fin 2)

/-- The actual matrix PMF retains signs and remainders in the bind law. -/
example :
    sparseRademacherMatrix 2 2 =
      (PMF.uniformOfFintype (DominantActivity 2)).bind fun activity =>
        (PMF.uniformOfFintype
          (DominantConditionalSeeds (m := 2) (1 : Fin 2))).map
            fun conditional =>
              sparseMatrixOfDominantView (1 : Fin 2) (activity, conditional) := by
  exact sparseRademacherMatrix_eq_dominant_bind (1 : Fin 2)

/-- The actual matrix recovers the active set, not merely a seed-side proxy. -/
example :
    matrixDominantActivity (0 : Fin 2) (sparseMatrix seedCanary) =
      ![true, false] := by
  decide

/-- The count counts true activity bits, not their inactive complement. -/
example : dominantActivityCount ![true, true, false] = (2 : Fin 4) := by
  decide

/-- The all-inactive mass is exactly `2^-256`. -/
example :
    ((sparseRademacherMatrix 256 1).map
        (dominantActivityCount ∘ matrixDominantActivity (0 : Fin 1)))
        (0 : Fin 257) = ((2 ^ 256 : ℕ) : ENNReal)⁻¹ := by
  simpa using sparseRademacherMatrix_dominantActivityCount_apply
    (0 : Fin 1) (0 : Fin 257)

/-- An interior mass pins the choose factor and count index. -/
example :
    ((sparseRademacherMatrix 256 1).map
        (dominantActivityCount ∘ matrixDominantActivity (0 : Fin 1)))
        (128 : Fin 257) =
      ((256 : ℕ).choose 128 : ENNReal) *
        ((2 ^ 256 : ℕ) : ENNReal)⁻¹ := by
  exact sparseRademacherMatrix_dominantActivityCount_apply
    (0 : Fin 1) (128 : Fin 257)

/-- A coordinate-one specialization pins the actual matrix projection index. -/
example :
    ((sparseRademacherMatrix 256 2).map
        (dominantActivityCount ∘ matrixDominantActivity (1 : Fin 2)))
        (128 : Fin 257) =
      ((256 : ℕ).choose 128 : ENNReal) *
        ((2 ^ 256 : ℕ) : ENNReal)⁻¹ := by
  exact sparseRademacherMatrix_dominantActivityCount_apply
    (1 : Fin 2) (128 : Fin 257)

/-- The all-active mass is also exactly `2^-256`. -/
example :
    ((sparseRademacherMatrix 256 1).map
        (dominantActivityCount ∘ matrixDominantActivity (0 : Fin 1)))
        (256 : Fin 257) = ((2 ^ 256 : ℕ) : ENNReal)⁻¹ := by
  simpa using sparseRademacherMatrix_dominantActivityCount_apply
    (0 : Fin 1) (256 : Fin 257)

end CertifiedJL.Tests
