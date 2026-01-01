/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.Counterexamples.L2Upper.ExperimentGeometry

-- See the corresponding note in `GaussianComparison`.
set_option Elab.async false

/-!
# The sparse upper-336 counterexample

This file identifies the analytic tensor bound with the modular sparse-matrix
experiment and exports the concrete all-ones counterexample theorem.
-/

open scoped BigOperators ENNReal

open MeasureTheory

namespace CertifiedJL
open Probability
namespace Counterexamples.SparseUpper.Internal

/--
The paper's modular failure event has exactly the row-sum probability used by
the tensor comparison.
-/
theorem counterexampleEventProbability_eq :
    eventProbability
        (sparseRademacherMatrix rowCount counterexampleDimension)
        (fun J =>
          modularProjectionSqNorm counterexampleModulus J
              sparseUpperCounterexampleVector >
            336 * sqNorm sparseUpperCounterexampleVector) =
      sparseAllOnesRowSumsPMF.toMeasure
        {z | 336 * dimension < discreteSqNorm z} := by
  have hcompact :
    eventProbability
        (sparseRademacherMatrix rowCount counterexampleDimension)
        sparseUpperMatrixFailure =
      sparseAllOnesRowSumsPMF.toMeasure
        {z | sparseUpperRowSumFailure z} := by
    rw [sparseRademacherMatrix_eq_map_uniformSeed,
      sparseAllOnesRowSumsPMF_eq_map_uniformSeed,
      ← eventProbability_eq_toMeasure]
    exact eventProbability_map_congr _ _ _ _ _ sparseUpperFailure_iff
  rw [show
      (fun J : Fin rowCount → Fin counterexampleDimension → ℤ =>
        modularProjectionSqNorm counterexampleModulus J
            sparseUpperCounterexampleVector >
          336 * sqNorm sparseUpperCounterexampleVector) =
        sparseUpperMatrixFailure by
      funext J
      unfold sparseUpperMatrixFailure
      rw [allOnesVector_eq_counterexampleVector],
    show
      {z : Fin 256 → ℤ | 336 * dimension < discreteSqNorm z} =
        {z | sparseUpperRowSumFailure z} by rfl]
  exact hcompact

/-- The strict sparse upper constant `336` fails with certified margin. -/
theorem sparseUpper336Counterexample_internal :
    SparseUpper336CounterexampleStatement := by
  dsimp only [SparseUpper336CounterexampleStatement]
  refine ⟨?_, ?_, ?_⟩
  · decide
  · intro hzero
    have hcoordinate := congrFun hzero
      (⟨0, by norm_num [counterexampleDimension, counterexampleSide]⟩ :
        Fin counterexampleDimension)
    norm_num [sparseUpperCounterexampleVector] at hcoordinate
  rw [counterexampleEventProbability_eq]
  exact tensorLowerBound_gt.trans_le (tensorComparison 336)

end Counterexamples.SparseUpper.Internal

/--
The sparse upper threshold cannot be lowered from `338` to `336`: the
explicit all-ones witness fails with probability greater than
`(69/50) · 2⁻¹²⁸`.
-/
theorem ternaryUpper336Counterexample :
    SparseUpper336CounterexampleStatement :=
  Counterexamples.SparseUpper.Internal.sparseUpper336Counterexample_internal

end CertifiedJL
