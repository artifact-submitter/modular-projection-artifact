/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Gaussian.HalfGaussian
import CertifiedJL.Projection.Counterexamples.L2Upper.EvenGaussianComparison

/-!
# Compatibility facade for the 256-row Gaussian comparison

The proof is row-parametric in `EvenGaussianComparison`; this module retains
the established 256-row names used by the two concrete endpoint assemblies.
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace CertifiedJL
open Probability
namespace Counterexamples.SparseUpper.Rows256.Internal


export Probability.SparseAllOnes
  (sparseRowSeedEquivBits sparseRowTrueCount sparseAllOnesRowSum
    sparseAllOnesRowSum_eq_trueCount sparseRowTrueCountFiberEquiv
    card_sparseRowTrueCount_fiber sparseAllOnesRowPMF
    sparseAllOnesRowPMF_apply_nat sparseAllOnesRowPMF_apply_int)

abbrev side : ℕ := highSecurityL2UpperCounterexampleSide
abbrev dimension : ℕ := highSecurityL2UpperCounterexampleDimension
def cutoff : ℕ := 10 * side
noncomputable def mesh : ℝ := (side : ℝ)⁻¹
noncomputable def coordinateBound : ℝ := 10 - mesh / 2
noncomputable def radialShift : ℝ := 256 * mesh * coordinateBound
noncomputable def radialThreshold (threshold : ℕ) : ℝ := threshold + radialShift
noncomputable def localLoss : ℝ :=
  (1 : ℝ) / dimension +
    cutoff * binomialLogStepError dimension cutoff + 10 / side
noncomputable def latticeLoss : ℝ :=
  (1 : ℝ) / dimension + cutoff * binomialLogStepError dimension cutoff
noncomputable def totalLoss : ℝ := radialShift + 256 * localLoss

@[simp] theorem side_eq : side = 100_000_000 := rfl
@[simp] theorem dimension_eq : dimension = 10_000_000_000_000_000 := by
  norm_num [dimension, side, highSecurityL2UpperCounterexampleDimension,
    highSecurityL2UpperCounterexampleSide]
@[simp] theorem cutoff_eq : cutoff = 1_000_000_000 := by
  norm_num [cutoff, side]
theorem side_pos : 0 < side := by norm_num [side]
theorem dimension_pos : 0 < dimension := by norm_num [dimension, side]
theorem cutoff_lt_dimension : cutoff < dimension := by
  norm_num [cutoff, dimension, side]
theorem mesh_pos : 0 < mesh := by norm_num [mesh, side]
theorem coordinateBound_pos : 0 < coordinateBound := by
  norm_num [coordinateBound, mesh, side]
theorem radialShift_nonneg : 0 ≤ radialShift := by
  norm_num [radialShift, coordinateBound, mesh, side]
theorem radialThreshold_nonneg (threshold : ℕ) :
    0 ≤ radialThreshold threshold := by
  unfold radialThreshold
  exact add_nonneg (Nat.cast_nonneg threshold) radialShift_nonneg

noncomputable abbrev boundedIndices : Finset ℤ := EvenGaussian.Internal.boundedIndices
noncomputable abbrev boundedVectors : Finset (Fin 256 → ℤ) :=
  EvenGaussian.Internal.boundedVectors
abbrev discreteSqNorm (z : Fin 256 → ℤ) : ℕ := EvenGaussian.Internal.discreteSqNorm z
noncomputable abbrev goodVectors (threshold : ℕ) : Finset (Fin 256 → ℤ) :=
  EvenGaussian.Internal.goodVectors threshold
abbrev gaussianBox (z : Fin 256 → ℤ) : Set (Fin 256 → ℝ) :=
  EvenGaussian.Internal.gaussianBox z
noncomputable abbrev roundIndex (x : ℝ) : ℤ := EvenGaussian.Internal.roundIndex x
noncomputable abbrev roundVector (x : Fin 256 → ℝ) : Fin 256 → ℤ :=
  EvenGaussian.Internal.roundVector x
abbrev gaussianCore (threshold : ℕ) : Set (Fin 256 → ℝ) :=
  EvenGaussian.Internal.gaussianCore threshold
noncomputable abbrev gaussianCellMass (k : ℤ) : ℝ := EvenGaussian.Internal.gaussianCellMass k
noncomputable abbrev sparseAllOnesRowSumsPMF : PMF (Fin 256 → ℤ) :=
  EvenGaussian.Internal.sparseAllOnesRowSumsPMF

/-! ## Legacy internal API

These aliases preserve the pre-generalization proof-engineering API without
duplicating its implementation. -/

abbrev gaussianCell (k : ℤ) : Set ℝ :=
  EvenGaussian.Internal.gaussianCell k
abbrev measurableSet_gaussianCell (k : ℤ) :=
  EvenGaussian.Internal.measurableSet_gaussianCell k
abbrev gaussianCell_disjoint {k l : ℤ} (hkl : k ≠ l) :=
  EvenGaussian.Internal.gaussianCell_disjoint hkl

theorem halfGaussianDensity_le_cellCenter {k : ℤ} {x : ℝ}
    (hk : k.natAbs ≤ cutoff) (hx : x ∈ gaussianCell k) :
    halfGaussianDensity x ≤
      halfGaussianDensity ((k : ℝ) * mesh) *
        Real.exp (10 / side : ℝ) := by
  simpa [halfGaussianDensity,
    HalfGaussianEven.halfGaussianDensity,
    gaussianCell, mesh, EvenGaussian.Internal.mesh,
    cutoff, EvenGaussian.Internal.cutoff,
    side, EvenGaussian.Internal.side] using
    (EvenGaussian.Internal.HalfGaussianEven.halfGaussianDensity_le_cellCenter
      hk hx)

abbrev gaussianCellMass_nonneg (k : ℤ) :=
  EvenGaussian.Internal.gaussianCellMass_nonneg k
abbrev gaussianCellMass_le {k : ℤ} (hk : k.natAbs ≤ cutoff) :=
  EvenGaussian.Internal.gaussianCellMass_le hk
abbrev sparseAllOnesRowPMF_toReal {k : ℤ} (hk : k.natAbs ≤ cutoff) :=
  EvenGaussian.Internal.sparseAllOnesRowPMF_toReal hk
abbrev sqrt_dimension :=
  EvenGaussian.Internal.sqrt_dimension
abbrev indexSquare_div_dimension (k : ℤ) :=
  EvenGaussian.Internal.indexSquare_div_dimension k
abbrev rowMass_ge_exp_mul_cell {k : ℤ} (hk : k.natAbs ≤ cutoff) :=
  EvenGaussian.Internal.rowMass_ge_exp_mul_cell hk

abbrev mem_goodVectors_iff {threshold : ℕ} {z : Fin 256 → ℤ} :=
  EvenGaussian.Internal.mem_goodVectors_iff
    (rows := 256) (threshold := threshold) (z := z)
abbrev measurableSet_gaussianBox (z : Fin 256 → ℤ) :=
  EvenGaussian.Internal.measurableSet_gaussianBox z
abbrev gaussianBox_disjoint {z z' : Fin 256 → ℤ} (hzz' : z ≠ z') :=
  EvenGaussian.Internal.gaussianBox_disjoint hzz'
abbrev integral_gaussianBox (z : Fin 256 → ℤ) :=
  EvenGaussian.Internal.integral_gaussianBox z
abbrev mem_gaussianCell_roundIndex (x : ℝ) :=
  EvenGaussian.Internal.mem_gaussianCell_roundIndex x
abbrev mem_gaussianBox_roundVector (x : Fin 256 → ℝ) :=
  EvenGaussian.Internal.mem_gaussianBox_roundVector x
abbrev roundIndex_center_close (x : ℝ) :=
  EvenGaussian.Internal.roundIndex_center_close x
abbrev roundIndex_bounded {x : ℝ} (hx : |x| < coordinateBound) :=
  EvenGaussian.Internal.roundIndex_bounded hx
abbrev roundIndex_square_lower (x : ℝ) :=
  EvenGaussian.Internal.roundIndex_square_lower x
abbrev measurableSet_gaussianCore (threshold : ℕ) :=
  EvenGaussian.Internal.measurableSet_gaussianCore
    (rows := 256) threshold
abbrev roundVector_mem_boundedVectors {threshold : ℕ} {x : Fin 256 → ℝ}
    (hx : x ∈ gaussianCore threshold) :=
  EvenGaussian.Internal.roundVector_mem_boundedVectors hx
abbrev roundVector_sqNorm_gt {threshold : ℕ} {x : Fin 256 → ℝ}
    (hx : x ∈ gaussianCore threshold) :=
  EvenGaussian.Internal.roundVector_sqNorm_gt hx
abbrev roundVector_mem_goodVectors {threshold : ℕ} {x : Fin 256 → ℝ}
    (hx : x ∈ gaussianCore threshold) :=
  EvenGaussian.Internal.roundVector_mem_goodVectors hx
abbrev gaussianCore_subset_goodBoxes (threshold : ℕ) :=
  EvenGaussian.Internal.gaussianCore_subset_goodBoxes
    (rows := 256) threshold
abbrev mem_boundedVectors_index {z : Fin 256 → ℤ}
    (hz : z ∈ boundedVectors) (j : Fin 256) :=
  EvenGaussian.Internal.mem_boundedVectors_index hz j
abbrev integral_gaussianCore_le_boxSum (threshold : ℕ) :=
  EvenGaussian.Internal.integral_gaussianCore_le_boxSum
    (rows := 256) threshold
abbrev sparseAllOnesRowSumsPMF_apply (z : Fin 256 → ℤ) :=
  EvenGaussian.Internal.sparseAllOnesRowSumsPMF_apply z
abbrev goodVector_pointMass_ge {threshold : ℕ} {z : Fin 256 → ℤ}
    (hz : z ∈ goodVectors threshold) :=
  EvenGaussian.Internal.goodVector_pointMass_ge hz
abbrev boxSum_le_goodProbability (threshold : ℕ) :=
  EvenGaussian.Internal.boxSum_le_goodProbability
    (rows := 256) threshold

theorem sparseAllOnesRowSumsPMF_eq_map_uniformSeed :
    sparseAllOnesRowSumsPMF =
      (PMF.uniformOfFintype (SparseSeed 256 dimension)).map
        (fun seed j => sparseAllOnesRowSum (seed j)) :=
  EvenGaussian.Internal.sparseAllOnesRowSumsPMF_eq_map_uniformSeed

theorem tensorComparison (threshold : ℕ) :
    ENNReal.ofReal
        (Real.exp (-(256 : ℝ) * localLoss) *
          ∫ x : Fin 256 → ℝ in gaussianCore threshold,
            halfGaussianProductDensity x) ≤
      sparseAllOnesRowSumsPMF.toMeasure
        {z | threshold * dimension < discreteSqNorm z} := by
  simpa [halfGaussianProductDensity,
    halfGaussianDensity,
    HalfGaussianEven.halfGaussianProductDensity,
    HalfGaussianEven.halfGaussianDensity,
    localLoss, EvenGaussian.Internal.localLoss,
    gaussianCore, EvenGaussian.Internal.gaussianCore,
    radialThreshold,
    EvenGaussian.Internal.radialThreshold,
    radialShift, EvenGaussian.Internal.radialShift,
    coordinateBound,
    EvenGaussian.Internal.coordinateBound,
    mesh, EvenGaussian.Internal.mesh] using
    (EvenGaussian.Internal.tensorComparison (rows := 256) threshold)

end Counterexamples.SparseUpper.Rows256.Internal
end CertifiedJL
