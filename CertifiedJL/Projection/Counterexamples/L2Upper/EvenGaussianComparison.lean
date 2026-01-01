/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.Counterexamples.L2Upper.ProjectionDistribution
import CertifiedJL.Model.Modular.Centered
import CertifiedJL.Model.Distributions.Entry
import CertifiedJL.Probability.Distributions.Binomial.LocalLimit
import CertifiedJL.Analysis.Gaussian.HalfGaussianEven
import CertifiedJL.Projection.Counterexamples.L2Upper.Statements
import Mathlib.Analysis.Real.Pi.Bounds

-- Lean 4.33's command-line asynchronous elaboration retains a very large
-- snapshot tree for this proof-heavy module.  Synchronous elaboration avoids
-- that frontend-only memory blowup; it does not change the checked terms.
set_option Elab.async false

/-!
# Gaussian comparison for even-row sparse upper obstructions

This module develops one half-Gaussian mesh comparison and its row-parametric
tensor consequence. Concrete obstruction modules retain only their numerical
tail estimates and experiment identification.
-/

open scoped BigOperators ENNReal

open MeasureTheory

namespace CertifiedJL
open Probability
namespace Counterexamples.SparseUpper.EvenGaussian.Internal

variable {rows : ℕ}

export Probability.SparseAllOnes
  (sparseRowSeedEquivBits sparseRowTrueCount sparseAllOnesRowSum
    sparseAllOnesRowSum_eq_trueCount sparseRowTrueCountFiberEquiv
    card_sparseRowTrueCount_fiber sparseAllOnesRowPMF
    sparseAllOnesRowPMF_apply_nat sparseAllOnesRowPMF_apply_int)

/-- Square-root dimension of the all-ones witness. -/
abbrev side : ℕ := highSecurityL2UpperCounterexampleSide
/-- Dimension of the all-ones witness. -/
abbrev dimension : ℕ := highSecurityL2UpperCounterexampleDimension
/-- Largest lattice index retained in each coordinate. -/
def cutoff : ℕ := 10 * side

/-- Mesh width `1 / side`. -/
noncomputable def mesh : ℝ := (side : ℝ)⁻¹
/-- Largest absolute coordinate represented by a retained mesh cell. -/
noncomputable def coordinateBound : ℝ := 10 - mesh / 2
/-- Radial rounding allowance across all rows coordinates. -/
noncomputable def radialShift : ℝ := rows * mesh * coordinateBound
/-- Shifted radial threshold whose rounded vectors exceed squared norm `threshold · d`. -/
noncomputable def radialThreshold (threshold : ℕ) : ℝ :=
  threshold + radialShift (rows := rows)

/-- Per-row exponent loss in the binomial-to-Gaussian comparison. -/
noncomputable def localLoss : ℝ :=
  (1 : ℝ) / dimension +
    cutoff * binomialLogStepError dimension cutoff +
      10 / side

/-- Binomial local-limit loss before the Gaussian-cell correction. -/
noncomputable def latticeLoss : ℝ :=
  (1 : ℝ) / dimension +
    cutoff * binomialLogStepError dimension cutoff

/-- Combined radial and rows-row local-comparison loss. -/
noncomputable def totalLoss : ℝ :=
  radialShift (rows := rows) + rows * localLoss

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

theorem mesh_pos : 0 < mesh := by
  norm_num [mesh, side]

theorem coordinateBound_pos : 0 < coordinateBound := by
  norm_num [coordinateBound, mesh, side]

theorem radialShift_nonneg : 0 ≤ radialShift (rows := rows) := by
  norm_num [radialShift, coordinateBound, mesh, side]

theorem radialThreshold_nonneg (threshold : ℕ) :
    0 ≤ radialThreshold (rows := rows) threshold := by
  unfold radialThreshold
  exact add_nonneg (Nat.cast_nonneg threshold) radialShift_nonneg

/-! ## Half-Gaussian mesh cells -/

/-- Half-open mesh cell centered at `k / side`. -/
def gaussianCell (k : ℤ) : Set ℝ :=
  Set.Ico ((k : ℝ) * mesh - mesh / 2)
    ((k : ℝ) * mesh + mesh / 2)

theorem measurableSet_gaussianCell (k : ℤ) :
    MeasurableSet (gaussianCell k) :=
  measurableSet_Ico

theorem gaussianCell_disjoint {k l : ℤ} (hkl : k ≠ l) :
    Disjoint (gaussianCell k) (gaussianCell l) := by
  rw [Set.disjoint_left]
  intro x hxk hxl
  simp only [gaussianCell, Set.mem_Ico] at hxk hxl
  have hmesh := mesh_pos
  have hsep : |(k : ℝ) - l| ≥ 1 := by
    have hint : |k - l| ≥ (1 : ℤ) :=
      Int.one_le_abs (sub_ne_zero.mpr hkl)
    exact_mod_cast hint
  have hclose : |(k : ℝ) - l| < 1 := by
    rw [abs_lt]
    constructor
    · have := hxl.1
      have := hxk.2
      norm_num [mesh, side] at *
      linarith
    · have := hxk.1
      have := hxl.2
      norm_num [mesh, side] at *
      linarith
  exact (not_lt_of_ge hsep) hclose

/-- The density on a bounded cell is controlled by its value at the center. -/
theorem HalfGaussianEven.halfGaussianDensity_le_cellCenter {k : ℤ} {x : ℝ}
    (hk : k.natAbs ≤ cutoff) (hx : x ∈ gaussianCell k) :
    HalfGaussianEven.halfGaussianDensity x ≤
      HalfGaussianEven.halfGaussianDensity ((k : ℝ) * mesh) *
        Real.exp (10 / side : ℝ) := by
  let c : ℝ := (k : ℝ) * mesh
  let e : ℝ := x - c
  have he :
      -(mesh / 2) ≤ e ∧ e ≤ mesh / 2 := by
    simp only [gaussianCell, Set.mem_Ico] at hx
    constructor <;> dsimp only [e, c] <;> linarith
  have heabs : |e| ≤ mesh / 2 := (abs_le).2 he
  have hcabs : |c| ≤ 10 := by
    calc
      |c| = (k.natAbs : ℝ) * mesh := by
        simp only [c, abs_mul, abs_of_pos mesh_pos]
        rw [Nat.cast_natAbs, Int.cast_abs]
      _ ≤ cutoff * mesh := by
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast hk) mesh_pos.le
      _ = 10 := by
        norm_num [cutoff, mesh, side]
  have hlinear : |2 * c * e| ≤ 10 * mesh := by
    calc
      |2 * c * e| = 2 * |c| * |e| := by
        rw [abs_mul, abs_mul]
        norm_num
      _ ≤ 2 * 10 * (mesh / 2) := by gcongr
      _ = 10 * mesh := by ring
  have hsquares : c ^ 2 - x ^ 2 ≤ 10 * mesh := by
    have heSq : 0 ≤ e ^ 2 := sq_nonneg e
    have hlinLower : -(10 * mesh) ≤ 2 * c * e :=
      (neg_le_of_abs_le hlinear)
    dsimp only [e] at heSq hlinLower
    nlinarith
  have hexp :
      Real.exp (-x ^ 2) ≤
        Real.exp (-c ^ 2 + 10 * mesh) := by
    rw [Real.exp_le_exp]
    linarith
  unfold HalfGaussianEven.halfGaussianDensity
  have hinvNonneg : 0 ≤ (Real.sqrt Real.pi)⁻¹ := by positivity
  calc
    (Real.sqrt Real.pi)⁻¹ * Real.exp (-x ^ 2) ≤
        (Real.sqrt Real.pi)⁻¹ *
          Real.exp (-c ^ 2 + 10 * mesh) := by
      gcongr
    _ = ((Real.sqrt Real.pi)⁻¹ * Real.exp (-c ^ 2)) *
        Real.exp (10 / side : ℝ) := by
      rw [show 10 * mesh = (10 / side : ℝ) by
        norm_num [mesh, side],
        Real.exp_add]
      ring

/-- Gaussian mass of a bounded mesh cell. -/
noncomputable def gaussianCellMass (k : ℤ) : ℝ :=
  ∫ x : ℝ in gaussianCell k, HalfGaussianEven.halfGaussianDensity x

theorem gaussianCellMass_nonneg (k : ℤ) :
    0 ≤ gaussianCellMass k := by
  unfold gaussianCellMass
  exact integral_nonneg_of_ae <|
    Filter.Eventually.of_forall fun _ => by
      unfold HalfGaussianEven.halfGaussianDensity
      positivity

theorem gaussianCellMass_le {k : ℤ}
    (hk : k.natAbs ≤ cutoff) :
    gaussianCellMass k ≤
      mesh * HalfGaussianEven.halfGaussianDensity ((k : ℝ) * mesh) *
        Real.exp (10 / side : ℝ) := by
  let C :=
    HalfGaussianEven.halfGaussianDensity ((k : ℝ) * mesh) *
      Real.exp (10 / side : ℝ)
  have hcellFinite : volume (gaussianCell k) ≠ ∞ := by
    unfold gaussianCell
    exact measure_Ico_lt_top.ne
  have hmono :
      gaussianCellMass k ≤
        ∫ _x : ℝ in gaussianCell k, C := by
    unfold gaussianCellMass
    apply setIntegral_mono_on
      HalfGaussianEven.integrable_halfGaussianDensity.integrableOn
      (integrableOn_const hcellFinite)
      (measurableSet_gaussianCell k)
    intro x hx
    exact HalfGaussianEven.halfGaussianDensity_le_cellCenter hk hx
  calc
    gaussianCellMass k ≤
        ∫ _x : ℝ in gaussianCell k, C := hmono
    _ = mesh * C := by
      simp [gaussianCell, C, mesh_pos.le]
    _ = mesh * HalfGaussianEven.halfGaussianDensity ((k : ℝ) * mesh) *
        Real.exp (10 / side : ℝ) := by
      simp only [C]
      ring

theorem sparseAllOnesRowPMF_toReal {k : ℤ}
    (hk : k.natAbs ≤ cutoff) :
    (sparseAllOnesRowPMF dimension k).toReal =
      centeredBinomialMassAt dimension k.natAbs := by
  rw [sparseAllOnesRowPMF_apply_int k
    (hk.trans cutoff_lt_dimension.le)]
  unfold centeredBinomialMassAt
  rw [ENNReal.toReal_mul]
  · simp only [ENNReal.toReal_natCast, ENNReal.toReal_inv]
    norm_cast

theorem sqrt_dimension :
    Real.sqrt (dimension : ℝ) = side := by
  rw [show (dimension : ℝ) = (side : ℝ) ^ 2 by
    norm_num [dimension, side]]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos]
  norm_num [side]

theorem indexSquare_div_dimension (k : ℤ) :
    (k.natAbs : ℝ) ^ 2 / dimension =
      ((k : ℝ) * mesh) ^ 2 := by
  rw [show (dimension : ℝ) = (side : ℝ) ^ 2 by
    norm_num [dimension, side]]
  rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  norm_num [mesh, side]
  ring

/--
Uniform one-row comparison between the exact centered-binomial mass and its
half-Gaussian mesh cell.
-/
theorem rowMass_ge_exp_mul_cell {k : ℤ}
    (hk : k.natAbs ≤ cutoff) :
    Real.exp (-localLoss) * gaussianCellMass k ≤
      (sparseAllOnesRowPMF dimension k).toReal := by
  let r := k.natAbs
  let E := binomialLogStepError dimension cutoff
  have hE : 0 ≤ E := by
    norm_num [E, binomialLogStepError, cutoff, dimension, side]
  have hbin :=
    centeredBinomialMassAt_lower
      (d := dimension) (K := cutoff) (k := r)
      hk cutoff_lt_dimension
  have hcentral :=
    centralBinomialMass_exp_lower dimension_pos
  have hrE :
      (r : ℝ) * E ≤ (cutoff : ℝ) * E := by
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast hk) hE
  have hexpError :
      Real.exp
          (-((r : ℝ) ^ 2 / dimension +
            (cutoff : ℝ) * E)) ≤
        Real.exp
          (-((r : ℝ) ^ 2 / dimension +
            (r : ℝ) * E)) := by
    rw [Real.exp_le_exp]
    linarith
  have hmeshSqrt :
      mesh = 1 / Real.sqrt (dimension : ℝ) := by
    rw [sqrt_dimension]
    norm_num [mesh, side]
  have htarget :
      mesh * HalfGaussianEven.halfGaussianDensity ((k : ℝ) * mesh) *
          Real.exp (-latticeLoss) =
        (Real.exp (-(1 : ℝ) / dimension) /
            (Real.sqrt Real.pi * Real.sqrt dimension)) *
          Real.exp
            (-((r : ℝ) ^ 2 / dimension +
              (cutoff : ℝ) * E)) := by
    unfold HalfGaussianEven.halfGaussianDensity latticeLoss
    rw [hmeshSqrt, indexSquare_div_dimension k]
    dsimp only [r, E]
    rw [show
        1 / Real.sqrt (dimension : ℝ) *
              ((Real.sqrt Real.pi)⁻¹ *
                Real.exp (-((k : ℝ) *
                  (1 / Real.sqrt (dimension : ℝ))) ^ 2)) *
              Real.exp
                (-(1 / (dimension : ℝ) +
                  (cutoff : ℝ) *
                    binomialLogStepError dimension cutoff)) =
            (1 / (Real.sqrt Real.pi * Real.sqrt dimension)) *
              (Real.exp (-((k : ℝ) *
                    (1 / Real.sqrt (dimension : ℝ))) ^ 2) *
                Real.exp
                  (-(1 / (dimension : ℝ) +
                    (cutoff : ℝ) *
                      binomialLogStepError dimension cutoff))) by
          ring]
    rw [← Real.exp_add]
    rw [show
        Real.exp (-(1 : ℝ) / dimension) /
              (Real.sqrt Real.pi * Real.sqrt dimension) *
            Real.exp
              (-(((k : ℝ) * mesh) ^ 2 +
                (cutoff : ℝ) *
                  binomialLogStepError dimension cutoff)) =
          (1 / (Real.sqrt Real.pi * Real.sqrt dimension)) *
            (Real.exp (-(1 : ℝ) / dimension) *
              Real.exp
                (-(((k : ℝ) * mesh) ^ 2 +
                  (cutoff : ℝ) *
                    binomialLogStepError dimension cutoff))) by
        ring]
    rw [← Real.exp_add]
    congr 2
    rw [hmeshSqrt]
    ring
  have hlattice :
      mesh * HalfGaussianEven.halfGaussianDensity ((k : ℝ) * mesh) *
          Real.exp (-latticeLoss) ≤
        centeredBinomialMassAt dimension r := by
    rw [htarget]
    calc
      (Real.exp (-(1 : ℝ) / dimension) /
            (Real.sqrt Real.pi * Real.sqrt dimension)) *
          Real.exp
            (-((r : ℝ) ^ 2 / dimension +
              (cutoff : ℝ) * E)) ≤
        (Real.exp (-(1 : ℝ) / dimension) /
            (Real.sqrt Real.pi * Real.sqrt dimension)) *
          Real.exp
            (-((r : ℝ) ^ 2 / dimension +
              (r : ℝ) * E)) := by
        exact mul_le_mul_of_nonneg_left hexpError (by positivity)
      _ ≤ centralBinomialMass dimension *
          Real.exp
            (-((r : ℝ) ^ 2 / dimension +
              (r : ℝ) * E)) := by
        exact mul_le_mul_of_nonneg_right hcentral
          (Real.exp_nonneg _)
      _ ≤ centeredBinomialMassAt dimension r := hbin
  rw [sparseAllOnesRowPMF_toReal hk]
  calc
    Real.exp (-localLoss) * gaussianCellMass k ≤
        Real.exp (-localLoss) *
          (mesh * HalfGaussianEven.halfGaussianDensity ((k : ℝ) * mesh) *
            Real.exp (10 / side : ℝ)) := by
      gcongr
      exact gaussianCellMass_le hk
    _ = mesh * HalfGaussianEven.halfGaussianDensity ((k : ℝ) * mesh) *
        Real.exp (-latticeLoss) := by
      unfold localLoss latticeLoss
      rw [show
          Real.exp
                (-(1 / (dimension : ℝ) +
                  (cutoff : ℝ) *
                    binomialLogStepError dimension cutoff +
                  10 / (side : ℝ))) *
              (mesh * HalfGaussianEven.halfGaussianDensity ((k : ℝ) * mesh) *
                Real.exp (10 / (side : ℝ))) =
            (mesh * HalfGaussianEven.halfGaussianDensity ((k : ℝ) * mesh)) *
              (Real.exp
                  (-(1 / (dimension : ℝ) +
                    (cutoff : ℝ) *
                      binomialLogStepError dimension cutoff +
                    10 / (side : ℝ))) *
                Real.exp (10 / (side : ℝ))) by
          ring]
      rw [← Real.exp_add]
      congr 1
      ring_nf
    _ ≤ centeredBinomialMassAt dimension r := hlattice

/-! ## Tensorized mesh comparison -/

/-- Lattice indices retained in one mesh coordinate. -/
noncomputable def boundedIndices : Finset ℤ :=
  Finset.Icc (-(cutoff : ℤ)) cutoff

/-- All row-count-parametric lattice vectors within the coordinate cutoff. -/
noncomputable irreducible_def boundedVectors
    (lemma := boundedVectors_def) : Finset (Fin rows → ℤ) :=
  Fintype.piFinset fun _ : Fin rows => boundedIndices

/-- Sum of squared integer coordinates of a row-sum vector. -/
def discreteSqNorm (z : Fin rows → ℤ) : ℕ :=
  ∑ j, (z j).natAbs ^ 2

/-- Bounded lattice vectors whose squared norm strictly exceeds `threshold · d`. -/
noncomputable irreducible_def goodVectors
    (lemma := goodVectors_def) (threshold : ℕ) : Finset (Fin rows → ℤ) :=
  boundedVectors.filter fun z =>
    threshold * dimension < discreteSqNorm z

theorem mem_goodVectors_iff {threshold : ℕ} {z : Fin rows → ℤ} :
    z ∈ goodVectors threshold ↔
      z ∈ boundedVectors ∧
        threshold * dimension < discreteSqNorm z := by
  rw [goodVectors_def, Finset.mem_filter]

/-- Product of the half-open Gaussian mesh cells indexed by `z`. -/
def gaussianBox (z : Fin rows → ℤ) : Set (Fin rows → ℝ) :=
  Set.pi Set.univ fun j => gaussianCell (z j)

theorem measurableSet_gaussianBox (z : Fin rows → ℤ) :
    MeasurableSet (gaussianBox z) := by
  unfold gaussianBox
  exact MeasurableSet.univ_pi fun j =>
    measurableSet_gaussianCell (z j)

theorem gaussianBox_disjoint {z z' : Fin rows → ℤ}
    (hzz' : z ≠ z') :
    Disjoint (gaussianBox z) (gaussianBox z') := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hzz'
  rw [Set.disjoint_left]
  intro x hx hx'
  have hxj : x j ∈ gaussianCell (z j) := hx j (Set.mem_univ j)
  have hxj' : x j ∈ gaussianCell (z' j) := hx' j (Set.mem_univ j)
  exact Set.disjoint_left.mp (gaussianCell_disjoint hj)
    hxj hxj'

theorem integral_gaussianBox (z : Fin rows → ℤ) :
    (∫ x : Fin rows → ℝ in gaussianBox z,
        HalfGaussianEven.halfGaussianProductDensity x) =
      ∏ j, gaussianCellMass (z j) := by
  rw [← integral_indicator (measurableSet_gaussianBox z)]
  have hindicator :
      (gaussianBox z).indicator HalfGaussianEven.halfGaussianProductDensity =
        fun x : Fin rows → ℝ =>
          ∏ j,
            (gaussianCell (z j)).indicator
              HalfGaussianEven.halfGaussianDensity (x j) := by
    funext x
    by_cases hx : x ∈ gaussianBox z
    · rw [Set.indicator_of_mem hx]
      unfold HalfGaussianEven.halfGaussianProductDensity
      apply Finset.prod_congr rfl
      intro j _
      rw [Set.indicator_of_mem (hx j (Set.mem_univ j))]
    · simp only [Set.indicator, hx, ↓reduceIte]
      have hnot : ∃ j, x j ∉ gaussianCell (z j) := by
        simpa [gaussianBox] using hx
      obtain ⟨j, hj⟩ := hnot
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [hj]
  rw [hindicator]
  rw [integral_fintype_prod_volume_eq_prod
    (fun j : Fin rows =>
      (gaussianCell (z j)).indicator HalfGaussianEven.halfGaussianDensity)]
  apply Finset.prod_congr rfl
  intro j _
  unfold gaussianCellMass
  rw [integral_indicator (measurableSet_gaussianCell (z j))]

/-- Nearest mesh-center index, with half-open tie breaking. -/
noncomputable def roundIndex (x : ℝ) : ℤ :=
  ⌊x / mesh + 1 / 2⌋

theorem mem_gaussianCell_roundIndex (x : ℝ) :
    x ∈ gaussianCell (roundIndex x) := by
  have hfloorLower :
      ((roundIndex x : ℤ) : ℝ) ≤ x / mesh + 1 / 2 :=
    Int.floor_le _
  have hfloorUpper :
      x / mesh + 1 / 2 < ((roundIndex x : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hmesh := mesh_pos
  simp only [gaussianCell, Set.mem_Ico]
  constructor
  · have hmul :=
      mul_le_mul_of_nonneg_right hfloorLower hmesh.le
    rw [add_mul, div_mul_cancel₀ x hmesh.ne'] at hmul
    dsimp only [roundIndex] at hmul ⊢
    nlinarith
  · have hmul :=
      mul_lt_mul_of_pos_right hfloorUpper hmesh
    rw [add_mul, div_mul_cancel₀ x hmesh.ne'] at hmul
    dsimp only [roundIndex] at hmul ⊢
    nlinarith

/-- Round every coordinate to its containing mesh-cell index. -/
noncomputable def roundVector (x : Fin rows → ℝ) : Fin rows → ℤ :=
  fun j => roundIndex (x j)

theorem mem_gaussianBox_roundVector (x : Fin rows → ℝ) :
    x ∈ gaussianBox (roundVector x) := by
  intro j _
  exact mem_gaussianCell_roundIndex (x j)

theorem roundIndex_center_close (x : ℝ) :
    |((roundIndex x : ℤ) : ℝ) * mesh - x| ≤ mesh / 2 := by
  have hx := mem_gaussianCell_roundIndex x
  simp only [gaussianCell, Set.mem_Ico] at hx
  rw [abs_le]
  constructor <;> linarith

theorem roundIndex_bounded {x : ℝ}
    (hx : |x| < coordinateBound) :
    (roundIndex x).natAbs ≤ cutoff := by
  let c : ℝ := ((roundIndex x : ℤ) : ℝ) * mesh
  have hclose : |c - x| ≤ mesh / 2 := roundIndex_center_close x
  have hc :
      |c| < 10 := by
    calc
      |c| = |x + (c - x)| := by
        congr 1
        ring
      _ ≤ |x| + |c - x| := abs_add_le _ _
      _ < coordinateBound + mesh / 2 := by
        exact add_lt_add_of_lt_of_le hx hclose
      _ = 10 := by
        unfold coordinateBound
        ring
  have hcast :
      ((roundIndex x).natAbs : ℝ) < cutoff := by
    have hc' :
        ((roundIndex x).natAbs : ℝ) * mesh < 10 := by
      simpa only [c, abs_mul, Nat.cast_natAbs, Int.cast_abs,
        abs_of_pos mesh_pos] using hc
    norm_num [mesh, cutoff, side] at hc' ⊢
    nlinarith
  have hnat : (roundIndex x).natAbs < cutoff := by
    exact_mod_cast hcast
  exact hnat.le

theorem roundIndex_square_lower (x : ℝ) :
    x ^ 2 - mesh * |x| ≤
      (((roundIndex x : ℤ) : ℝ) * mesh) ^ 2 := by
  let e : ℝ := ((roundIndex x : ℤ) : ℝ) * mesh - x
  have heabs : |e| ≤ mesh / 2 := roundIndex_center_close x
  have hxe : -(mesh * |x|) ≤ 2 * x * e := by
    have habs : |2 * x * e| ≤ mesh * |x| := by
      calc
        |2 * x * e| = 2 * |x| * |e| := by
          rw [abs_mul, abs_mul]
          norm_num
        _ ≤ 2 * |x| * (mesh / 2) := by
          gcongr
        _ = mesh * |x| := by ring
    exact neg_le_of_abs_le habs
  have heSq : 0 ≤ e ^ 2 := sq_nonneg e
  dsimp only [e] at hxe heSq
  nlinarith

/-- Strict radial tail remaining after every coordinate cutoff. -/
def gaussianCore (threshold : ℕ) : Set (Fin rows → ℝ) :=
  {x | radialThreshold (rows := rows) threshold < HalfGaussianEven.squaredRadius x ∧
    ∀ j, |x j| < coordinateBound}

theorem measurableSet_gaussianCore (threshold : ℕ) :
    MeasurableSet (gaussianCore (rows := rows) threshold) := by
  unfold gaussianCore HalfGaussianEven.squaredRadius
  have hradial :
      MeasurableSet
        {x : Fin rows → ℝ |
          radialThreshold (rows := rows) threshold < ∑ j, (x j) ^ 2} :=
    measurableSet_lt measurable_const
      (Finset.measurable_sum _ fun j _ =>
        (measurable_pi_apply j).pow_const 2)
  have hcoordinate :
      MeasurableSet
        (⋂ j : Fin rows,
          {x : Fin rows → ℝ | |x j| < coordinateBound}) :=
    MeasurableSet.iInter fun j =>
      measurableSet_lt
        (continuous_abs.measurable.comp (measurable_pi_apply j))
        measurable_const
  convert hradial.inter hcoordinate using 1
  ext x
  simp

theorem roundVector_mem_boundedVectors {threshold : ℕ}
    {x : Fin rows → ℝ} (hx : x ∈ gaussianCore threshold) :
    roundVector x ∈ boundedVectors := by
  rw [boundedVectors_def, Fintype.mem_piFinset]
  intro j
  simp only [boundedIndices, Finset.mem_Icc]
  have hj := roundIndex_bounded (hx.2 j)
  change
    -(cutoff : ℤ) ≤ roundIndex (x j) ∧
      roundIndex (x j) ≤ cutoff
  omega

theorem roundVector_sqNorm_gt [NeZero rows]
    {threshold : ℕ} {x : Fin rows → ℝ}
    (hx : x ∈ gaussianCore threshold) :
    threshold * dimension < discreteSqNorm (roundVector x) := by
  have hround :
      ∑ j, ((roundVector x j : ℤ) : ℝ) ^ 2 * mesh ^ 2 ≥
        HalfGaussianEven.squaredRadius x - mesh * ∑ j, |x j| := by
    unfold HalfGaussianEven.squaredRadius
    calc
      ∑ j, ((roundVector x j : ℤ) : ℝ) ^ 2 * mesh ^ 2 =
          ∑ j, (((roundVector x j : ℤ) : ℝ) * mesh) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≥ ∑ j, ((x j) ^ 2 - mesh * |x j|) := by
        apply Finset.sum_le_sum
        intro j _
        exact roundIndex_square_lower (x j)
      _ = (∑ j, (x j) ^ 2) - mesh * ∑ j, |x j| := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
  have habs :
      (∑ j, |x j|) < rows * coordinateBound := by
    calc
      (∑ j, |x j|) <
          ∑ _j : Fin rows, coordinateBound :=
        Finset.sum_lt_sum_of_nonempty (by simp)
          (fun j _ => hx.2 j)
      _ = rows * coordinateBound := by simp [mul_comm]
  have hmeshAbs :
      mesh * (∑ j, |x j|) < radialShift (rows := rows) := by
    unfold radialShift
    have := mul_lt_mul_of_pos_left habs mesh_pos
    nlinarith
  have hcenter : (threshold : ℝ) <
      ∑ j, ((roundVector x j : ℤ) : ℝ) ^ 2 * mesh ^ 2 := by
    unfold gaussianCore at hx
    unfold radialThreshold at hx
    calc
      (threshold : ℝ) < HalfGaussianEven.squaredRadius x - radialShift (rows := rows) := by
        linarith [hx.1]
      _ < HalfGaussianEven.squaredRadius x - mesh * ∑ j, |x j| := by
        linarith
      _ ≤ ∑ j,
          ((roundVector x j : ℤ) : ℝ) ^ 2 * mesh ^ 2 := hround
  have henergy :
      (∑ j, ((roundVector x j).natAbs : ℝ) ^ 2) =
        (discreteSqNorm (roundVector x) : ℝ) := by
    unfold discreteSqNorm
    push_cast
    rfl
  have hcenter' :
      (threshold : ℝ) <
        (discreteSqNorm (roundVector x) : ℝ) /
          dimension := by
    have hcenterNat :
        (threshold : ℝ) <
          ∑ j, ((roundVector x j).natAbs : ℝ) ^ 2 *
            mesh ^ 2 := by
      convert hcenter using 1
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
    rw [show mesh ^ 2 = (1 : ℝ) / dimension by
      norm_num [mesh, dimension, side]] at hcenterNat
    rw [← Finset.sum_mul] at hcenterNat
    rw [← henergy]
    simpa [div_eq_mul_inv] using hcenterNat
  rw [lt_div_iff₀ (by norm_num [dimension, side])] at hcenter'
  apply (Nat.cast_lt (α := ℝ)).mp
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcenter'

theorem roundVector_mem_goodVectors [NeZero rows]
    {threshold : ℕ} {x : Fin rows → ℝ}
    (hx : x ∈ gaussianCore threshold) :
    roundVector x ∈ goodVectors threshold := by
  refine (mem_goodVectors_iff
    (z := roundVector x)).mpr ?_
  apply And.intro
  · exact roundVector_mem_boundedVectors hx
  · exact roundVector_sqNorm_gt hx

theorem gaussianCore_subset_goodBoxes [NeZero rows] (threshold : ℕ) :
    gaussianCore (rows := rows) threshold ⊆
      ⋃ z ∈ goodVectors (rows := rows) threshold, gaussianBox z := by
  intro x hx
  apply Set.mem_iUnion_of_mem (roundVector x)
  apply Set.mem_iUnion_of_mem (roundVector_mem_goodVectors hx)
  exact mem_gaussianBox_roundVector x

theorem mem_boundedVectors_index {z : Fin rows → ℤ}
    (hz : z ∈ boundedVectors) (j : Fin rows) :
    (z j).natAbs ≤ cutoff := by
  rw [boundedVectors_def, Fintype.mem_piFinset] at hz
  have hj := hz j
  simp only [boundedIndices, Finset.mem_Icc] at hj
  omega

theorem integral_gaussianCore_le_boxSum [NeZero rows] (threshold : ℕ) :
    (∫ x : Fin rows → ℝ in gaussianCore (rows := rows) threshold,
        HalfGaussianEven.halfGaussianProductDensity x) ≤
      ∑ z ∈ goodVectors (rows := rows) threshold,
        ∏ j, gaussianCellMass (z j) := by
  let boxUnion : Set (Fin rows → ℝ) :=
    ⋃ z ∈ goodVectors threshold, gaussianBox z
  have hsubset : gaussianCore threshold ⊆ boxUnion :=
    gaussianCore_subset_goodBoxes threshold
  have hmono :
      (∫ x : Fin rows → ℝ in gaussianCore threshold,
          HalfGaussianEven.halfGaussianProductDensity x) ≤
        ∫ x : Fin rows → ℝ in boxUnion,
          HalfGaussianEven.halfGaussianProductDensity x := by
    apply setIntegral_mono_set
      HalfGaussianEven.integrable_halfGaussianProductDensity.integrableOn
    · exact Filter.Eventually.of_forall fun x => by
        unfold HalfGaussianEven.halfGaussianProductDensity HalfGaussianEven.halfGaussianDensity
        positivity
    · exact Filter.Eventually.of_forall hsubset
  calc
    (∫ x : Fin rows → ℝ in gaussianCore threshold,
        HalfGaussianEven.halfGaussianProductDensity x) ≤
        ∫ x : Fin rows → ℝ in boxUnion,
          HalfGaussianEven.halfGaussianProductDensity x := hmono
    _ = ∑ z ∈ goodVectors threshold,
        ∫ x : Fin rows → ℝ in gaussianBox z,
          HalfGaussianEven.halfGaussianProductDensity x := by
      unfold boxUnion
      apply integral_biUnion_finset
      · intro z _
        exact measurableSet_gaussianBox z
      · intro z hz z' hz' hzz'
        exact gaussianBox_disjoint hzz'
      · intro z _
        exact HalfGaussianEven.integrable_halfGaussianProductDensity.integrableOn
    _ = ∑ z ∈ goodVectors threshold,
        ∏ j, gaussianCellMass (z j) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [integral_gaussianBox]

/-! ## Exact product distribution of the rows row sums -/

/-- Product distribution of the row-count-parametric sparse row sums against the all-ones vector. -/
noncomputable def sparseAllOnesRowSumsPMF :
    PMF (Fin rows → ℤ) :=
  uniformPiMap
    (α := fun _ : Fin rows => SparseRowSeed dimension)
    (fun _ : Fin rows => @sparseAllOnesRowSum dimension)

theorem sparseAllOnesRowSumsPMF_apply (z : Fin rows → ℤ) :
    sparseAllOnesRowSumsPMF z =
      ∏ j, sparseAllOnesRowPMF dimension (z j) := by
  unfold sparseAllOnesRowSumsPMF sparseAllOnesRowPMF
  exact uniformPiMap_apply
    (fun _ : Fin rows => @sparseAllOnesRowSum dimension)
    (fun _ : Fin rows => measurable_of_finite
      (@sparseAllOnesRowSum dimension)) z

theorem sparseAllOnesRowSumsPMF_eq_map_uniformSeed :
    sparseAllOnesRowSumsPMF =
      (PMF.uniformOfFintype (SparseSeed rows dimension)).map
        (fun seed j => sparseAllOnesRowSum (seed j)) := by
  unfold sparseAllOnesRowSumsPMF uniformPiMap
  rw [uniformPiPMF_eq_uniformOfFintype]

theorem goodVector_pointMass_ge {threshold : ℕ} {z : Fin rows → ℤ}
    (hz : z ∈ goodVectors threshold) :
    ENNReal.ofReal
        (Real.exp (-(rows : ℝ) * localLoss) *
          ∏ j, gaussianCellMass (z j)) ≤
      sparseAllOnesRowSumsPMF z := by
  have hbounded := (mem_goodVectors_iff.mp hz).1
  have hrow (j : Fin rows) :
      Real.exp (-localLoss) * gaussianCellMass (z j) ≤
        (sparseAllOnesRowPMF dimension (z j)).toReal :=
    rowMass_ge_exp_mul_cell
      (mem_boundedVectors_index hbounded j)
  have hprod :
      ∏ j,
          (Real.exp (-localLoss) * gaussianCellMass (z j)) ≤
        ∏ j,
          (sparseAllOnesRowPMF dimension (z j)).toReal :=
    Finset.prod_le_prod
      (fun j _ => mul_nonneg (Real.exp_nonneg _)
        (gaussianCellMass_nonneg (z j)))
      (fun j _ => hrow j)
  have hleft :
      (∏ j,
          (Real.exp (-localLoss) * gaussianCellMass (z j))) =
        Real.exp (-(rows : ℝ) * localLoss) *
          ∏ j, gaussianCellMass (z j) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    rw [← Real.exp_nat_mul]
    congr 2
    ring
  rw [← hleft]
  rw [sparseAllOnesRowSumsPMF_apply]
  rw [ENNReal.ofReal_le_iff_le_toReal]
  · simpa only [ENNReal.toReal_prod] using hprod
  · exact ENNReal.prod_ne_top fun j _ =>
      PMF.apply_ne_top _ _

theorem boxSum_le_goodProbability (threshold : ℕ) :
    ENNReal.ofReal
        (Real.exp (-(rows : ℝ) * localLoss) *
          ∑ z ∈ goodVectors (rows := rows) threshold,
            ∏ j, gaussianCellMass (z j)) ≤
      (sparseAllOnesRowSumsPMF (rows := rows)).toMeasure
        {z : Fin rows → ℤ |
          threshold * dimension < discreteSqNorm z} := by
  have hset :
      (goodVectors (rows := rows) threshold : Set (Fin rows → ℤ)) ⊆
        {z | threshold * dimension < discreteSqNorm z} := by
    intro z hz
    exact (mem_goodVectors_iff.mp hz).2
  calc
    ENNReal.ofReal
        (Real.exp (-(rows : ℝ) * localLoss) *
          ∑ z ∈ goodVectors threshold,
            ∏ j, gaussianCellMass (z j)) =
        ∑ z ∈ goodVectors threshold,
          ENNReal.ofReal
            (Real.exp (-(rows : ℝ) * localLoss) *
              ∏ j, gaussianCellMass (z j)) := by
      rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
      intro z hz
      exact mul_nonneg (Real.exp_nonneg _) <|
        Finset.prod_nonneg fun j _ =>
          gaussianCellMass_nonneg (z j)
    _ ≤ ∑ z ∈ goodVectors (rows := rows) threshold,
        sparseAllOnesRowSumsPMF (rows := rows) z := by
      exact Finset.sum_le_sum fun z hz =>
        goodVector_pointMass_ge hz
    _ = (sparseAllOnesRowSumsPMF (rows := rows)).toMeasure
        (goodVectors (rows := rows) threshold : Set (Fin rows → ℤ)) := by
      rw [PMF.toMeasure_apply_finset]
    _ ≤ (sparseAllOnesRowSumsPMF (rows := rows)).toMeasure
        {z : Fin rows → ℤ |
          threshold * dimension < discreteSqNorm z} :=
      measure_mono hset

theorem tensorComparison [NeZero rows] (threshold : ℕ) :
    ENNReal.ofReal
        (Real.exp (-(rows : ℝ) * localLoss) *
          ∫ x : Fin rows → ℝ in gaussianCore (rows := rows) threshold,
            HalfGaussianEven.halfGaussianProductDensity x) ≤
      (sparseAllOnesRowSumsPMF (rows := rows)).toMeasure
        {z : Fin rows → ℤ |
          threshold * dimension < discreteSqNorm z} := by
  exact (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left
      (integral_gaussianCore_le_boxSum threshold)
      (Real.exp_nonneg _))).trans (boxSum_le_goodProbability threshold)

end Counterexamples.SparseUpper.EvenGaussian.Internal

end CertifiedJL
