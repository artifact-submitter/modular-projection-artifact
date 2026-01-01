/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.Counterexamples.L2Upper.ProjectionDistribution
import CertifiedJL.Model.Modular.Centered
import CertifiedJL.Model.Distributions.Entry
import CertifiedJL.Probability.Distributions.Binomial.LocalLimit
import CertifiedJL.Analysis.Gaussian.HalfGaussian
import CertifiedJL.Projection.Counterexamples.L2Upper.Statements
import Mathlib.Analysis.Real.Pi.Bounds

-- Lean 4.33's command-line asynchronous elaboration retains a very large
-- snapshot tree for this proof-heavy module.  Synchronous elaboration avoids
-- that frontend-only memory blowup; it does not change the checked terms.
set_option Elab.async false

/-!
# Gaussian comparison for the sparse upper-336 counterexample

This module develops the half-Gaussian mesh comparison and its 256-fold tensor
consequence. Quantitative tail estimates and the final experiment
identification are factored into downstream modules so Lean can release each
command-line snapshot tree before elaborating the next stage.
-/

open scoped BigOperators ENNReal

open MeasureTheory

namespace CertifiedJL
open Probability
namespace Counterexamples.SparseUpper.Internal

/-- Square-root dimension of the all-ones witness. -/
abbrev side : ℕ := counterexampleSide
/-- Dimension of the all-ones witness. -/
abbrev dimension : ℕ := counterexampleDimension
/-- Largest lattice index retained in each coordinate. -/
def cutoff : ℕ := 6 * side

/-- Mesh width `1 / side`. -/
noncomputable def mesh : ℝ := (side : ℝ)⁻¹
/-- Largest absolute coordinate represented by a retained mesh cell. -/
noncomputable def coordinateBound : ℝ := 6 - mesh / 2
/-- Radial rounding allowance across all 256 coordinates. -/
noncomputable def radialShift : ℝ := 256 * mesh * coordinateBound
/-- Shifted radial threshold whose rounded vectors exceed squared norm `threshold · d`. -/
noncomputable def radialThreshold (threshold : ℕ) : ℝ :=
  threshold + radialShift

/-- Per-row exponent loss in the binomial-to-Gaussian comparison. -/
noncomputable def localLoss : ℝ :=
  (1 : ℝ) / dimension +
    cutoff * binomialLogStepError dimension cutoff +
      6 / side

/-- Binomial local-limit loss before the Gaussian-cell correction. -/
noncomputable def latticeLoss : ℝ :=
  (1 : ℝ) / dimension +
    cutoff * binomialLogStepError dimension cutoff

/-- Combined radial and 256-row local-comparison loss. -/
noncomputable def totalLoss : ℝ :=
  radialShift + 256 * localLoss

@[simp] theorem side_eq : side = 46_340 := rfl
@[simp] theorem dimension_eq : dimension = 2_147_395_600 := by
  norm_num [dimension, side, counterexampleDimension,
    counterexampleSide]
@[simp] theorem cutoff_eq : cutoff = 278_040 := by
  norm_num [cutoff, side]

theorem side_pos : 0 < side := by norm_num [side]
theorem dimension_pos : 0 < dimension := by norm_num [dimension, side]
theorem cutoff_lt_dimension : cutoff < dimension := by
  norm_num [cutoff, dimension, side]

theorem mesh_pos : 0 < mesh := by
  norm_num [mesh, side]

theorem coordinateBound_pos : 0 < coordinateBound := by
  norm_num [coordinateBound, mesh, side]

theorem radialShift_nonneg : 0 ≤ radialShift := by
  norm_num [radialShift, coordinateBound, mesh, side]

theorem radialThreshold_nonneg (threshold : ℕ) :
    0 ≤ radialThreshold threshold := by
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
theorem halfGaussianDensity_le_cellCenter {k : ℤ} {x : ℝ}
    (hk : k.natAbs ≤ cutoff) (hx : x ∈ gaussianCell k) :
    halfGaussianDensity x ≤
      halfGaussianDensity ((k : ℝ) * mesh) *
        Real.exp (6 / side : ℝ) := by
  let c : ℝ := (k : ℝ) * mesh
  let e : ℝ := x - c
  have he :
      -(mesh / 2) ≤ e ∧ e ≤ mesh / 2 := by
    simp only [gaussianCell, Set.mem_Ico] at hx
    constructor <;> dsimp only [e, c] <;> linarith
  have heabs : |e| ≤ mesh / 2 := (abs_le).2 he
  have hcabs : |c| ≤ 6 := by
    calc
      |c| = (k.natAbs : ℝ) * mesh := by
        simp only [c, abs_mul, abs_of_pos mesh_pos]
        rw [Nat.cast_natAbs, Int.cast_abs]
      _ ≤ cutoff * mesh := by
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast hk) mesh_pos.le
      _ = 6 := by
        norm_num [cutoff, mesh, side]
  have hlinear : |2 * c * e| ≤ 6 * mesh := by
    calc
      |2 * c * e| = 2 * |c| * |e| := by
        rw [abs_mul, abs_mul]
        norm_num
      _ ≤ 2 * 6 * (mesh / 2) := by gcongr
      _ = 6 * mesh := by ring
  have hsquares : c ^ 2 - x ^ 2 ≤ 6 * mesh := by
    have heSq : 0 ≤ e ^ 2 := sq_nonneg e
    have hlinLower : -(6 * mesh) ≤ 2 * c * e :=
      (neg_le_of_abs_le hlinear)
    dsimp only [e] at heSq hlinLower
    nlinarith
  have hexp :
      Real.exp (-x ^ 2) ≤
        Real.exp (-c ^ 2 + 6 * mesh) := by
    rw [Real.exp_le_exp]
    linarith
  unfold halfGaussianDensity
  have hinvNonneg : 0 ≤ (Real.sqrt Real.pi)⁻¹ := by positivity
  calc
    (Real.sqrt Real.pi)⁻¹ * Real.exp (-x ^ 2) ≤
        (Real.sqrt Real.pi)⁻¹ *
          Real.exp (-c ^ 2 + 6 * mesh) := by
      gcongr
    _ = ((Real.sqrt Real.pi)⁻¹ * Real.exp (-c ^ 2)) *
        Real.exp (6 / side : ℝ) := by
      rw [show 6 * mesh = (6 / side : ℝ) by
        norm_num [mesh, side],
        Real.exp_add]
      ring

/-- Gaussian mass of a bounded mesh cell. -/
noncomputable def gaussianCellMass (k : ℤ) : ℝ :=
  ∫ x : ℝ in gaussianCell k, halfGaussianDensity x

theorem gaussianCellMass_nonneg (k : ℤ) :
    0 ≤ gaussianCellMass k := by
  unfold gaussianCellMass
  exact integral_nonneg_of_ae <|
    Filter.Eventually.of_forall fun _ => by
      unfold halfGaussianDensity
      positivity

theorem gaussianCellMass_le {k : ℤ}
    (hk : k.natAbs ≤ cutoff) :
    gaussianCellMass k ≤
      mesh * halfGaussianDensity ((k : ℝ) * mesh) *
        Real.exp (6 / side : ℝ) := by
  let C :=
    halfGaussianDensity ((k : ℝ) * mesh) *
      Real.exp (6 / side : ℝ)
  have hcellFinite : volume (gaussianCell k) ≠ ∞ := by
    unfold gaussianCell
    exact measure_Ico_lt_top.ne
  have hmono :
      gaussianCellMass k ≤
        ∫ _x : ℝ in gaussianCell k, C := by
    unfold gaussianCellMass
    apply setIntegral_mono_on
      integrable_halfGaussianDensity.integrableOn
      (integrableOn_const hcellFinite)
      (measurableSet_gaussianCell k)
    intro x hx
    exact halfGaussianDensity_le_cellCenter hk hx
  calc
    gaussianCellMass k ≤
        ∫ _x : ℝ in gaussianCell k, C := hmono
    _ = mesh * C := by
      simp [gaussianCell, C, mesh_pos.le]
    _ = mesh * halfGaussianDensity ((k : ℝ) * mesh) *
        Real.exp (6 / side : ℝ) := by
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
      mesh * halfGaussianDensity ((k : ℝ) * mesh) *
          Real.exp (-latticeLoss) =
        (Real.exp (-(1 : ℝ) / dimension) /
            (Real.sqrt Real.pi * Real.sqrt dimension)) *
          Real.exp
            (-((r : ℝ) ^ 2 / dimension +
              (cutoff : ℝ) * E)) := by
    unfold halfGaussianDensity latticeLoss
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
      mesh * halfGaussianDensity ((k : ℝ) * mesh) *
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
          (mesh * halfGaussianDensity ((k : ℝ) * mesh) *
            Real.exp (6 / side : ℝ)) := by
      gcongr
      exact gaussianCellMass_le hk
    _ = mesh * halfGaussianDensity ((k : ℝ) * mesh) *
        Real.exp (-latticeLoss) := by
      unfold localLoss latticeLoss
      rw [show
          Real.exp
                (-(1 / (dimension : ℝ) +
                  (cutoff : ℝ) *
                    binomialLogStepError dimension cutoff +
                  6 / (side : ℝ))) *
              (mesh * halfGaussianDensity ((k : ℝ) * mesh) *
                Real.exp (6 / (side : ℝ))) =
            (mesh * halfGaussianDensity ((k : ℝ) * mesh)) *
              (Real.exp
                  (-(1 / (dimension : ℝ) +
                    (cutoff : ℝ) *
                      binomialLogStepError dimension cutoff +
                    6 / (side : ℝ))) *
                Real.exp (6 / (side : ℝ))) by
          ring]
      rw [← Real.exp_add]
      congr 1
      ring_nf
    _ ≤ centeredBinomialMassAt dimension r := hlattice

/-! ## Tensorized mesh comparison -/

/-- Lattice indices retained in one mesh coordinate. -/
noncomputable def boundedIndices : Finset ℤ :=
  Finset.Icc (-(cutoff : ℤ)) cutoff

/-- All 256-dimensional lattice vectors within the coordinate cutoff. -/
noncomputable irreducible_def boundedVectors
    (lemma := boundedVectors_def) : Finset (Fin 256 → ℤ) :=
  Fintype.piFinset fun _ : Fin 256 => boundedIndices

/-- Sum of squared integer coordinates of a row-sum vector. -/
def discreteSqNorm (z : Fin 256 → ℤ) : ℕ :=
  ∑ j, (z j).natAbs ^ 2

/-- Bounded lattice vectors whose squared norm strictly exceeds `threshold · d`. -/
noncomputable irreducible_def goodVectors
    (lemma := goodVectors_def) (threshold : ℕ) : Finset (Fin 256 → ℤ) :=
  boundedVectors.filter fun z =>
    threshold * dimension < discreteSqNorm z

theorem mem_goodVectors_iff {threshold : ℕ} {z : Fin 256 → ℤ} :
    z ∈ goodVectors threshold ↔
      z ∈ boundedVectors ∧
        threshold * dimension < discreteSqNorm z := by
  rw [goodVectors_def, Finset.mem_filter]

/-- Product of the half-open Gaussian mesh cells indexed by `z`. -/
def gaussianBox (z : Fin 256 → ℤ) : Set (Fin 256 → ℝ) :=
  Set.pi Set.univ fun j => gaussianCell (z j)

theorem measurableSet_gaussianBox (z : Fin 256 → ℤ) :
    MeasurableSet (gaussianBox z) := by
  unfold gaussianBox
  exact MeasurableSet.univ_pi fun j =>
    measurableSet_gaussianCell (z j)

theorem gaussianBox_disjoint {z z' : Fin 256 → ℤ}
    (hzz' : z ≠ z') :
    Disjoint (gaussianBox z) (gaussianBox z') := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hzz'
  rw [Set.disjoint_left]
  intro x hx hx'
  have hxj : x j ∈ gaussianCell (z j) := hx j (Set.mem_univ j)
  have hxj' : x j ∈ gaussianCell (z' j) := hx' j (Set.mem_univ j)
  exact Set.disjoint_left.mp (gaussianCell_disjoint hj)
    hxj hxj'

theorem integral_gaussianBox (z : Fin 256 → ℤ) :
    (∫ x : Fin 256 → ℝ in gaussianBox z,
        halfGaussianProductDensity x) =
      ∏ j, gaussianCellMass (z j) := by
  rw [← integral_indicator (measurableSet_gaussianBox z)]
  have hindicator :
      (gaussianBox z).indicator halfGaussianProductDensity =
        fun x : Fin 256 → ℝ =>
          ∏ j,
            (gaussianCell (z j)).indicator
              halfGaussianDensity (x j) := by
    funext x
    by_cases hx : x ∈ gaussianBox z
    · rw [Set.indicator_of_mem hx]
      unfold halfGaussianProductDensity
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
    (fun j : Fin 256 =>
      (gaussianCell (z j)).indicator halfGaussianDensity)]
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
noncomputable def roundVector (x : Fin 256 → ℝ) : Fin 256 → ℤ :=
  fun j => roundIndex (x j)

theorem mem_gaussianBox_roundVector (x : Fin 256 → ℝ) :
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
      |c| < 6 := by
    calc
      |c| = |x + (c - x)| := by
        congr 1
        ring
      _ ≤ |x| + |c - x| := abs_add_le _ _
      _ < coordinateBound + mesh / 2 := by
        exact add_lt_add_of_lt_of_le hx hclose
      _ = 6 := by
        unfold coordinateBound
        ring
  have hcast :
      ((roundIndex x).natAbs : ℝ) < cutoff := by
    have hc' :
        ((roundIndex x).natAbs : ℝ) * mesh < 6 := by
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
def gaussianCore (threshold : ℕ) : Set (Fin 256 → ℝ) :=
  {x | radialThreshold threshold < squaredRadius x ∧
    ∀ j, |x j| < coordinateBound}

theorem measurableSet_gaussianCore (threshold : ℕ) :
    MeasurableSet (gaussianCore threshold) := by
  unfold gaussianCore squaredRadius
  have hradial :
      MeasurableSet
        {x : Fin 256 → ℝ |
          radialThreshold threshold < ∑ j, (x j) ^ 2} :=
    measurableSet_lt measurable_const
      (Finset.measurable_sum _ fun j _ =>
        (measurable_pi_apply j).pow_const 2)
  have hcoordinate :
      MeasurableSet
        (⋂ j : Fin 256,
          {x : Fin 256 → ℝ | |x j| < coordinateBound}) :=
    MeasurableSet.iInter fun j =>
      measurableSet_lt
        (continuous_abs.measurable.comp (measurable_pi_apply j))
        measurable_const
  convert hradial.inter hcoordinate using 1
  ext x
  simp

theorem roundVector_mem_boundedVectors {threshold : ℕ}
    {x : Fin 256 → ℝ} (hx : x ∈ gaussianCore threshold) :
    roundVector x ∈ boundedVectors := by
  rw [boundedVectors_def, Fintype.mem_piFinset]
  intro j
  simp only [boundedIndices, Finset.mem_Icc]
  have hj := roundIndex_bounded (hx.2 j)
  change
    -(cutoff : ℤ) ≤ roundIndex (x j) ∧
      roundIndex (x j) ≤ cutoff
  omega

theorem roundVector_sqNorm_gt {threshold : ℕ} {x : Fin 256 → ℝ}
    (hx : x ∈ gaussianCore threshold) :
    threshold * dimension < discreteSqNorm (roundVector x) := by
  have hround :
      ∑ j, ((roundVector x j : ℤ) : ℝ) ^ 2 * mesh ^ 2 ≥
        squaredRadius x - mesh * ∑ j, |x j| := by
    unfold squaredRadius
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
      (∑ j, |x j|) < 256 * coordinateBound := by
    calc
      (∑ j, |x j|) <
          ∑ _j : Fin 256, coordinateBound :=
        Finset.sum_lt_sum_of_nonempty (by simp)
          (fun j _ => hx.2 j)
      _ = 256 * coordinateBound := by simp [mul_comm]
  have hmeshAbs :
      mesh * (∑ j, |x j|) < radialShift := by
    unfold radialShift
    have := mul_lt_mul_of_pos_left habs mesh_pos
    nlinarith
  have hcenter : (threshold : ℝ) <
      ∑ j, ((roundVector x j : ℤ) : ℝ) ^ 2 * mesh ^ 2 := by
    unfold gaussianCore at hx
    unfold radialThreshold at hx
    calc
      (threshold : ℝ) < squaredRadius x - radialShift := by
        linarith [hx.1]
      _ < squaredRadius x - mesh * ∑ j, |x j| := by
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

theorem roundVector_mem_goodVectors {threshold : ℕ} {x : Fin 256 → ℝ}
    (hx : x ∈ gaussianCore threshold) :
    roundVector x ∈ goodVectors threshold := by
  refine (mem_goodVectors_iff
    (z := roundVector x)).mpr ?_
  apply And.intro
  · exact roundVector_mem_boundedVectors hx
  · exact roundVector_sqNorm_gt hx

theorem gaussianCore_subset_goodBoxes (threshold : ℕ) :
    gaussianCore threshold ⊆
      ⋃ z ∈ goodVectors threshold, gaussianBox z := by
  intro x hx
  apply Set.mem_iUnion_of_mem (roundVector x)
  apply Set.mem_iUnion_of_mem (roundVector_mem_goodVectors hx)
  exact mem_gaussianBox_roundVector x

theorem mem_boundedVectors_index {z : Fin 256 → ℤ}
    (hz : z ∈ boundedVectors) (j : Fin 256) :
    (z j).natAbs ≤ cutoff := by
  rw [boundedVectors_def, Fintype.mem_piFinset] at hz
  have hj := hz j
  simp only [boundedIndices, Finset.mem_Icc] at hj
  omega

theorem integral_gaussianCore_le_boxSum (threshold : ℕ) :
    (∫ x : Fin 256 → ℝ in gaussianCore threshold,
        halfGaussianProductDensity x) ≤
      ∑ z ∈ goodVectors threshold,
        ∏ j, gaussianCellMass (z j) := by
  let boxUnion : Set (Fin 256 → ℝ) :=
    ⋃ z ∈ goodVectors threshold, gaussianBox z
  have hsubset : gaussianCore threshold ⊆ boxUnion :=
    gaussianCore_subset_goodBoxes threshold
  have hmono :
      (∫ x : Fin 256 → ℝ in gaussianCore threshold,
          halfGaussianProductDensity x) ≤
        ∫ x : Fin 256 → ℝ in boxUnion,
          halfGaussianProductDensity x := by
    apply setIntegral_mono_set
      integrable_halfGaussianProductDensity.integrableOn
    · exact Filter.Eventually.of_forall fun x => by
        unfold halfGaussianProductDensity halfGaussianDensity
        positivity
    · exact Filter.Eventually.of_forall hsubset
  calc
    (∫ x : Fin 256 → ℝ in gaussianCore threshold,
        halfGaussianProductDensity x) ≤
        ∫ x : Fin 256 → ℝ in boxUnion,
          halfGaussianProductDensity x := hmono
    _ = ∑ z ∈ goodVectors threshold,
        ∫ x : Fin 256 → ℝ in gaussianBox z,
          halfGaussianProductDensity x := by
      unfold boxUnion
      apply integral_biUnion_finset
      · intro z _
        exact measurableSet_gaussianBox z
      · intro z hz z' hz' hzz'
        exact gaussianBox_disjoint hzz'
      · intro z _
        exact integrable_halfGaussianProductDensity.integrableOn
    _ = ∑ z ∈ goodVectors threshold,
        ∏ j, gaussianCellMass (z j) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [integral_gaussianBox]

/-! ## Exact product distribution of the 256 row sums -/

/-- Product distribution of the 256 sparse row sums against the all-ones vector. -/
noncomputable def sparseAllOnesRowSumsPMF :
    PMF (Fin 256 → ℤ) :=
  uniformPiMap
    (α := fun _ : Fin 256 => SparseRowSeed dimension)
    (fun _ : Fin 256 => @sparseAllOnesRowSum dimension)

theorem sparseAllOnesRowSumsPMF_apply (z : Fin 256 → ℤ) :
    sparseAllOnesRowSumsPMF z =
      ∏ j, sparseAllOnesRowPMF dimension (z j) := by
  unfold sparseAllOnesRowSumsPMF sparseAllOnesRowPMF
  exact uniformPiMap_apply
    (fun _ : Fin 256 => @sparseAllOnesRowSum dimension)
    (fun _ : Fin 256 => measurable_of_finite
      (@sparseAllOnesRowSum dimension)) z

theorem sparseAllOnesRowSumsPMF_eq_map_uniformSeed :
    sparseAllOnesRowSumsPMF =
      (PMF.uniformOfFintype (SparseSeed 256 dimension)).map
        (fun seed j => sparseAllOnesRowSum (seed j)) := by
  unfold sparseAllOnesRowSumsPMF uniformPiMap
  rw [uniformPiPMF_eq_uniformOfFintype]

theorem goodVector_pointMass_ge {threshold : ℕ} {z : Fin 256 → ℤ}
    (hz : z ∈ goodVectors threshold) :
    ENNReal.ofReal
        (Real.exp (-(256 : ℝ) * localLoss) *
          ∏ j, gaussianCellMass (z j)) ≤
      sparseAllOnesRowSumsPMF z := by
  have hbounded := (mem_goodVectors_iff.mp hz).1
  have hrow (j : Fin 256) :
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
        Real.exp (-(256 : ℝ) * localLoss) *
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
        (Real.exp (-(256 : ℝ) * localLoss) *
          ∑ z ∈ goodVectors threshold,
            ∏ j, gaussianCellMass (z j)) ≤
      sparseAllOnesRowSumsPMF.toMeasure
        {z | threshold * dimension < discreteSqNorm z} := by
  have hset :
      (goodVectors threshold : Set (Fin 256 → ℤ)) ⊆
        {z | threshold * dimension < discreteSqNorm z} := by
    intro z hz
    exact (mem_goodVectors_iff.mp hz).2
  calc
    ENNReal.ofReal
        (Real.exp (-(256 : ℝ) * localLoss) *
          ∑ z ∈ goodVectors threshold,
            ∏ j, gaussianCellMass (z j)) =
        ∑ z ∈ goodVectors threshold,
          ENNReal.ofReal
            (Real.exp (-(256 : ℝ) * localLoss) *
              ∏ j, gaussianCellMass (z j)) := by
      rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
      intro z hz
      exact mul_nonneg (Real.exp_nonneg _) <|
        Finset.prod_nonneg fun j _ =>
          gaussianCellMass_nonneg (z j)
    _ ≤ ∑ z ∈ goodVectors threshold,
        sparseAllOnesRowSumsPMF z := by
      exact Finset.sum_le_sum fun z hz =>
        goodVector_pointMass_ge hz
    _ = sparseAllOnesRowSumsPMF.toMeasure
        (goodVectors threshold : Set (Fin 256 → ℤ)) := by
      rw [PMF.toMeasure_apply_finset]
    _ ≤ sparseAllOnesRowSumsPMF.toMeasure
        {z | threshold * dimension < discreteSqNorm z} :=
      measure_mono hset

theorem tensorComparison (threshold : ℕ) :
    ENNReal.ofReal
        (Real.exp (-(256 : ℝ) * localLoss) *
          ∫ x : Fin 256 → ℝ in gaussianCore threshold,
            halfGaussianProductDensity x) ≤
      sparseAllOnesRowSumsPMF.toMeasure
        {z | threshold * dimension < discreteSqNorm z} := by
  exact (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left
      (integral_gaussianCore_le_boxSum threshold)
      (Real.exp_nonneg _))).trans (boxSum_le_goodProbability threshold)

end Counterexamples.SparseUpper.Internal

end CertifiedJL
