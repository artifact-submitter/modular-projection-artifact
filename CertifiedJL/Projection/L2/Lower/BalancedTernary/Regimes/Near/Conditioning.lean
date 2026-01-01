/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Unrestricted.Scalar
import CertifiedJL.Projection.L2.Lower.BalancedTernary.WrappedFourier

/-!
# Exact one-coordinate conditioning for sparse near-threshold rows

The distinguished balanced-ternary entry is inactive with probability one
half and active with probability one half.  This file exposes that identity
directly at the row-integral boundary, so retained-coordinate modular image
bounds can average their inactive and shifted-active tails without passing
through the coarse unconditional subgaussian tail.
-/

open scoped BigOperators ENNReal NNReal

open MeasureTheory ProbabilityTheory

namespace CertifiedJL

private theorem nearIntegral_comp_eq_of_pmf_map_eq
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ]
    (p : PMF α) (q : PMF β) (X : α → γ) (Y : β → γ) (f : γ → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hf : Measurable f)
    (hmap : p.map X = q.map Y) :
    ∫ x, f (X x) ∂p.toMeasure = ∫ y, f (Y y) ∂q.toMeasure := by
  calc
    ∫ x, f (X x) ∂p.toMeasure =
        ∫ z, f z ∂Measure.map X p.toMeasure := by
      exact (integral_map hX.aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ z, f z ∂(p.map X).toMeasure := by
      rw [PMF.toMeasure_map X p hX]
    _ = ∫ z, f z ∂(q.map Y).toMeasure := by rw [hmap]
    _ = ∫ z, f z ∂Measure.map Y q.toMeasure := by
      rw [PMF.toMeasure_map Y q hY]
    _ = ∫ y, f (Y y) ∂q.toMeasure := by
      exact integral_map hY.aemeasurable hf.aestronglyMeasurable

private theorem nearIntegral_even_comp_eq_of_square_map_eq
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [Countable β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (p : PMF α) (q : PMF β) (X : α → ℤ) (Y : β → ℤ) (f : ℤ → ℝ)
    (heven : Function.Even f)
    (hmap : p.map (fun x => X x ^ 2) = q.map (fun y => Y y ^ 2)) :
    ∫ x, f (X x) ∂p.toMeasure = ∫ y, f (Y y) ∂q.toMeasure := by
  classical
  let g : ℤ → ℝ := fun t =>
    if h : ∃ x : ℤ, x ^ 2 = t then f h.choose else 0
  have hfactor (x : ℤ) : g (x ^ 2) = f x := by
    dsimp [g]
    let hexists : ∃ y : ℤ, y ^ 2 = x ^ 2 := ⟨x, rfl⟩
    rw [dif_pos hexists]
    let y := Classical.choose hexists
    change f y = f x
    have hsquare : y ^ 2 = x ^ 2 := Classical.choose_spec hexists
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with h | h
    · rw [h]
    · rw [h]
      exact heven x
  calc
    ∫ x, f (X x) ∂p.toMeasure =
        ∫ x, g (X x ^ 2) ∂p.toMeasure := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hfactor]
    _ = ∫ y, g (Y y ^ 2) ∂q.toMeasure :=
      nearIntegral_comp_eq_of_pmf_map_eq p q
        (fun x => X x ^ 2) (fun y => Y y ^ 2) g
        (measurable_of_countable _) (measurable_of_countable _)
        (measurable_of_countable _) hmap
    _ = ∫ y, f (Y y) ∂q.toMeasure := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hfactor]

/-- Any even row statistic reindexes after conditioning one activity bit to
the canonical balanced-ternary remainder row, with shift zero or the retained
amplitude.  This generic form is needed for the complete wrapped kernel. -/
theorem dominantConditionalRow_integral_eq_shiftedRemainder_of_even
    {d : ℕ} (w : Fin d → ℤ) (i : Fin d) (activity : Bool)
    (f : ℤ → ℝ) (hf_even : Function.Even f) :
    (∫ row, f (∑ j, row j * w j)
        ∂(dominantConditionalRowPMF i activity).toMeasure) =
      ∫ row, f
        ((if activity then (dominantAmplitude w i : ℤ) else 0) +
          ∑ j, row j * dominantRemainderFinWeights w i j)
        ∂(sparseRademacherRow
          (Fintype.card (DominantRemainderIndex i))).toMeasure := by
  let X : (Fin d → ℤ) → ℤ := fun row => ∑ j, row j * w j
  let shift : ℤ := if activity then (dominantAmplitude w i : ℤ) else 0
  let Y : (DominantRemainderIndex i → Bool × Bool) → ℤ := fun seed =>
    shift + dominantRemainderRowSeedDot seed w
  let Z :
      (Fin (Fintype.card (DominantRemainderIndex i)) → ℤ) → ℤ := fun row =>
    shift + ∑ j, row j * dominantRemainderFinWeights w i j
  have hactual_uniform :
      ∫ row, f (X row) ∂(dominantConditionalRowPMF i activity).toMeasure =
        ∫ seed, f (Y seed)
          ∂(PMF.uniformOfFintype
            (DominantRemainderIndex i → Bool × Bool)).toMeasure := by
    cases activity
    · have hmap := dominantConditionalRowPMF_inactive_dot i w
      apply nearIntegral_comp_eq_of_pmf_map_eq
        (dominantConditionalRowPMF i false)
        (PMF.uniformOfFintype
          (DominantRemainderIndex i → Bool × Bool))
        X Y f (measurable_of_countable _) (measurable_of_countable _)
          (measurable_of_countable _)
      simpa [X, Y, shift] using hmap
    · apply nearIntegral_even_comp_eq_of_square_map_eq
      · exact hf_even
      · simpa [X, Y, shift] using
          dominantConditionalRowPMF_active_square_dot i w
  have hmap_reindex :
      (PMF.uniformOfFintype
        (DominantRemainderIndex i → Bool × Bool)).map Y =
      (sparseRademacherRow
        (Fintype.card (DominantRemainderIndex i))).map Z := by
    calc
      _ = (PMF.uniformOfFintype
          (DominantRemainderIndex i → Bool × Bool)).map
            (fun seed => Z (sparseRow
              (dominantRemainderRowSeedEquivFin i seed))) := by
        congr 1
        funext seed
        dsimp [Y, Z]
        rw [dominantRemainderRowSeedDot_eq_fin]
        rfl
      _ = ((PMF.uniformOfFintype
          (DominantRemainderIndex i → Bool × Bool)).map
            (fun seed => sparseRow
              (dominantRemainderRowSeedEquivFin i seed))).map Z := by
        rw [PMF.map_comp]
        rfl
      _ = (sparseRademacherRow
          (Fintype.card (DominantRemainderIndex i))).map Z := by
        rw [map_uniformDominantRemainderRowSeed_reindex]
  have huniform_reindex :
      ∫ seed, f (Y seed)
          ∂(PMF.uniformOfFintype
            (DominantRemainderIndex i → Bool × Bool)).toMeasure =
        ∫ row, f (Z row)
          ∂(sparseRademacherRow
            (Fintype.card (DominantRemainderIndex i))).toMeasure := by
    exact nearIntegral_comp_eq_of_pmf_map_eq
      (PMF.uniformOfFintype (DominantRemainderIndex i → Bool × Bool))
      (sparseRademacherRow (Fintype.card (DominantRemainderIndex i)))
      Y Z f (measurable_of_countable _) (measurable_of_countable _)
        (measurable_of_countable _) hmap_reindex
  calc
    (∫ row, f (∑ j, row j * w j)
        ∂(dominantConditionalRowPMF i activity).toMeasure) =
        ∫ row, f (X row)
          ∂(dominantConditionalRowPMF i activity).toMeasure := by rfl
    _ = ∫ seed, f (Y seed)
          ∂(PMF.uniformOfFintype
            (DominantRemainderIndex i → Bool × Bool)).toMeasure :=
      hactual_uniform
    _ = ∫ row, f (Z row)
          ∂(sparseRademacherRow
            (Fintype.card (DominantRemainderIndex i))).toMeasure :=
      huniform_reindex
    _ = ∫ row, f
        ((if activity then (dominantAmplitude w i : ℤ) else 0) +
          ∑ j, row j * dominantRemainderFinWeights w i j)
        ∂(sparseRademacherRow
          (Fintype.card (DominantRemainderIndex i))).toMeasure := by rfl

/-- The complete wrapped kernel conditioned on one activity bit is the
canonical residual wrapped kernel shifted by zero or the retained amplitude. -/
theorem dominantConditionalRow_wrappedGaussianKernel_integral_eq_shiftedRemainder
    {d q : ℕ} (w : Fin d → ℤ) (i : Fin d) (activity : Bool) (s : ℝ) :
    (∫ row, wrappedGaussianKernel q s (∑ j, row j * w j)
        ∂(dominantConditionalRowPMF i activity).toMeasure) =
      ∫ row, wrappedGaussianKernel q s
        ((if activity then (dominantAmplitude w i : ℤ) else 0) +
          ∑ j, row j * dominantRemainderFinWeights w i j)
        ∂(sparseRademacherRow
          (Fintype.card (DominantRemainderIndex i))).toMeasure := by
  exact dominantConditionalRow_integral_eq_shiftedRemainder_of_even
    w i activity (wrappedGaussianKernel q s)
      (wrappedGaussianKernel_even q s)

/-- Split one sparse-row seed into activity, sign, and all remaining seeds. -/
def sparseRowSeedView {d : ℕ} (i : Fin d) (seed : SparseRowSeed d) :
    Bool × DominantConditionalRowSeed i :=
  (sparsePairActivity (seed i),
    (sparsePairSign (seed i), fun j => seed j.1))

/-- Reassemble a sparse-row seed from its one-coordinate conditioned view. -/
def sparseRowSeedOfView {d : ℕ} (i : Fin d)
    (view : Bool × DominantConditionalRowSeed i) : SparseRowSeed d :=
  fun j => if hj : j = i then
    sparsePairOfActivitySign view.1 view.2.1
  else view.2.2 ⟨j, hj⟩

@[simp]
theorem sparseRowSeedOfView_view {d : ℕ} (i : Fin d)
    (seed : SparseRowSeed d) :
    sparseRowSeedOfView i (sparseRowSeedView i seed) = seed := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [sparseRowSeedOfView, sparseRowSeedView]
  · simp [sparseRowSeedOfView, sparseRowSeedView, hj]

@[simp]
theorem sparseRowSeedView_ofView {d : ℕ} (i : Fin d)
    (view : Bool × DominantConditionalRowSeed i) :
    sparseRowSeedView i (sparseRowSeedOfView i view) = view := by
  apply Prod.ext
  · simp [sparseRowSeedView, sparseRowSeedOfView]
  · apply Prod.ext
    · simp [sparseRowSeedView, sparseRowSeedOfView]
    · funext j
      simp [sparseRowSeedView, sparseRowSeedOfView, j.2]

/-- The one-coordinate seed split is a finite equivalence. -/
def sparseRowSeedEquivView {d : ℕ} (i : Fin d) :
    SparseRowSeed d ≃ Bool × DominantConditionalRowSeed i where
  toFun := sparseRowSeedView i
  invFun := sparseRowSeedOfView i
  left_inv := sparseRowSeedOfView_view i
  right_inv := sparseRowSeedView_ofView i

/-- Reconstructing the row from the split seed is exactly the established
conditioned-row reconstruction. -/
theorem sparseRow_ofView_eq_conditionalRow {d : ℕ} (i : Fin d)
    (view : Bool × DominantConditionalRowSeed i) :
    sparseRow (sparseRowSeedOfView i view) =
      dominantConditionalRow i view.1 view.2 := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [sparseRow, sparseRowSeedOfView, dominantConditionalRow]
  · simp [sparseRow, sparseRowSeedOfView, dominantConditionalRow, hj]

/-- The actual balanced-ternary row distribution is the uniform activity mixture of
the two exact conditioned row distributions. -/
theorem sparseRademacherRow_eq_bind_conditioned {d : ℕ} (i : Fin d) :
    sparseRademacherRow d =
      (PMF.uniformOfFintype Bool).bind fun activity =>
        dominantConditionalRowPMF i activity := by
  rw [sparseRademacherRow_eq_map_uniformRowSeed]
  calc
    (PMF.uniformOfFintype (SparseRowSeed d)).map sparseRow =
        (PMF.uniformOfFintype
          (Bool × DominantConditionalRowSeed i)).map
            (fun view => dominantConditionalRow i view.1 view.2) := by
      rw [← map_uniformOfFintype_equiv (sparseRowSeedEquivView i)]
      rw [PMF.map_comp]
      congr 1
      funext seed
      change sparseRow seed = dominantConditionalRow i
        (sparseRowSeedView i seed).1 (sparseRowSeedView i seed).2
      rw [← sparseRow_ofView_eq_conditionalRow i (sparseRowSeedView i seed)]
      simp
    _ = (PMF.uniformOfFintype Bool).bind fun activity =>
        dominantConditionalRowPMF i activity := by
      rw [Probability.uniformOfFintype_prod_eq_bind]
      rw [PMF.map_bind]
      congr 1
      funext activity
      rw [dominantConditionalRowPMF, PMF.map_comp]
      rfl

/-- Every integrable row statistic is the arithmetic mean of its inactive
and active conditioned expectations. -/
theorem sparseRademacherRow_integral_eq_half_conditioned
    {d : ℕ} (i : Fin d) (f : (Fin d → ℤ) → ℝ)
    (hfalse : Integrable f (dominantConditionalRowPMF i false).toMeasure)
    (htrue : Integrable f (dominantConditionalRowPMF i true).toMeasure) :
    (∫ row, f row ∂(sparseRademacherRow d).toMeasure) =
      ((∫ row, f row ∂(dominantConditionalRowPMF i false).toMeasure) +
        ∫ row, f row ∂(dominantConditionalRowPMF i true).toMeasure) / 2 := by
  let p : PMF Bool := PMF.uniformOfFintype Bool
  let q : Bool → PMF (Fin d → ℤ) := fun activity =>
    dominantConditionalRowPMF i activity
  have hmeasure : (p.bind q).toMeasure =
      ((1 / 2 : ℝ≥0∞) • (q false).toMeasure) +
        ((1 / 2 : ℝ≥0∞) • (q true).toMeasure) := by
    ext s hs
    rw [PMF.toMeasure_bind_apply p q s hs]
    rw [tsum_fintype]
    simp [p, q, PMF.uniformOfFintype_apply]
    ac_rfl
  rw [sparseRademacherRow_eq_bind_conditioned i]
  change (∫ row, f row ∂(p.bind q).toMeasure) = _
  rw [hmeasure]
  rw [integral_add_measure
      (hfalse.smul_measure (by finiteness))
      (htrue.smul_measure (by finiteness)),
    integral_smul_measure, integral_smul_measure]
  simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat]
  norm_num
  ring

end CertifiedJL
