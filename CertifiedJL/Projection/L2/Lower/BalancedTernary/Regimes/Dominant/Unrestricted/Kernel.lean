/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Unrestricted.Normalization
import CertifiedJL.Analysis.SmoothBounds.NegativeLaplace

/-!
# Conditioned dominant row kernels

The conditional sign/remainder law is reorganized as an independent finite
product of row-local seeds. This exposes the exact inactive and active row
kernels to which the analytic estimates apply.
-/

open scoped BigOperators

open MeasureTheory

namespace CertifiedJL

/-- Squared centered modular row value normalized by the dominant amplitude `A²`. -/
noncomputable def dominantNormalizedRowKernel (q : ℕ) {d : ℕ}
    (w : Fin d → ℤ) (i : Fin d) (row : Fin d → ℤ) : ℝ :=
  ((centeredMod q (∑ j, row j * w j) : ℝ) /
    (dominantAmplitude w i : ℝ)) ^ 2

/-- The normalized row kernels sum to the natural modular projection squared norm divided by `A²`. -/
theorem sum_dominantNormalizedRowKernel {q m d : ℕ}
    (J : Matrix (Fin m) (Fin d) ℤ) (w : Fin d → ℤ) (i : Fin d) :
    ∑ row, dominantNormalizedRowKernel q w i (J row) =
      (modularProjectionSqNorm q J w : ℝ) / (dominantAmplitude w i : ℝ) ^ 2 := by
  change (∑ row, ((centeredMod q (rowDot J w row) : ℝ) /
      (dominantAmplitude w i : ℝ)) ^ 2) = _
  calc
    _ = (∑ row, (centeredMod q (rowDot J w row) : ℝ) ^ 2) /
          (dominantAmplitude w i : ℝ) ^ 2 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro row _
        rw [div_pow]
    _ = _ := by rw [← realCast_modularProjectionSqNorm J w]

/-- One row of the sign and remainder data after fixing activity. -/
abbrev DominantConditionalRowSeed {d : ℕ} (i : Fin d) :=
  Bool × (DominantRemainderIndex i → Bool × Bool)

/-- Curry the conditioned sign/remainder seed into independent row seeds. -/
def dominantConditionalSeedsEquivRows {m d : ℕ} (i : Fin d) :
    DominantConditionalSeeds (m := m) i ≃
      (Fin m → DominantConditionalRowSeed i) where
  toFun seed row := (seed.1 row, fun j => seed.2 row j)
  invFun rows := (fun row => (rows row).1, fun row j => (rows row).2 j)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Integer row reconstructed from fixed activity and one row-local seed. -/
def dominantConditionalRow {d : ℕ} (i : Fin d) (activity : Bool)
    (seed : DominantConditionalRowSeed i) : Fin d → ℤ :=
  fun j => if hj : j = i then
    sparseBit (sparsePairOfActivitySign activity seed.1)
  else sparseBit (seed.2 ⟨j, hj⟩)

/-- Remainder dot product read from one row-local remainder seed. -/
def dominantRemainderRowSeedDot {d : ℕ} {i : Fin d}
    (seed : DominantRemainderIndex i → Bool × Bool)
    (w : Fin d → ℤ) : ℤ :=
  ∑ j : DominantRemainderIndex i, sparseBit (seed j) * w j.1

/-- Remainder dot product read from one row-local conditional seed. -/
def dominantConditionalRowRemainderDot {d : ℕ} {i : Fin d}
    (seed : DominantConditionalRowSeed i) (w : Fin d → ℤ) : ℤ :=
  dominantRemainderRowSeedDot seed.2 w

/-- A conditioned row is exactly inactive `R` or active `±wᵢ + R`. -/
theorem dominantConditionalRow_dot {d : ℕ} (i : Fin d)
    (activity : Bool) (seed : DominantConditionalRowSeed i)
    (w : Fin d → ℤ) :
    ∑ j, dominantConditionalRow i activity seed j * w j =
      if activity then
        signBit seed.1 * w i + dominantConditionalRowRemainderDot seed w
      else dominantConditionalRowRemainderDot seed w := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i]
  have hdominant :
      dominantConditionalRow i activity seed i * w i =
        (if activity then signBit seed.1 * w i else 0) := by
    simp [dominantConditionalRow, sparseBit_ofActivitySign]
  have hremainder :
      (∑ j : DominantRemainderIndex i,
          dominantConditionalRow i activity seed j.1 * w j.1) =
        dominantConditionalRowRemainderDot seed w := by
    apply Finset.sum_congr rfl
    intro j _
    simp [dominantConditionalRow, j.2]
  rw [hdominant, hremainder]
  cases activity <;> simp

/-- Row reconstruction agrees with the full dominant seed-view reconstruction. -/
theorem sparseMatrixOfDominantView_row_eq_conditionalRow {m d : ℕ}
    (i : Fin d) (activity : DominantActivity m)
    (conditional : DominantConditionalSeeds (m := m) i) (row : Fin m) :
    sparseMatrixOfDominantView i (activity, conditional) row =
      dominantConditionalRow i (activity row)
        ((dominantConditionalSeedsEquivRows i) conditional row) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [sparseMatrixOfDominantView, sparseMatrix, sparseRow,
      sparseSeedOfDominantView, dominantConditionalRow,
      dominantConditionalSeedsEquivRows, sparseBit_ofActivitySign]
  · simp [sparseMatrixOfDominantView, sparseMatrix, sparseRow,
      sparseSeedOfDominantView, dominantConditionalRow,
      dominantConditionalSeedsEquivRows, hj]

/-- The row-local matrix distribution at a fixed activity bit. -/
noncomputable def dominantConditionalRowPMF {d : ℕ} (i : Fin d)
    (activity : Bool) : PMF (Fin d → ℤ) :=
  (PMF.uniformOfFintype (DominantConditionalRowSeed i)).map
    (dominantConditionalRow i activity)

/-- The inactive row dot law is exactly the uniform remainder dot law. -/
theorem dominantConditionalRowPMF_inactive_dot {d : ℕ} (i : Fin d)
    (w : Fin d → ℤ) :
    (dominantConditionalRowPMF i false).map
        (fun row => ∑ j, row j * w j) =
      (PMF.uniformOfFintype
        (DominantRemainderIndex i → Bool × Bool)).map
          (fun seed => dominantRemainderRowSeedDot seed w) := by
  rw [dominantConditionalRowPMF, PMF.map_comp]
  have hfun :
      (fun seed : DominantConditionalRowSeed i =>
        ∑ j, dominantConditionalRow i false seed j * w j) =
      (fun seed => dominantRemainderRowSeedDot seed.2 w) := by
    funext seed
    simpa [dominantConditionalRowRemainderDot] using
      dominantConditionalRow_dot i false seed w
  change (PMF.uniformOfFintype (DominantConditionalRowSeed i)).map
      (fun seed => ∑ j, dominantConditionalRow i false seed j * w j) = _
  rw [hfun]
  calc
    _ = ((PMF.uniformOfFintype (DominantConditionalRowSeed i)).map
          Prod.snd).map (fun seed => dominantRemainderRowSeedDot seed w) := by
        rw [PMF.map_comp]
        rfl
    _ = _ := by rw [Probability.map_uniformOfFintype_prod_snd]

/-- The inactive normalized modular kernel is a scalar remainder pushforward. -/
theorem dominantConditionalRowPMF_inactive_normalizedKernel
    (q : ℕ) {d : ℕ} (w : Fin d → ℤ) (i : Fin d) :
    (dominantConditionalRowPMF i false).map
        (dominantNormalizedRowKernel q w i) =
      (PMF.uniformOfFintype
        (DominantRemainderIndex i → Bool × Bool)).map
          (fun seed =>
            ((centeredMod q (dominantRemainderRowSeedDot seed w) : ℝ) /
              (dominantAmplitude w i : ℝ)) ^ 2) := by
  have h := congrArg
    (PMF.map fun x : ℤ =>
      ((centeredMod q x : ℝ) / (dominantAmplitude w i : ℝ)) ^ 2)
    (dominantConditionalRowPMF_inactive_dot i w)
  change (dominantConditionalRowPMF i false).map
      ((fun x : ℤ => ((centeredMod q x : ℝ) /
        (dominantAmplitude w i : ℝ)) ^ 2) ∘
        (fun row => ∑ j, row j * w j)) =
    (PMF.uniformOfFintype
      (DominantRemainderIndex i → Bool × Bool)).map
        ((fun x : ℤ => ((centeredMod q x : ℝ) /
          (dominantAmplitude w i : ℝ)) ^ 2) ∘
          (fun seed => dominantRemainderRowSeedDot seed w))
  rw [PMF.map_comp, PMF.map_comp] at h
  exact h

/-- Negate every sparse entry in one row-local remainder seed. -/
def negateDominantRemainderRowSeed {d : ℕ} {i : Fin d}
    (seed : DominantRemainderIndex i → Bool × Bool) :
    DominantRemainderIndex i → Bool × Bool :=
  fun j => negateSparsePairSeed (seed j)

@[simp]
theorem negateDominantRemainderRowSeed_involutive {d : ℕ} {i : Fin d}
    (seed : DominantRemainderIndex i → Bool × Bool) :
    negateDominantRemainderRowSeed (negateDominantRemainderRowSeed seed) =
      seed := by
  funext j
  exact negateSparsePairSeed_involutive (seed j)

/-- Row-local remainder negation as a finite equivalence. -/
def negateDominantRemainderRowSeedEquiv {d : ℕ} (i : Fin d) :
    (DominantRemainderIndex i → Bool × Bool) ≃
      (DominantRemainderIndex i → Bool × Bool) where
  toFun := negateDominantRemainderRowSeed
  invFun := negateDominantRemainderRowSeed
  left_inv := negateDominantRemainderRowSeed_involutive
  right_inv := negateDominantRemainderRowSeed_involutive

theorem map_uniformDominantRemainderRowSeed_negate {d : ℕ} (i : Fin d) :
    (PMF.uniformOfFintype
      (DominantRemainderIndex i → Bool × Bool)).map
        negateDominantRemainderRowSeed =
      PMF.uniformOfFintype (DominantRemainderIndex i → Bool × Bool) := by
  change (PMF.uniformOfFintype
      (DominantRemainderIndex i → Bool × Bool)).map
        (negateDominantRemainderRowSeedEquiv i) = _
  exact map_uniformOfFintype_equiv (negateDominantRemainderRowSeedEquiv i)

@[simp]
theorem dominantRemainderRowSeedDot_negate {d : ℕ} {i : Fin d}
    (seed : DominantRemainderIndex i → Bool × Bool)
    (w : Fin d → ℤ) :
    dominantRemainderRowSeedDot (negateDominantRemainderRowSeed seed) w =
      -dominantRemainderRowSeedDot seed w := by
  simp only [dominantRemainderRowSeedDot, negateDominantRemainderRowSeed,
    sparseBit_negateSparsePairSeed, neg_mul, Finset.sum_neg_distrib]

/-- The two signed active shifts have the same row-local squared law. -/
theorem activeRemainderRowShiftSquarePMF_symm {d : ℕ} (i : Fin d)
    (w : Fin d → ℤ) :
    (PMF.uniformOfFintype
      (DominantRemainderIndex i → Bool × Bool)).map
        (fun seed => (-w i + dominantRemainderRowSeedDot seed w) ^ 2) =
      (PMF.uniformOfFintype
        (DominantRemainderIndex i → Bool × Bool)).map
          (fun seed => (w i + dominantRemainderRowSeedDot seed w) ^ 2) := by
  let p := PMF.uniformOfFintype
    (DominantRemainderIndex i → Bool × Bool)
  calc
    p.map (fun seed => (-w i + dominantRemainderRowSeedDot seed w) ^ 2) =
        p.map (fun seed =>
          (w i + dominantRemainderRowSeedDot
            (negateDominantRemainderRowSeed seed) w) ^ 2) := by
      congr 1
      funext seed
      rw [dominantRemainderRowSeedDot_negate]
      exact congrArg Prod.fst
        (activeSign_square_pair (w i) (dominantRemainderRowSeedDot seed w))
    _ = (p.map negateDominantRemainderRowSeed).map
          (fun seed => (w i + dominantRemainderRowSeedDot seed w) ^ 2) := by
      rw [PMF.map_comp]
      rfl
    _ = _ := by rw [map_uniformDominantRemainderRowSeed_negate]

/-- Either active sign reduces to the row-local nonnegative-amplitude shift. -/
theorem activeRemainderRowSignedShiftSquarePMF_eq_amplitude {d : ℕ}
    (i : Fin d) (w : Fin d → ℤ) (sign : Bool) :
    (PMF.uniformOfFintype
      (DominantRemainderIndex i → Bool × Bool)).map
        (fun seed =>
          (signBit sign * w i + dominantRemainderRowSeedDot seed w) ^ 2) =
      (PMF.uniformOfFintype
        (DominantRemainderIndex i → Bool × Bool)).map
          (fun seed =>
            (((dominantAmplitude w i : ℕ) : ℤ) +
              dominantRemainderRowSeedDot seed w) ^ 2) := by
  cases sign
  · calc
      _ = (PMF.uniformOfFintype
            (DominantRemainderIndex i → Bool × Bool)).map
            (fun seed => (w i + dominantRemainderRowSeedDot seed w) ^ 2) := by
          simpa [signBit] using activeRemainderRowShiftSquarePMF_symm i w
      _ = _ := by
        by_cases hi : 0 ≤ w i
        · have hw : w i = ((dominantAmplitude w i : ℕ) : ℤ) := by
            simp [dominantAmplitude, Int.natAbs_of_nonneg hi]
          rw [hw]
        · have hi' : w i < 0 := lt_of_not_ge hi
          have hw : -w i = ((dominantAmplitude w i : ℕ) : ℤ) := by
            simp [dominantAmplitude, abs_of_neg hi']
          rw [← hw]
          exact (activeRemainderRowShiftSquarePMF_symm i w).symm
  · simp only [signBit, one_mul]
    by_cases hi : 0 ≤ w i
    · have hw : w i = ((dominantAmplitude w i : ℕ) : ℤ) := by
        simp [dominantAmplitude, Int.natAbs_of_nonneg hi]
      rw [hw]
    · have hi' : w i < 0 := lt_of_not_ge hi
      have hw : -w i = ((dominantAmplitude w i : ℕ) : ℤ) := by
        simp [dominantAmplitude, abs_of_neg hi']
      rw [← hw]
      exact (activeRemainderRowShiftSquarePMF_symm i w).symm

/-- The active conditional row square is exactly the uniform `(A + R)²` law. -/
theorem dominantConditionalRowPMF_active_square_dot {d : ℕ} (i : Fin d)
    (w : Fin d → ℤ) :
    (dominantConditionalRowPMF i true).map
        (fun row => (∑ j, row j * w j) ^ 2) =
      (PMF.uniformOfFintype
        (DominantRemainderIndex i → Bool × Bool)).map
          (fun seed =>
            (((dominantAmplitude w i : ℕ) : ℤ) +
              dominantRemainderRowSeedDot seed w) ^ 2) := by
  rw [dominantConditionalRowPMF, PMF.map_comp]
  change (PMF.uniformOfFintype (DominantConditionalRowSeed i)).map
      (fun seed => (∑ j, dominantConditionalRow i true seed j * w j) ^ 2) = _
  have hfun :
      (fun seed : DominantConditionalRowSeed i =>
        (∑ j, dominantConditionalRow i true seed j * w j) ^ 2) =
      (fun seed =>
        (signBit seed.1 * w i + dominantRemainderRowSeedDot seed.2 w) ^ 2) := by
    funext seed
    rw [dominantConditionalRow_dot]
    rfl
  rw [hfun]
  rw [Probability.uniformOfFintype_prod_eq_bind]
  rw [PMF.map_bind]
  let target :=
    (PMF.uniformOfFintype
      (DominantRemainderIndex i → Bool × Bool)).map
        (fun seed =>
          (((dominantAmplitude w i : ℕ) : ℤ) +
            dominantRemainderRowSeedDot seed w) ^ 2)
  calc
    _ = (PMF.uniformOfFintype Bool).bind fun _ => target := by
      congr 1
      funext sign
      rw [PMF.map_comp]
      exact activeRemainderRowSignedShiftSquarePMF_eq_amplitude i w sign
    _ = target := PMF.bind_const _ _

/-- The fixed-activity conditional matrix distribution is a product of row distributions. -/
theorem dominantConditionalMatrixPMF_eq_uniformPiMap {m d : ℕ}
    (i : Fin d) (activity : DominantActivity m) :
    dominantConditionalMatrixPMF i activity =
      uniformPiMap fun row => dominantConditionalRow i (activity row) := by
  rw [dominantConditionalMatrixPMF]
  rw [uniformPiMap]
  rw [uniformPiPMF_eq_uniformOfFintype]
  rw [← map_uniformOfFintype_equiv
    (dominantConditionalSeedsEquivRows (m := m) i)]
  rw [PMF.map_comp]
  congr 1
  funext conditional row
  exact sparseMatrixOfDominantView_row_eq_conditionalRow
    i activity conditional row

/--
Strict negative-Laplace tensorization under the exact fixed-activity law.
-/
theorem dominantConditional_eventProbability_strictNegativeLaplace
    {m d : ℕ} (i : Fin d) (activity : DominantActivity m)
    (f : Fin m → (Fin d → ℤ) → ℝ) (s c : ℝ) (hs : 0 < s) :
    (eventProbability (dominantConditionalMatrixPMF i activity)
        (fun J => ∑ row, f row (J row) < c)).toReal ≤
      Real.exp (s * c) *
        ∏ row, ∫ x, Real.exp (-s * f row x)
          ∂(dominantConditionalRowPMF i (activity row)).toMeasure := by
  rw [dominantConditionalMatrixPMF_eq_uniformPiMap]
  rw [eventProbability_eq_toMeasure]
  have h_integrable :
      Integrable (fun J => Real.exp (-s * ∑ row, f row (J row)))
        (uniformPiMap
          (fun row => dominantConditionalRow i (activity row))).toMeasure :=
    by
      rw [uniformPiMap]
      rw [← PMF.toMeasure_map
        (p := uniformPiPMF fun _ : Fin m => DominantConditionalRowSeed i)
        (f := fun seeds row =>
          dominantConditionalRow i (activity row) (seeds row))
        (measurable_of_finite _)]
      apply (integrable_map_measure
        (measurable_of_countable _).aestronglyMeasurable
        (measurable_of_finite _).aemeasurable).2
      exact Integrable.of_finite
  have hmarkov := strictExponentialMarkov
    (μ := (uniformPiMap
      (fun row => dominantConditionalRow i (activity row))).toMeasure)
    (X := fun J => ∑ row, f row (J row)) s c hs h_integrable
  calc
    _ ≤ Real.exp (s * c) *
          ∫ J, Real.exp (-s * ∑ row, f row (J row))
            ∂(uniformPiMap
              (fun row => dominantConditionalRow i (activity row))).toMeasure :=
        hmarkov
    _ = Real.exp (s * c) *
          ∫ J, ∏ row, Real.exp (-s * f row (J row))
            ∂(uniformPiMap
              (fun row => dominantConditionalRow i (activity row))).toMeasure := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with J
        rw [Finset.mul_sum, Real.exp_sum]
    _ = _ := by
      congr 1
      rw [uniformPiMap_toMeasure]
      · simpa [dominantConditionalRowPMF] using
          (MeasureTheory.integral_fintype_prod_eq_prod
            (μ := fun row =>
              (dominantConditionalRowPMF i (activity row)).toMeasure)
            (fun row x => Real.exp (-s * f row x)))
      · intro row
        exact measurable_of_finite _

/-- Product of inactive/active row bounds, grouped by the true active count. -/
theorem prod_dominantActivity_ite {m : ℕ} (activity : DominantActivity m)
    (L₀ L₁ : ℝ) :
    ∏ row, (if activity row then L₁ else L₀) =
      L₁ ^ (dominantActivityCount activity : ℕ) *
        L₀ ^ (m - (dominantActivityCount activity : ℕ)) := by
  classical
  let p : Fin m → Prop := fun row => activity row = true
  change (∏ row, (if p row then L₁ else L₀)) = _
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m))) (p := p)
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  have hactive :
      ((Finset.univ.filter p).card) =
        (dominantActivityCount activity : ℕ) := by
    rfl
  have hinactive :
      ((Finset.univ.filter fun row => ¬p row).card) =
        m - (dominantActivityCount activity : ℕ) := by
    omega
  rw [hactive, hinactive]

/--
Explicit inactive/active kernel interface for one fixed activity set.
The premise consists only of row Laplace integrals under the actual row distributions.
-/
theorem dominantConditional_eventProbability_le_activeInactiveKernels
    {m d : ℕ} (i : Fin d) (activity : DominantActivity m)
    (f : Fin m → (Fin d → ℤ) → ℝ) (s c L₀ L₁ : ℝ) (hs : 0 < s)
    (hrow : ∀ row,
      ∫ x, Real.exp (-s * f row x)
          ∂(dominantConditionalRowPMF i (activity row)).toMeasure ≤
        if activity row then L₁ else L₀) :
    (eventProbability (dominantConditionalMatrixPMF i activity)
        (fun J => ∑ row, f row (J row) < c)).toReal ≤
      Real.exp (s * c) *
        L₁ ^ (dominantActivityCount activity : ℕ) *
          L₀ ^ (m - (dominantActivityCount activity : ℕ)) := by
  calc
    _ ≤ Real.exp (s * c) *
          ∏ row, ∫ x, Real.exp (-s * f row x)
            ∂(dominantConditionalRowPMF i (activity row)).toMeasure :=
        dominantConditional_eventProbability_strictNegativeLaplace
          i activity f s c hs
    _ ≤ Real.exp (s * c) *
          ∏ row, (if activity row then L₁ else L₀) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply Finset.prod_le_prod
        · intro row _
          exact integral_nonneg_of_ae
            (Filter.Eventually.of_forall fun x => Real.exp_nonneg _)
        · intro row _
          exact hrow row
    _ = _ := by
      rw [prod_dominantActivity_ite]
      ring

/-- Every finite-PMF event has real probability at most one. -/
theorem eventProbability_toReal_le_one {Ω : Type*}
    (p : PMF Ω) (event : Ω → Prop) :
    (eventProbability p event).toReal ≤ 1 := by
  unfold eventProbability
  rw [← ENNReal.toReal_one]
  exact (ENNReal.toReal_le_toReal
    ((p.map event).apply_ne_top True) ENNReal.one_ne_top).2
      ((p.map event).coe_le_one True)

end CertifiedJL
