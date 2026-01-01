/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Distributions.Entry
import CertifiedJL.Probability.Finite.Counting
import Mathlib.Tactic.FinCases

/-!
# Finite conditioning for a dominant sparse coordinate

This module splits a uniform sparse-matrix seed into the active-row set, the
dominant-coordinate signs, and all remainder seeds.  The split is an explicit
finite equivalence, so the exact binomial activity law and conditional
independence remain connected to the public sparse-matrix PMF.
-/

open scoped BigOperators ENNReal

namespace CertifiedJL

open Probability

/-- Whether the sparse entry represented by two bits is nonzero. -/
def sparsePairActivity (b : Bool × Bool) : Bool :=
  b.1 == b.2

/-- The sign bit used when a sparse entry is active. -/
def sparsePairSign (b : Bool × Bool) : Bool :=
  b.1

/-- Reassemble the two-bit sparse-entry seed from activity and sign. -/
def sparsePairOfActivitySign (activity sign : Bool) : Bool × Bool :=
  if activity then (sign, sign) else (sign, !sign)

@[simp]
theorem sparsePairOfActivitySign_view (b : Bool × Bool) :
    sparsePairOfActivitySign (sparsePairActivity b) (sparsePairSign b) = b := by
  rcases b with ⟨b₀, b₁⟩
  cases b₀ <;> cases b₁ <;>
    decide

@[simp]
theorem sparsePairActivity_ofActivitySign (activity sign : Bool) :
    sparsePairActivity (sparsePairOfActivitySign activity sign) = activity := by
  cases activity <;> cases sign <;> decide

@[simp]
theorem sparsePairSign_ofActivitySign (activity sign : Bool) :
    sparsePairSign (sparsePairOfActivitySign activity sign) = sign := by
  cases activity <;> cases sign <;> decide

/-- The two-bit sparse seed is activity together with an independent sign. -/
def sparsePairEquivActivitySign :
    Bool × Bool ≃ Bool × Bool where
  toFun b := (sparsePairActivity b, sparsePairSign b)
  invFun b := sparsePairOfActivitySign b.1 b.2
  left_inv := sparsePairOfActivitySign_view
  right_inv b := by
    apply Prod.ext
    · exact sparsePairActivity_ofActivitySign b.1 b.2
    · exact sparsePairSign_ofActivitySign b.1 b.2

/-- Coordinates other than a fixed dominant coordinate. -/
abbrev DominantRemainderIndex {d : ℕ} (i : Fin d) :=
  {j : Fin d // j ≠ i}

/-- Activity bits of the distinguished coordinate, one per row. -/
abbrev DominantActivity (m : ℕ) := Fin m → Bool

/-- Signs of the distinguished coordinate, one per row. -/
abbrev DominantSigns (m : ℕ) := Fin m → Bool

/-- Sparse seeds for every coefficient other than the distinguished one. -/
abbrev DominantRemainderSeeds {m d : ℕ} (i : Fin d) :=
  Fin m → DominantRemainderIndex i → Bool × Bool

/-- Sign and remainder data left after fixing the active-row set. -/
abbrev DominantConditionalSeeds {m d : ℕ} (i : Fin d) :=
  DominantSigns m × DominantRemainderSeeds (m := m) i

/-- Complete seed view used to condition on the active-row set. -/
abbrev DominantSeedView {m d : ℕ} (i : Fin d) :=
  DominantActivity m × DominantConditionalSeeds (m := m) i

/-- Split a sparse-matrix seed at a distinguished coordinate. -/
def dominantSeedView {m d : ℕ} (i : Fin d) (seed : SparseSeed m d) :
    DominantSeedView (m := m) i :=
  (fun row => sparsePairActivity (seed row i),
    (fun row => sparsePairSign (seed row i),
      fun row j => seed row j.1))

/-- Reassemble a sparse-matrix seed from its dominant-coordinate view. -/
def sparseSeedOfDominantView {m d : ℕ} (i : Fin d)
    (view : DominantSeedView (m := m) i) : SparseSeed m d :=
  fun row j =>
    if hj : j = i then
      sparsePairOfActivitySign (view.1 row) (view.2.1 row)
    else view.2.2 row ⟨j, hj⟩

@[simp]
theorem sparseSeedOfDominantView_view {m d : ℕ} (i : Fin d)
    (seed : SparseSeed m d) :
    sparseSeedOfDominantView i (dominantSeedView i seed) = seed := by
  funext row j
  by_cases hj : j = i
  · subst j
    simp [sparseSeedOfDominantView, dominantSeedView]
  · simp [sparseSeedOfDominantView, dominantSeedView, hj]

@[simp]
theorem dominantSeedView_ofView {m d : ℕ} (i : Fin d)
    (view : DominantSeedView (m := m) i) :
    dominantSeedView i (sparseSeedOfDominantView i view) = view := by
  apply Prod.ext
  · funext row
    simp [dominantSeedView, sparseSeedOfDominantView]
  · apply Prod.ext
    · funext row
      simp [dominantSeedView, sparseSeedOfDominantView]
    · funext row j
      simp [dominantSeedView, sparseSeedOfDominantView, j.2]

/-- Sparse-matrix seeds are exactly activity, signs, and remainder seeds. -/
def sparseSeedEquivDominantView {m d : ℕ} (i : Fin d) :
    SparseSeed m d ≃ DominantSeedView (m := m) i where
  toFun := dominantSeedView i
  invFun := sparseSeedOfDominantView i
  left_inv := sparseSeedOfDominantView_view i
  right_inv := dominantSeedView_ofView i

/-- The dominant-coordinate view of a uniform sparse seed is uniform. -/
theorem map_uniformSparseSeed_dominantView {m d : ℕ} (i : Fin d) :
    (PMF.uniformOfFintype (SparseSeed m d)).map (dominantSeedView i) =
      PMF.uniformOfFintype (DominantSeedView (m := m) i) := by
  change
    (PMF.uniformOfFintype (SparseSeed m d)).map
        (sparseSeedEquivDominantView i) =
      PMF.uniformOfFintype (DominantSeedView (m := m) i)
  exact map_uniformOfFintype_equiv (sparseSeedEquivDominantView i)

/-- The active-row set is uniform. -/
theorem dominantActivityPMF_eq_uniform {m d : ℕ} (i : Fin d) :
    (PMF.uniformOfFintype (DominantSeedView (m := m) i)).map Prod.fst =
      PMF.uniformOfFintype (DominantActivity m) := by
  exact Probability.map_uniformOfFintype_prod_fst
    (DominantActivity m) (DominantConditionalSeeds (m := m) i)

/--
Exact finite conditioning statement: after the active-row set is sampled,
dominant signs and all remainder seeds retain their uniform joint law.  In
particular, this conditional law does not depend on the chosen active set.
-/
theorem uniformDominantSeedView_eq_bind {m d : ℕ} (i : Fin d) :
    PMF.uniformOfFintype (DominantSeedView (m := m) i) =
      (PMF.uniformOfFintype (DominantActivity m)).bind fun activity =>
        (PMF.uniformOfFintype
          (DominantConditionalSeeds (m := m) i)).map fun conditional =>
            (activity, conditional) := by
  exact Probability.uniformOfFintype_prod_eq_bind
    (DominantActivity m) (DominantConditionalSeeds (m := m) i)

/-- The finite sparse-seed law in explicitly conditioned form. -/
theorem map_uniformSparseSeed_dominantView_eq_bind {m d : ℕ} (i : Fin d) :
    (PMF.uniformOfFintype (SparseSeed m d)).map (dominantSeedView i) =
      (PMF.uniformOfFintype (DominantActivity m)).bind fun activity =>
        (PMF.uniformOfFintype
          (DominantConditionalSeeds (m := m) i)).map fun conditional =>
            (activity, conditional) := by
  rw [map_uniformSparseSeed_dominantView i]
  exact uniformDominantSeedView_eq_bind i

/-- Interpret a complete dominant seed view as its integer sparse matrix. -/
def sparseMatrixOfDominantView {m d : ℕ} (i : Fin d)
    (view : DominantSeedView (m := m) i) : Fin m → Fin d → ℤ :=
  sparseMatrix (sparseSeedOfDominantView i view)

/-- Actual conditional matrix distribution after fixing the active-row set. -/
noncomputable def dominantConditionalMatrixPMF {m d : ℕ} (i : Fin d)
    (activity : DominantActivity m) : PMF (Fin m → Fin d → ℤ) :=
  (PMF.uniformOfFintype (DominantConditionalSeeds (m := m) i)).map
    fun conditional => sparseMatrixOfDominantView i (activity, conditional)

/-- The actual sparse-matrix PMF is the image of the uniform dominant view. -/
theorem sparseRademacherMatrix_eq_map_uniformDominantView {m d : ℕ} (i : Fin d) :
    sparseRademacherMatrix m d =
      (PMF.uniformOfFintype (DominantSeedView (m := m) i)).map
        (sparseMatrixOfDominantView i) := by
  rw [sparseRademacherMatrix_eq_map_uniformSeed]
  rw [← map_uniformSparseSeed_dominantView i]
  rw [PMF.map_comp]
  congr 1
  funext seed
  simp [sparseMatrixOfDominantView]

/--
Exact conditioning theorem on the actual sparse-matrix PMF. First sample the
active-row set; conditional on it, sample one uniform law of dominant signs
and remainder seeds, independent of the chosen set, then reconstruct the
integer matrix.
-/
theorem sparseRademacherMatrix_eq_dominant_bind {m d : ℕ} (i : Fin d) :
    sparseRademacherMatrix m d =
      (PMF.uniformOfFintype (DominantActivity m)).bind fun activity =>
        (PMF.uniformOfFintype
          (DominantConditionalSeeds (m := m) i)).map fun conditional =>
            sparseMatrixOfDominantView i (activity, conditional) := by
  rw [sparseRademacherMatrix_eq_map_uniformDominantView i]
  rw [uniformDominantSeedView_eq_bind i]
  rw [PMF.map_bind]
  congr 1
  funext activity
  rw [PMF.map_comp]
  rfl

/-- Number of active distinguished-coordinate rows. -/
def dominantActivityCount {m : ℕ} (activity : DominantActivity m) : Fin (m + 1) :=
  ⟨(boolSupport activity).card,
    Nat.lt_succ_of_le (by
      simpa using (boolSupport activity).card_le_univ)⟩

/-- The fiber of activity sets of size `k` has cardinality `choose m k`. -/
theorem card_dominantActivityCount_fiber (m : ℕ) (k : Fin (m + 1)) :
    Fintype.card {activity : DominantActivity m // dominantActivityCount activity = k} =
      m.choose (k : ℕ) := by
  let e :
      {activity : DominantActivity m // dominantActivityCount activity = k} ≃
        {activity : DominantActivity m // (boolSupport activity).card = (k : ℕ)} :=
    Equiv.subtypeEquiv (Equiv.refl _) fun activity => by
      constructor
      · intro h
        exact congrArg Fin.val h
      · intro h
        apply Fin.ext
        exact h
  rw [Fintype.card_congr e]
  simpa using card_bool_true_count (Fin m) (k : ℕ)

/-- Exact `Binomial(m, 1/2)` mass of an active-row count. -/
theorem dominantActivityCountPMF_apply (m : ℕ) (k : Fin (m + 1)) :
    ((PMF.uniformOfFintype (DominantActivity m)).map dominantActivityCount) k =
      (m.choose (k : ℕ) : ℝ≥0∞) * ((2 ^ m : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  rw [map_uniform_apply_eq_card]
  rw [card_dominantActivityCount_fiber]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- In particular, the 256-row mass is `choose 256 k / 2^256`. -/
theorem dominantActivityCount256PMF_apply (k : Fin 257) :
    ((PMF.uniformOfFintype (DominantActivity 256)).map dominantActivityCount) k =
      ((256 : ℕ).choose (k : ℕ) : ℝ≥0∞) *
        ((2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ :=
  dominantActivityCountPMF_apply 256 k

/-- Activity of the distinguished coordinate read from an integer matrix. -/
def matrixDominantActivity {m d : ℕ} (i : Fin d)
    (J : Fin m → Fin d → ℤ) : DominantActivity m :=
  fun row => decide (J row i ≠ 0)

@[simp]
theorem sparseBit_ofActivitySign (activity sign : Bool) :
    sparseBit (sparsePairOfActivitySign activity sign) =
      if activity then signBit sign else 0 := by
  cases activity <;> cases sign <;> decide

@[simp]
theorem matrixDominantActivity_sparseMatrix {m d : ℕ} (i : Fin d)
    (seed : SparseSeed m d) :
    matrixDominantActivity i (sparseMatrix seed) =
      (dominantSeedView i seed).1 := by
  funext row
  change decide (sparseBit (seed row i) ≠ 0) =
    sparsePairActivity (seed row i)
  rcases h : seed row i with ⟨b₀, b₁⟩
  cases b₀ <;> cases b₁ <;> decide

/-- The actual sparse-matrix PMF has a uniform dominant active-row set. -/
theorem sparseRademacherMatrix_dominantActivity {m d : ℕ} (i : Fin d) :
    (sparseRademacherMatrix m d).map (matrixDominantActivity i) =
      PMF.uniformOfFintype (DominantActivity m) := by
  rw [sparseRademacherMatrix_eq_map_uniformSeed]
  rw [PMF.map_comp]
  have hfun :
      matrixDominantActivity (m := m) i ∘ (@sparseMatrix m d) =
        Prod.fst ∘ dominantSeedView (m := m) i := by
    funext seed
    exact matrixDominantActivity_sparseMatrix i seed
  rw [hfun, ← PMF.map_comp]
  rw [map_uniformSparseSeed_dominantView]
  exact dominantActivityPMF_eq_uniform i

/-- The actual 256-row sparse-matrix experiment has exact binomial mass. -/
theorem sparseRademacherMatrix_dominantActivityCount_apply {d : ℕ} (i : Fin d)
    (k : Fin 257) :
    ((sparseRademacherMatrix 256 d).map
        (dominantActivityCount ∘ matrixDominantActivity i)) k =
      ((256 : ℕ).choose (k : ℕ) : ℝ≥0∞) *
        ((2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [show
      (sparseRademacherMatrix 256 d).map
          (dominantActivityCount ∘ matrixDominantActivity i) =
        ((sparseRademacherMatrix 256 d).map (matrixDominantActivity i)).map
          dominantActivityCount by rw [PMF.map_comp]]
  rw [sparseRademacherMatrix_dominantActivity]
  exact dominantActivityCount256PMF_apply k

end CertifiedJL
