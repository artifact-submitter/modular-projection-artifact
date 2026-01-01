/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Unrestricted.Conditioning
import CertifiedJL.Model.Vectors.SquaredNorm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Dominant-coordinate normalization

This module keeps the natural squared-norm decomposition visible while
introducing the paper's real normalization `u = U/A²`.  It also records the
exact inactive/active row shapes before any analytic estimate is applied.
-/

open scoped BigOperators

namespace CertifiedJL

/-- Natural squared mass outside the distinguished coordinate. -/
def dominantRemainderSqNorm {d : ℕ} (w : Fin d → ℤ) (i : Fin d) : ℕ :=
  ∑ j : DominantRemainderIndex i, (w j.1).natAbs ^ 2

/-- The natural squared norm splits exactly as `A² + U`. -/
theorem sqNorm_eq_dominant_add_remainder {d : ℕ}
    (w : Fin d → ℤ) (i : Fin d) :
    sqNorm w = (w i).natAbs ^ 2 + dominantRemainderSqNorm w i := by
  rw [sqNorm, Fintype.sum_eq_add_sum_subtype_ne _ i]
  rfl

/-- The paper's nonnegative dominant amplitude. -/
def dominantAmplitude {d : ℕ} (w : Fin d → ℤ) (i : Fin d) : ℕ :=
  (w i).natAbs

/-- The normalized residual mass `u = U/A²`. -/
noncomputable def dominantResidualRatio {d : ℕ}
    (w : Fin d → ℤ) (i : Fin d) : ℝ :=
  (dominantRemainderSqNorm w i : ℝ) / (dominantAmplitude w i : ℝ) ^ 2

/-- A nonzero distinguished coefficient has positive amplitude. -/
theorem dominantAmplitude_pos {d : ℕ} {w : Fin d → ℤ} {i : Fin d}
    (hi : w i ≠ 0) :
    0 < dominantAmplitude w i := by
  simpa [dominantAmplitude] using Int.natAbs_pos.mpr hi

/-- The normalized residual mass is nonnegative. -/
theorem dominantResidualRatio_nonneg {d : ℕ}
    (w : Fin d → ℤ) (i : Fin d) :
    0 ≤ dominantResidualRatio w i := by
  exact div_nonneg (by positivity) (sq_nonneg _)

/-- `1 + u` is the total natural squared mass divided by `A²`. -/
theorem one_add_dominantResidualRatio {d : ℕ}
    (w : Fin d → ℤ) (i : Fin d) (hi : w i ≠ 0) :
    1 + dominantResidualRatio w i =
      (sqNorm w : ℝ) / (dominantAmplitude w i : ℝ) ^ 2 := by
  have hA : (dominantAmplitude w i : ℝ) ≠ 0 := by
    exact_mod_cast (dominantAmplitude_pos hi).ne'
  rw [sqNorm_eq_dominant_add_remainder w i]
  push_cast
  simp only [dominantResidualRatio]
  field_simp
  simp [dominantAmplitude]

/-- The headline total-norm modulus lower bound becomes the paper's `D₀ = 3`
endpoint after normalization by the dominant amplitude. -/
theorem dominantAmplitude_modulus_lower
    {d q : ℕ} (w : Fin d → ℤ) (i : Fin d) (hi : w i ≠ 0)
    (hD : (3 : ℝ) ≤ (q : ℝ) / Real.sqrt (sqNorm w : ℝ))
    {lower : ℝ} (hlower : 0 ≤ lower)
    (hlower_u : lower ≤ dominantResidualRatio w i) :
    3 * Real.sqrt (1 + lower) ≤
      (q : ℝ) / (dominantAmplitude w i : ℝ) := by
  let A : ℝ := dominantAmplitude w i
  let u : ℝ := dominantResidualRatio w i
  have hA : 0 < A := by
    dsimp [A]
    exact_mod_cast dominantAmplitude_pos hi
  have hVnat : 0 < sqNorm w := by
    apply (sqNorm_pos_iff w).2
    intro hw
    exact hi (congrFun hw i)
  have hV : 0 < (sqNorm w : ℝ) := by exact_mod_cast hVnat
  have hsqrtV : Real.sqrt (sqNorm w : ℝ) ^ 2 = (sqNorm w : ℝ) :=
    Real.sq_sqrt hV.le
  have hu : 0 ≤ u := dominantResidualRatio_nonneg w i
  have hratio : 1 + u = (sqNorm w : ℝ) / A ^ 2 := by
    simpa [A, u] using one_add_dominantResidualRatio w i hi
  have hsqrt_relation :
      Real.sqrt (sqNorm w : ℝ) = A * Real.sqrt (1 + u) := by
    have hleft : 0 ≤ Real.sqrt (sqNorm w : ℝ) := Real.sqrt_nonneg _
    have hright : 0 ≤ A * Real.sqrt (1 + u) := by positivity
    have hsqrtu : Real.sqrt (1 + u) ^ 2 = 1 + u :=
      Real.sq_sqrt (by linarith)
    have hsq :
        (Real.sqrt (sqNorm w : ℝ)) ^ 2 =
          (A * Real.sqrt (1 + u)) ^ 2 := by
      rw [hsqrtV, mul_pow, hsqrtu, hratio]
      field_simp [hA.ne']
    nlinarith
  have hq : 3 * Real.sqrt (sqNorm w : ℝ) ≤ (q : ℝ) :=
    (le_div_iff₀ (Real.sqrt_pos.2 hV)).mp hD
  have hsqrt_mono : Real.sqrt (1 + lower) ≤ Real.sqrt (1 + u) :=
    Real.sqrt_le_sqrt (by linarith)
  apply (le_div_iff₀ hA).2
  calc
    3 * Real.sqrt (1 + lower) * A ≤
        3 * Real.sqrt (1 + u) * A := by
      nlinarith [mul_le_mul_of_nonneg_left hsqrt_mono
        (by positivity : 0 ≤ 3 * A)]
    _ = 3 * Real.sqrt (sqNorm w : ℝ) := by rw [hsqrt_relation]; ring
    _ ≤ (q : ℝ) := hq

/-- Integer remainder dot product outside the distinguished coordinate. -/
def dominantRemainderDot {d : ℕ} (row : Fin d → ℤ)
    (w : Fin d → ℤ) (i : Fin d) : ℤ :=
  ∑ j : DominantRemainderIndex i, row j.1 * w j.1

/-- Every row dot product is its dominant term plus the remainder. -/
theorem rowDot_eq_dominant_add_remainder {m d : ℕ}
    (J : Matrix (Fin m) (Fin d) ℤ) (w : Fin d → ℤ)
    (row : Fin m) (i : Fin d) :
    rowDot J w row =
      J row i * w i + dominantRemainderDot (J row) w i := by
  rw [rowDot, Fintype.sum_eq_add_sum_subtype_ne _ i]
  rfl

/-- The integer value of the distinguished sparse entry in seed-view form. -/
theorem sparseMatrix_dominantEntry {m d : ℕ} (seed : SparseSeed m d)
    (row : Fin m) (i : Fin d) :
    sparseMatrix seed row i =
      if (dominantSeedView i seed).1 row then
        signBit ((dominantSeedView i seed).2.1 row)
      else 0 := by
  change sparseBit (seed row i) = _
  change sparseBit (seed row i) =
    if sparsePairActivity (seed row i) then
      signBit (sparsePairSign (seed row i)) else 0
  simpa using sparseBit_ofActivitySign
    (sparsePairActivity (seed row i)) (sparsePairSign (seed row i))

/--
An inactive row is exactly `R`; an active row is `±wᵢ + R`, with the sign
bit kept independent in the finite conditioning view.
-/
theorem sparseMatrix_rowDot_dominantView {m d : ℕ}
    (seed : SparseSeed m d) (w : Fin d → ℤ)
    (row : Fin m) (i : Fin d) :
    rowDot (sparseMatrix seed) w row =
      if (dominantSeedView i seed).1 row then
        signBit ((dominantSeedView i seed).2.1 row) * w i +
          dominantRemainderDot (sparseMatrix seed row) w i
      else dominantRemainderDot (sparseMatrix seed row) w i := by
  rw [rowDot_eq_dominant_add_remainder
    (J := sparseMatrix seed) (w := w) (row := row) (i := i)]
  rw [sparseMatrix_dominantEntry seed row i]
  split <;> simp

/-- The two active signs give the paper's `A+R` and `-A+R` square pair. -/
theorem activeSign_square_pair (A R : ℤ) :
    ((-A + R) ^ 2, (A + R) ^ 2) =
      ((A + -R) ^ 2, (A + R) ^ 2) := by
  apply Prod.ext
  · ring
  · rfl

/-- Flip both sign bits underlying one sparse entry. -/
def negateSparsePairSeed (b : Bool × Bool) : Bool × Bool :=
  (!b.1, !b.2)

@[simp]
theorem negateSparsePairSeed_involutive (b : Bool × Bool) :
    negateSparsePairSeed (negateSparsePairSeed b) = b := by
  rcases b with ⟨b₀, b₁⟩
  cases b₀ <;> cases b₁ <;> rfl

@[simp]
theorem sparseBit_negateSparsePairSeed (b : Bool × Bool) :
    sparseBit (negateSparsePairSeed b) = -sparseBit b := by
  rcases b with ⟨b₀, b₁⟩
  cases b₀ <;> cases b₁ <;> decide

/-- Negate every sparse entry in a conditioned remainder seed. -/
def negateDominantRemainderSeeds {m d : ℕ} {i : Fin d}
    (seed : DominantRemainderSeeds (m := m) i) :
    DominantRemainderSeeds (m := m) i :=
  fun row j => negateSparsePairSeed (seed row j)

@[simp]
theorem negateDominantRemainderSeeds_involutive {m d : ℕ} {i : Fin d}
    (seed : DominantRemainderSeeds (m := m) i) :
    negateDominantRemainderSeeds (negateDominantRemainderSeeds seed) = seed := by
  funext row j
  exact negateSparsePairSeed_involutive (seed row j)

/-- Negation is an equivalence of the finite remainder seed space. -/
def negateDominantRemainderSeedsEquiv {m d : ℕ} (i : Fin d) :
    DominantRemainderSeeds (m := m) i ≃
      DominantRemainderSeeds (m := m) i where
  toFun := negateDominantRemainderSeeds
  invFun := negateDominantRemainderSeeds
  left_inv := negateDominantRemainderSeeds_involutive
  right_inv := negateDominantRemainderSeeds_involutive

/-- Uniform conditioned remainder seeds are invariant under negation. -/
theorem map_uniformDominantRemainderSeeds_negate {m d : ℕ} (i : Fin d) :
    (PMF.uniformOfFintype (DominantRemainderSeeds (m := m) i)).map
        negateDominantRemainderSeeds =
      PMF.uniformOfFintype (DominantRemainderSeeds (m := m) i) := by
  change
    (PMF.uniformOfFintype (DominantRemainderSeeds (m := m) i)).map
        (negateDominantRemainderSeedsEquiv i) =
      PMF.uniformOfFintype (DominantRemainderSeeds (m := m) i)
  exact map_uniformOfFintype_equiv (negateDominantRemainderSeedsEquiv i)

/-- Integer remainder sum read directly from conditioned remainder seeds. -/
def dominantRemainderSeedDot {m d : ℕ} {i : Fin d}
    (seed : DominantRemainderSeeds (m := m) i)
    (w : Fin d → ℤ) (row : Fin m) : ℤ :=
  ∑ j : DominantRemainderIndex i, sparseBit (seed row j) * w j.1

/-- The reconstructed matrix remainder is exactly the conditioned-seed remainder. -/
theorem dominantRemainderDot_sparseMatrixOfDominantView {m d : ℕ}
    (i : Fin d) (view : DominantSeedView (m := m) i)
    (w : Fin d → ℤ) (row : Fin m) :
    dominantRemainderDot (sparseMatrixOfDominantView i view row) w i =
      dominantRemainderSeedDot view.2.2 w row := by
  apply Finset.sum_congr rfl
  intro j _
  simp [sparseMatrixOfDominantView, sparseMatrix, sparseRow,
    sparseSeedOfDominantView, j.2]

/-- Paper-shaped row formula on a reconstructed conditioned seed view. -/
theorem sparseMatrixOfDominantView_rowDot {m d : ℕ}
    (i : Fin d) (view : DominantSeedView (m := m) i)
    (w : Fin d → ℤ) (row : Fin m) :
    rowDot (sparseMatrixOfDominantView i view) w row =
      if view.1 row then
        signBit (view.2.1 row) * w i +
          dominantRemainderSeedDot view.2.2 w row
      else dominantRemainderSeedDot view.2.2 w row := by
  change rowDot (sparseMatrix (sparseSeedOfDominantView i view)) w row = _
  rw [sparseMatrix_rowDot_dominantView
    (sparseSeedOfDominantView i view) w row i]
  rw [dominantSeedView_ofView]
  have hR :
      dominantRemainderDot
          (sparseMatrix (sparseSeedOfDominantView i view) row) w i =
        dominantRemainderSeedDot view.2.2 w row := by
    simpa [sparseMatrixOfDominantView] using
      dominantRemainderDot_sparseMatrixOfDominantView i view w row
  rw [hR]

@[simp]
theorem dominantRemainderSeedDot_negate {m d : ℕ} {i : Fin d}
    (seed : DominantRemainderSeeds (m := m) i)
    (w : Fin d → ℤ) (row : Fin m) :
    dominantRemainderSeedDot (negateDominantRemainderSeeds seed) w row =
      -dominantRemainderSeedDot seed w row := by
  simp only [dominantRemainderSeedDot, negateDominantRemainderSeeds,
    sparseBit_negateSparsePairSeed, neg_mul, Finset.sum_neg_distrib]

/--
For a uniform conditioned remainder, the two active dominant signs have the
same squared-row distribution. This is the finite symmetry reducing active rows to
`A + R`.
-/
theorem activeShiftSquarePMF_symm {m d : ℕ} (i : Fin d)
    (w : Fin d → ℤ) (row : Fin m) :
    (PMF.uniformOfFintype (DominantRemainderSeeds (m := m) i)).map
        (fun seed => (-w i + dominantRemainderSeedDot seed w row) ^ 2) =
      (PMF.uniformOfFintype (DominantRemainderSeeds (m := m) i)).map
        (fun seed => (w i + dominantRemainderSeedDot seed w row) ^ 2) := by
  let p := PMF.uniformOfFintype (DominantRemainderSeeds (m := m) i)
  calc
    p.map (fun seed => (-w i + dominantRemainderSeedDot seed w row) ^ 2) =
        p.map (fun seed =>
          (w i + dominantRemainderSeedDot
            (negateDominantRemainderSeeds seed) w row) ^ 2) := by
      congr 1
      funext seed
      rw [dominantRemainderSeedDot_negate]
      exact congrArg Prod.fst
        (activeSign_square_pair (w i)
          (dominantRemainderSeedDot seed w row))
    _ = (p.map negateDominantRemainderSeeds).map
          (fun seed => (w i + dominantRemainderSeedDot seed w row) ^ 2) := by
      rw [PMF.map_comp]
      rfl
    _ = p.map (fun seed =>
          (w i + dominantRemainderSeedDot seed w row) ^ 2) := by
      rw [map_uniformDominantRemainderSeeds_negate]

/-- The active shifted-square law may use the nonnegative amplitude `|wᵢ|`. -/
theorem activeShiftSquarePMF_eq_amplitude {m d : ℕ} (i : Fin d)
    (w : Fin d → ℤ) (row : Fin m) :
    (PMF.uniformOfFintype (DominantRemainderSeeds (m := m) i)).map
        (fun seed => (w i + dominantRemainderSeedDot seed w row) ^ 2) =
      (PMF.uniformOfFintype (DominantRemainderSeeds (m := m) i)).map
        (fun seed =>
          (((dominantAmplitude w i : ℕ) : ℤ) +
            dominantRemainderSeedDot seed w row) ^ 2) := by
  by_cases hi : 0 ≤ w i
  · have hw : w i = ((dominantAmplitude w i : ℕ) : ℤ) := by
      simp [dominantAmplitude, Int.natAbs_of_nonneg hi]
    rw [hw]
  · have hi' : w i < 0 := lt_of_not_ge hi
    have hw : -w i = ((dominantAmplitude w i : ℕ) : ℤ) := by
      simp [dominantAmplitude, abs_of_neg hi']
    rw [← hw]
    exact (activeShiftSquarePMF_symm i w row).symm

/-- After averaging the remainder, either active sign reduces to `A + R`. -/
theorem activeSignedShiftSquarePMF_eq_amplitude {m d : ℕ} (i : Fin d)
    (w : Fin d → ℤ) (row : Fin m) (sign : Bool) :
    (PMF.uniformOfFintype (DominantRemainderSeeds (m := m) i)).map
        (fun seed =>
          (signBit sign * w i + dominantRemainderSeedDot seed w row) ^ 2) =
      (PMF.uniformOfFintype (DominantRemainderSeeds (m := m) i)).map
        (fun seed =>
          (((dominantAmplitude w i : ℕ) : ℤ) +
            dominantRemainderSeedDot seed w row) ^ 2) := by
  cases sign
  · calc
      _ = (PMF.uniformOfFintype
            (DominantRemainderSeeds (m := m) i)).map
            (fun seed =>
              (w i + dominantRemainderSeedDot seed w row) ^ 2) := by
          simpa [signBit] using activeShiftSquarePMF_symm i w row
      _ = _ := activeShiftSquarePMF_eq_amplitude i w row
  · simpa [signBit] using activeShiftSquarePMF_eq_amplitude i w row

end CertifiedJL
