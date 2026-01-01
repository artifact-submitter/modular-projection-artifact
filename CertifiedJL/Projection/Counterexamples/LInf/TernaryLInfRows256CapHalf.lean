/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Product.RowTensorization
import CertifiedJL.Probability.Finite.Counting
import CertifiedJL.Statements.LInf.Lower
import Mathlib.Tactic

/-!
# The 256-row coordinate-cap-one-half obstruction

For the four-coordinate input `k(1,1,1,1)` and public threshold `2k`, a
balanced-ternary row passes the closed cap `1/2` exactly when the sum of its
four entries has magnitude at most one.  Exactly 182 of the 256 row seeds pass,
so the 256-row event has probability `(182/256)^256 > 2⁻¹²⁸`.
-/

open scoped BigOperators ENNReal

namespace CertifiedJL.Counterexamples.TernaryLInfRows256CapHalf

def parameters (margin : NonnegativeRatio) : LInfThresholdLowerParameters :=
  { distribution := .balancedTernary
    rows := 256
    coordinateCap :=
      { numerator := 1, denominator := 2, denominator_pos := by decide }
    modulusMargin := margin }

def witness (k : ℕ) : Fin 4 → ℤ := fun _ => k

def baseRowPass (seed : SparseRowSeed 4) : Prop :=
  (∑ i, sparseBit (seed i)).natAbs ≤ 1

instance baseRowPassDecidable : DecidablePred baseRowPass := by
  intro seed
  unfold baseRowPass
  infer_instance

def rowPass (k q : ℕ) (row : Fin 4 → ℤ) : Prop :=
  2 ^ 2 * (centeredMod q (∑ i, row i * witness k i)).natAbs ^ 2 ≤
    (2 * k) ^ 2

instance rowPassDecidable (k q : ℕ) : DecidablePred (rowPass k q) := by
  intro row
  unfold rowPass
  infer_instance

theorem witness_centered {k q : ℕ} (_hq : Odd q) (hnowrap : 8 * k < q) :
    CenteredInput q (witness k) := by
  intro i
  simp only [witness, centeredInterval, Set.mem_Icc]
  have hkhalf : k ≤ q / 2 := by omega
  constructor <;> omega

theorem witness_sqNorm (k : ℕ) : sqNorm (witness k) = (2 * k) ^ 2 := by
  simp [sqNorm, witness]
  ring

private theorem centeredMod_sparseRow_witness
    {k q : ℕ} (hq : Odd q) (hnowrap : 8 * k < q)
    (seed : SparseRowSeed 4) :
    centeredMod q (∑ i, sparseRow seed i * witness k i) =
      ∑ i, sparseRow seed i * witness k i := by
  apply centeredMod_eq_self hq
  have hkhalf : 4 * k ≤ q / 2 := by omega
  have hbit (i : Fin 4) : |sparseBit (seed i)| ≤ (1 : ℤ) := by
    rcases pair : seed i with ⟨left, right⟩
    cases left <;> cases right <;> decide
  have habs : |∑ i, sparseRow seed i * witness k i| ≤ (4 * k : ℕ) := by
    calc
      |∑ i, sparseRow seed i * witness k i| ≤
          ∑ i, |sparseRow seed i * witness k i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 4, (k : ℤ) := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [abs_mul]
        simp only [sparseRow, witness]
        rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ k)]
        simpa [abs_of_nonneg (by positivity : (0 : ℤ) ≤ k)] using
          mul_le_mul_of_nonneg_right (hbit i) (abs_nonneg (k : ℤ))
      _ = (4 * k : ℕ) := by simp
  rw [abs_le] at habs
  simp only [centeredInterval, Set.mem_Icc]
  constructor <;> omega

theorem rowPass_sparseRow_iff
    {k q : ℕ} (hk : 0 < k) (hq : Odd q) (hnowrap : 8 * k < q)
    (seed : SparseRowSeed 4) :
    rowPass k q (sparseRow seed) ↔ baseRowPass seed := by
  rw [rowPass, centeredMod_sparseRow_witness hq hnowrap]
  simp only [baseRowPass, sparseRow, witness]
  rw [← Finset.sum_mul]
  simp only [Int.natAbs_mul, Int.natAbs_natCast]
  have hk2 : 0 < k ^ 2 := sq_pos_of_pos hk
  rw [mul_pow, show 2 ^ 2 * ((∑ i, sparseBit (seed i)).natAbs ^ 2 * k ^ 2) =
      k ^ 2 * (2 ^ 2 * (∑ i, sparseBit (seed i)).natAbs ^ 2) by ring,
    show (2 * k) ^ 2 = k ^ 2 * 2 ^ 2 by ring]
  constructor
  · intro h
    have hcancel := Nat.le_of_mul_le_mul_left h hk2
    nlinarith
  · intro h
    apply Nat.mul_le_mul_left
    have hs : (∑ i, sparseBit (seed i)).natAbs = 0 ∨
        (∑ i, sparseBit (seed i)).natAbs = 1 := by omega
    rcases hs with hs | hs <;> simp [hs]

set_option maxRecDepth 10000 in
theorem baseRowPass_card :
    Fintype.card {seed : SparseRowSeed 4 // baseRowPass seed} = 182 := by
  decide +kernel

theorem rowSeed_card : Fintype.card (SparseRowSeed 4) = 256 := by
  classical
  rw [Fintype.card_fun, Fintype.card_prod]
  norm_num

theorem rowProbability_exact
    {k q : ℕ} (hk : 0 < k) (hq : Odd q) (hnowrap : 8 * k < q) :
    eventProbability (sparseRademacherRow 4) (rowPass k q) =
      (182 : ℝ≥0∞) * (256 : ℝ≥0∞)⁻¹ := by
  have hcard :
      Fintype.card {seed : SparseRowSeed 4 // rowPass k q (sparseRow seed)} = 182 := by
    rw [← baseRowPass_card]
    exact Fintype.card_congr
      (Equiv.subtypeEquiv (Equiv.refl _) (rowPass_sparseRow_iff hk hq hnowrap))
  rw [sparseRademacherRow_eq_map_uniformRowSeed,
    Probability.eventProbability_map_uniform_eq_card, hcard, rowSeed_card]
  norm_num

theorem matrix_event_eq
    (margin : NonnegativeRatio) (k q : ℕ) (J : Fin 256 → Fin 4 → ℤ) :
    LInfThresholdSmallProjection (parameters margin) (2 * k) q (witness k) J ↔
      ∀ j, rowPass k q (J j) := by
  simp [LInfThresholdSmallProjection, parameters, rowPass, rowDot]

theorem probability_exact
    (margin : NonnegativeRatio) {k q : ℕ}
    (hk : 0 < k) (hq : Odd q) (hnowrap : 8 * k < q) :
    eventProbability (sparseRademacherMatrix 256 4)
        (LInfThresholdSmallProjection (parameters margin) (2 * k) q (witness k)) =
      ((182 : ℝ≥0∞) * (256 : ℝ≥0∞)⁻¹) ^ 256 := by
  rw [eventProbability_congr
    (sparseRademacherMatrix 256 4)
    (event' := fun J => ∀ j, rowPass k q (J j))
    (matrix_event_eq margin k q)]
  rw [sparseRademacherMatrix_eventProbability_allRows_eq_pow,
    rowProbability_exact hk hq hnowrap]

set_option maxRecDepth 10000 in
theorem probability_integerComparison :
    (2 : ℕ) ^ 1664 < 91 ^ 256 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem probability_gt_failureTarget128
    (margin : NonnegativeRatio) {k q : ℕ}
    (hk : 0 < k) (hq : Odd q) (hnowrap : 8 * k < q) :
    eventProbability (sparseRademacherMatrix 256 4)
        (LInfThresholdSmallProjection (parameters margin) (2 * k) q (witness k)) >
      failureTarget 128 := by
  rw [probability_exact margin hk hq hnowrap]
  change (2 : ℝ≥0∞)⁻¹ ^ 128 <
    ((182 : ℝ≥0∞) * (256 : ℝ≥0∞)⁻¹) ^ 256
  rw [← ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_mul]
  norm_num only [Nat.cast_ofNat]

def modulusForMargin (margin : NonnegativeRatio) : ℕ :=
  2 * (8 + 2 * margin.numerator) + 1

theorem modulusForMargin_odd (margin : NonnegativeRatio) :
    Odd (modulusForMargin margin) := by
  exact ⟨8 + 2 * margin.numerator, by simp [modulusForMargin]⟩

theorem modulusForMargin_nowrap (margin : NonnegativeRatio) :
    8 * 1 < modulusForMargin margin := by
  simp [modulusForMargin]
  omega

theorem modulusForMargin_satisfies (margin : NonnegativeRatio) :
    InputThresholdWithinModulus margin (modulusForMargin margin) 2 := by
  have hden : 1 ≤ margin.denominator := margin.denominator_pos
  simp only [InputThresholdWithinModulus, modulusForMargin]
  nlinarith

/-- For every exact modulus margin, an explicit odd modulus gives an admissible
four-coordinate witness whose closed cap-one-half event exceeds `2⁻¹²⁸`. -/
theorem admissible_family (margin : NonnegativeRatio) :
    ∃ q : ℕ,
      Odd q ∧
      CenteredInput q (witness 1) ∧
      0 < (2 : ℕ) ∧
      InputThresholdAtMostNorm 2 (witness 1) ∧
      InputThresholdWithinModulus margin q 2 ∧
      eventProbability (sparseRademacherMatrix 256 4)
          (LInfThresholdSmallProjection (parameters margin) 2 q (witness 1)) =
        ((182 : ℝ≥0∞) * (256 : ℝ≥0∞)⁻¹) ^ 256 ∧
      eventProbability (sparseRademacherMatrix 256 4)
          (LInfThresholdSmallProjection (parameters margin) 2 q (witness 1)) >
        failureTarget 128 := by
  refine ⟨modulusForMargin margin, modulusForMargin_odd margin,
    witness_centered (modulusForMargin_odd margin) (modulusForMargin_nowrap margin),
    by norm_num, ?_, modulusForMargin_satisfies margin,
    probability_exact margin (by norm_num) (modulusForMargin_odd margin)
      (modulusForMargin_nowrap margin),
    probability_gt_failureTarget128 margin (by norm_num)
      (modulusForMargin_odd margin) (modulusForMargin_nowrap margin)⟩
  simp [InputThresholdAtMostNorm, witness_sqNorm]

/-- The paper's real-margin quantifier: for every positive real `M`, an odd
modulus can be chosen with `M * b ≤ q` while preserving the same exact finite
counterexample.  The probability event itself does not depend on the margin
encoding. -/
theorem realMargin_admissible_family (M : ℝ) (_hM : 0 < M) :
    ∃ q : ℕ,
      Odd q ∧
      8 * 1 < q ∧
      M * (2 : ℝ) ≤ q ∧
      CenteredInput q (witness 1) ∧
      InputThresholdAtMostNorm 2 (witness 1) ∧
      eventProbability (sparseRademacherMatrix 256 4)
          (LInfThresholdSmallProjection
            (parameters (NonnegativeRatio.ofNat 1)) 2 q (witness 1)) =
        ((182 : ℝ≥0∞) * (256 : ℝ≥0∞)⁻¹) ^ 256 ∧
      eventProbability (sparseRademacherMatrix 256 4)
          (LInfThresholdSmallProjection
            (parameters (NonnegativeRatio.ofNat 1)) 2 q (witness 1)) >
        failureTarget 128 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max 4 M)
  let q := 2 * n + 1
  have hn4 : (4 : ℝ) < (n : ℝ) := lt_of_le_of_lt (le_max_left 4 M) hn
  have hn4Nat : 4 < n := by exact_mod_cast hn4
  have hnM : M < (n : ℝ) := lt_of_le_of_lt (le_max_right 4 M) hn
  have hq : Odd q := ⟨n, by simp [q]⟩
  have hnowrap : 8 * 1 < q := by
    dsimp [q]
    omega
  have hrealMargin : M * (2 : ℝ) ≤ q := by
    dsimp [q]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    linarith
  refine ⟨q, hq, hnowrap, hrealMargin,
    witness_centered hq hnowrap, ?_,
    probability_exact (NonnegativeRatio.ofNat 1) (by norm_num) hq hnowrap,
    probability_gt_failureTarget128 (NonnegativeRatio.ofNat 1)
      (by norm_num) hq hnowrap⟩
  simp [InputThresholdAtMostNorm, witness_sqNorm]

/-- Coordinate cap `1/2` is impossible at 256 rows and 128 bits for every
exact modulus margin. -/
theorem bits128_false (margin : NonnegativeRatio) :
    ¬ LInfThresholdLowerTailAt (parameters margin) (failureTarget 128) := by
  intro hclaimed
  obtain ⟨q, hq, hcentered, hb, hnorm, hmargin, _hexact, hprob⟩ :=
    admissible_family margin
  have hbad := hclaimed q 4 (witness 1) 2 hq hcentered hb hnorm hmargin
  simp only [parameters, ProjectionDistribution.matrixPMF_balancedTernary] at hbad
  exact (not_lt_of_ge hprob.le) hbad

end CertifiedJL.Counterexamples.TernaryLInfRows256CapHalf
