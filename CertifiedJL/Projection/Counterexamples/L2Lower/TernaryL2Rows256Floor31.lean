/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.Counterexamples.L2Lower.LNPLowerTail
import Mathlib.Tactic

/-!
# The 256-row threshold-floor-31 obstruction

For every positive natural `b` and odd modulus `q` with `3 * b ≤ q`, the
singleton input `(b)` has modular projected squared norm `b² K`, where `K` is
the number of active balanced-ternary entries.  Thus the strict floor-31 event
is exactly the binomial tail `K ≤ 30`, whose probability is greater than
`2⁻¹²⁸`.
-/

open scoped BigOperators ENNReal

namespace CertifiedJL.Counterexamples.TernaryL2Rows256Floor31

open Probability

def parameters : L2ThresholdLowerParameters :=
  { distribution := .balancedTernary
    rows := 256
    squaredNormFloor := NonnegativeRatio.ofNat 31
    modulusMargin := NonnegativeRatio.ofNat 3 }

/-- Singleton-family parameters at arbitrary row count and integral strict
cutoff.  The historical 256-row floor-31 parameters are a specialization. -/
def familyParameters (rows squaredNormFloor : ℕ) : L2ThresholdLowerParameters :=
  { distribution := .balancedTernary
    rows := rows
    squaredNormFloor := NonnegativeRatio.ofNat squaredNormFloor
    modulusMargin := NonnegativeRatio.ofNat 3 }

/-- Exact binomial lower-tail numerator for the singleton family. -/
def binomialTailNumerator (rows squaredNormFloor : ℕ) : ℕ :=
  ∑ k ∈ Finset.range squaredNormFloor, rows.choose k

def witness (b : ℕ) : Fin 1 → ℤ := fun _ => b

theorem witness_centered {b q : ℕ} (_hq : Odd q) (hmargin : 3 * b ≤ q) :
    CenteredInput q (witness b) := by
  intro i
  simp only [witness]
  simp only [centeredInterval, Set.mem_Icc]
  have hbhalf : b ≤ q / 2 := by omega
  constructor <;> omega

theorem witness_sqNorm (b : ℕ) : sqNorm (witness b) = b ^ 2 := by
  simp [sqNorm, witness]

private theorem centered_sparseBit_mul
    {b q : ℕ} (hq : Odd q) (hmargin : 3 * b ≤ q) (pair : Bool × Bool) :
    centeredMod q (sparseBit pair * (b : ℤ)) = sparseBit pair * (b : ℤ) := by
  apply centeredMod_eq_self hq
  rcases pair with ⟨left, right⟩
  cases left <;> cases right <;>
    simp only [sparseBit, Int.reduceNeg, neg_mul, one_mul, zero_mul,
      centeredInterval, Set.mem_Icc]
  all_goals
    have hbhalf : b ≤ q / 2 := by omega
    omega

private theorem centered_sparseBit_mul_sq_eq_dominantView
    {rows b q : ℕ} (hq : Odd q) (hmargin : 3 * b ≤ q)
    (seed : SparseSeed rows 1) (row : Fin rows) :
    (centeredMod q (sparseBit (seed row 0) * (b : ℤ))).natAbs ^ 2 =
      b ^ 2 * if (dominantSeedView (0 : Fin 1) seed).1 row then 1 else 0 := by
  rw [centered_sparseBit_mul hq hmargin]
  change (sparseBit (seed row 0) * (b : ℤ)).natAbs ^ 2 =
    b ^ 2 * if sparsePairActivity (seed row 0) then 1 else 0
  rcases pair : seed row 0 with ⟨left, right⟩
  cases left <;> cases right <;>
    simp [sparseBit, sparsePairActivity]

theorem modularProjectionSqNorm_sparseMatrix
    {rows b q : ℕ} (hq : Odd q) (hmargin : 3 * b ≤ q)
    (seed : SparseSeed rows 1) :
    modularProjectionSqNorm q (sparseMatrix seed) (witness b) =
      b ^ 2 * dominantActivityCount
        (matrixDominantActivity (0 : Fin 1) (sparseMatrix seed)) := by
  classical
  rw [matrixDominantActivity_sparseMatrix]
  simp only [modularProjectionSqNorm, rowDot, witness, Fin.sum_univ_one,
    sparseMatrix, sparseRow, dominantActivityCount, boolSupport]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro row _
  exact centered_sparseBit_mul_sq_eq_dominantView hq hmargin seed row

theorem failure_iff_activityCount_lt
    {b q : ℕ} (hb : 0 < b) (hq : Odd q) (hmargin : 3 * b ≤ q)
    (seed : SparseSeed 256 1) :
    L2ThresholdLowerFailure (NonnegativeRatio.ofNat 31) b q (witness b)
        (sparseMatrix seed) ↔
      (dominantActivityCount
        (matrixDominantActivity (0 : Fin 1) (sparseMatrix seed)) : ℕ) < 31 := by
  rw [L2ThresholdLowerFailure, modularProjectionSqNorm_sparseMatrix hq hmargin]
  simp only [NonnegativeRatio.ofNat, one_mul]
  rw [mul_comm 31 (b ^ 2), Nat.mul_lt_mul_left (sq_pos_of_pos hb)]

/-- Arbitrary-row, arbitrary-integral-cutoff form of the singleton event
equivalence.  Strictness gives `activityCount < squaredNormFloor`, including
the cutoff-zero case. -/
theorem failure_iff_activityCount_lt_family
    {rows squaredNormFloor b q : ℕ} (hb : 0 < b) (hq : Odd q)
    (hmargin : 3 * b ≤ q) (seed : SparseSeed rows 1) :
    L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
        b q (witness b) (sparseMatrix seed) ↔
      (dominantActivityCount
        (matrixDominantActivity (0 : Fin 1) (sparseMatrix seed)) : ℕ) <
          squaredNormFloor := by
  rw [L2ThresholdLowerFailure, modularProjectionSqNorm_sparseMatrix hq hmargin]
  simp only [NonnegativeRatio.ofNat, one_mul]
  rw [mul_comm squaredNormFloor (b ^ 2),
    Nat.mul_lt_mul_left (sq_pos_of_pos hb)]

theorem probability_exact
    {b q : ℕ} (hb : 0 < b) (hq : Odd q) (hmargin : 3 * b ≤ q) :
    eventProbability (sparseRademacherMatrix 256 1)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 31) b q (witness b)) =
      ((∑ k ∈ Finset.range 31, (256 : ℕ).choose k : ℕ) : ℝ≥0∞) *
        ((2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [sparseRademacherMatrix_eq_map_uniformSeed]
  rw [eventProbability_map_congr
    (PMF.uniformOfFintype (SparseSeed 256 1))
    sparseMatrix sparseMatrix
    (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 31) b q (witness b))
    (fun J =>
      (dominantActivityCount
        (matrixDominantActivity (0 : Fin 1) J) : ℕ) < 31)
    (failure_iff_activityCount_lt hb hq hmargin)]
  rw [← sparseRademacherMatrix_eq_map_uniformSeed]
  exact sparse_dominantActivityCount_lt_probability_eq (0 : Fin 1) 31

/-- Exact singleton failure probability for arbitrary rows and integral strict
cutoff. -/
theorem probability_exact_family
    {rows squaredNormFloor b q : ℕ} (hb : 0 < b) (hq : Odd q)
    (hmargin : 3 * b ≤ q) :
    eventProbability (sparseRademacherMatrix rows 1)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
          b q (witness b)) =
      (binomialTailNumerator rows squaredNormFloor : ℝ≥0∞) *
        ((2 ^ rows : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [sparseRademacherMatrix_eq_map_uniformSeed]
  rw [eventProbability_map_congr
    (PMF.uniformOfFintype (SparseSeed rows 1))
    sparseMatrix sparseMatrix
    (L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
      b q (witness b))
    (fun J =>
      (dominantActivityCount
        (matrixDominantActivity (0 : Fin 1) J) : ℕ) < squaredNormFloor)
    (failure_iff_activityCount_lt_family hb hq hmargin)]
  rw [← sparseRademacherMatrix_eq_map_uniformSeed]
  simpa [binomialTailNumerator] using
    sparse_dominantActivityCount_lt_probability_eq_at
      rows (0 : Fin 1) squaredNormFloor

/-- Cross-multiplied exact criterion turning a binomial numerator check into a
strict security-budget violation. -/
theorem probability_gt_failureTarget_of_scaled
    {rows squaredNormFloor securityBits b q : ℕ}
    (hscaled : 2 ^ rows <
      2 ^ securityBits * binomialTailNumerator rows squaredNormFloor)
    (hb : 0 < b) (hq : Odd q) (hmargin : 3 * b ≤ q) :
    eventProbability (sparseRademacherMatrix rows 1)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
          b q (witness b)) > failureTarget securityBits := by
  rw [probability_exact_family hb hq hmargin]
  change
    (2 : ℝ≥0∞)⁻¹ ^ securityBits <
      (binomialTailNumerator rows squaredNormFloor : ℝ≥0∞) *
        ((2 ^ rows : ℕ) : ℝ≥0∞)⁻¹
  rw [← ENNReal.toReal_lt_toReal
    (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by norm_num)))
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.inv_ne_top.mpr (by positivity)))]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  rw [inv_pow]
  norm_cast
  rw [← one_div, ← div_eq_mul_inv]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have hscaledReal : (2 : ℝ) ^ rows <
      2 ^ securityBits * binomialTailNumerator rows squaredNormFloor := by
    exact_mod_cast hscaled
  simpa [mul_comm] using hscaledReal

/-- Generic singleton obstruction from one exact binomial comparison. -/
theorem lowerTail_false_of_scaled
    (rows squaredNormFloor securityBits : ℕ)
    (hscaled : 2 ^ rows <
      2 ^ securityBits * binomialTailNumerator rows squaredNormFloor) :
    ¬ L2ThresholdLowerTailAt
      (familyParameters rows squaredNormFloor) (failureTarget securityBits) := by
  intro hclaimed
  have hbad := hclaimed 3 1 (witness 1) 1 (by norm_num)
    (witness_centered (by norm_num) (by norm_num)) (by norm_num)
    (by simp [InputThresholdAtMostNorm, witness_sqNorm])
    (by norm_num [InputThresholdWithinModulus, familyParameters,
      NonnegativeRatio.ofNat])
  simp only [familyParameters,
    ProjectionDistribution.matrixPMF_balancedTernary] at hbad
  exact (not_lt_of_ge (probability_gt_failureTarget_of_scaled hscaled
    (b := 1) (q := 3) (by norm_num) (by norm_num) (by norm_num)).le) hbad

/-! ## Computed singleton consequences

These exact kernel checks instantiate the generic family at the four new norm
cutoffs and four same-cutoff security ceilings from the systematic audit.
-/

set_option maxRecDepth 10000 in
theorem rows192_floor14_bits128_scaled :
    2 ^ 192 < 2 ^ 128 * binomialTailNumerator 192 14 := by
  simp only [binomialTailNumerator]
  simp_rw [Nat.choose_eq_fast_choose]
  decide +kernel

set_option maxRecDepth 10000 in
theorem rows256_floor13_bits192_scaled :
    2 ^ 256 < 2 ^ 192 * binomialTailNumerator 256 13 := by
  simp only [binomialTailNumerator]
  simp_rw [Nat.choose_eq_fast_choose]
  decide +kernel

set_option maxRecDepth 10000 in
theorem rows384_floor45_bits192_scaled :
    2 ^ 384 < 2 ^ 192 * binomialTailNumerator 384 45 := by
  simp only [binomialTailNumerator]
  simp_rw [Nat.choose_eq_fast_choose]
  decide +kernel

set_option maxRecDepth 10000 in
theorem rows512_floor59_bits256_scaled :
    2 ^ 512 < 2 ^ 256 * binomialTailNumerator 512 59 := by
  simp only [binomialTailNumerator]
  simp_rw [Nat.choose_eq_fast_choose]
  decide +kernel

set_option maxRecDepth 10000 in
theorem rows256_floor29_bits132_scaled :
    2 ^ 256 < 2 ^ 132 * binomialTailNumerator 256 29 := by
  simp only [binomialTailNumerator]
  simp_rw [Nat.choose_eq_fast_choose]
  decide +kernel

set_option maxRecDepth 10000 in
theorem rows256_floor9_bits208_scaled :
    2 ^ 256 < 2 ^ 208 * binomialTailNumerator 256 9 := by
  simp only [binomialTailNumerator]
  simp_rw [Nat.choose_eq_fast_choose]
  decide +kernel

set_option maxRecDepth 10000 in
theorem rows384_floor43_bits197_scaled :
    2 ^ 384 < 2 ^ 197 * binomialTailNumerator 384 43 := by
  simp only [binomialTailNumerator]
  simp_rw [Nat.choose_eq_fast_choose]
  decide +kernel

set_option maxRecDepth 10000 in
theorem rows512_floor57_bits261_scaled :
    2 ^ 512 < 2 ^ 261 * binomialTailNumerator 512 57 := by
  simp only [binomialTailNumerator]
  simp_rw [Nat.choose_eq_fast_choose]
  decide +kernel

theorem rows192_floor14_bits128_false :
    ¬ L2ThresholdLowerTailAt (familyParameters 192 14) (failureTarget 128) :=
  lowerTail_false_of_scaled 192 14 128 rows192_floor14_bits128_scaled

theorem rows256_floor13_bits192_false :
    ¬ L2ThresholdLowerTailAt (familyParameters 256 13) (failureTarget 192) :=
  lowerTail_false_of_scaled 256 13 192 rows256_floor13_bits192_scaled

theorem rows384_floor45_bits192_false :
    ¬ L2ThresholdLowerTailAt (familyParameters 384 45) (failureTarget 192) :=
  lowerTail_false_of_scaled 384 45 192 rows384_floor45_bits192_scaled

theorem rows512_floor59_bits256_false :
    ¬ L2ThresholdLowerTailAt (familyParameters 512 59) (failureTarget 256) :=
  lowerTail_false_of_scaled 512 59 256 rows512_floor59_bits256_scaled

theorem rows256_floor29_bits132_false :
    ¬ L2ThresholdLowerTailAt (familyParameters 256 29) (failureTarget 132) :=
  lowerTail_false_of_scaled 256 29 132 rows256_floor29_bits132_scaled

theorem rows256_floor9_bits208_false :
    ¬ L2ThresholdLowerTailAt (familyParameters 256 9) (failureTarget 208) :=
  lowerTail_false_of_scaled 256 9 208 rows256_floor9_bits208_scaled

theorem rows384_floor43_bits197_false :
    ¬ L2ThresholdLowerTailAt (familyParameters 384 43) (failureTarget 197) :=
  lowerTail_false_of_scaled 384 43 197 rows384_floor43_bits197_scaled

theorem rows512_floor57_bits261_false :
    ¬ L2ThresholdLowerTailAt (familyParameters 512 57) (failureTarget 261) :=
  lowerTail_false_of_scaled 512 57 261 rows512_floor57_bits261_scaled

set_option maxRecDepth 10000 in
theorem binomialTail31_scaled_gt :
    (2 : ℕ) ^ 128 < ∑ k ∈ Finset.range 31, (256 : ℕ).choose k := by
  simp_rw [Nat.choose_eq_fast_choose]
  decide +kernel

set_option maxRecDepth 100000 in
theorem probability_gt_failureTarget128
    {b q : ℕ} (hb : 0 < b) (hq : Odd q) (hmargin : 3 * b ≤ q) :
    eventProbability (sparseRademacherMatrix 256 1)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 31) b q (witness b)) >
      failureTarget 128 := by
  rw [probability_exact hb hq hmargin]
  change
    (2 : ℝ≥0∞)⁻¹ ^ 128 <
      ((∑ k ∈ Finset.range 31, (256 : ℕ).choose k : ℕ) : ℝ≥0∞) *
        ((2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹
  rw [← ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  field_simp
  have htailReal : (2 : ℝ) ^ 128 <
      ∑ k ∈ Finset.range 31, (256 : ℕ).choose k := by
    exact_mod_cast binomialTail31_scaled_gt
  calc
    (↑((2 : ℕ) ^ 256) : ℝ) = (2 : ℝ) ^ 128 * 2 ^ 128 := by
      norm_num [← pow_add]
    _ < 2 ^ 128 *
        (↑(∑ k ∈ Finset.range 31, (256 : ℕ).choose k) : ℝ) :=
      mul_lt_mul_of_pos_left htailReal (by positivity)

/-- The exact singleton construction works for every positive scale and every
odd modulus satisfying the claimed margin. -/
theorem admissible_family
    {b q : ℕ} (hb : 0 < b) (hq : Odd q) (hmargin : 3 * b ≤ q) :
    CenteredInput q (witness b) ∧
      InputThresholdAtMostNorm b (witness b) ∧
      InputThresholdWithinModulus (NonnegativeRatio.ofNat 3) q b ∧
      eventProbability (sparseRademacherMatrix 256 1)
          (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 31) b q (witness b)) =
        ((∑ k ∈ Finset.range 31, (256 : ℕ).choose k : ℕ) : ℝ≥0∞) *
          ((2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ ∧
      eventProbability (sparseRademacherMatrix 256 1)
          (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 31) b q (witness b)) >
        failureTarget 128 := by
  refine ⟨witness_centered hq hmargin, ?_, ?_,
    probability_exact hb hq hmargin, probability_gt_failureTarget128 hb hq hmargin⟩
  · simp [InputThresholdAtMostNorm, witness_sqNorm]
  · simpa [InputThresholdWithinModulus, NonnegativeRatio.ofNat] using hmargin

/-- Squared threshold `31` is impossible at 256 rows and 128 bits. -/
theorem bits128_false :
    ¬ L2ThresholdLowerTailAt parameters (failureTarget 128) := by
  intro hclaimed
  have hbad := hclaimed 3 1 (witness 1) 1 (by norm_num)
    (witness_centered (by norm_num) (by norm_num)) (by norm_num)
    (by simp [InputThresholdAtMostNorm, witness_sqNorm])
    (by norm_num [InputThresholdWithinModulus, parameters, NonnegativeRatio.ofNat])
  simp only [parameters, ProjectionDistribution.matrixPMF_balancedTernary] at hbad
  exact (not_lt_of_ge (probability_gt_failureTarget128
    (b := 1) (q := 3) (by norm_num) (by norm_num) (by norm_num)).le) hbad

end CertifiedJL.Counterexamples.TernaryL2Rows256Floor31
