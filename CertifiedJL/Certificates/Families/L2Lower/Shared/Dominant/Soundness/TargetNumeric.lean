/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Soundness.ScalarNumericSoundness
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.TargetNumericData

/-!
# Shared target-dependent dominant Fourier endgame

This module owns the row-count and squared-norm-floor dependent arithmetic shared by
the direct, capped-Fourier, and singleton-Fourier covers. Their distinct
modules remain responsible for bounding their respective semantic one-row
kernels.
-/

namespace CertifiedJL.SparseThresholdDominant.TargetNumeric

open DominantNumeric

private theorem growthIntervalAt_contains (rows squaredNormFloor : ℕ)
    (z thresholdUpper : ℚ) (hrows : 0 < rows)
    (hsafe : (rat (squaredNormFloor * z * thresholdUpper / rows)).upperRat ≤ 1) :
    (growthIntervalAt rows squaredNormFloor z thresholdUpper).Contains
      (Real.exp (squaredNormFloor * (z : ℝ) * (thresholdUpper : ℝ))) := by
  have hbase := contains_expUpper
    (contains_rat (squaredNormFloor * z * thresholdUpper / rows)) hsafe
  have hpow := contains_powNat hbase rows
  unfold growthIntervalAt
  convert hpow using 1
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  have hrowsReal : (rows : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hrows)
  field_simp [hrowsReal]

theorem growth_le_upperRat (rows squaredNormFloor : ℕ)
    (z thresholdUpper : ℚ) (hrows : 0 < rows)
    (hsafe : (rat (squaredNormFloor * z * thresholdUpper / rows)).upperRat ≤ 1) :
    Real.exp (squaredNormFloor * (z : ℝ) * (thresholdUpper : ℝ)) ≤
      ((growthIntervalAt rows squaredNormFloor z thresholdUpper).upperRat : ℝ) := by
  have hcontains := growthIntervalAt_contains rows squaredNormFloor
    z thresholdUpper hrows hsafe
  simpa only [Interval.upperRat, Dyadic.cast_toRat] using hcontains.2

set_option maxRecDepth 10000 in
/-- Shared soundness theorem for a certified exponential-times-row-power
target. The caller supplies only semantic nonnegativity and its row cap. -/
theorem certifiedCheckAt_sound (rows squaredNormFloor : ℕ)
    (z thresholdUpper rowUpper budget : ℚ) (semanticRow : ℝ)
    (hsemanticNonneg : 0 ≤ semanticRow)
    (hsemanticUpper : semanticRow ≤ rowUpper)
    (hcheck : certifiedCheckAt rows squaredNormFloor z thresholdUpper rowUpper
      budget = true) :
    Real.exp (squaredNormFloor * (z : ℝ) * (thresholdUpper : ℝ)) *
        semanticRow ^ rows <
      (budget : ℝ) := by
  have h := of_decide_eq_true (by
    simpa only [certifiedCheckAt] using hcheck)
  rcases h with ⟨hrows, hgrowthSafe, hfinal⟩
  have hgrowth := growth_le_upperRat rows squaredNormFloor z thresholdUpper
    hrows hgrowthSafe
  have hrowPow := pow_le_pow_left₀ hsemanticNonneg hsemanticUpper rows
  have hnonnegGrowth : (0 : ℝ) ≤
      (growthIntervalAt rows squaredNormFloor z thresholdUpper).upperRat :=
    (Real.exp_nonneg _).trans hgrowth
  have hmajorant :
      Real.exp (squaredNormFloor * (z : ℝ) * (thresholdUpper : ℝ)) *
          (semanticRow : ℝ) ^ rows ≤
        (finalUpperRatAt rows squaredNormFloor z thresholdUpper rowUpper : ℝ) := by
    unfold finalUpperRatAt
    push_cast
    exact mul_le_mul hgrowth hrowPow
      (pow_nonneg hsemanticNonneg _) hnonnegGrowth
  apply hmajorant.trans_lt
  exact_mod_cast hfinal

private theorem growthIntervalAtRatio_contains (rows : ℕ)
    (squaredNormFloor z thresholdUpper : ℚ) (hrows : 0 < rows)
    (hsafe :
      (rat (squaredNormFloor * z * thresholdUpper / rows)).upperRat ≤ 1) :
    (growthIntervalAtRatio rows squaredNormFloor z thresholdUpper).Contains
      (Real.exp ((squaredNormFloor : ℝ) * (z : ℝ) *
        (thresholdUpper : ℝ))) := by
  have hbase := contains_expUpper
    (contains_rat (squaredNormFloor * z * thresholdUpper / rows)) hsafe
  have hpow := contains_powNat hbase rows
  unfold growthIntervalAtRatio
  convert hpow using 1
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  have hrowsReal : (rows : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hrows)
  field_simp [hrowsReal]

theorem growthRatio_le_upperRat (rows : ℕ)
    (squaredNormFloor z thresholdUpper : ℚ) (hrows : 0 < rows)
    (hsafe :
      (rat (squaredNormFloor * z * thresholdUpper / rows)).upperRat ≤ 1) :
    Real.exp ((squaredNormFloor : ℝ) * (z : ℝ) *
        (thresholdUpper : ℝ)) ≤
      ((growthIntervalAtRatio rows squaredNormFloor z thresholdUpper).upperRat : ℝ) := by
  have hcontains := growthIntervalAtRatio_contains rows squaredNormFloor
    z thresholdUpper hrows hsafe
  simpa only [Interval.upperRat, Dyadic.cast_toRat] using hcontains.2

set_option maxRecDepth 10000 in
/-- Soundness of the rational-floor executable target check. -/
theorem certifiedCheckAtRatio_sound (rows : ℕ)
    (squaredNormFloor z thresholdUpper rowUpper budget : ℚ) (semanticRow : ℝ)
    (hsemanticNonneg : 0 ≤ semanticRow)
    (hsemanticUpper : semanticRow ≤ rowUpper)
    (hcheck : certifiedCheckAtRatio rows squaredNormFloor z thresholdUpper rowUpper
      budget = true) :
    Real.exp ((squaredNormFloor : ℝ) * (z : ℝ) *
        (thresholdUpper : ℝ)) * semanticRow ^ rows <
      (budget : ℝ) := by
  have h := of_decide_eq_true (by
    simpa only [certifiedCheckAtRatio] using hcheck)
  rcases h with ⟨hrows, _hfloor, hgrowthSafe, hfinal⟩
  have hgrowth := growthRatio_le_upperRat rows squaredNormFloor z thresholdUpper
    hrows hgrowthSafe
  have hrowPow := pow_le_pow_left₀ hsemanticNonneg hsemanticUpper rows
  have hnonnegGrowth : (0 : ℝ) ≤
      (growthIntervalAtRatio rows squaredNormFloor z thresholdUpper).upperRat :=
    (Real.exp_nonneg _).trans hgrowth
  have hmajorant :
      Real.exp ((squaredNormFloor : ℝ) * (z : ℝ) *
          (thresholdUpper : ℝ)) * semanticRow ^ rows ≤
        (finalUpperRatAtRatio rows squaredNormFloor z thresholdUpper rowUpper : ℝ) := by
    unfold finalUpperRatAtRatio
    push_cast
    exact mul_le_mul hgrowth hrowPow
      (pow_nonneg hsemanticNonneg _) hnonnegGrowth
  apply hmajorant.trans_lt
  exact_mod_cast hfinal

end CertifiedJL.SparseThresholdDominant.TargetNumeric
