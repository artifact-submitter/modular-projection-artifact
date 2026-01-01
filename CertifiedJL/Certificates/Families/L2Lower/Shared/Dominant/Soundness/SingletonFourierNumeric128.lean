/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.SingletonFourierNumeric128Data
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Soundness.ScalarNumericSoundness
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Soundness.TargetNumeric
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.SingletonFourier128

/-! # Interval checker for the resonant large-singleton Fourier branch -/

namespace CertifiedJL
namespace SparseThresholdDominant
namespace SingletonFourierNumeric128

open DominantNumeric

theorem certifiedCheck_geometry (cell : Cell)
    (hcheck : certifiedCheck cell = true) :
    (0 : ℝ) < cell.lower := by
  have hchecks : safeCheck cell = true ∧
      decide (finalUpperRat cell < 187 / (200 * 2 ^ 128)) = true := by
    simpa only [certifiedCheck, Bool.and_eq_true] using hcheck
  have hsafe := hchecks.1
  have h := of_decide_eq_true (by simpa only [safeCheck] using hsafe)
  have : (0 : ℚ) < cell.lower := lt_of_lt_of_le (by norm_num) h.1
  exact_mod_cast this

private theorem rowInterval_contains (cell : Cell)
    (hcheck : safeCheck cell = true) :
    (rowInterval cell).Contains
      (thresholdDominantSingletonLowFourierCellRow
        (cell.lower : ℝ) (cell.upper : ℝ) z) := by
  have h := of_decide_eq_true (by simpa only [safeCheck] using hcheck)
  rcases h with ⟨hlower, hlowerUpper, hupper, hthreshold, hrowNonneg,
    hlowerPos, hupperPos, hpiPos, hcDenPos, hprefRadNonneg,
    hprefSqrtPos, hcSafe, hfourSafe, hsevenSafe, hnineSafe,
    hfirstSafe, htailDenPos, hgrowthSafe, hrowUpper⟩
  have hpi := contains_piInterval
  have hlowerRat := contains_rat cell.lower
  have hupperRat := contains_rat cell.upper
  have hzRat := contains_rat z
  have hcDen := Interval.contains_mul hzRat (contains_powNat hupperRat 2)
  have hcInv := contains_div hcDenPos (contains_rat 1) hcDen
  have hc : (cUpper cell).Contains
      (Real.pi ^ 2 / ((z : ℝ) * (cell.upper : ℝ) ^ 2)) := by
    simpa [cUpper, div_eq_mul_inv] using
      Interval.contains_mul (contains_powNat hpi 2) hcInv
  have hpiDiv : (piDivUpper cell).Contains
      (Real.pi / (cell.upper : ℝ)) :=
    contains_div hupperPos hpi hupperRat
  have hexpC := contains_expUpper (Interval.contains_neg hc) hcSafe
  have hfourArg := Interval.contains_neg
    (Interval.contains_mul (contains_rat 4) hc)
  have hexpFour := contains_expUpper hfourArg hfourSafe
  have hsevenArg := Interval.contains_neg
    (Interval.contains_mul (contains_rat 7) hc)
  have hexpSeven := contains_expUpper hsevenArg hsevenSafe
  have hnineArg := Interval.contains_neg
    (Interval.contains_mul (contains_rat 9) hc)
  have hexpNine := contains_expUpper hnineArg hnineSafe
  have hfirstArg := Interval.contains_neg
    (Interval.contains_mul (contains_powNat hpiDiv 2) (contains_rat (3 / 2)))
  have hfirst := contains_expUpper hfirstArg hfirstSafe
  have htailDen := Interval.contains_sub (contains_rat 1) hexpSeven
  have htail := contains_div htailDenPos hexpNine htailDen
  have hprefNumerator := Interval.contains_mul hzRat
    (contains_powNat hlowerRat 2)
  have hprefRad := contains_div hpiPos hprefNumerator hpi
  have hprefSqrt := Interval.contains_sqrt hprefRadNonneg hprefRad
  have hpref := contains_div hprefSqrtPos (contains_rat 1) hprefSqrt
  have hmodeOne := Interval.contains_mul hexpC hfirst
  have hinside := Interval.contains_add
    (Interval.contains_add (contains_rat 1)
      (Interval.contains_mul (contains_rat 2)
        (Interval.contains_add hmodeOne hexpFour)))
    (Interval.contains_mul (contains_rat 2) htail)
  have hrow := Interval.contains_mul hpref hinside
  simpa [rowInterval, cUpper, piDivUpper, firstMode, prefactor,
    thresholdDominantSingletonLowFourierCellRow, z] using hrow

private theorem growthInterval_contains (cell : Cell)
    (hcheck : safeCheck cell = true) :
    (growthInterval cell).Contains
      (Real.exp (29 * (z : ℝ) * (cell.thresholdUpper : ℝ))) := by
  have h := of_decide_eq_true (by simpa only [safeCheck] using hcheck)
  rcases h with ⟨hlower, hlowerUpper, hupper, hthreshold, hrowNonneg,
    hlowerPos, hupperPos, hpiPos, hcDenPos, hprefRadNonneg,
    hprefSqrtPos, hcSafe, hfourSafe, hsevenSafe, hnineSafe,
    hfirstSafe, htailDenPos, hgrowthSafe, hrowUpper⟩
  have hbase := contains_expUpper
    (contains_rat (29 * z * cell.thresholdUpper / 256)) hgrowthSafe
  have hpow := contains_powNat hbase 256
  unfold growthInterval
  convert hpow using 1
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

set_option maxRecDepth 10000 in
/-- A successful singleton cell closes its full-event Chernoff ratio. -/
theorem certifiedCheck_sound (cell : Cell)
    (hcheck : certifiedCheck cell = true) :
    Real.exp (29 * (z : ℝ) * (cell.thresholdUpper : ℝ)) *
        thresholdDominantSingletonLowFourierCellRow
            (cell.lower : ℝ) (cell.upper : ℝ) z ^ 256 <
      (187 / 200 : ℝ) * (2 : ℝ)⁻¹ ^ 128 := by
  have hchecks : safeCheck cell = true ∧
      decide (finalUpperRat cell < 187 / (200 * 2 ^ 128)) = true := by
    simpa only [certifiedCheck, Bool.and_eq_true] using hcheck
  have hsafe := hchecks.1
  have h := of_decide_eq_true (by simpa only [safeCheck] using hsafe)
  rcases h with ⟨hlower, hlowerUpper, hupper, hthreshold, hrowNonneg,
    hlowerPos, hupperPos, hpiPos, hcDenPos, hprefRadNonneg,
    hprefSqrtPos, hcSafe, hfourSafe, hsevenSafe, hnineSafe,
    hfirstSafe, htailDenPos, hgrowthSafe, hrowUpper⟩
  have hrowContains := rowInterval_contains cell hsafe
  have hrow : thresholdDominantSingletonLowFourierCellRow
      (cell.lower : ℝ) (cell.upper : ℝ) z ≤ (cell.rowUpper : ℝ) :=
    hrowContains.2.trans (by
      have hreal : ((rowInterval cell).upperRat : ℝ) ≤
          (cell.rowUpper : ℝ) := by exact_mod_cast hrowUpper
      simpa only [Interval.upperRat, Dyadic.cast_toRat] using hreal)
  have hgrowthContains := growthInterval_contains cell hsafe
  have hgrowth : Real.exp (29 * (z : ℝ) * (cell.thresholdUpper : ℝ)) ≤
      ((growthInterval cell).upperRat : ℝ) := by
    simpa only [Interval.upperRat, Dyadic.cast_toRat] using hgrowthContains.2
  have hrowNonnegative : 0 ≤ thresholdDominantSingletonLowFourierCellRow
      (cell.lower : ℝ) (cell.upper : ℝ) z := by
    have hLreal : (0 : ℝ) < cell.lower := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 2) hlower)
    have hUreal : (0 : ℝ) < cell.upper :=
      hLreal.trans_le (by exact_mod_cast hlowerUpper)
    have hcReal : 0 < Real.pi ^ 2 /
        ((z : ℝ) * (cell.upper : ℝ) ^ 2) := by
      norm_num [z]
      positivity
    have hdenReal : 0 < 1 - Real.exp (-7 *
        (Real.pi ^ 2 / ((z : ℝ) * (cell.upper : ℝ) ^ 2))) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
    unfold thresholdDominantSingletonLowFourierCellRow
    dsimp only
    positivity
  have hrowPow := pow_le_pow_left₀ hrowNonnegative hrow 256
  have hnonnegGrowth : (0 : ℝ) ≤ (growthInterval cell).upperRat :=
    (Real.exp_nonneg _).trans hgrowth
  have hmajorant :
      Real.exp (29 * (z : ℝ) * (cell.thresholdUpper : ℝ)) *
          thresholdDominantSingletonLowFourierCellRow
              (cell.lower : ℝ) (cell.upper : ℝ) z ^ 256 ≤
        (finalUpperRat cell : ℝ) := by
    unfold finalUpperRat
    push_cast
    exact mul_le_mul hgrowth hrowPow (by positivity) hnonnegGrowth
  have hfinal : finalUpperRat cell < 187 / (200 * 2 ^ 128) :=
    of_decide_eq_true hchecks.2
  apply hmajorant.trans_lt
  have hfinalReal : (finalUpperRat cell : ℝ) <
      ((187 / (200 * 2 ^ 128) : ℚ) : ℝ) := by exact_mod_cast hfinal
  calc
    (finalUpperRat cell : ℝ) <
        ((187 / (200 * 2 ^ 128) : ℚ) : ℝ) := hfinalReal
    _ = (187 / 200 : ℝ) * (2 : ℝ)⁻¹ ^ 128 := by
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_pow]

/-! ## Target-dependent replay -/

theorem certifiedCheckAt_geometry (rows squaredNormFloor : ℕ) (budget : ℚ)
    (cell : Cell) (hcheck : certifiedCheckAt rows squaredNormFloor budget cell = true) :
    (0 : ℝ) < cell.lower := by
  have hchecks : safeCheck cell = true ∧
      TargetNumeric.certifiedCheckAt rows squaredNormFloor z cell.thresholdUpper
        cell.rowUpper budget = true := by
    simpa only [certifiedCheckAt, Bool.and_eq_true] using hcheck
  have hsafe : safeCheck cell = true := hchecks.1
  have h := of_decide_eq_true (by simpa only [safeCheck] using hsafe)
  have : (0 : ℚ) < cell.lower := lt_of_lt_of_le (by norm_num) h.1
  exact_mod_cast this

set_option maxRecDepth 10000 in
/-- A successful singleton cell closes its target-dependent Chernoff ratio. -/
theorem certifiedCheckAt_sound (rows squaredNormFloor : ℕ) (budget : ℚ)
    (cell : Cell) (hcheck : certifiedCheckAt rows squaredNormFloor budget cell = true) :
    Real.exp (squaredNormFloor * (z : ℝ) * (cell.thresholdUpper : ℝ)) *
        thresholdDominantSingletonLowFourierCellRow
            (cell.lower : ℝ) (cell.upper : ℝ) z ^ rows <
      (budget : ℝ) := by
  have hchecks : safeCheck cell = true ∧
      TargetNumeric.certifiedCheckAt rows squaredNormFloor z cell.thresholdUpper
        cell.rowUpper budget = true := by
    simpa only [certifiedCheckAt, Bool.and_eq_true] using hcheck
  have hsafe := hchecks.1
  have h := of_decide_eq_true (by simpa only [safeCheck] using hsafe)
  rcases h with ⟨hlower, hlowerUpper, hupper, hthreshold, hrowNonneg,
    hlowerPos, hupperPos, hpiPos, hcDenPos, hprefRadNonneg,
    hprefSqrtPos, hcSafe, hfourSafe, hsevenSafe, hnineSafe,
    hfirstSafe, htailDenPos, _hgrowthSafe128, hrowUpper⟩
  have hrowContains := rowInterval_contains cell hsafe
  have hrow : thresholdDominantSingletonLowFourierCellRow
      (cell.lower : ℝ) (cell.upper : ℝ) z ≤ (cell.rowUpper : ℝ) :=
    hrowContains.2.trans (by
      have hreal : ((rowInterval cell).upperRat : ℝ) ≤
          (cell.rowUpper : ℝ) := by exact_mod_cast hrowUpper
      simpa only [Interval.upperRat, Dyadic.cast_toRat] using hreal)
  have hrowNonnegative : 0 ≤ thresholdDominantSingletonLowFourierCellRow
      (cell.lower : ℝ) (cell.upper : ℝ) z := by
    have hLreal : (0 : ℝ) < cell.lower := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 2) hlower)
    have hUreal : (0 : ℝ) < cell.upper :=
      hLreal.trans_le (by exact_mod_cast hlowerUpper)
    have hcReal : 0 < Real.pi ^ 2 /
        ((z : ℝ) * (cell.upper : ℝ) ^ 2) := by
      norm_num [z]
      positivity
    have hdenReal : 0 < 1 - Real.exp (-7 *
        (Real.pi ^ 2 / ((z : ℝ) * (cell.upper : ℝ) ^ 2))) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
    unfold thresholdDominantSingletonLowFourierCellRow
    dsimp only
    positivity
  exact TargetNumeric.certifiedCheckAt_sound rows squaredNormFloor z
    cell.thresholdUpper cell.rowUpper budget
    (thresholdDominantSingletonLowFourierCellRow
      (cell.lower : ℝ) (cell.upper : ℝ) z)
    hrowNonnegative hrow hchecks.2

end SingletonFourierNumeric128
end SparseThresholdDominant
end CertifiedJL
