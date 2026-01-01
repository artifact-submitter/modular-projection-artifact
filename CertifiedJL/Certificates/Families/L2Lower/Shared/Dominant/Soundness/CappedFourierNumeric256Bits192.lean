/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Transcendental.Trigonometric.Trig
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.CappedFourierNumeric256Bits192Data
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Soundness.ScalarNumericSoundness
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Soundness.TargetNumeric
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.RetainedFourier128

/-!
# Target-specific retained Fourier cells for the 256-row, 192-bit threshold endpoint

The analytic layer separates every modulus-dependent factor at the two cell
endpoints.  This checker evaluates that scalar expression with dyadic interval
arithmetic and a first-quadrant cosine Taylor enclosure.
-/

namespace CertifiedJL
namespace SparseThresholdDominant
namespace CappedFourierNumeric256Bits192

open DominantNumeric

/-- Every certified cell lies in the analytic modulus domain. -/
theorem certifiedCheck_geometry (cell : Cell)
    (hcheck : certifiedCheck cell = true) :
    (2 : ℝ) ≤ cell.lower ∧ (cell.upper : ℝ) ≤ 3 := by
  have hchecks : safeCheck cell = true ∧
      decide (finalUpperRat cell < 99 / (100 * 2 ^ 192)) = true := by
    simpa only [certifiedCheck, Bool.and_eq_true] using hcheck
  have hsafe := hchecks.1
  have h := of_decide_eq_true (by simpa only [safeCheck] using hsafe)
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2.2.1⟩

private theorem contains_reflectedPhase (cell : Cell)
    (hlower : 2 ≤ cell.lower) (hupper : cell.lower ≤ 3) :
    (reflectedPhase cell).Contains
      (Real.cos (2 * Real.pi / (cell.lower : ℝ)) ^ 2) := by
  have hL : (0 : ℝ) < cell.lower := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hlower)
  have hs0 : 0 ≤ 1 - 2 / cell.lower := by
    rw [sub_nonneg, div_le_one (by positivity)]
    exact hlower
  have hshalf : 1 - 2 / cell.lower ≤ 1 / 2 := by
    rw [sub_le_iff_le_add]
    have hhalf : (1 / 2 : ℚ) ≤ 2 / cell.lower := by
      apply (le_div_iff₀ (by exact_mod_cast hL)).2
      nlinarith
    linarith
  have hcos := TrigInterval.cosPiHalf_contains
    (p := precision) hs0 hshalf 10
  have hsq := contains_powNat hcos 2
  have hreflect :
      Real.cos (Real.pi * ((1 - 2 / cell.lower : ℚ) : ℝ)) ^ 2 =
        Real.cos (2 * Real.pi / (cell.lower : ℝ)) ^ 2 := by
    rw [show Real.pi * ((1 - 2 / cell.lower : ℚ) : ℝ) =
        Real.pi - 2 * Real.pi / (cell.lower : ℝ) by
      push_cast
      ring,
      Real.cos_pi_sub, neg_sq]
  simpa only [reflectedPhase, hreflect] using hsq

private theorem rowInterval_contains (cell : Cell)
    (hcheck : safeCheck cell = true) :
    (rowInterval cell).Contains
      (thresholdDominantCappedFourierCellRow
        (cell.lower : ℝ) (cell.upper : ℝ) z) := by
  have h := of_decide_eq_true (by simpa only [safeCheck] using hcheck)
  rcases h with ⟨hlower, hlowerUpper, hupper, hthreshold, hrowNonneg,
    hlowerPos, hupperPos, hpiPos, hcDenPos, hprefRadNonneg,
    hprefSqrtPos, hcSafe, hfourSafe, hsevenSafe, hnineSafe,
    hfirstSafe, hsecondSafe, htailDenPos, hgrowthSafe, hrowUpper⟩
  have hpi := contains_piInterval
  have hlowerRat := contains_rat cell.lower
  have hupperRat := contains_rat cell.upper
  have hzRat := contains_rat z
  have hcDen := Interval.contains_mul hzRat
    (contains_powNat hupperRat 2)
  have hcInv := contains_div hcDenPos (contains_rat 1) hcDen
  have hc : (cUpper cell).Contains
      (Real.pi ^ 2 / ((z : ℝ) * (cell.upper : ℝ) ^ 2)) := by
    simpa [cUpper, div_eq_mul_inv] using
      Interval.contains_mul (contains_powNat hpi 2) hcInv
  have hpiDiv : (piDivUpper cell).Contains
      (Real.pi / (cell.upper : ℝ)) := by
    exact contains_div hupperPos hpi hupperRat
  have htwoPiDiv : (twoPiDivUpper cell).Contains
      (2 * Real.pi / (cell.upper : ℝ)) := by
    convert Interval.contains_mul (contains_rat 2) hpiDiv using 1
    · rfl
    · ring
  have hphase := contains_reflectedPhase cell hlower (hlowerUpper.trans hupper)
  have hcNeg := Interval.contains_neg hc
  have hexpC := contains_expUpper hcNeg hcSafe
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
  have hsecondArg := Interval.contains_neg
    (Interval.contains_mul
      (Interval.contains_mul (contains_rat (7 / 200))
        (contains_powNat htwoPiDiv 2)) (contains_rat (1 / 2)))
  have hsecond := contains_expUpper hsecondArg hsecondSafe
  have htailDen := Interval.contains_sub (contains_rat 1) hexpSeven
  have htail := contains_div htailDenPos hexpNine htailDen
  have hprefNumerator := Interval.contains_mul hzRat
    (contains_powNat hlowerRat 2)
  have hprefRad := contains_div hpiPos hprefNumerator hpi
  have hprefSqrt := Interval.contains_sqrt hprefRadNonneg hprefRad
  have hpref := contains_div hprefSqrtPos (contains_rat 1) hprefSqrt
  have hmodeOne := Interval.contains_mul hexpC hfirst
  have hmodeTwo := Interval.contains_mul hexpFour
    (Interval.contains_mul hphase hsecond)
  have hinside := Interval.contains_add
    (Interval.contains_add (contains_rat 1)
      (Interval.contains_mul (contains_rat 2)
        (Interval.contains_add hmodeOne hmodeTwo)))
    (Interval.contains_mul (contains_rat 2) htail)
  have hrow := Interval.contains_mul hpref hinside
  simpa [rowInterval, cUpper, piDivUpper, twoPiDivUpper, firstMode,
    secondResidualMode, prefactor, thresholdDominantCappedFourierCellRow,
    z] using hrow

/-- The target-selected capped-Fourier row interval supplies a reusable
nonnegative semantic row cap.  Only the target-dependent exponential and
row power need to be replayed for a new row-count specialization. -/
theorem semanticRow_bounds_of_safeCheck (cell : Cell)
    (hcheck : safeCheck cell = true) :
    0 ≤ thresholdDominantCappedFourierCellRow
        (cell.lower : ℝ) (cell.upper : ℝ) z ∧
      thresholdDominantCappedFourierCellRow
        (cell.lower : ℝ) (cell.upper : ℝ) z ≤ (cell.rowUpper : ℝ) := by
  have h := of_decide_eq_true (by simpa only [safeCheck] using hcheck)
  rcases h with ⟨hlower, hlowerUpper, hdomainUpper, hthreshold,
    hrowNonneg, hlowerPos, hupperPos, hpiPos, hcDenPos,
    hprefRadNonneg, hprefSqrtPos, hcSafe, hfourSafe, hsevenSafe,
    hnineSafe, hfirstSafe, hsecondSafe, htailDenPos, hgrowthSafe,
    hrowUpper⟩
  have hrowContains := rowInterval_contains cell hcheck
  have hupper : thresholdDominantCappedFourierCellRow
      (cell.lower : ℝ) (cell.upper : ℝ) z ≤ (cell.rowUpper : ℝ) :=
    hrowContains.2.trans (by
      have hreal : ((rowInterval cell).upperRat : ℝ) ≤
          (cell.rowUpper : ℝ) := by exact_mod_cast hrowUpper
      simpa only [Interval.upperRat, Dyadic.cast_toRat] using hreal)
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
  refine ⟨?_, hupper⟩
  unfold thresholdDominantCappedFourierCellRow
  dsimp only
  positivity

private theorem growthInterval_contains (cell : Cell)
    (hcheck : safeCheck cell = true) :
    (growthInterval cell).Contains
      (Real.exp (9 * (z : ℝ) * (cell.thresholdUpper : ℝ))) := by
  have h := of_decide_eq_true (by simpa only [safeCheck] using hcheck)
  rcases h with ⟨hlower, hlowerUpper, hupper, hthreshold, hrowNonneg,
    hlowerPos, hupperPos, hpiPos, hcDenPos, hprefRadNonneg,
    hprefSqrtPos, hcSafe, hfourSafe, hsevenSafe, hnineSafe,
    hfirstSafe, hsecondSafe, htailDenPos, hgrowthSafe, hrowUpper⟩
  have hbase := contains_expUpper
    (contains_rat (9 * z * cell.thresholdUpper / 256)) hgrowthSafe
  have hpow := contains_powNat hbase 256
  unfold growthInterval
  convert hpow using 1
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

set_option maxRecDepth 10000 in
/-- A successful reflected cell closes its full-event Chernoff ratio. -/
theorem certifiedCheck_sound (cell : Cell)
    (hcheck : certifiedCheck cell = true) :
    Real.exp (9 * (z : ℝ) * (cell.thresholdUpper : ℝ)) *
        thresholdDominantCappedFourierCellRow
            (cell.lower : ℝ) (cell.upper : ℝ) z ^ 256 <
      ((99 / (100 * 2 ^ 192) : ℚ) : ℝ) := by
  have hchecks : safeCheck cell = true ∧
      decide (finalUpperRat cell < 99 / (100 * 2 ^ 192)) = true := by
    simpa only [certifiedCheck, Bool.and_eq_true] using hcheck
  have hsafe := hchecks.1
  have h := of_decide_eq_true (by simpa only [safeCheck] using hsafe)
  rcases h with ⟨hlower, hlowerUpper, hupper, hthreshold, hrowNonneg,
    hlowerPos, hupperPos, hpiPos, hcDenPos, hprefRadNonneg,
    hprefSqrtPos, hcSafe, hfourSafe, hsevenSafe, hnineSafe,
    hfirstSafe, hsecondSafe, htailDenPos, hgrowthSafe, hrowUpper⟩
  have hrowContains := rowInterval_contains cell hsafe
  have hrow : thresholdDominantCappedFourierCellRow
      (cell.lower : ℝ) (cell.upper : ℝ) z ≤ (cell.rowUpper : ℝ) :=
    hrowContains.2.trans (by
      have hreal : ((rowInterval cell).upperRat : ℝ) ≤
          (cell.rowUpper : ℝ) := by exact_mod_cast hrowUpper
      simpa only [Interval.upperRat, Dyadic.cast_toRat] using hreal)
  have hgrowthContains := growthInterval_contains cell hsafe
  have hgrowth : Real.exp (9 * (z : ℝ) * (cell.thresholdUpper : ℝ)) ≤
      ((growthInterval cell).upperRat : ℝ) := by
    simpa only [Interval.upperRat, Dyadic.cast_toRat] using hgrowthContains.2
  have hrowNonnegative : 0 ≤ thresholdDominantCappedFourierCellRow
      (cell.lower : ℝ) (cell.upper : ℝ) z := by
    have hLreal : (0 : ℝ) < cell.lower := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 2) hlower)
    have hUreal : (0 : ℝ) < cell.upper := hLreal.trans_le (by exact_mod_cast hlowerUpper)
    have hcReal : 0 < Real.pi ^ 2 /
        ((z : ℝ) * (cell.upper : ℝ) ^ 2) := by
      norm_num [z]
      positivity
    have hdenReal : 0 < 1 - Real.exp (-7 *
        (Real.pi ^ 2 / ((z : ℝ) * (cell.upper : ℝ) ^ 2))) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
    unfold thresholdDominantCappedFourierCellRow
    dsimp only
    positivity
  have hrowPow := pow_le_pow_left₀ hrowNonnegative hrow 256
  have hnonnegGrowth : (0 : ℝ) ≤ (growthInterval cell).upperRat :=
    (Real.exp_nonneg _).trans hgrowth
  have hmajorant :
      Real.exp (9 * (z : ℝ) * (cell.thresholdUpper : ℝ)) *
          thresholdDominantCappedFourierCellRow
              (cell.lower : ℝ) (cell.upper : ℝ) z ^ 256 ≤
        (finalUpperRat cell : ℝ) := by
    unfold finalUpperRat
    push_cast
    exact mul_le_mul hgrowth hrowPow (by positivity) hnonnegGrowth
  have hfinal : finalUpperRat cell < 99 / (100 * 2 ^ 192) :=
    of_decide_eq_true hchecks.2
  apply hmajorant.trans_lt
  have hfinalReal : (finalUpperRat cell : ℝ) <
      ((99 / (100 * 2 ^ 192) : ℚ) : ℝ) := by exact_mod_cast hfinal
  calc
    (finalUpperRat cell : ℝ) <
        ((99 / (100 * 2 ^ 192) : ℚ) : ℝ) := hfinalReal
    _ = ((99 / (100 * 2 ^ 192) : ℚ) : ℝ) := by
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_pow]

end CappedFourierNumeric256Bits192
end SparseThresholdDominant
end CertifiedJL
