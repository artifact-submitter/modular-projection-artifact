/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Lower
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.Cell

/-! # Target-neutral dominant event endgame -/

open scoped ENNReal
open MeasureTheory

namespace CertifiedJL

/-- Turn a dominant one-row bound and its target-dependent scalar comparison
into a high-activity event bound. The activity condition is discarded only
after the row kernel has retained the dominant coordinate. -/
theorem sparseThresholdDominantHighActivity_of_rowKernel_at
    (rows squaredNormFloor : ℕ) {highBudget : ℝ}
    {q d : ℕ} (w : Fin d → ℤ) (inputThreshold : ℕ) (i : Fin d)
    (z K thresholdUpper : ℝ)
    (hbudget : 0 < highBudget)
    (hinputThreshold : 0 < inputThreshold) (hi : w i ≠ 0)
    (hz : 0 < z)
    (hthreshold : (inputThreshold : ℝ) ^ 2 /
        (dominantAmplitude w i : ℝ) ^ 2 ≤ thresholdUpper)
    (hrow :
      (∫ row, Real.exp (-(z / (dominantAmplitude w i : ℝ) ^ 2) *
          sparseLowerRowKernel q w row)
          ∂(sparseRademacherRow d).toMeasure) ≤ K)
    (hratio : Real.exp (squaredNormFloor * z * thresholdUpper) * K ^ rows <
      highBudget) :
    eventProbability (sparseRademacherMatrix rows d)
        (fun J =>
          L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
              inputThreshold q w J ∧
            squaredNormFloor ≤ (dominantActivityCount
              (matrixDominantActivity i J) : ℕ)) <
      ENNReal.ofReal highBudget := by
  let A := dominantAmplitude w i
  let s : ℝ := z * (inputThreshold : ℝ) ^ 2 / (A : ℝ) ^ 2
  have hA : 0 < A := dominantAmplitude_pos hi
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  have hbReal : (0 : ℝ) < inputThreshold := by exact_mod_cast hinputThreshold
  have hs : 0 < s := by dsimp [s]; positivity
  have hcoefficient : s / (inputThreshold : ℝ) ^ 2 =
      z / (A : ℝ) ^ 2 := by
    dsimp [s]
    field_simp
  have hrowThreshold :
      ∫ row, Real.exp
          (-(s / (inputThreshold : ℝ) ^ 2) * sparseLowerRowKernel q w row)
          ∂(sparseRademacherRow d).toMeasure ≤ K := by
    simpa only [hcoefficient] using hrow
  have hfull := ternaryThresholdLowerTail_from_rowKernelIntegral_at
    rows squaredNormFloor q d w inputThreshold s K hinputThreshold hs hrowThreshold
  have hsUpper : s ≤ z * thresholdUpper := by
    dsimp [s]
    calc
      z * (inputThreshold : ℝ) ^ 2 / (A : ℝ) ^ 2 =
          z * ((inputThreshold : ℝ) ^ 2 / (A : ℝ) ^ 2) := by ring
      _ ≤ z * thresholdUpper :=
        mul_le_mul_of_nonneg_left hthreshold hz.le
  have hratioActual : Real.exp (squaredNormFloor * s) * K ^ rows < highBudget := by
    have hKpow : 0 ≤ K ^ rows := pow_nonneg (by
      have hIntegralNonneg : 0 ≤
          ∫ row, Real.exp (-(z / (dominantAmplitude w i : ℝ) ^ 2) *
            sparseLowerRowKernel q w row)
            ∂(sparseRademacherRow d).toMeasure :=
        integral_nonneg_of_ae
          (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)
      exact hIntegralNonneg.trans hrow) _
    apply (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hsUpper (Nat.cast_nonneg _)))
      hKpow).trans_lt
    simpa only [mul_assoc] using hratio
  have hfullStrict :
      (eventProbability (sparseRademacherMatrix rows d)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
          inputThreshold q w)).toReal < highBudget :=
    hfull.trans_lt hratioActual
  have hjoint :
      eventProbability (sparseRademacherMatrix rows d)
          (fun J =>
            L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
                inputThreshold q w J ∧
              squaredNormFloor ≤ (dominantActivityCount
                (matrixDominantActivity i J) : ℕ)) ≤
        eventProbability (sparseRademacherMatrix rows d)
          (L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
            inputThreshold q w) := by
    apply eventProbability_mono
    intro J hJ
    exact hJ.1
  rw [← ENNReal.toReal_lt_toReal
    (by
      unfold eventProbability
      exact PMF.apply_ne_top _ _)
    ENNReal.ofReal_ne_top]
  calc
    _ ≤ (eventProbability (sparseRademacherMatrix rows d)
          (L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
            inputThreshold q w)).toReal :=
      ENNReal.toReal_mono
        (by
          unfold eventProbability
          exact PMF.apply_ne_top _ _) hjoint
    _ < highBudget := hfullStrict
    _ = (ENNReal.ofReal highBudget).toReal :=
      (ENNReal.toReal_ofReal hbudget.le).symm

end CertifiedJL
