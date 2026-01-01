/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Near.Conditioning
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Near.Coupled

/-!
# Retained-coordinate wrapped-row assembly

This file keeps the zero modular image and the nonzero modular images on
opposite sides of the one-coordinate conditioning identity.  The zero-image
terms are reassembled before applying the retained-coordinate scalar bound;
the inactive and active nonzero-image tails are averaged exactly once.
-/

open scoped BigOperators ENNReal NNReal

open MeasureTheory ProbabilityTheory

namespace CertifiedJL

private theorem retainedAssembly_integrable_conditional
    {d : ℕ} (i : Fin d) (activity : Bool) (f : (Fin d → ℤ) → ℝ) :
    Integrable f (dominantConditionalRowPMF i activity).toMeasure := by
  rw [dominantConditionalRowPMF]
  rw [← PMF.toMeasure_map
    (p := PMF.uniformOfFintype (DominantConditionalRowSeed i))
    (f := dominantConditionalRow i activity)
    (measurable_of_finite _)]
  apply (integrable_map_measure
    (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_finite _).aemeasurable).2
  exact Integrable.of_finite

private theorem retainedAssembly_integrable_sparseRow
    {d : ℕ} (f : (Fin d → ℤ) → ℝ) :
    Integrable f (sparseRademacherRow d).toMeasure := by
  rw [sparseRademacherRow_eq_map_uniformRowSeed]
  rw [← PMF.toMeasure_map
    (p := PMF.uniformOfFintype (SparseRowSeed d))
    (f := sparseRow) (measurable_of_finite sparseRow)]
  apply (integrable_map_measure
    (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_finite sparseRow).aemeasurable).2
  exact Integrable.of_finite

/-- Inactive nonzero modular-image allowance after normalizing by the
retained amplitude. -/
noncomputable def retainedInactiveImageTail
    (q A : ℕ) (V z : ℝ) : ℝ :=
  let u := V / (A : ℝ) ^ 2
  let B := (q : ℝ) / (A : ℝ)
  let alpha := z / (1 + z * u)
  2 * Real.exp (-alpha * B ^ 2) /
    (1 - (Real.exp (-alpha * B ^ 2)) ^ 3)

/-- Active nonzero modular-image allowance after normalizing by the retained
amplitude. -/
noncomputable def retainedActiveImageTail
    (q A : ℕ) (V z : ℝ) : ℝ :=
  let u := V / (A : ℝ) ^ 2
  let B := (q : ℝ) / (A : ℝ)
  let alpha := z / (1 + z * u)
  Real.exp (-alpha * (B - 1) ^ 2) /
      (1 - Real.exp (-alpha * (3 * B ^ 2 - 2 * B))) +
    Real.exp (-alpha * (B + 1) ^ 2) /
      (1 - Real.exp (-alpha * (3 * B ^ 2 + 2 * B)))

/-- The complete wrapped row is bounded by the *reassembled* retained
zero-image moment plus the arithmetic mean of the two conditioned image
tails.  In particular, the modular tail is not tensorized and is not added
twice. -/
theorem sparseRow_wrapped_le_retainedZero_add_conditionedTail
    {d q : ℕ} (w : Fin d → ℤ) (i : Fin d) (V z C : ℝ)
    (hq : Odd q) (hi : w i ≠ 0) (hV : 0 < V)
    (hnorm : dominantRemainderSqNorm w i = V)
    (hz : 0 < z)
    (hB : 1 < (q : ℝ) / (dominantAmplitude w i : ℝ))
    (hC : 0 ≤ C)
    (hcentral :
      ENNReal.ofReal
          (∫ row, Real.exp
            (-(z / (dominantAmplitude w i : ℝ) ^ 2) *
              (((∑ j, row j * w j : ℤ) : ℝ) ^ 2))
            ∂(sparseRademacherRow d).toMeasure) ≤
        ENNReal.ofReal C) :
    ENNReal.ofReal
        (∫ row, wrappedGaussianKernel q
          (z / (dominantAmplitude w i : ℝ) ^ 2)
          (∑ j, row j * w j)
          ∂(sparseRademacherRow d).toMeasure) ≤
      ENNReal.ofReal C +
        ENNReal.ofReal
          ((retainedInactiveImageTail q (dominantAmplitude w i) V z +
            retainedActiveImageTail q (dominantAmplitude w i) V z) / 2) := by
  let A : ℕ := dominantAmplitude w i
  let residual : Fin (Fintype.card (DominantRemainderIndex i)) → ℤ :=
    dominantRemainderFinWeights w i
  let inactiveZero : ℝ :=
    ∫ row, Real.exp
      (-(z / (A : ℝ) ^ 2) *
        (((∑ j, row j * residual j : ℤ) : ℝ) ^ 2))
      ∂(sparseRademacherRow
        (Fintype.card (DominantRemainderIndex i))).toMeasure
  let activeZero : ℝ :=
    ∫ row, Real.exp
      (-(z / (A : ℝ) ^ 2) *
        ((((A : ℤ) + ∑ j, row j * residual j : ℤ) : ℝ) ^ 2))
      ∂(sparseRademacherRow
        (Fintype.card (DominantRemainderIndex i))).toMeasure
  have hA : 0 < A := by
    dsimp [A]
    exact dominantAmplitude_pos hi
  have hAReal : 0 < (A : ℝ) := by exact_mod_cast hA
  have hs : 0 < z / (A : ℝ) ^ 2 := by positivity
  have hresnorm : ∑ j, (residual j : ℝ) ^ 2 = V := by
    dsimp [residual]
    rw [← realCast_sqNorm, sqNorm_dominantRemainderFinWeights, hnorm]
  have hu : 0 < V / (A : ℝ) ^ 2 := by positivity
  have hzu : 0 < z * (V / (A : ℝ) ^ 2) := mul_pos hz hu
  have hs_eq :
      (z * (V / (A : ℝ) ^ 2)) / V = z / (A : ℝ) ^ 2 := by
    field_simp [hV.ne', hAReal.ne']
  have hinactive :=
    sparseRow_wrappedGaussianKernel_normalized_nonzeroImageBound
      residual q V (z * (V / (A : ℝ) ^ 2)) hq.pos hV hresnorm hzu
  have hactive :=
    sparseRow_shifted_wrappedGaussianKernel_normalized_nonzeroImageBound
      residual q A V z hq.pos hA hV hresnorm hz (by simpa [A] using hB)
  have hinactive' :
      ENNReal.ofReal
          (∫ row, wrappedGaussianKernel q (z / (A : ℝ) ^ 2)
            (∑ j, row j * residual j)
            ∂(sparseRademacherRow
              (Fintype.card (DominantRemainderIndex i))).toMeasure) ≤
        ENNReal.ofReal inactiveZero +
          ENNReal.ofReal (retainedInactiveImageTail q A V z) := by
    have hzeroEq :
        (∫ row, Real.exp
            (-(z * (V / (A : ℝ) ^ 2)) *
              ((((∑ j, row j * residual j : ℤ) : ℝ) / Real.sqrt V) ^ 2))
            ∂(sparseRademacherRow
              (Fintype.card (DominantRemainderIndex i))).toMeasure) =
          inactiveZero := by
      dsimp [inactiveZero]
      apply integral_congr_ae
      filter_upwards [] with row
      congr 1
      have hsqrt : Real.sqrt V ^ 2 = V := Real.sq_sqrt hV.le
      have hsqrtNe : Real.sqrt V ≠ 0 := (Real.sqrt_pos.2 hV).ne'
      field_simp [hsqrtNe, hAReal.ne', hV.ne']
      rw [hsqrt]
      ring
    have htailEq :
        2 * Real.exp
            (-(z * (V / (A : ℝ) ^ 2)) *
              ((q : ℝ) / Real.sqrt V) ^ 2 /
                (1 + z * (V / (A : ℝ) ^ 2))) /
            (1 - (Real.exp
              (-(z * (V / (A : ℝ) ^ 2)) *
                ((q : ℝ) / Real.sqrt V) ^ 2 /
                  (1 + z * (V / (A : ℝ) ^ 2)))) ^ 3) =
          retainedInactiveImageTail q A V z := by
      have hexponent :
          -(z * (V / (A : ℝ) ^ 2)) *
              ((q : ℝ) / Real.sqrt V) ^ 2 /
                (1 + z * (V / (A : ℝ) ^ 2)) =
            -(z / (1 + z * (V / (A : ℝ) ^ 2))) *
              ((q : ℝ) / (A : ℝ)) ^ 2 := by
        have hsqrt : Real.sqrt V ^ 2 = V := Real.sq_sqrt hV.le
        have hsqrtNe : Real.sqrt V ≠ 0 := (Real.sqrt_pos.2 hV).ne'
        field_simp [hsqrtNe, hAReal.ne', hV.ne']
        rw [hsqrt]
        ring
      unfold retainedInactiveImageTail
      rw [hexponent]
    rw [← hs_eq]
    simpa only [hzeroEq, htailEq] using hinactive
  have hactive' :
      ENNReal.ofReal
          (∫ row, wrappedGaussianKernel q (z / (A : ℝ) ^ 2)
            ((A : ℤ) + ∑ j, row j * residual j)
            ∂(sparseRademacherRow
              (Fintype.card (DominantRemainderIndex i))).toMeasure) ≤
        ENNReal.ofReal activeZero +
          ENNReal.ofReal (retainedActiveImageTail q A V z) := by
    convert hactive using 1
    congr 2
    apply integral_congr_ae
    filter_upwards [] with row
    congr 1
    field_simp [hAReal.ne']
  let B : ℝ := (q : ℝ) / (A : ℝ)
  let alpha : ℝ := z / (1 + z * (V / (A : ℝ) ^ 2))
  have hB' : 1 < B := by simpa [B, A] using hB
  have halpha : 0 < alpha := by dsimp [alpha]; positivity
  have hinactiveRate : 0 < alpha * B ^ 2 := by positivity
  have hinactiveExp : Real.exp (-(alpha * B ^ 2)) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hinactiveRate)
  have hinactivePow : Real.exp (-(alpha * B ^ 2)) ^ 3 < 1 := by
    simpa using pow_lt_pow_left₀ hinactiveExp
      (Real.exp_pos (-(alpha * B ^ 2))).le
      (by norm_num : (3 : ℕ) ≠ 0)
  have hinactiveDen :
      0 < 1 - Real.exp (-(alpha * B ^ 2)) ^ 3 :=
    sub_pos.mpr hinactivePow
  have hTi : 0 ≤ retainedInactiveImageTail q A V z := by
    unfold retainedInactiveImageTail
    dsimp only
    apply div_nonneg (by positivity)
    apply (sub_pos.mpr ?_).le
    have hrate : 0 <
        (z / (1 + z * (V / (A : ℝ) ^ 2))) *
          ((q : ℝ) / (A : ℝ)) ^ 2 := by
      simpa only [alpha, B] using hinactiveRate
    have hexp : Real.exp
        (-(z / (1 + z * (V / (A : ℝ) ^ 2))) *
          ((q : ℝ) / (A : ℝ)) ^ 2) < 1 := by
      apply Real.exp_lt_one_iff.mpr
      nlinarith
    simpa using pow_lt_pow_left₀ hexp (Real.exp_pos _).le
      (by norm_num : (3 : ℕ) ≠ 0)
  have hminusRate : 0 < alpha * (3 * B ^ 2 - 2 * B) := by
    have hBpos : 0 < B := lt_trans zero_lt_one hB'
    have hfactor : 0 < 3 * B - 2 := by nlinarith
    have hpoly : 0 < 3 * B ^ 2 - 2 * B := by
      nlinarith [mul_pos hBpos hfactor]
    exact mul_pos halpha hpoly
  have hplusRate : 0 < alpha * (3 * B ^ 2 + 2 * B) := by
    have hBpos : 0 < B := lt_trans zero_lt_one hB'
    have hfactor : 0 < 3 * B + 2 := by nlinarith
    have hpoly : 0 < 3 * B ^ 2 + 2 * B := by
      nlinarith [mul_pos hBpos hfactor]
    exact mul_pos halpha hpoly
  have hminusDen :
      0 < 1 - Real.exp (-(alpha * (3 * B ^ 2 - 2 * B))) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hminusRate))
  have hplusDen :
      0 < 1 - Real.exp (-(alpha * (3 * B ^ 2 + 2 * B))) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hplusRate))
  have hTa : 0 ≤ retainedActiveImageTail q A V z := by
    unfold retainedActiveImageTail
    dsimp only
    have hminusDen' : 0 < 1 - Real.exp
        (-(z / (1 + z * (V / (A : ℝ) ^ 2))) *
          (3 * ((q : ℝ) / (A : ℝ)) ^ 2 -
            2 * ((q : ℝ) / (A : ℝ)))) := by
      apply sub_pos.mpr
      apply Real.exp_lt_one_iff.mpr
      have hrate : 0 <
          (z / (1 + z * (V / (A : ℝ) ^ 2))) *
            (3 * ((q : ℝ) / (A : ℝ)) ^ 2 -
              2 * ((q : ℝ) / (A : ℝ))) := by
        simpa only [alpha, B] using hminusRate
      nlinarith
    have hplusDen' : 0 < 1 - Real.exp
        (-(z / (1 + z * (V / (A : ℝ) ^ 2))) *
          (3 * ((q : ℝ) / (A : ℝ)) ^ 2 +
            2 * ((q : ℝ) / (A : ℝ)))) := by
      apply sub_pos.mpr
      apply Real.exp_lt_one_iff.mpr
      have hrate : 0 <
          (z / (1 + z * (V / (A : ℝ) ^ 2))) *
            (3 * ((q : ℝ) / (A : ℝ)) ^ 2 +
              2 * ((q : ℝ) / (A : ℝ))) := by
        simpa only [alpha, B] using hplusRate
      nlinarith
    exact add_nonneg
      (div_nonneg (Real.exp_nonneg _) hminusDen'.le)
      (div_nonneg (Real.exp_nonneg _) hplusDen'.le)
  have hZi : 0 ≤ inactiveZero := by
    dsimp [inactiveZero]
    exact integral_nonneg fun _ => Real.exp_nonneg _
  have hZa : 0 ≤ activeZero := by
    dsimp [activeZero]
    exact integral_nonneg fun _ => Real.exp_nonneg _
  have hinactiveReal :
      (∫ row, wrappedGaussianKernel q (z / (A : ℝ) ^ 2)
          (∑ j, row j * residual j)
          ∂(sparseRademacherRow
            (Fintype.card (DominantRemainderIndex i))).toMeasure) ≤
        inactiveZero + retainedInactiveImageTail q A V z := by
    have h := hinactive'
    rw [← ENNReal.ofReal_add hZi hTi] at h
    exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg hZi hTi)).mp h
  have hactiveReal :
      (∫ row, wrappedGaussianKernel q (z / (A : ℝ) ^ 2)
          ((A : ℤ) + ∑ j, row j * residual j)
          ∂(sparseRademacherRow
            (Fintype.card (DominantRemainderIndex i))).toMeasure) ≤
        activeZero + retainedActiveImageTail q A V z := by
    have h := hactive'
    rw [← ENNReal.ofReal_add hZa hTa] at h
    exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg hZa hTa)).mp h
  let wrappedStat : (Fin d → ℤ) → ℝ := fun row ↦
    wrappedGaussianKernel q (z / (A : ℝ) ^ 2) (∑ j, row j * w j)
  have hwrappedSplit := sparseRademacherRow_integral_eq_half_conditioned
    i wrappedStat
      (retainedAssembly_integrable_conditional i false wrappedStat)
      (retainedAssembly_integrable_conditional i true wrappedStat)
  have hwrappedFalse :=
    dominantConditionalRow_wrappedGaussianKernel_integral_eq_shiftedRemainder
      (q := q) w i false (z / (A : ℝ) ^ 2)
  have hwrappedTrue :=
    dominantConditionalRow_wrappedGaussianKernel_integral_eq_shiftedRemainder
      (q := q) w i true (z / (A : ℝ) ^ 2)
  have hwrappedMean :
      (∫ row, wrappedGaussianKernel q (z / (A : ℝ) ^ 2)
          (∑ j, row j * w j)
          ∂(sparseRademacherRow d).toMeasure) =
        ((∫ row, wrappedGaussianKernel q (z / (A : ℝ) ^ 2)
            (∑ j, row j * residual j)
            ∂(sparseRademacherRow
              (Fintype.card (DominantRemainderIndex i))).toMeasure) +
          (∫ row, wrappedGaussianKernel q (z / (A : ℝ) ^ 2)
            ((A : ℤ) + ∑ j, row j * residual j)
            ∂(sparseRademacherRow
              (Fintype.card (DominantRemainderIndex i))).toMeasure)) / 2 := by
    calc
      _ = ((∫ row, wrappedStat row
            ∂(dominantConditionalRowPMF i false).toMeasure) +
          (∫ row, wrappedStat row
            ∂(dominantConditionalRowPMF i true).toMeasure)) / 2 := by
        simpa only [wrappedStat] using hwrappedSplit
      _ = _ := by
        rw [show (∫ row, wrappedStat row
              ∂(dominantConditionalRowPMF i false).toMeasure) =
            ∫ row, wrappedGaussianKernel q (z / (A : ℝ) ^ 2)
              (∑ j, row j * residual j)
            ∂(sparseRademacherRow
                (Fintype.card (DominantRemainderIndex i))).toMeasure by
              simpa [wrappedStat, A, residual] using hwrappedFalse,
          show (∫ row, wrappedStat row
              ∂(dominantConditionalRowPMF i true).toMeasure) =
            ∫ row, wrappedGaussianKernel q (z / (A : ℝ) ^ 2)
              ((A : ℤ) + ∑ j, row j * residual j)
            ∂(sparseRademacherRow
                (Fintype.card (DominantRemainderIndex i))).toMeasure by
              simpa [wrappedStat, A, residual] using hwrappedTrue]
  let zeroStat : ℤ → ℝ := fun t ↦
    Real.exp (-(z / (A : ℝ) ^ 2) * (t : ℝ) ^ 2)
  have hzeroEven : Function.Even zeroStat := by
    intro t
    dsimp [zeroStat]
    congr 2
    push_cast
    ring
  let zeroRowStat : (Fin d → ℤ) → ℝ := fun row ↦
    zeroStat (∑ j, row j * w j)
  have hzeroSplit := sparseRademacherRow_integral_eq_half_conditioned
    i zeroRowStat
      (retainedAssembly_integrable_conditional i false zeroRowStat)
      (retainedAssembly_integrable_conditional i true zeroRowStat)
  have hzeroFalse := dominantConditionalRow_integral_eq_shiftedRemainder_of_even
    w i false zeroStat hzeroEven
  have hzeroTrue := dominantConditionalRow_integral_eq_shiftedRemainder_of_even
    w i true zeroStat hzeroEven
  have hzeroMean :
      (∫ row, Real.exp
          (-(z / (A : ℝ) ^ 2) *
            (((∑ j, row j * w j : ℤ) : ℝ) ^ 2))
          ∂(sparseRademacherRow d).toMeasure) =
        (inactiveZero + activeZero) / 2 := by
    calc
      _ = ((∫ row, zeroRowStat row
            ∂(dominantConditionalRowPMF i false).toMeasure) +
          (∫ row, zeroRowStat row
            ∂(dominantConditionalRowPMF i true).toMeasure)) / 2 := by
        simpa only [zeroRowStat, zeroStat] using hzeroSplit
      _ = (inactiveZero + activeZero) / 2 := by
        rw [show (∫ row, zeroRowStat row
              ∂(dominantConditionalRowPMF i false).toMeasure) =
            inactiveZero by
              simpa [zeroRowStat, zeroStat, inactiveZero, A, residual]
                using hzeroFalse,
          show (∫ row, zeroRowStat row
              ∂(dominantConditionalRowPMF i true).toMeasure) =
            activeZero by
              simpa [zeroRowStat, zeroStat, activeZero, A, residual]
                using hzeroTrue]
  have hcentralReal :
      (∫ row, Real.exp
          (-(z / (A : ℝ) ^ 2) *
            (((∑ j, row j * w j : ℤ) : ℝ) ^ 2))
          ∂(sparseRademacherRow d).toMeasure) ≤ C := by
    exact (ENNReal.ofReal_le_ofReal_iff hC).mp (by simpa only [A] using hcentral)
  have htailMean :
      0 ≤ (retainedInactiveImageTail q A V z +
        retainedActiveImageTail q A V z) / 2 := by positivity
  have hreal :
      (∫ row, wrappedGaussianKernel q (z / (A : ℝ) ^ 2)
          (∑ j, row j * w j)
          ∂(sparseRademacherRow d).toMeasure) ≤
        C + (retainedInactiveImageTail q A V z +
          retainedActiveImageTail q A V z) / 2 := by
    rw [hwrappedMean]
    calc
      _ ≤ ((inactiveZero + retainedInactiveImageTail q A V z) +
          (activeZero + retainedActiveImageTail q A V z)) / 2 := by
        gcongr
      _ = (inactiveZero + activeZero) / 2 +
          (retainedInactiveImageTail q A V z +
            retainedActiveImageTail q A V z) / 2 := by ring
      _ ≤ C + (retainedInactiveImageTail q A V z +
            retainedActiveImageTail q A V z) / 2 := by
        gcongr
        rw [← hzeroMean]
        exact hcentralReal
  simpa only [A, ENNReal.ofReal_add hC htailMean] using
    ENNReal.ofReal_mono hreal

end CertifiedJL
