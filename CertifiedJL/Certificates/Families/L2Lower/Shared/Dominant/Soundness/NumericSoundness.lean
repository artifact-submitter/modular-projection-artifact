/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Soundness.ScalarNumericSoundness
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Regimes.Dominant.Threshold.Cell
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.Numeric

/-!
# Soundness of public-threshold dominant-cell replay

The row arithmetic is shared with the established dominant evaluator.  The
new proof obligation is the independently distributed public-threshold
exponential, together with the exact-zero `k < 29` branch.
-/

namespace CertifiedJL
namespace SparseThresholdDominant
namespace Numeric

open DominantNumeric

/-- Reflected premises needed by the explicit-modulus inactive row. -/
structure InactiveRowSafe (cell : DecodedCell) (z : ℚ) : Prop where
  upperDenominator : 0 < (rat 1 + rat (z * cell.upper)).lo
  thetaExponent :
    (-(powNat piInterval 2 *
      div (rat 1) (rat 1 + rat (z * cell.upper)))).upperRat ≤ 1
  sqrtRadicand : 0 ≤ (rat 1 + rat (z * cell.lower)).lo
  sqrtDenominator : 0 < (rat 1 + rat (z * cell.lower)).sqrt.lo
  thetaDenominator :
    0 < (rat 1 - powNat
      (expUpper (-(powNat piInterval 2 *
        div (rat 1) (rat 1 + rat (z * cell.upper))))) 3).lo
  wrapExponent :
    (-(alphaInterval cell z * powNat (bInterval cell) 2)).upperRat ≤ 1
  wrapRatioExponent :
    (rat 3 * (-(alphaInterval cell z *
      powNat (bInterval cell) 2))).upperRat ≤ 1
  wrapDenominator :
    0 < (rat 1 - expUpper
      (rat 3 * (-(alphaInterval cell z *
        powNat (bInterval cell) 2)))).lo

/-- Reflected premises needed by the explicit-modulus active row. -/
structure ActiveRowSafe (cell : DecodedCell) (z : ℚ) : Prop where
  upperDenominator : 0 < (rat 1 + rat (z * cell.upper)).lo
  rowExponent :
    (-(div (rat z) (rat 1 + rat (z * cell.upper)))).upperRat ≤ 1
  minusExponent :
    (-(alphaInterval cell z *
      powNat (bInterval cell - rat 1) 2)).upperRat ≤ 1
  minusRatioExponent :
    (-(alphaInterval cell z *
      (rat 3 * powNat (bInterval cell) 2 -
        rat 2 * bInterval cell))).upperRat ≤ 1
  plusExponent :
    (-(alphaInterval cell z *
      powNat (bInterval cell + rat 1) 2)).upperRat ≤ 1
  plusRatioExponent :
    (-(alphaInterval cell z *
      (rat 3 * powNat (bInterval cell) 2 +
        rat 2 * bInterval cell))).upperRat ≤ 1
  minusDenominator :
    0 < (rat 1 - expUpper (-(alphaInterval cell z *
      (rat 3 * powNat (bInterval cell) 2 -
        rat 2 * bInterval cell)))).lo
  plusDenominator :
    0 < (rat 1 - expUpper (-(alphaInterval cell z *
      (rat 3 * powNat (bInterval cell) 2 +
        rat 2 * bInterval cell)))).lo

/-- Reflected premises for a nontrivial public-threshold conditional term. -/
structure ConditionalSafe (cell : DecodedCell) (k : Fin 257) : Prop where
  growthExponent :
    (rat (29 * cell.z k * cell.thresholdUpper /
      ((k : ℕ) * DominantNumeric.growthScale))).upperRat ≤ 1
  inactive : InactiveRowSafe cell (cell.z k)
  active : ActiveRowSafe cell (cell.z k)

theorem inactiveRowSafeCheck_sound {cell : DecodedCell} {z : ℚ}
    (hcheck : inactiveRowSafeCheck cell z = true) :
    InactiveRowSafe cell z := by
  have h := of_decide_eq_true (by
    simpa only [inactiveRowSafeCheck] using hcheck)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2⟩

theorem activeRowSafeCheck_sound {cell : DecodedCell} {z : ℚ}
    (hcheck : activeRowSafeCheck cell z = true) :
    ActiveRowSafe cell z := by
  have h := of_decide_eq_true (by
    simpa only [activeRowSafeCheck] using hcheck)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2⟩

theorem conditionalSafeCheck_sound {cell : DecodedCell} {k : Fin 257}
    (hk : ¬(k : ℕ) < 29) (hz : cell.z k ≠ 0)
    (hcheck : conditionalSafeCheck cell k = true) :
    ConditionalSafe cell k := by
  simp only [conditionalSafeCheck, hk, hz, or_false, if_false,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact ⟨hcheck.1, inactiveRowSafeCheck_sound hcheck.2.1,
    activeRowSafeCheck_sound hcheck.2.2⟩

theorem cellNumericSafeCheck_sound {cell : DecodedCell}
    (hcheck : cellNumericSafeCheck cell = true) :
    ∀ k : Fin 257, ¬(k : ℕ) < 29 →
      cell.z k ≠ 0 → ConditionalSafe cell k := by
  intro k hk hz
  rw [cellNumericSafeCheck, List.all_eq_true,
    List.forall_mem_ofFn_iff] at hcheck
  exact conditionalSafeCheck_sound hk hz (hcheck k)

theorem modulusMatched_sqrt (cell : DecodedCell)
    (hmatch : ModulusMatched cell) :
    3 * Real.sqrt (1 + (cell.lower : ℝ)) =
      (cell.modulusLower : ℝ) := by
  have hB : (3 : ℝ) ≤ (cell.modulusLower : ℝ) := by
    exact_mod_cast hmatch.1
  have hsq : (cell.modulusLower : ℝ) ^ 2 =
      9 * (1 + (cell.lower : ℝ)) := by
    exact_mod_cast hmatch.2
  have hrad : 0 ≤ 1 + (cell.lower : ℝ) := by nlinarith [sq_nonneg (cell.modulusLower : ℝ)]
  have hsqrtSq := Real.sq_sqrt hrad
  have hsqrtNonneg := Real.sqrt_nonneg (1 + (cell.lower : ℝ))
  nlinarith

theorem inactiveRow_semantic_eq (cell : DecodedCell) (z : ℚ)
    (hmatch : ModulusMatched cell) :
    dominantCellInactiveRow cell.lower cell.upper z =
      thresholdDominantCellInactiveRow cell.lower cell.upper
        cell.modulusLower z := by
  unfold dominantCellInactiveRow thresholdDominantCellInactiveRow
    dominantCellInactiveWrap thresholdDominantCellInactiveWrap
  rw [modulusMatched_sqrt cell hmatch]

theorem activeRow_semantic_eq (cell : DecodedCell) (z : ℚ)
    (hmatch : ModulusMatched cell) :
    dominantCellActiveRow cell.lower cell.upper z =
      thresholdDominantCellActiveRow cell.lower cell.upper
        cell.modulusLower z := by
  unfold dominantCellActiveRow thresholdDominantCellActiveRow
    dominantCellActiveWrap thresholdDominantCellActiveWrap
  rw [modulusMatched_sqrt cell hmatch]

theorem contains_inactiveWrap (cell : DecodedCell) (z : ℚ)
    (hexponent :
      (-(alphaInterval cell z * powNat (bInterval cell) 2)).upperRat ≤ 1)
    (hratioExponent :
      (rat 3 * (-(alphaInterval cell z *
        powNat (bInterval cell) 2))).upperRat ≤ 1)
    (hdenominator :
      0 < (rat 1 - expUpper
        (rat 3 * (-(alphaInterval cell z *
          powNat (bInterval cell) 2)))).lo) :
    (inactiveWrap cell z).Contains
      (thresholdDominantCellInactiveWrap cell.lower cell.upper
        cell.modulusLower z) := by
  let B : ℝ := cell.modulusLower
  let alpha : ℝ := (z : ℝ) /
    (1 + (z : ℝ) * (cell.upper : ℝ))
  let exponentI := -(alphaInterval cell z * powNat (bInterval cell) 2)
  have hB : (bInterval cell).Contains B := by
    simpa [bInterval, B] using contains_rat cell.modulusLower
  have halpha : (alphaInterval cell z).Contains alpha := by
    simpa [alphaInterval, alpha] using
      contains_rat (z / (1 + z * cell.upper))
  have hexponentContains : exponentI.Contains (-alpha * B ^ 2) := by
    simpa [exponentI] using Interval.contains_neg
      (Interval.contains_mul halpha (contains_powNat hB 2))
  have hexp := contains_expUpper hexponentContains hexponent
  have hratioExponentContains : (rat 3 * exponentI).Contains
      (-3 * alpha * B ^ 2) := by
    convert Interval.contains_mul (contains_rat 3) hexponentContains using 1
    ring
  have hratioExp := contains_expUpper hratioExponentContains hratioExponent
  have hden : (rat 1 - expUpper (rat 3 * exponentI)).Contains
      (1 - Real.exp (-3 * alpha * B ^ 2)) :=
    Interval.contains_sub (by simpa using contains_rat (1 : ℚ)) hratioExp
  have hresult := Interval.contains_mul (contains_rat 2)
    (contains_div hdenominator hexp hden)
  unfold thresholdDominantCellInactiveWrap
  dsimp only
  change (inactiveWrap cell z).Contains _
  convert hresult using 1 <;>
    simp [inactiveWrap, exponentI, B, alpha] <;> ring

theorem contains_activeWrap (cell : DecodedCell) (z : ℚ)
    (hminusExponent :
      (-(alphaInterval cell z *
        powNat (bInterval cell - rat 1) 2)).upperRat ≤ 1)
    (hminusRatioExponent :
      (-(alphaInterval cell z *
        (rat 3 * powNat (bInterval cell) 2 -
          rat 2 * bInterval cell))).upperRat ≤ 1)
    (hplusExponent :
      (-(alphaInterval cell z *
        powNat (bInterval cell + rat 1) 2)).upperRat ≤ 1)
    (hplusRatioExponent :
      (-(alphaInterval cell z *
        (rat 3 * powNat (bInterval cell) 2 +
          rat 2 * bInterval cell))).upperRat ≤ 1)
    (hminusDenominator :
      0 < (rat 1 - expUpper (-(alphaInterval cell z *
        (rat 3 * powNat (bInterval cell) 2 -
          rat 2 * bInterval cell)))).lo)
    (hplusDenominator :
      0 < (rat 1 - expUpper (-(alphaInterval cell z *
        (rat 3 * powNat (bInterval cell) 2 +
          rat 2 * bInterval cell)))).lo) :
    (activeWrap cell z).Contains
      (thresholdDominantCellActiveWrap cell.lower cell.upper
        cell.modulusLower z) := by
  let B : ℝ := cell.modulusLower
  let alpha : ℝ := (z : ℝ) /
    (1 + (z : ℝ) * (cell.upper : ℝ))
  let BI := bInterval cell
  let alphaI := alphaInterval cell z
  let minusExponentI := -(alphaI * powNat (BI - rat 1) 2)
  let minusRatioExponentI :=
    -(alphaI * (rat 3 * powNat BI 2 - rat 2 * BI))
  let plusExponentI := -(alphaI * powNat (BI + rat 1) 2)
  let plusRatioExponentI :=
    -(alphaI * (rat 3 * powNat BI 2 + rat 2 * BI))
  have hB : BI.Contains B := by
    simpa [BI, bInterval, B] using contains_rat cell.modulusLower
  have halpha : alphaI.Contains alpha := by
    simpa [alphaI, alphaInterval, alpha] using
      contains_rat (z / (1 + z * cell.upper))
  have hminusBase : (BI - rat 1).Contains (B - 1) :=
    Interval.contains_sub hB (by simpa using contains_rat (1 : ℚ))
  have hplusBase : (BI + rat 1).Contains (B + 1) :=
    Interval.contains_add hB (by simpa using contains_rat (1 : ℚ))
  have hBSq := contains_powNat hB 2
  have hminusExponentContains : minusExponentI.Contains
      (-alpha * (B - 1) ^ 2) := by
    simpa [minusExponentI] using Interval.contains_neg
      (Interval.contains_mul halpha (contains_powNat hminusBase 2))
  have hplusExponentContains : plusExponentI.Contains
      (-alpha * (B + 1) ^ 2) := by
    simpa [plusExponentI] using Interval.contains_neg
      (Interval.contains_mul halpha (contains_powNat hplusBase 2))
  have hthreeBSq : (rat 3 * powNat BI 2).Contains (3 * B ^ 2) :=
    Interval.contains_mul (contains_rat 3) hBSq
  have htwoB : (rat 2 * BI).Contains (2 * B) :=
    Interval.contains_mul (contains_rat 2) hB
  have hminusRatioBase := Interval.contains_sub hthreeBSq htwoB
  have hplusRatioBase := Interval.contains_add hthreeBSq htwoB
  have hminusRatioExponentContains : minusRatioExponentI.Contains
      (-alpha * (3 * B ^ 2 - 2 * B)) := by
    simpa [minusRatioExponentI] using Interval.contains_neg
      (Interval.contains_mul halpha hminusRatioBase)
  have hplusRatioExponentContains : plusRatioExponentI.Contains
      (-alpha * (3 * B ^ 2 + 2 * B)) := by
    simpa [plusRatioExponentI] using Interval.contains_neg
      (Interval.contains_mul halpha hplusRatioBase)
  have hminusExp := contains_expUpper hminusExponentContains hminusExponent
  have hminusRatioExp := contains_expUpper
    hminusRatioExponentContains hminusRatioExponent
  have hplusExp := contains_expUpper hplusExponentContains hplusExponent
  have hplusRatioExp := contains_expUpper
    hplusRatioExponentContains hplusRatioExponent
  have hminusDen : (rat 1 - expUpper minusRatioExponentI).Contains
      (1 - Real.exp (-alpha * (3 * B ^ 2 - 2 * B))) :=
    Interval.contains_sub (by simpa using contains_rat (1 : ℚ))
      hminusRatioExp
  have hplusDen : (rat 1 - expUpper plusRatioExponentI).Contains
      (1 - Real.exp (-alpha * (3 * B ^ 2 + 2 * B))) :=
    Interval.contains_sub (by simpa using contains_rat (1 : ℚ))
      hplusRatioExp
  have hresult := Interval.contains_add
    (contains_div hminusDenominator hminusExp hminusDen)
    (contains_div hplusDenominator hplusExp hplusDen)
  unfold thresholdDominantCellActiveWrap
  simpa [activeWrap, B, alpha, BI, alphaI, minusExponentI,
    minusRatioExponentI, plusExponentI, plusRatioExponentI] using hresult

theorem contains_inactiveRow_of_safe {cell : DecodedCell} {z : ℚ}
    (hsafe : InactiveRowSafe cell z) :
    (inactiveRow cell z).Contains
      (thresholdDominantCellInactiveRow cell.lower cell.upper
        cell.modulusLower z) := by
  let sLower : ℝ := (z : ℝ) * (cell.lower : ℝ)
  let sUpper : ℝ := (z : ℝ) * (cell.upper : ℝ)
  let sLowerI := rat (z * cell.lower)
  let sUpperI := rat (z * cell.upper)
  let denominatorI := rat 1 + sUpperI
  let thetaExponentI := -(powNat piInterval 2 * div (rat 1) denominatorI)
  let thetaI := expUpper thetaExponentI
  let sqrtI := (rat 1 + sLowerI).sqrt
  have hsLower : sLowerI.Contains sLower := by
    simpa [sLowerI, sLower] using contains_rat (z * cell.lower)
  have hsUpper : sUpperI.Contains sUpper := by
    simpa [sUpperI, sUpper] using contains_rat (z * cell.upper)
  have hden : denominatorI.Contains (1 + sUpper) :=
    Interval.contains_add (by simpa using contains_rat (1 : ℚ)) hsUpper
  have hinv := contains_div hsafe.upperDenominator
    (by simpa using contains_rat (1 : ℚ)) hden
  have hpiSq := contains_powNat contains_piInterval 2
  have hthetaExponentContains : thetaExponentI.Contains
      (-Real.pi ^ 2 / (1 + sUpper)) := by
    simpa [thetaExponentI, div_eq_mul_inv] using Interval.contains_neg
      (Interval.contains_mul hpiSq hinv)
  have htheta := contains_expUpper hthetaExponentContains hsafe.thetaExponent
  have hsqrtInput : (rat 1 + sLowerI).Contains (1 + sLower) :=
    Interval.contains_add (by simpa using contains_rat (1 : ℚ)) hsLower
  have hsqrt := Interval.contains_sqrt hsafe.sqrtRadicand hsqrtInput
  have hinvSqrt := contains_div hsafe.sqrtDenominator
    (by simpa using contains_rat (1 : ℚ)) hsqrt
  have hthetaCube := contains_powNat htheta 3
  have hthetaDen : (rat 1 - powNat thetaI 3).Contains
      (1 - Real.exp (-Real.pi ^ 2 / (1 + sUpper)) ^ 3) :=
    Interval.contains_sub (by simpa using contains_rat (1 : ℚ)) hthetaCube
  have hthetaNum := Interval.contains_mul (contains_rat 2) htheta
  have hthetaRatio := contains_div hsafe.thetaDenominator hthetaNum hthetaDen
  have hcorrection := Interval.contains_add
    (by simpa using contains_rat (1 : ℚ)) hthetaRatio
  have hmain := Interval.contains_mul hinvSqrt hcorrection
  have hwrap := contains_inactiveWrap cell z hsafe.wrapExponent
    hsafe.wrapRatioExponent hsafe.wrapDenominator
  have hresult := Interval.contains_add hmain hwrap
  simpa [inactiveRow, thresholdDominantCellInactiveRow, sLower, sUpper,
    sLowerI, sUpperI, denominatorI, thetaExponentI, thetaI, sqrtI] using hresult

theorem contains_activeRow_of_safe {cell : DecodedCell} {z : ℚ}
    (hsafe : ActiveRowSafe cell z) :
    (activeRow cell z).Contains
      (thresholdDominantCellActiveRow cell.lower cell.upper
        cell.modulusLower z) := by
  let sUpper : ℝ := (z : ℝ) * (cell.upper : ℝ)
  let sUpperI := rat (z * cell.upper)
  let denominatorI := rat 1 + sUpperI
  let exponentI := -(div (rat z) denominatorI)
  have hsUpper : sUpperI.Contains sUpper := by
    simpa [sUpperI, sUpper] using contains_rat (z * cell.upper)
  have hden : denominatorI.Contains (1 + sUpper) :=
    Interval.contains_add (by simpa using contains_rat (1 : ℚ)) hsUpper
  have hratio := contains_div hsafe.upperDenominator (contains_rat z) hden
  have hexp := contains_expUpper (Interval.contains_neg hratio)
    hsafe.rowExponent
  have hrho :
      (rat (DominantNumeric.rhoRat cell.lower cell.upper z)).Contains
      (dominantCellRho cell.lower cell.upper z) := by
    convert contains_rat
      (DominantNumeric.rhoRat cell.lower cell.upper z) using 1
    exact (DominantNumeric.rhoRat_cast cell.lower cell.upper z).symm
  have hmain := Interval.contains_mul hexp hrho
  have hwrap := contains_activeWrap cell z hsafe.minusExponent
    hsafe.minusRatioExponent hsafe.plusExponent hsafe.plusRatioExponent
    hsafe.minusDenominator hsafe.plusDenominator
  have hresult := Interval.contains_add hmain hwrap
  simpa [activeRow, thresholdDominantCellActiveRow, sUpper, sUpperI,
    denominatorI, exponentI, neg_div] using hresult

theorem thresholdConditionalMajorant_distributed
    (cell : DecodedCell) (k : Fin 257)
    (hk : ¬(k : ℕ) < 29) (hz : cell.z k ≠ 0) :
    thresholdDominantCellConditionalMajorant cell k =
      min 1
        ((Real.exp
            (29 * (cell.z k : ℝ) * (cell.thresholdUpper : ℝ) / (k : ℕ)) *
          thresholdDominantCellActiveRow cell.lower cell.upper
            cell.modulusLower (cell.z k)) ^ (k : ℕ) *
        thresholdDominantCellInactiveRow cell.lower cell.upper
          cell.modulusLower (cell.z k) ^ (256 - (k : ℕ))) := by
  rw [thresholdDominantCellConditionalMajorant, if_neg hk, if_neg hz]
  apply congrArg (min 1)
  exact DominantNumeric.exp_mul_pow_eq_pow_exp_div_mul
    _ _ _ _ _ (by omega)

theorem contains_conditionalMajorant_of_low
    (cell : DecodedCell) (k : Fin 257) (hk : (k : ℕ) < 29) :
    (conditionalMajorant cell k).Contains
      (thresholdDominantCellConditionalMajorant cell k) := by
  simpa [conditionalMajorant, thresholdDominantCellConditionalMajorant, hk]
    using contains_rat (0 : ℚ)

theorem contains_conditionalMajorant_of_zero
    (cell : DecodedCell) (k : Fin 257)
    (hk : ¬(k : ℕ) < 29) (hz : cell.z k = 0) :
    (conditionalMajorant cell k).Contains
      (thresholdDominantCellConditionalMajorant cell k) := by
  simpa [conditionalMajorant, thresholdDominantCellConditionalMajorant,
    hk, hz] using contains_rat (1 : ℚ)

theorem contains_conditionalMajorant_of_pos
    (cell : DecodedCell) (k : Fin 257)
    (hk : ¬(k : ℕ) < 29) (hz : 0 < cell.z k)
    (hsafe : ConditionalSafe cell k) :
    (conditionalMajorant cell k).Contains
      (thresholdDominantCellConditionalMajorant cell k) := by
  have hkpos : 0 < (k : ℕ) := by omega
  have hgrowthBase :
      (expUpper (rat (29 * cell.z k * cell.thresholdUpper /
        ((k : ℕ) * DominantNumeric.growthScale)))).Contains
        (Real.exp (((29 * cell.z k * cell.thresholdUpper /
          ((k : ℕ) * DominantNumeric.growthScale) : ℚ) : ℝ))) := by
    apply contains_expUpper
    · simpa using contains_rat (29 * cell.z k * cell.thresholdUpper /
        ((k : ℕ) * DominantNumeric.growthScale))
    · exact hsafe.growthExponent
  have hgrowthPow := contains_powNat hgrowthBase
    DominantNumeric.growthScale
  have hgrowthReal :
      (Real.exp (((29 * cell.z k * cell.thresholdUpper /
        ((k : ℕ) * DominantNumeric.growthScale) : ℚ) : ℝ))) ^
          DominantNumeric.growthScale =
        Real.exp (29 * (cell.z k : ℝ) * (cell.thresholdUpper : ℝ) /
          (k : ℕ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num [DominantNumeric.growthScale]
    field_simp
  have hgrowth :
      (growthUpper cell (cell.z k) (k : ℕ)).Contains
        (Real.exp (29 * (cell.z k : ℝ) * (cell.thresholdUpper : ℝ) /
          (k : ℕ))) := by
    rw [growthUpper, ← hgrowthReal]
    exact hgrowthPow
  have hactive := contains_activeRow_of_safe hsafe.active
  have hinactive := contains_inactiveRow_of_safe hsafe.inactive
  have hbody := Interval.contains_mul
    (contains_powNat (Interval.contains_mul hgrowth hactive) (k : ℕ))
    (contains_powNat hinactive (256 - (k : ℕ)))
  have hminimum := contains_minInterval (contains_rat 1) hbody
  rw [thresholdConditionalMajorant_distributed cell k hk hz.ne']
  simpa [conditionalMajorant, hk, hz.ne'] using hminimum

theorem conditionalMajorant_le_upperRat
    (cell : DecodedCell) (k : Fin 257)
    (hvalid : cell.Valid)
    (hsafe : ¬(k : ℕ) < 29 → cell.z k ≠ 0 → ConditionalSafe cell k) :
    thresholdDominantCellConditionalMajorant cell k ≤
      ((conditionalMajorant cell k).upperRat : ℝ) := by
  by_cases hk : (k : ℕ) < 29
  · have hcontains := contains_conditionalMajorant_of_low cell k hk
    simpa only [Interval.upperRat, Dyadic.cast_toRat] using hcontains.2
  · by_cases hz : cell.z k = 0
    · have hcontains := contains_conditionalMajorant_of_zero cell k hk hz
      simpa only [Interval.upperRat, Dyadic.cast_toRat] using hcontains.2
    · have hzpos : 0 < cell.z k :=
        lt_of_le_of_ne (hvalid.2.2.2.2 k) (Ne.symm hz)
      have hcontains := contains_conditionalMajorant_of_pos
        cell k hk hzpos (hsafe hk hz)
      simpa only [Interval.upperRat, Dyadic.cast_toRat] using hcontains.2

private theorem upperRat_add (I J : DInterval) :
    ((I + J).upperRat : ℝ) =
      (I.upperRat : ℝ) + (J.upperRat : ℝ) := by
  change (Dyadic.toRat DominantNumeric.precision (I.hi + J.hi) : ℝ) =
    (Dyadic.toRat DominantNumeric.precision I.hi : ℝ) +
      (Dyadic.toRat DominantNumeric.precision J.hi : ℝ)
  rw [Dyadic.toRat_add]
  norm_num

private theorem le_upperRat_of_contains {I : DInterval} {x : ℝ}
    (h : I.Contains x) : x ≤ (I.upperRat : ℝ) := by
  simpa only [Interval.upperRat, Dyadic.cast_toRat] using h.2

theorem weightedConditional_le_upperRat
    (cell : DecodedCell) (k : Fin 257)
    (hvalid : cell.Valid)
    (hsafe : ¬(k : ℕ) < 29 → cell.z k ≠ 0 → ConditionalSafe cell k) :
    (((256 : ℕ).choose (k : ℕ) : ℝ) / 2 ^ 256) *
        thresholdDominantCellConditionalMajorant cell k ≤
      ((rat (((256 : ℕ).choose (k : ℕ) : ℚ) / 2 ^ 256) *
        conditionalMajorant cell k).upperRat : ℝ) := by
  let weight : ℚ := ((256 : ℕ).choose (k : ℕ) : ℚ) / 2 ^ 256
  have hconditional : (conditionalMajorant cell k).Contains
      (thresholdDominantCellConditionalMajorant cell k) := by
    by_cases hk : (k : ℕ) < 29
    · exact contains_conditionalMajorant_of_low cell k hk
    · by_cases hz : cell.z k = 0
      · exact contains_conditionalMajorant_of_zero cell k hk hz
      · have hzpos : 0 < cell.z k :=
          lt_of_le_of_ne (hvalid.2.2.2.2 k) (Ne.symm hz)
        exact contains_conditionalMajorant_of_pos
          cell k hk hzpos (hsafe hk hz)
  have hterm := Interval.contains_mul (contains_rat weight) hconditional
  simpa [weight] using le_upperRat_of_contains hterm

private theorem foldl_weighted_le_upperRat
    (cell : DecodedCell) (hvalid : cell.Valid)
    (hsafe : ∀ k : Fin 257, ¬(k : ℕ) < 29 →
      cell.z k ≠ 0 → ConditionalSafe cell k)
    (indices : List (Fin 257)) (accI : DInterval) (accR : ℝ)
    (hacc : accR ≤ (accI.upperRat : ℝ)) :
    (((indices.foldl
        (fun acc (k : Fin 257) => acc +
          rat (((256 : ℕ).choose (k : ℕ) : ℚ) / 2 ^ 256) *
            conditionalMajorant cell k) accI).upperRat : ℚ) : ℝ) ≥
      indices.foldl
        (fun acc (k : Fin 257) => acc +
          (((256 : ℕ).choose (k : ℕ) : ℝ) / 2 ^ 256) *
            thresholdDominantCellConditionalMajorant cell k) accR := by
  induction indices generalizing accI accR with
  | nil => exact hacc
  | cons k indices ih =>
      simp only [List.foldl_cons]
      apply ih
      rw [upperRat_add]
      exact add_le_add hacc
        (weightedConditional_le_upperRat cell k hvalid (hsafe k))

private theorem foldl_add_eq_add_sum (xs : List ℝ) (a : ℝ) :
    xs.foldl (fun acc x => acc + x) a = a + xs.sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons, ih, List.sum_cons]; ring

private theorem sum_ofFn_eq_finsetSum {n : ℕ} (f : Fin n → ℝ) :
    (List.ofFn f).sum = ∑ k, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ', List.sum_concat, Fin.sum_univ_castSucc, ih]

private theorem foldl_ofFn_eq_sum {f : Fin 257 → ℝ} :
    (List.ofFn f).foldl (fun acc x => acc + x) 0 = ∑ k, f k := by
  rw [foldl_add_eq_add_sum, zero_add, sum_ofFn_eq_finsetSum]

private theorem foldl_ofFn_apply {n : ℕ} {A B : Type*}
    (f : Fin n → B) (op : A → B → A) (init : A) :
    (List.ofFn f).foldl op init =
      (List.finRange n).foldl (fun acc k => op acc (f k)) init := by
  simp only [List.ofFn_eq_map, List.foldl_map]

theorem thresholdMajorant_le_majorantUpper_upperRat
    (cell : DecodedCell) (hvalid : cell.Valid)
    (hsafe : ∀ k : Fin 257, ¬(k : ℕ) < 29 →
      cell.z k ≠ 0 → ConditionalSafe cell k) :
    thresholdDominantCellMajorant cell ≤
      ((majorantUpper cell).upperRat : ℝ) := by
  let term := fun k : Fin 257 =>
    (((256 : ℕ).choose (k : ℕ) : ℝ) / 2 ^ 256) *
      thresholdDominantCellConditionalMajorant cell k
  have hzero : (0 : ℝ) ≤ ((rat 0).upperRat : ℝ) :=
    le_upperRat_of_contains (by simpa using contains_rat (0 : ℚ))
  have hfold := foldl_weighted_le_upperRat cell hvalid hsafe
    (List.finRange 257) (rat 0) 0 hzero
  have hreal :
      (List.ofFn term).foldl (fun acc x => acc + x) 0 = ∑ k, term k :=
    foldl_ofFn_eq_sum
  change (∑ k, term k) ≤ ((majorantUpper cell).upperRat : ℝ)
  rw [← hreal, foldl_ofFn_apply]
  change
    (List.finRange 257).foldl (fun acc k => acc + term k) 0 ≤
      (((List.ofFn fun k : Fin 257 =>
        rat (((256 : ℕ).choose (k : ℕ) : ℚ) / 2 ^ 256) *
          conditionalMajorant cell k).foldl (fun acc x => acc + x)
            (rat 0)).upperRat : ℚ)
  rw [foldl_ofFn_apply]
  exact hfold

/-- A successful kernel-reduced replay proves its exact rational cell budget. -/
theorem localCertifiedCheckAt_sound (cell : DecodedCell) (budget : ℚ)
    (hvalid : cell.Valid)
    (hcheck : localCertifiedCheckAt cell budget = true) :
    thresholdDominantCellMajorant cell < (budget : ℝ) := by
  rw [localCertifiedCheckAt, Bool.and_eq_true] at hcheck
  have hmajorant := thresholdMajorant_le_majorantUpper_upperRat
    cell hvalid (cellNumericSafeCheck_sound hcheck.1)
  have hupper := Interval.upperLTCheck_sound hcheck.2
  have hupperReal :
      ((majorantUpper cell).upperRat : ℝ) < (budget : ℝ) := by
    exact_mod_cast hupper
  exact hmajorant.trans_lt hupperReal

end Numeric
end SparseThresholdDominant
end CertifiedJL
