/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ConstantNumericData
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Soundness.NumericSoundness
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Soundness.TargetNumeric
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Compressed constant-tilt public-threshold dominant cells

The general direct-cell checker reevaluates both row intervals at every
activity count.  For a constant tilt those intervals are identical, so this
checker certifies them once and performs the remaining binomial average over
three short rational upper bounds.  This substantially reduces replay memory.
-/

namespace CertifiedJL
namespace SparseThresholdDominant
namespace ConstantNumeric

open DominantNumeric
open SparseThresholdDominant.Numeric
open scoped BigOperators

private theorem contains_growthInterval (cell : Cell)
    (hsafe : (rat (29 * cell.z * cell.thresholdUpper / 256)).upperRat ≤ 1) :
    (growthInterval cell).Contains
      (Real.exp (29 * (cell.z : ℝ) * (cell.thresholdUpper : ℝ))) := by
  have hbase := contains_expUpper
    (contains_rat (29 * cell.z * cell.thresholdUpper / 256)) hsafe
  have hpow := contains_powNat hbase 256
  unfold growthInterval
  convert hpow using 1
  · rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring

set_option maxHeartbeats 1000000 in
-- Normalizing the public-threshold row interval through the decoded cell is intensive.
private theorem semantic_inactive_bounds (cell : Cell) (certificate : Certificate)
    (hsafe : inactiveRowSafeCheck cell.decode cell.z = true)
    (hupper : (inactiveRow cell.decode cell.z).upperRat ≤
      certificate.inactiveUpper)
    (hlower : 0 ≤ (inactiveRow cell.decode cell.z).lo) :
    0 ≤ thresholdDominantCellInactiveRow cell.lower cell.upper
        cell.modulusLower cell.z ∧
      thresholdDominantCellInactiveRow cell.lower cell.upper
        cell.modulusLower cell.z ≤ (certificate.inactiveUpper : ℝ) := by
  have hcontains := contains_inactiveRow_of_safe
    (inactiveRowSafeCheck_sound hsafe)
  have hnonneg : 0 ≤ thresholdDominantCellInactiveRow cell.lower cell.upper
      cell.modulusLower cell.z := by
    have hloReal : (0 : ℝ) ≤ Dyadic.toReal precision
        (inactiveRow cell.decode cell.z).lo := by
      simpa using Dyadic.toReal_mono (p := precision) hlower
    have hsemanticLower : Dyadic.toReal precision
        (inactiveRow cell.decode cell.z).lo ≤
        thresholdDominantCellInactiveRow cell.lower cell.upper
          cell.modulusLower cell.z := by
      simpa [Cell.decode] using hcontains.1
    exact hloReal.trans hsemanticLower
  have hinterval :
      thresholdDominantCellInactiveRow cell.lower cell.upper
          cell.modulusLower cell.z ≤
        ((inactiveRow cell.decode cell.z).upperRat : ℝ) := by
    simpa [Cell.decode, Interval.upperRat, Dyadic.cast_toRat] using hcontains.2
  exact ⟨hnonneg, hinterval.trans (by exact_mod_cast hupper)⟩

set_option maxHeartbeats 1000000 in
-- Normalizing the shifted public-threshold row interval through the decoded cell is intensive.
private theorem semantic_active_bounds (cell : Cell) (certificate : Certificate)
    (hsafe : activeRowSafeCheck cell.decode cell.z = true)
    (hupper : (activeRow cell.decode cell.z).upperRat ≤
      certificate.activeUpper)
    (hlower : 0 ≤ (activeRow cell.decode cell.z).lo) :
    0 ≤ thresholdDominantCellActiveRow cell.lower cell.upper
        cell.modulusLower cell.z ∧
      thresholdDominantCellActiveRow cell.lower cell.upper
        cell.modulusLower cell.z ≤ (certificate.activeUpper : ℝ) := by
  have hcontains := contains_activeRow_of_safe
    (activeRowSafeCheck_sound hsafe)
  have hnonneg : 0 ≤ thresholdDominantCellActiveRow cell.lower cell.upper
      cell.modulusLower cell.z := by
    have hloReal : (0 : ℝ) ≤ Dyadic.toReal precision
        (activeRow cell.decode cell.z).lo := by
      simpa using Dyadic.toReal_mono (p := precision) hlower
    have hsemanticLower : Dyadic.toReal precision
        (activeRow cell.decode cell.z).lo ≤
        thresholdDominantCellActiveRow cell.lower cell.upper
          cell.modulusLower cell.z := by
      simpa [Cell.decode] using hcontains.1
    exact hloReal.trans hsemanticLower
  have hinterval :
      thresholdDominantCellActiveRow cell.lower cell.upper
          cell.modulusLower cell.z ≤
        ((activeRow cell.decode cell.z).upperRat : ℝ) := by
    simpa [Cell.decode, Interval.upperRat, Dyadic.cast_toRat] using hcontains.2
  exact ⟨hnonneg, hinterval.trans (by exact_mod_cast hupper)⟩

private theorem semantic_growth_le (cell : Cell) (certificate : Certificate)
    (hsafe : (rat (29 * cell.z * cell.thresholdUpper / 256)).upperRat ≤ 1)
    (hupper : (growthInterval cell).upperRat ≤ certificate.growthUpper) :
    Real.exp (29 * (cell.z : ℝ) * (cell.thresholdUpper : ℝ)) ≤
      (certificate.growthUpper : ℝ) := by
  have hcontains := contains_growthInterval cell hsafe
  have hinterval :
      Real.exp (29 * (cell.z : ℝ) * (cell.thresholdUpper : ℝ)) ≤
        ((growthInterval cell).upperRat : ℝ) := by
    simpa [Interval.upperRat, Dyadic.cast_toRat] using hcontains.2
  exact hinterval.trans (by exact_mod_cast hupper)

private theorem conditional_le (cell : Cell) (certificate : Certificate)
    (hcell : cell.Valid) (hcertificate : certificate.Valid)
    (hinactive : thresholdDominantCellInactiveRow cell.lower cell.upper
        cell.modulusLower cell.z ≤ (certificate.inactiveUpper : ℝ))
    (hinactiveNonneg : 0 ≤ thresholdDominantCellInactiveRow cell.lower cell.upper
        cell.modulusLower cell.z)
    (hactive : thresholdDominantCellActiveRow cell.lower cell.upper
        cell.modulusLower cell.z ≤ (certificate.activeUpper : ℝ))
    (hactiveNonneg : 0 ≤ thresholdDominantCellActiveRow cell.lower cell.upper
        cell.modulusLower cell.z)
    (hgrowth : Real.exp (29 * (cell.z : ℝ) *
        (cell.thresholdUpper : ℝ)) ≤ (certificate.growthUpper : ℝ))
    (k : Fin 257) :
    thresholdDominantCellConditionalMajorant cell.decode k ≤
      (conditionalUpper certificate k : ℝ) := by
  by_cases hk : (k : ℕ) < 29
  · simp [thresholdDominantCellConditionalMajorant, conditionalUpper, hk]
  have hz : cell.z ≠ 0 := ne_of_gt hcell.2
  rw [thresholdDominantCellConditionalMajorant]
  simp only [Cell.decode, hk, if_false, hz]
  rw [conditionalUpper, if_neg hk]
  push_cast
  apply min_le_min_left
  have hactivePow := pow_le_pow_left₀ hactiveNonneg hactive (k : ℕ)
  have hinactivePow := pow_le_pow_left₀ hinactiveNonneg hinactive
    (256 - (k : ℕ))
  have hcertificateGrowth : (0 : ℝ) ≤ certificate.growthUpper := by
    exact_mod_cast hcertificate.2.2
  have hcertificateActive : (0 : ℝ) ≤ certificate.activeUpper := by
    exact_mod_cast hcertificate.2.1
  have hfirst := mul_le_mul hgrowth hactivePow
    (pow_nonneg hactiveNonneg _) hcertificateGrowth
  have hsecond := mul_le_mul hfirst hinactivePow
    (pow_nonneg hinactiveNonneg _)
    (mul_nonneg hcertificateGrowth
      (pow_nonneg hcertificateActive _))
  simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_min, Rat.cast_one] using hsecond

private theorem sum_ofFn_eq_finsetSum {R : Type*} [AddCommMonoid R]
    {n : ℕ} (f : Fin n → R) :
    (List.ofFn f).sum = ∑ k, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ', List.sum_concat, Fin.sum_univ_castSucc, ih]

/-! ### Generic geometric-tail arithmetic -/

/-- A finite nonnegative sequence whose successive terms contract by at most
`ratio` is bounded by the corresponding infinite geometric series. -/
theorem sum_Ico_le_geometric (a : ℕ → ℚ) (start stop : ℕ) (ratio : ℚ)
    (hstart : start ≤ stop) (ha : ∀ k, 0 ≤ a k)
    (hratioNonneg : 0 ≤ ratio) (hratioLt : ratio < 1)
    (hstep : ∀ k, start ≤ k → k < stop →
      a (k + 1) ≤ ratio * a k) :
    ∑ k ∈ Finset.Ico start (stop + 1), a k ≤
      a start / (1 - ratio) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hpow : ∀ i, start + i ≤ stop →
      a (start + i) ≤ a start * ratio ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      intro hi
      calc
        a (start + (i + 1)) = a (start + i + 1) := by
          simp [Nat.add_assoc]
        _ ≤ ratio * a (start + i) := hstep (start + i) (by omega) (by omega)
        _ ≤ ratio * (a start * ratio ^ i) :=
          mul_le_mul_of_nonneg_left (ih (by omega)) hratioNonneg
        _ = a start * ratio ^ (i + 1) := by rw [pow_succ]; ring
  calc
    (∑ k ∈ Finset.range (stop + 1 - start), a (start + k)) ≤
        ∑ k ∈ Finset.range (stop + 1 - start),
          a start * ratio ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      apply hpow
      simp only [Finset.mem_range] at hk
      omega
    _ = a start * ∑ k ∈ Finset.range (stop + 1 - start),
        ratio ^ k := by rw [Finset.mul_sum]
    _ ≤ a start * (1 / (1 - ratio)) := by
      apply mul_le_mul_of_nonneg_left _ (ha start)
      simpa [Nat.Ico_zero_eq_range] using
        (geom_sum_Ico_le_of_lt_one (m := 0) (n := stop + 1 - start)
          hratioNonneg hratioLt)
    _ = a start / (1 - ratio) := by ring

private theorem weightedRawTermRat_cross (rows k : ℕ) (hk : k < rows)
    (growth active inactive : ℚ) :
    weightedRawTermRat rows growth active inactive (k + 1) *
        (((k + 1 : ℕ) : ℚ) * inactive) =
      weightedRawTermRat rows growth active inactive k *
        (((rows - k : ℕ) : ℚ) * active) := by
  unfold weightedRawTermRat
  simp only [← Nat.choose_eq_fast_choose]
  have hpow : inactive ^ (rows - k) =
      inactive ^ (rows - (k + 1)) * inactive := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpow, pow_succ]
  have hc := Nat.choose_succ_right_eq rows k
  have hc' : (rows.choose (k + 1) : ℚ) * (((k + 1 : ℕ) : ℚ)) =
      (rows.choose k : ℚ) * (((rows - k : ℕ) : ℚ)) := by
    exact_mod_cast hc
  field_simp
  linear_combination
    (growth * active ^ k * active * inactive ^ (rows - (k + 1)) * inactive) * hc'

private theorem weightedRawTermRat_nonneg (rows : ℕ)
    (growth active inactive : ℚ) (hgrowth : 0 ≤ growth)
    (hactive : 0 ≤ active) (hinactive : 0 ≤ inactive) (k : ℕ) :
    0 ≤ weightedRawTermRat rows growth active inactive k := by
  unfold weightedRawTermRat
  positivity

private theorem weightedRawTermRat_step_le (rows start k : ℕ)
    (growth active inactive ratio : ℚ)
    (hkstart : start ≤ k) (hkrows : k < rows)
    (hgrowth : 0 ≤ growth) (hactive : 0 ≤ active)
    (hinactive : 0 < inactive) (hratioNonneg : 0 ≤ ratio)
    (hratio : ((rows - start : ℕ) : ℚ) * active ≤
      ratio * (((start + 1 : ℕ) : ℚ)) * inactive) :
    weightedRawTermRat rows growth active inactive (k + 1) ≤
      ratio * weightedRawTermRat rows growth active inactive k := by
  have hcross := weightedRawTermRat_cross rows k hkrows growth active inactive
  have hleft : ((rows - k : ℕ) : ℚ) * active ≤
      ((rows - start : ℕ) : ℚ) * active := by
    gcongr
  have hright : ratio * (((start + 1 : ℕ) : ℚ)) * inactive ≤
      ratio * (((k + 1 : ℕ) : ℚ)) * inactive := by
    gcongr
  have hratio' : ((rows - k : ℕ) : ℚ) * active ≤
      ratio * (((k + 1 : ℕ) : ℚ)) * inactive :=
    hleft.trans (hratio.trans hright)
  have hden : 0 < (((k + 1 : ℕ) : ℚ) * inactive) := by positivity
  rw [← mul_le_mul_iff_left₀ hden]
  rw [hcross]
  calc
    weightedRawTermRat rows growth active inactive k *
        (((rows - k : ℕ) : ℚ) * active) ≤
      weightedRawTermRat rows growth active inactive k *
        (ratio * (((k + 1 : ℕ) : ℚ)) * inactive) :=
        mul_le_mul_of_nonneg_left hratio'
          (weightedRawTermRat_nonneg rows growth active inactive
            hgrowth hactive hinactive.le k)
    _ = ratio * weightedRawTermRat rows growth active inactive k *
        (((k + 1 : ℕ) : ℚ) * inactive) := by ring

/-- The complete truncated binomial sum is bounded by a checked exact prefix
and geometric remainder. -/
theorem weightedConditionalSum_le_prefixGeometric (rows squaredNormFloor : ℕ)
    (growth active inactive : ℚ) (tail : GeometricTailCertificate)
    (htailStart : squaredNormFloor + tail.prefixTerms ≤ rows)
    (hgrowth : 0 ≤ growth) (hactive : 0 ≤ active)
    (hinactive : 0 < inactive) (hratioNonneg : 0 ≤ tail.ratioUpper)
    (hratioLt : tail.ratioUpper < 1)
    (hratio : ((rows - (squaredNormFloor + tail.prefixTerms) : ℕ) : ℚ) *
        active ≤ tail.ratioUpper *
          (((squaredNormFloor + tail.prefixTerms + 1 : ℕ) : ℚ)) * inactive) :
    (∑ k ∈ Finset.range (rows + 1),
      weightedConditionalTermRat rows squaredNormFloor growth active inactive k) ≤
      prefixGeometricUpperRat rows squaredNormFloor growth active inactive tail := by
  let tailStart := squaredNormFloor + tail.prefixTerms
  let conditional := weightedConditionalTermRat rows squaredNormFloor
    growth active inactive
  let raw := weightedRawTermRat rows growth active inactive
  have hfloorStart : squaredNormFloor ≤ tailStart := by
    simp [tailStart]
  have hstartRows : tailStart ≤ rows := by
    simpa [tailStart] using htailStart
  have hzero : (∑ k ∈ Finset.range squaredNormFloor, conditional k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : k < squaredNormFloor := Finset.mem_range.mp hk
    simp [conditional, weightedConditionalTermRat, hk']
  have hprefix : (∑ k ∈ Finset.range tailStart, conditional k) =
      ∑ k ∈ Finset.Ico squaredNormFloor tailStart, conditional k := by
    have hsplit := Finset.sum_range_add_sum_Ico conditional hfloorStart
    rw [hzero, zero_add] at hsplit
    exact hsplit.symm
  have hconditionalRaw : ∀ k, tailStart ≤ k → k ≤ rows →
      conditional k ≤ raw k := by
    intro k hkstart hkrows
    have hkfloor : ¬ k < squaredNormFloor :=
      not_lt_of_ge (hfloorStart.trans hkstart)
    simp only [conditional, raw, weightedConditionalTermRat,
      weightedRawTermRat, hkfloor, if_false]
    rw [← Nat.choose_eq_fast_choose]
    have hcoefficient : (0 : ℚ) ≤ (rows.choose k : ℚ) / 2 ^ rows := by
      positivity
    calc
      (rows.choose k : ℚ) *
          min 1 (growth * active ^ k * inactive ^ (rows - k)) / 2 ^ rows =
        ((rows.choose k : ℚ) / 2 ^ rows) *
          min 1 (growth * active ^ k * inactive ^ (rows - k)) := by ring
      _ ≤ ((rows.choose k : ℚ) / 2 ^ rows) *
          (growth * active ^ k * inactive ^ (rows - k)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hcoefficient
      _ = (rows.choose k : ℚ) * growth * active ^ k *
          inactive ^ (rows - k) / 2 ^ rows := by ring
  have hrawNonneg : ∀ k, 0 ≤ raw k := by
    intro k
    exact weightedRawTermRat_nonneg rows growth active inactive
      hgrowth hactive hinactive.le k
  have hrawStep : ∀ k, tailStart ≤ k → k < rows →
      raw (k + 1) ≤ tail.ratioUpper * raw k := by
    intro k hkstart hkrows
    apply weightedRawTermRat_step_le rows tailStart k growth active inactive
      tail.ratioUpper hkstart hkrows hgrowth hactive hinactive hratioNonneg
    simpa [tailStart] using hratio
  have htailGeometric :
      (∑ k ∈ Finset.Ico tailStart (rows + 1), raw k) ≤
        raw tailStart / (1 - tail.ratioUpper) :=
    sum_Ico_le_geometric raw tailStart rows tail.ratioUpper hstartRows
      hrawNonneg hratioNonneg hratioLt hrawStep
  have hsplit := Finset.sum_range_add_sum_Ico conditional
    (show tailStart ≤ rows + 1 by omega)
  rw [← hsplit, hprefix]
  unfold prefixGeometricUpperRat
  simp only [tailStart, conditional]
  apply add_le_add (le_refl _)
  exact (Finset.sum_le_sum fun k hk =>
      hconditionalRaw k (Finset.mem_Ico.mp hk).1
        (by have := (Finset.mem_Ico.mp hk).2; omega : k ≤ rows)).trans
    htailGeometric

private theorem majorantUpper_eq_weightedConditionalSum
    (certificate : Certificate) :
    majorantUpper certificate =
      ∑ k ∈ Finset.range (256 + 1),
        weightedConditionalTermRat 256 29 certificate.growthUpper
          certificate.activeUpper certificate.inactiveUpper k := by
  rw [majorantUpper, binomialAverageRat_eq, sum_ofFn_eq_finsetSum]
  calc
    (∑ k : Fin 257, (((256 : ℕ).choose (k : ℕ) : ℚ) / 2 ^ 256) *
        conditionalUpper certificate k) =
      ∑ k : Fin 257,
        weightedConditionalTermRat 256 29 certificate.growthUpper
          certificate.activeUpper certificate.inactiveUpper (k : ℕ) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [conditionalUpper, weightedConditionalTermRat,
        ← Nat.choose_eq_fast_choose]
      split <;> ring
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun k => weightedConditionalTermRat 256 29 certificate.growthUpper
        certificate.activeUpper certificate.inactiveUpper k) 257

private theorem majorantUpperAt_eq_weightedConditionalSum
    (rows squaredNormFloor : ℕ) (cell : Cell) (certificate : Certificate) :
    majorantUpperAt rows squaredNormFloor cell certificate =
      ∑ k ∈ Finset.range (rows + 1),
        weightedConditionalTermRat rows squaredNormFloor
          (growthIntervalAt rows squaredNormFloor cell).upperRat
          certificate.activeUpper certificate.inactiveUpper k := by
  rw [majorantUpperAt, binomialAverageRat_eq, sum_ofFn_eq_finsetSum]
  calc
    (∑ k : Fin (rows + 1), ((rows.choose (k : ℕ) : ℚ) / 2 ^ rows) *
        conditionalUpperAt rows squaredNormFloor cell certificate k) =
      ∑ k : Fin (rows + 1),
        weightedConditionalTermRat rows squaredNormFloor
          (growthIntervalAt rows squaredNormFloor cell).upperRat
          certificate.activeUpper certificate.inactiveUpper (k : ℕ) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [conditionalUpperAt, weightedConditionalTermRat,
        ← Nat.choose_eq_fast_choose]
      split <;> ring
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun k => weightedConditionalTermRat rows squaredNormFloor
        (growthIntervalAt rows squaredNormFloor cell).upperRat
        certificate.activeUpper certificate.inactiveUpper k) (rows + 1)

set_option maxRecDepth 10000 in
private theorem majorant_le (cell : Cell) (certificate : Certificate)
    (hcell : cell.Valid) (hcertificate : certificate.Valid)
    (hinactive : thresholdDominantCellInactiveRow cell.lower cell.upper
        cell.modulusLower cell.z ≤ (certificate.inactiveUpper : ℝ))
    (hinactiveNonneg : 0 ≤ thresholdDominantCellInactiveRow cell.lower
        cell.upper cell.modulusLower cell.z)
    (hactive : thresholdDominantCellActiveRow cell.lower cell.upper
        cell.modulusLower cell.z ≤ (certificate.activeUpper : ℝ))
    (hactiveNonneg : 0 ≤ thresholdDominantCellActiveRow cell.lower
        cell.upper cell.modulusLower cell.z)
    (hgrowth : Real.exp (29 * (cell.z : ℝ) *
        (cell.thresholdUpper : ℝ)) ≤ (certificate.growthUpper : ℝ)) :
    thresholdDominantCellMajorant cell.decode ≤
      (majorantUpper certificate : ℝ) := by
  unfold thresholdDominantCellMajorant dominantBinomialAverage
  calc
    (∑ k : Fin 257, (((256 : ℕ).choose (k : ℕ) : ℝ) / 2 ^ 256) *
        thresholdDominantCellConditionalMajorant cell.decode k) ≤
      ∑ k : Fin 257, (((256 : ℕ).choose (k : ℕ) : ℝ) / 2 ^ 256) *
        (conditionalUpper certificate k : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          exact mul_le_mul_of_nonneg_left
            (conditional_le cell certificate hcell hcertificate
              hinactive hinactiveNonneg hactive hactiveNonneg hgrowth k)
            (by positivity)
    _ = (majorantUpper certificate : ℝ) := by
      rw [majorantUpper, binomialAverageRat_eq, sum_ofFn_eq_finsetSum]
      push_cast
      rfl

/-- A successful compressed replay proves the semantic direct-cell budget. -/
theorem localCertifiedCheckAt_sound (cell : Cell) (certificate : Certificate)
    (budget : ℚ) (hcell : cell.Valid) (hcertificate : certificate.Valid)
    (hcheck : localCertifiedCheckAt cell certificate budget = true) :
    thresholdDominantCellMajorant cell.decode < (budget : ℝ) := by
  have hchecks : rowCapsCheck cell certificate = true ∧
      localTargetCheckAt cell certificate budget = true := by
    simpa only [localCertifiedCheckAt, Bool.and_eq_true] using hcheck
  have hcaps := rowCapsCheck_sound cell certificate hchecks.1
  rcases hcaps with
    ⟨hinactiveSafe, hactiveSafe, hinactiveUpper, hactiveUpper,
      hinactiveLower, hactiveLower⟩
  have htarget := of_decide_eq_true (by
    simpa only [localTargetCheckAt] using hchecks.2)
  rcases htarget with ⟨hgrowthSafe, hgrowthUpper, hbudget⟩
  have hinactive := semantic_inactive_bounds cell certificate
    hinactiveSafe hinactiveUpper hinactiveLower
  have hactive := semantic_active_bounds cell certificate
    hactiveSafe hactiveUpper hactiveLower
  have hgrowth := semantic_growth_le cell certificate hgrowthSafe hgrowthUpper
  exact (majorant_le cell certificate hcell hcertificate
    hinactive.2 hinactive.1 hactive.2 hactive.1 hgrowth).trans_lt
      (by exact_mod_cast hbudget)

/-- A successful prefix/geometric replay proves the same semantic direct-cell
budget as the complete exact sum. -/
theorem localCertifiedGeometricCheckAt_sound (cell : Cell)
    (certificate : Certificate) (tail : GeometricTailCertificate)
    (budget : ℚ) (hcell : cell.Valid) (hcertificate : certificate.Valid)
    (hcheck : localCertifiedGeometricCheckAt cell certificate tail budget = true) :
    thresholdDominantCellMajorant cell.decode < (budget : ℝ) := by
  have h := of_decide_eq_true (by
    simpa only [localCertifiedGeometricCheckAt] using hcheck)
  rcases h with
    ⟨hinactiveSafe, hactiveSafe, hinactiveUpper, hactiveUpper,
      hinactiveLower, hactiveLower, hgrowthSafe, hgrowthUpper,
      htailStart, hinactivePositive, hactiveNonneg, hratioNonneg,
      hratioLt, hratio, hbudget⟩
  have hinactive := semantic_inactive_bounds cell certificate
    hinactiveSafe hinactiveUpper hinactiveLower
  have hactive := semantic_active_bounds cell certificate
    hactiveSafe hactiveUpper hactiveLower
  have hgrowth := semantic_growth_le cell certificate hgrowthSafe hgrowthUpper
  have hratio' : ((256 - (29 + tail.prefixTerms) : ℕ) : ℚ) *
      certificate.activeUpper ≤ tail.ratioUpper *
        (((29 + tail.prefixTerms + 1 : ℕ) : ℚ)) *
          certificate.inactiveUpper := by
    rw [Nat.cast_sub htailStart]
    simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using hratio
  have hsum : majorantUpper certificate ≤
      prefixGeometricUpper certificate tail := by
    rw [majorantUpper_eq_weightedConditionalSum]
    exact weightedConditionalSum_le_prefixGeometric 256 29
      certificate.growthUpper certificate.activeUpper certificate.inactiveUpper
      tail htailStart hcertificate.2.2 hactiveNonneg hinactivePositive
      hratioNonneg hratioLt hratio'
  have hsumReal : (majorantUpper certificate : ℝ) ≤
      (prefixGeometricUpper certificate tail : ℝ) := by
    exact_mod_cast hsum
  exact ((majorant_le cell certificate hcell hcertificate
    hinactive.2 hinactive.1 hactive.2 hactive.1 hgrowth).trans hsumReal).trans_lt
      (by exact_mod_cast hbudget)

private theorem semantic_growth_leAt (rows squaredNormFloor : ℕ)
    (cell : Cell) (hrows : 0 < rows)
    (hsafe : (rat (squaredNormFloor * cell.z * cell.thresholdUpper / rows)).upperRat ≤ 1) :
    Real.exp (squaredNormFloor * (cell.z : ℝ) *
        (cell.thresholdUpper : ℝ)) ≤
      ((growthIntervalAt rows squaredNormFloor cell).upperRat : ℝ) := by
  simpa only [growthIntervalAt] using
    (TargetNumeric.growth_le_upperRat rows squaredNormFloor cell.z
      cell.thresholdUpper hrows hsafe)

private theorem conditional_leAt (rows squaredNormFloor : ℕ)
    (cell : Cell) (certificate : Certificate)
    (hcell : cell.Valid) (hcertificate : certificate.Valid)
    (hinactive : thresholdDominantCellInactiveRow cell.lower cell.upper
        cell.modulusLower cell.z ≤ (certificate.inactiveUpper : ℝ))
    (hinactiveNonneg : 0 ≤ thresholdDominantCellInactiveRow cell.lower cell.upper
        cell.modulusLower cell.z)
    (hactive : thresholdDominantCellActiveRow cell.lower cell.upper
        cell.modulusLower cell.z ≤ (certificate.activeUpper : ℝ))
    (hactiveNonneg : 0 ≤ thresholdDominantCellActiveRow cell.lower cell.upper
        cell.modulusLower cell.z)
    (hgrowth : Real.exp (squaredNormFloor * (cell.z : ℝ) *
        (cell.thresholdUpper : ℝ)) ≤
      ((growthIntervalAt rows squaredNormFloor cell).upperRat : ℝ))
    (k : Fin (rows + 1)) :
    thresholdDominantCellConditionalMajorantAt rows squaredNormFloor
        (cell.decodeAt rows) k ≤
      (conditionalUpperAt rows squaredNormFloor cell certificate k : ℝ) := by
  by_cases hk : (k : ℕ) < squaredNormFloor
  · simp [thresholdDominantCellConditionalMajorantAt, conditionalUpperAt, hk]
  have hz : cell.z ≠ 0 := ne_of_gt hcell.2
  rw [thresholdDominantCellConditionalMajorantAt]
  simp only [Cell.decodeAt, hk, if_false, hz]
  rw [conditionalUpperAt, if_neg hk]
  push_cast
  apply min_le_min_left
  have hactivePow := pow_le_pow_left₀ hactiveNonneg hactive (k : ℕ)
  have hinactivePow := pow_le_pow_left₀ hinactiveNonneg hinactive
    (rows - (k : ℕ))
  have hgrowthNonneg : (0 : ℝ) ≤
      (growthIntervalAt rows squaredNormFloor cell).upperRat :=
    (Real.exp_nonneg _).trans hgrowth
  have hcertificateActive : (0 : ℝ) ≤ certificate.activeUpper := by
    exact_mod_cast hcertificate.2.1
  have hfirst := mul_le_mul hgrowth hactivePow
    (pow_nonneg hactiveNonneg _) hgrowthNonneg
  have hsecond := mul_le_mul hfirst hinactivePow
    (pow_nonneg hinactiveNonneg _)
    (mul_nonneg hgrowthNonneg (pow_nonneg hcertificateActive _))
  simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_min, Rat.cast_one] using hsecond

set_option maxRecDepth 10000 in
private theorem majorant_leAt (rows squaredNormFloor : ℕ)
    (cell : Cell) (certificate : Certificate)
    (hcell : cell.Valid) (hcertificate : certificate.Valid)
    (hinactive : thresholdDominantCellInactiveRow cell.lower cell.upper
        cell.modulusLower cell.z ≤ (certificate.inactiveUpper : ℝ))
    (hinactiveNonneg : 0 ≤ thresholdDominantCellInactiveRow cell.lower
        cell.upper cell.modulusLower cell.z)
    (hactive : thresholdDominantCellActiveRow cell.lower cell.upper
        cell.modulusLower cell.z ≤ (certificate.activeUpper : ℝ))
    (hactiveNonneg : 0 ≤ thresholdDominantCellActiveRow cell.lower
        cell.upper cell.modulusLower cell.z)
    (hgrowth : Real.exp (squaredNormFloor * (cell.z : ℝ) *
        (cell.thresholdUpper : ℝ)) ≤
      ((growthIntervalAt rows squaredNormFloor cell).upperRat : ℝ)) :
    thresholdDominantCellMajorantAt rows squaredNormFloor (cell.decodeAt rows) ≤
      (majorantUpperAt rows squaredNormFloor cell certificate : ℝ) := by
  unfold thresholdDominantCellMajorantAt dominantBinomialAverageAt
  calc
    (∑ k : Fin (rows + 1), ((rows.choose (k : ℕ) : ℝ) / 2 ^ rows) *
        thresholdDominantCellConditionalMajorantAt rows squaredNormFloor
          (cell.decodeAt rows) k) ≤
      ∑ k : Fin (rows + 1), ((rows.choose (k : ℕ) : ℝ) / 2 ^ rows) *
        (conditionalUpperAt rows squaredNormFloor cell certificate k : ℝ) := by
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_of_nonneg_left
            (conditional_leAt rows squaredNormFloor cell certificate hcell hcertificate
              hinactive hinactiveNonneg hactive hactiveNonneg hgrowth k)
            (by positivity)
    _ = (majorantUpperAt rows squaredNormFloor cell certificate : ℝ) := by
      rw [majorantUpperAt, binomialAverageRat_eq, sum_ofFn_eq_finsetSum]
      push_cast
      rfl

/-- Soundness of target-dependent constant-cell replay. -/
theorem localCertifiedCheckFor_sound (rows squaredNormFloor : ℕ)
    (cell : Cell) (certificate : Certificate) (budget : ℚ)
    (hcell : cell.Valid) (hcertificate : certificate.Valid)
    (hcheck : localCertifiedCheckFor rows squaredNormFloor cell certificate budget = true) :
    thresholdDominantCellMajorantAt rows squaredNormFloor (cell.decodeAt rows) <
      (budget : ℝ) := by
  have hchecks : rowCapsCheck cell certificate = true ∧
      localTargetCheckFor rows squaredNormFloor cell certificate budget = true := by
    simpa only [localCertifiedCheckFor, Bool.and_eq_true] using hcheck
  have hcaps := rowCapsCheck_sound cell certificate hchecks.1
  rcases hcaps with
    ⟨hinactiveSafe, hactiveSafe, hinactiveUpper, hactiveUpper,
      hinactiveLower, hactiveLower⟩
  have htarget := of_decide_eq_true (by
    simpa only [localTargetCheckFor] using hchecks.2)
  rcases htarget with ⟨hrows, hgrowthSafe, hbudget⟩
  have hinactive := semantic_inactive_bounds cell certificate
    hinactiveSafe hinactiveUpper hinactiveLower
  have hactive := semantic_active_bounds cell certificate
    hactiveSafe hactiveUpper hactiveLower
  have hgrowth := semantic_growth_leAt rows squaredNormFloor cell hrows hgrowthSafe
  exact (majorant_leAt rows squaredNormFloor cell certificate hcell hcertificate
    hinactive.2 hinactive.1 hactive.2 hactive.1 hgrowth).trans_lt
      (by exact_mod_cast hbudget)

/-- Soundness of the target-dependent prefix/geometric replay. -/
theorem localCertifiedGeometricCheckFor_sound (rows squaredNormFloor : ℕ)
    (cell : Cell) (certificate : Certificate)
    (tail : GeometricTailCertificate) (budget : ℚ)
    (hcell : cell.Valid) (hcertificate : certificate.Valid)
    (hcheck : localCertifiedGeometricCheckFor rows squaredNormFloor cell
      certificate tail budget = true) :
    thresholdDominantCellMajorantAt rows squaredNormFloor (cell.decodeAt rows) <
      (budget : ℝ) := by
  have h := of_decide_eq_true (by
    simpa only [localCertifiedGeometricCheckFor] using hcheck)
  rcases h with
    ⟨hrows, hinactiveSafe, hactiveSafe, hinactiveUpper, hactiveUpper,
      hinactiveLower, hactiveLower, hgrowthSafe, htailStart, hgrowthNonneg,
      hinactivePositive, hactiveNonneg, hratioNonneg, hratioLt, hratio,
      hbudget⟩
  have hinactive := semantic_inactive_bounds cell certificate
    hinactiveSafe hinactiveUpper hinactiveLower
  have hactive := semantic_active_bounds cell certificate
    hactiveSafe hactiveUpper hactiveLower
  have hgrowth := semantic_growth_leAt rows squaredNormFloor cell hrows hgrowthSafe
  have hratio' :
      ((rows - (squaredNormFloor + tail.prefixTerms) : ℕ) : ℚ) *
          certificate.activeUpper ≤ tail.ratioUpper *
        (((squaredNormFloor + tail.prefixTerms + 1 : ℕ) : ℚ)) *
          certificate.inactiveUpper := by
    rw [Nat.cast_sub htailStart]
    simpa only [Nat.cast_add, Nat.cast_one] using hratio
  have hsum : majorantUpperAt rows squaredNormFloor cell certificate ≤
      prefixGeometricUpperAt rows squaredNormFloor cell certificate tail := by
    rw [majorantUpperAt_eq_weightedConditionalSum]
    exact weightedConditionalSum_le_prefixGeometric rows squaredNormFloor
      (growthIntervalAt rows squaredNormFloor cell).upperRat
      certificate.activeUpper certificate.inactiveUpper tail htailStart
      hgrowthNonneg hactiveNonneg hinactivePositive hratioNonneg hratioLt hratio'
  have hsumReal : (majorantUpperAt rows squaredNormFloor cell certificate : ℝ) ≤
      (prefixGeometricUpperAt rows squaredNormFloor cell certificate tail : ℝ) := by
    exact_mod_cast hsum
  exact ((majorant_leAt rows squaredNormFloor cell certificate hcell hcertificate
    hinactive.2 hinactive.1 hactive.2 hactive.1 hgrowth).trans hsumReal).trans_lt
      (by exact_mod_cast hbudget)

/-- Extract a semantic bound for any member of a kernel-replayed shard. -/
theorem entry_bound_of_mem_of_checks (entries : List Entry) (budget : ℚ)
    (hvalid : entriesValidCheck entries = true)
    (hcertified : entriesCertifiedCheckAt entries budget = true)
    {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorant entry.cell.decode < (budget : ℝ) := by
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  rw [entriesCertifiedCheckAt, List.all_eq_true] at hcertified
  have hv := entryValidCheck_sound (hvalid entry hmem)
  exact localCertifiedCheckAt_sound entry.cell entry.certificate budget
    hv.1 hv.2 (hcertified entry hmem)

/-- Extract a generic semantic bound for any member of a target-dependent
kernel replay. -/
theorem entry_boundAt_of_mem_of_checks (rows squaredNormFloor : ℕ)
    (entries : List Entry) (budget : ℚ)
    (hvalid : entriesValidCheck entries = true)
    (hcertified : entriesCertifiedCheckFor rows squaredNormFloor entries budget = true)
    {entry : Entry} (hmem : entry ∈ entries) :
    thresholdDominantCellMajorantAt rows squaredNormFloor
        (entry.cell.decodeAt rows) < (budget : ℝ) := by
  rw [entriesValidCheck, List.all_eq_true] at hvalid
  rw [entriesCertifiedCheckFor, List.all_eq_true] at hcertified
  have hv := entryValidCheck_sound (hvalid entry hmem)
  exact localCertifiedCheckFor_sound rows squaredNormFloor entry.cell
    entry.certificate budget hv.1 hv.2 (hcertified entry hmem)

end ConstantNumeric
end SparseThresholdDominant
end CertifiedJL
