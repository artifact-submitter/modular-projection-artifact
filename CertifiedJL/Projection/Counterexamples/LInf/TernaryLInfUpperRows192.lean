/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Interval.Reflection
import CertifiedJL.Probability.Distributions.Binomial.LocalLimit
import CertifiedJL.Probability.Product.RowTensorization
import CertifiedJL.Projection.Counterexamples.Shared.SparseAllOnesRow
import CertifiedJL.Statements.LInf.Upper
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# A finite 192-row obstruction for the balanced-ternary L-infinity upper tail

This file supplies the finite obstruction showing that the `487/50` upper threshold cannot
have a 134-bit failure budget.  The witness is the all-ones vector in dimension `500^2`, and
the modulus `2d+1` makes centered reduction inactive on every possible row sum.  A public
alias below is registered alongside the literal obstruction wrapper.

The numerical core is not a large binomial-coefficient computation.  A local-limit lower
bound controls the mass at the first failing lattice point `4871`; the next 128 masses are
bounded below by an exact geometric progression.  All remaining numerical comparisons use
exact rational reflection.
-/

set_option Elab.async false

open scoped BigOperators ENNReal
open MeasureTheory

namespace CertifiedJL
open Probability
namespace Counterexamples.TernaryLInfUpperRows192

abbrev side : ℕ := 500
abbrev dimension : ℕ := side ^ 2
abbrev firstBad : ℕ := 4871
abbrev prefixLength : ℕ := 128
abbrev modulus : ℕ := 2 * dimension + 1

noncomputable def ratio : ℝ := (245002 : ℝ) / 254999

def parameters : LInfUpperParameters :=
  { distribution := .balancedTernary
    rows := 192
    coordinateThreshold :=
      { numerator := 487, denominator := 50, denominator_pos := by decide } }

abbrev witness : Fin dimension → ℤ := fun _ => 1

def rowBad (row : Fin dimension → ℤ) : Prop :=
  firstBad ≤ (∑ i, row i).natAbs

instance rowBadDecidable : DecidablePred rowBad := by
  intro row
  unfold rowBad
  infer_instance

/-! ## Reflected lower bound for `exp (-95)` -/

def expPrecision : ℕ := 256
def expSquarings : ℕ := 24

private def expNegInterval (x : ℚ) : Interval expPrecision :=
  ⟨((Exp.posBase expPrecision x expSquarings).squareN expSquarings).reciprocal.lo,
    (Exp.negUpper expPrecision x expSquarings).hi⟩

private theorem expNegInterval_contains {x : ℚ}
    (hx : 0 ≤ x) (hupper : x < (2 ^ expSquarings : ℕ))
    (hbase : 0 < (Interval.ofRat expPrecision
      (1 - x / (2 ^ expSquarings : ℕ))).lo)
    (hrawPos : 0 <
      ((Exp.posBase expPrecision x expSquarings).squareN expSquarings).lo) :
    (expNegInterval x).Contains (Real.exp (-(x : ℝ))) := by
  let argument : ℚ := x / (2 ^ expSquarings : ℕ)
  have hdiff :
      (Interval.ofRat expPrecision (1 - argument)).Contains
        (1 - (argument : ℝ)) := by
    simpa [argument] using
      Interval.contains_ofRat expPrecision (1 - argument)
  have hbaseContains :
      (Exp.posBase expPrecision x expSquarings).Contains
        ((1 - (argument : ℝ))⁻¹) := by
    unfold Exp.posBase
    apply Interval.contains_reciprocal_of_pos
    · simpa [argument] using hbase
    · exact hdiff
  have hpow := Interval.contains_squareN hbaseContains expSquarings
  have hargLt : (argument : ℝ) < 1 := by
    have hden : (0 : ℝ) < (2 ^ expSquarings : ℕ) := by positivity
    rw [show (argument : ℝ) = (x : ℝ) / (2 ^ expSquarings : ℕ) by
      simp [argument]]
    rw [div_lt_one hden]
    exact_mod_cast hupper
  have hbaseExp :
      Real.exp (argument : ℝ) ≤ (1 - (argument : ℝ))⁻¹ := by
    calc
      Real.exp (argument : ℝ) = (Real.exp (-(argument : ℝ)))⁻¹ := by
        simpa using Real.exp_neg (-(argument : ℝ))
      _ ≤ (1 - (argument : ℝ))⁻¹ :=
        (inv_le_inv₀ (Real.exp_pos _) (sub_pos.mpr hargLt)).mpr <|
          by linarith [Real.add_one_le_exp (-(argument : ℝ))]
  have hupperReal :
      Real.exp (x : ℝ) ≤
        Interval.iterSquare ((1 - (argument : ℝ))⁻¹) expSquarings := by
    rw [Interval.iterSquare_eq_pow_two_pow]
    calc
      Real.exp (x : ℝ) =
          Real.exp ((2 ^ expSquarings : ℕ) * (argument : ℝ)) := by
        congr 1
        rw [show (argument : ℝ) =
          (x : ℝ) / (2 ^ expSquarings : ℕ) by simp [argument]]
        field_simp
      _ = Real.exp (argument : ℝ) ^ (2 ^ expSquarings : ℕ) := by
        rw [Real.exp_nat_mul]
      _ ≤ ((1 - (argument : ℝ))⁻¹) ^ (2 ^ expSquarings : ℕ) :=
        pow_le_pow_left₀ (Real.exp_nonneg _) hbaseExp _
  have hrecip := Interval.contains_reciprocal_of_pos hrawPos hpow
  have hinv :
      (Interval.iterSquare ((1 - (argument : ℝ))⁻¹)
          expSquarings)⁻¹ ≤ Real.exp (-(x : ℝ)) := by
    have hUPos : 0 < Interval.iterSquare
        ((1 - (argument : ℝ))⁻¹) expSquarings := by
      rw [Interval.iterSquare_eq_pow_two_pow]
      positivity
    rw [Real.exp_neg]
    exact (inv_le_inv₀ hUPos (Real.exp_pos _)).mpr hupperReal
  have hupperNeg := Exp.negUpper_contains
    (p := expPrecision) (k := expSquarings) (x := x) hx
  exact ⟨hrecip.1.trans hinv, by simpa [expNegInterval] using hupperNeg.2⟩

set_option maxHeartbeats 10000000 in
-- The 256-bit reflected reciprocal expands 24 exact interval-squaring rounds.
set_option maxRecDepth 100000 in
theorem exp_neg_95_gt :
    (54 / (10 : ℝ) ^ 43) < Real.exp (-95) := by
  have hcontains :
      (expNegInterval 95).Contains (Real.exp (-95)) := by
    have h := expNegInterval_contains (x := (95 : ℚ))
      (by norm_num) (by norm_num [expSquarings])
      (by
        change 0 < Dyadic.roundDown expPrecision
          (1 - (95 : ℚ) / (2 ^ expSquarings : ℕ))
        apply Dyadic.roundDown_pos
        norm_num [expPrecision, expSquarings, Dyadic.scale])
      (by decide +kernel)
    convert h using 1 <;> norm_num
  have h := Interval.lt_of_lowerGTCheck_of_contains
    (I := expNegInterval 95) (bound := (54 / (10 : ℚ) ^ 43))
    (x := Real.exp (-95))
    (by decide +kernel) hcontains
  norm_num at h ⊢
  exact h

/-! ## One-row binomial lower bound -/

theorem localExponent_lt_95 :
    (1 : ℝ) / dimension +
        (firstBad : ℝ) ^ 2 / dimension +
        firstBad * binomialLogStepError dimension firstBad < 95 := by
  norm_num [dimension, side, firstBad, binomialLogStepError]

theorem sqrt_dimension : Real.sqrt (dimension : ℝ) = side := by
  norm_num [dimension, side]

theorem sqrt_pi_lt_nine_fifths : Real.sqrt Real.pi < (9 / 5 : ℝ) := by
  have hpi : Real.pi < (63 / 20 : ℝ) :=
    Real.pi_lt_d2.trans_le (by norm_num)
  have hsq : Real.pi < (9 / 5 : ℝ) ^ 2 := hpi.trans (by norm_num)
  nlinarith [Real.sq_sqrt Real.pi_pos.le, Real.sqrt_nonneg Real.pi]

theorem firstBad_mass_gt :
    Real.exp (-95) / 900 < centeredBinomialMassAt dimension firstBad := by
  have hlocal := centeredBinomialMassAt_lower
    (d := dimension) (K := firstBad) (k := firstBad)
    (by omega) (by norm_num [dimension, side, firstBad])
  have hcentral := centralBinomialMass_exp_lower
    (d := dimension) (by norm_num [dimension, side])
  have htotal :
      Real.exp (-95) <
        Real.exp (-(1 : ℝ) / dimension) *
          Real.exp (-((firstBad : ℝ) ^ 2 / dimension +
            firstBad * binomialLogStepError dimension firstBad)) := by
    rw [← Real.exp_add, Real.exp_lt_exp]
    linarith [localExponent_lt_95]
  have hsqrt : Real.sqrt (dimension : ℝ) = 500 := by
    simpa [side] using sqrt_dimension
  have hden :
      Real.sqrt Real.pi * Real.sqrt (dimension : ℝ) < 900 := by
    rw [hsqrt]
    nlinarith [sqrt_pi_lt_nine_fifths]
  have hdenPos : 0 < Real.sqrt Real.pi * Real.sqrt (dimension : ℝ) := by
    positivity
  have hchain :
      Real.exp (-95) / 900 <
        (Real.exp (-(1 : ℝ) / dimension) /
          (Real.sqrt Real.pi * Real.sqrt dimension)) *
          Real.exp (-((firstBad : ℝ) ^ 2 / dimension +
            firstBad * binomialLogStepError dimension firstBad)) := by
    rw [div_mul_eq_mul_div]
    exact div_lt_div₀ htotal hden.le (by positivity) hdenPos
  exact hchain.trans_le <| (mul_le_mul_of_nonneg_right hcentral
    (Real.exp_nonneg _)).trans hlocal

theorem ratio_pos : 0 < ratio := by norm_num [ratio]
theorem ratio_le_one : ratio ≤ 1 := by norm_num [ratio]

theorem adjacent_ratio_ge {i : ℕ} (hi : i < prefixLength) :
    ratio ≤
      (((dimension - (firstBad + i) : ℕ) : ℝ) /
        (dimension + (firstBad + i) + 1)) := by
  have hki : firstBad + i ≤ dimension := by
    norm_num [dimension, side, firstBad, prefixLength] at hi ⊢
    omega
  rw [Nat.cast_sub hki]
  push_cast
  have hiR : (i : ℝ) ≤ 127 := by
    exact_mod_cast (Nat.le_pred_of_lt hi)
  norm_num [ratio, dimension, side, firstBad, prefixLength] at ⊢
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  ring_nf
  have hiScaled : (i : ℝ) * 500001 ≤ 127 * 500001 :=
    mul_le_mul_of_nonneg_right hiR (by norm_num)
  linarith

theorem prefix_mass_ge (i : ℕ) (hi : i ≤ prefixLength) :
    centeredBinomialMassAt dimension firstBad * ratio ^ i ≤
      centeredBinomialMassAt dimension (firstBad + i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hi' : i < prefixLength := Nat.lt_of_succ_le hi
    have hkd : firstBad + i < dimension := by
      norm_num [dimension, side, firstBad, prefixLength] at hi' ⊢
      omega
    calc
      centeredBinomialMassAt dimension firstBad * ratio ^ (i + 1) =
          (centeredBinomialMassAt dimension firstBad * ratio ^ i) * ratio := by
        rw [pow_succ]
        ring
      _ ≤ centeredBinomialMassAt dimension (firstBad + i) * ratio :=
        mul_le_mul_of_nonneg_right (ih hi'.le) ratio_pos.le
      _ ≤ centeredBinomialMassAt dimension (firstBad + i) *
          (((dimension - (firstBad + i) : ℕ) : ℝ) /
            (dimension + (firstBad + i) + 1)) :=
        mul_le_mul_of_nonneg_left (adjacent_ratio_ge hi')
          (centeredBinomialMassAt_pos hkd.le).le
      _ = centeredBinomialMassAt dimension (firstBad + (i + 1)) := by
        rw [show firstBad + (i + 1) = (firstBad + i) + 1 by omega]
        symm
        convert centeredBinomialMassAt_succ hkd using 1 <;> push_cast <;> ring

set_option maxHeartbeats 10000000 in
-- Exact reduction expands the 128-term rational geometric prefix.
theorem geometric_prefix_gt_25 :
    (25 : ℝ) < ∑ i ∈ Finset.range prefixLength, ratio ^ i := by
  norm_num [prefixLength, ratio, Finset.sum_range_succ]

def positiveSupport : Finset ℤ :=
  (Finset.range prefixLength).image fun i => (firstBad + i : ℕ)

def negativeSupport : Finset ℤ :=
  (Finset.range prefixLength).image fun i => -((firstBad + i : ℕ) : ℤ)

def tailSupport : Finset ℤ := positiveSupport ∪ negativeSupport

theorem support_disjoint : Disjoint positiveSupport negativeSupport := by
  rw [Finset.disjoint_left]
  intro z hzPos hzNeg
  simp only [positiveSupport, Finset.mem_image, Finset.mem_range] at hzPos
  simp only [negativeSupport, Finset.mem_image, Finset.mem_range] at hzNeg
  obtain ⟨i, hi, rfl⟩ := hzPos
  obtain ⟨j, hj, hEq⟩ := hzNeg
  norm_num [firstBad] at hEq
  omega

theorem tailSupport_bad {z : ℤ} (hz : z ∈ tailSupport) :
    firstBad ≤ z.natAbs := by
  rw [tailSupport, Finset.mem_union] at hz
  rcases hz with hz | hz
  · simp only [positiveSupport, Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨i, hi, rfl⟩ := hz
    have hnonneg : (0 : ℤ) ≤ (firstBad + i : ℕ) := by positivity
    have hnabs := Int.natAbs_of_nonneg hnonneg
    have hnabsNat : ((firstBad + i : ℕ) : ℤ).natAbs = firstBad + i := by
      exact_mod_cast hnabs
    rw [hnabsNat]
    omega
  · simp only [negativeSupport, Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨i, hi, rfl⟩ := hz
    rw [Int.natAbs_neg]
    have hnonneg : (0 : ℤ) ≤ (firstBad + i : ℕ) := by positivity
    have hnabs := Int.natAbs_of_nonneg hnonneg
    have hnabsNat : ((firstBad + i : ℕ) : ℤ).natAbs = firstBad + i := by
      exact_mod_cast hnabs
    rw [hnabsNat]
    omega

theorem rowPMF_toReal {z : ℤ}
    (hz : z.natAbs ≤ dimension) :
    (SparseAllOnes.sparseAllOnesRowPMF dimension z).toReal =
      centeredBinomialMassAt dimension z.natAbs := by
  rw [SparseAllOnes.sparseAllOnesRowPMF_apply_int z hz]
  unfold centeredBinomialMassAt
  rw [ENNReal.toReal_mul]
  · simp only [ENNReal.toReal_natCast, ENNReal.toReal_inv]
    norm_cast

theorem tailSupport_le_dimension {z : ℤ} (hz : z ∈ tailSupport) :
    z.natAbs ≤ dimension := by
  rw [tailSupport, Finset.mem_union] at hz
  rcases hz with hz | hz
  · simp only [positiveSupport, Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨i, hi, rfl⟩ := hz
    norm_num [dimension, side, firstBad, prefixLength] at hi ⊢
    omega
  · simp only [negativeSupport, Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨i, hi, rfl⟩ := hz
    norm_num [dimension, side, firstBad, prefixLength] at hi ⊢
    omega

theorem natAbs_firstBad_add (i : ℕ) :
    ((firstBad + i : ℕ) : ℤ).natAbs = firstBad + i := by
  have h := Int.natAbs_of_nonneg
    (show (0 : ℤ) ≤ (firstBad + i : ℕ) by positivity)
  exact_mod_cast h

theorem tailSupport_measure_toReal :
    ((SparseAllOnes.sparseAllOnesRowPMF dimension).toMeasure
        (tailSupport : Set ℤ)).toReal =
      2 * ∑ i ∈ Finset.range prefixLength,
        centeredBinomialMassAt dimension (firstBad + i) := by
  rw [PMF.toMeasure_apply_finset, ENNReal.toReal_sum]
  · rw [tailSupport, Finset.sum_union support_disjoint]
    rw [positiveSupport, Finset.sum_image]
    · rw [negativeSupport, Finset.sum_image]
      · have hpos :
            ∑ i ∈ Finset.range prefixLength,
                (SparseAllOnes.sparseAllOnesRowPMF dimension
                  (firstBad + i : ℕ)).toReal =
              ∑ i ∈ Finset.range prefixLength,
                centeredBinomialMassAt dimension (firstBad + i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [rowPMF_toReal (by
            norm_num [dimension, side, firstBad, prefixLength] at hi ⊢
            omega)]
          rw [natAbs_firstBad_add]
        have hneg :
            ∑ i ∈ Finset.range prefixLength,
                (SparseAllOnes.sparseAllOnesRowPMF dimension
                  (-((firstBad + i : ℕ) : ℤ))).toReal =
              ∑ i ∈ Finset.range prefixLength,
                centeredBinomialMassAt dimension (firstBad + i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [rowPMF_toReal (by
            norm_num [dimension, side, firstBad, prefixLength] at hi ⊢
            omega)]
          rw [Int.natAbs_neg, natAbs_firstBad_add]
        rw [hpos, hneg]
        ring
      · intro i hi j hj hij
        change -((firstBad + i : ℕ) : ℤ) =
          -((firstBad + j : ℕ) : ℤ) at hij
        simp only [neg_inj] at hij
        have : firstBad + i = firstBad + j := by exact_mod_cast hij
        omega
    · intro i hi j hj hij
      change ((firstBad + i : ℕ) : ℤ) =
        ((firstBad + j : ℕ) : ℤ) at hij
      have : firstBad + i = firstBad + j := by exact_mod_cast hij
      omega
  · intro z hz
    exact (SparseAllOnes.sparseAllOnesRowPMF dimension).apply_ne_top z

theorem rowTail_toReal_gt :
    (3 / (10 : ℝ) ^ 43) <
      (eventProbability (SparseAllOnes.sparseAllOnesRowPMF dimension)
        (fun z => firstBad ≤ z.natAbs)).toReal := by
  have hsubset : (tailSupport : Set ℤ) ⊆ {z | firstBad ≤ z.natAbs} := by
    intro z hz
    exact tailSupport_bad hz
  have hmeasure :
      (SparseAllOnes.sparseAllOnesRowPMF dimension).toMeasure
          (tailSupport : Set ℤ) ≤
        eventProbability (SparseAllOnes.sparseAllOnesRowPMF dimension)
          (fun z => firstBad ≤ z.natAbs) := by
    rw [eventProbability_eq_toMeasure]
    exact measure_mono hsubset
  have hmeasureReal := (ENNReal.toReal_le_toReal
    (measure_ne_top _ _)
    (by unfold eventProbability; exact PMF.apply_ne_top _ _)).2 hmeasure
  rw [tailSupport_measure_toReal] at hmeasureReal
  have hsum :
      centeredBinomialMassAt dimension firstBad *
          (∑ i ∈ Finset.range prefixLength, ratio ^ i) ≤
        ∑ i ∈ Finset.range prefixLength,
          centeredBinomialMassAt dimension (firstBad + i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    exact prefix_mass_ge i (by
      simp only [Finset.mem_range] at hi
      omega)
  have hpositive : 0 < centeredBinomialMassAt dimension firstBad :=
    centeredBinomialMassAt_pos (by norm_num [dimension, side, firstBad])
  have hreal :
      (3 / (10 : ℝ) ^ 43) <
        2 * ∑ i ∈ Finset.range prefixLength,
          centeredBinomialMassAt dimension (firstBad + i) := by
    have hmass := firstBad_mass_gt
    have hgeo := geometric_prefix_gt_25
    have hexp := exp_neg_95_gt
    calc
      (3 / (10 : ℝ) ^ 43) < 2 * (Real.exp (-95) / 900 * 25) := by
        nlinarith
      _ < 2 * (centeredBinomialMassAt dimension firstBad *
          (∑ i ∈ Finset.range prefixLength, ratio ^ i)) := by
        gcongr
      _ ≤ 2 * ∑ i ∈ Finset.range prefixLength,
          centeredBinomialMassAt dimension (firstBad + i) := by
        gcongr
  exact hreal.trans_le hmeasureReal

/-! ## Exact row and matrix tensorization -/

theorem rowBad_probability_eq :
    eventProbability (sparseRademacherRow dimension) rowBad =
      eventProbability (SparseAllOnes.sparseAllOnesRowPMF dimension)
        (fun z => firstBad ≤ z.natAbs) := by
  rw [sparseRademacherRow_eq_map_uniformRowSeed,
    SparseAllOnes.sparseAllOnesRowPMF]
  apply eventProbability_map_congr
  intro seed
  rfl

theorem rowBad_probability_toReal_gt :
    (3 / (10 : ℝ) ^ 43) <
      (eventProbability (sparseRademacherRow dimension) rowBad).toReal := by
  rw [rowBad_probability_eq]
  exact rowTail_toReal_gt

theorem eventProbability_le_one
    {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (p : PMF α) (event : α → Prop) :
    eventProbability p event ≤ 1 := by
  rw [eventProbability_eq_toMeasure]
  calc
    p.toMeasure {x | event x} ≤ p.toMeasure Set.univ :=
      measure_mono (Set.subset_univ _)
    _ = 1 := by simp

theorem eventProbability_not_eq_one_sub
    {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (p : PMF α) (event : α → Prop) :
    eventProbability p (fun x => ¬ event x) =
      1 - eventProbability p event := by
  rw [eventProbability_eq_toMeasure, eventProbability_eq_toMeasure]
  have hset : {x | ¬ event x} = {x | event x}ᶜ := by rfl
  rw [hset, measure_compl
    (Set.Countable.measurableSet (Set.to_countable _)) (measure_ne_top _ _)]
  simp

theorem matrixRowBad_probability_eq :
    eventProbability (sparseRademacherMatrix 192 dimension)
        (fun J => ∃ j, rowBad (J j)) =
      1 - (1 - eventProbability (sparseRademacherRow dimension) rowBad) ^ 192 := by
  calc
    eventProbability (sparseRademacherMatrix 192 dimension)
        (fun J => ∃ j, rowBad (J j)) =
      eventProbability (sparseRademacherMatrix 192 dimension)
        (fun J => ¬ ∀ j, ¬ rowBad (J j)) := by
          apply eventProbability_congr
          intro J
          simp
    _ = 1 - eventProbability (sparseRademacherMatrix 192 dimension)
        (fun J => ∀ j, ¬ rowBad (J j)) :=
      eventProbability_not_eq_one_sub _ _
    _ = 1 - (eventProbability (sparseRademacherRow dimension)
        (fun row => ¬ rowBad row)) ^ 192 := by
      congr 1
      exact sparseRademacherMatrix_eventProbability_allRows_eq_pow
        192 dimension (fun row => ¬ rowBad row)
    _ = 1 - (1 - eventProbability (sparseRademacherRow dimension) rowBad) ^ 192 := by
      rw [eventProbability_not_eq_one_sub]

theorem matrixRowBad_probability_toReal_eq :
    (eventProbability (sparseRademacherMatrix 192 dimension)
        (fun J => ∃ j, rowBad (J j))).toReal =
      1 - (1 -
        (eventProbability (sparseRademacherRow dimension) rowBad).toReal) ^ 192 := by
  rw [matrixRowBad_probability_eq]
  have hp := eventProbability_le_one
    (sparseRademacherRow dimension) rowBad
  have hsub : 1 - eventProbability (sparseRademacherRow dimension) rowBad ≤ 1 :=
    tsub_le_self
  have hpow :
      (1 - eventProbability (sparseRademacherRow dimension) rowBad) ^ 192 ≤
        (1 : ENNReal) := by
    simpa using pow_le_one₀ (by positivity) hsub
  rw [ENNReal.toReal_sub_of_le hpow (by norm_num), ENNReal.toReal_one,
    ENNReal.toReal_pow, ENNReal.toReal_sub_of_le hp (by norm_num),
    ENNReal.toReal_one]

-- Check the rational margin directly, then transport it to the reals.
theorem rational_tensor_margin :
    (2 : ℝ)⁻¹ ^ 134 <
      1 - (1 - 3 / (10 : ℝ) ^ 43) ^ 192 := by
  have h : (2 : ℚ)⁻¹ ^ 134 <
      1 - (1 - 3 / (10 : ℚ) ^ 43) ^ 192 := by
    decide +kernel
  have hcast := (Rat.cast_lt (K := ℝ)).2 h
  push_cast at hcast
  exact hcast

theorem matrixRowBad_probability_gt_failureTarget134 :
    failureTarget 134 <
      eventProbability (sparseRademacherMatrix 192 dimension)
        (fun J => ∃ j, rowBad (J j)) := by
  rw [← ENNReal.toReal_lt_toReal
    (by unfold failureTarget; finiteness)
    (by unfold eventProbability; exact PMF.apply_ne_top _ _)]
  rw [matrixRowBad_probability_toReal_eq, failureTarget,
    ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  have hp := rowBad_probability_toReal_gt
  have hpOne :
      (eventProbability (sparseRademacherRow dimension) rowBad).toReal ≤ 1 := by
    have h := (ENNReal.toReal_le_toReal
      (by unfold eventProbability; exact PMF.apply_ne_top _ _)
      (by norm_num : (1 : ENNReal) ≠ ⊤)).2
        (eventProbability_le_one (sparseRademacherRow dimension) rowBad)
    simpa using h
  have hmono :
      1 - (1 - 3 / (10 : ℝ) ^ 43) ^ 192 <
        1 - (1 -
          (eventProbability (sparseRademacherRow dimension) rowBad).toReal) ^ 192 := by
    have hbase :
        1 - (eventProbability (sparseRademacherRow dimension) rowBad).toReal <
          1 - 3 / (10 : ℝ) ^ 43 := sub_lt_sub_left hp 1
    have hnonneg :
        0 ≤ 1 - (eventProbability
          (sparseRademacherRow dimension) rowBad).toReal := sub_nonneg.mpr hpOne
    have hpow :
        (1 - (eventProbability
          (sparseRademacherRow dimension) rowBad).toReal) ^ 192 <
          (1 - 3 / (10 : ℝ) ^ 43) ^ 192 :=
      pow_lt_pow_left₀ hbase hnonneg (by norm_num)
    exact sub_lt_sub_left hpow 1
  exact rational_tensor_margin.trans hmono

/-! ## Identification with the modular L-infinity experiment -/

theorem sqNorm_witness : sqNorm witness = dimension := by
  unfold sqNorm
  calc
    (∑ i, (witness i).natAbs ^ 2) = ∑ _ : Fin dimension, 1 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [witness]
    _ = dimension := by simp

theorem rowDot_witness
    (seed : SparseSeed 192 dimension) (j : Fin 192) :
    rowDot (sparseMatrix seed) witness j =
      SparseAllOnes.sparseAllOnesRowSum (seed j) := by
  unfold rowDot sparseMatrix sparseRow SparseAllOnes.sparseAllOnesRowSum
  apply Finset.sum_congr rfl
  intro i hi
  simp [witness]

theorem rowSum_mem_centeredInterval
    (seed : SparseSeed 192 dimension) (j : Fin 192) :
    SparseAllOnes.sparseAllOnesRowSum (seed j) ∈ centeredInterval modulus := by
  have hcount : SparseAllOnes.sparseRowTrueCount (seed j) ≤ 2 * dimension := by
    change
      (boolSupport
        (SparseAllOnes.sparseRowSeedEquivBits dimension (seed j))).card ≤
        2 * dimension
    simpa [Fintype.card_fin] using Finset.card_le_univ
      (s := boolSupport
        (SparseAllOnes.sparseRowSeedEquivBits dimension (seed j)))
  rw [SparseAllOnes.sparseAllOnesRowSum_eq_trueCount]
  simp only [centeredInterval, Set.mem_Icc]
  change -(250000 : ℤ) ≤
      (SparseAllOnes.sparseRowTrueCount (seed j) : ℤ) - 250000 ∧
    (SparseAllOnes.sparseRowTrueCount (seed j) : ℤ) - 250000 ≤ 250000
  have hcount' : SparseAllOnes.sparseRowTrueCount (seed j) ≤ 500000 := by
    simpa [dimension, side] using hcount
  omega

theorem centeredMod_rowSum
    (seed : SparseSeed 192 dimension) (j : Fin 192) :
    centeredMod modulus (SparseAllOnes.sparseAllOnesRowSum (seed j)) =
      SparseAllOnes.sparseAllOnesRowSum (seed j) := by
  exact centeredMod_eq_self
    (by
      refine ⟨250000, ?_⟩
      norm_num [modulus, dimension, side])
    (rowSum_mem_centeredInterval seed j)

theorem failure_iff_rowBad
    (seed : SparseSeed 192 dimension) :
    LInfUpperFailure parameters modulus witness (sparseMatrix seed) ↔
      ∃ j, rowBad (sparseRow (seed j)) := by
  unfold LInfUpperFailure rowBad
  simp only [parameters, sqNorm_witness]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    rw [rowDot_witness, centeredMod_rowSum] at hj
    change firstBad ≤
      (SparseAllOnes.sparseAllOnesRowSum (seed j)).natAbs
    norm_num [dimension, side, firstBad] at hj ⊢
    by_contra h
    have hx : (SparseAllOnes.sparseAllOnesRowSum (seed j)).natAbs ≤ 4870 := by
      omega
    have hsquare := Nat.mul_self_le_mul_self hx
    rw [← pow_two, ← pow_two] at hsquare
    nlinarith
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    change firstBad ≤
      (SparseAllOnes.sparseAllOnesRowSum (seed j)).natAbs at hj
    rw [rowDot_witness, centeredMod_rowSum]
    norm_num [dimension, side, firstBad] at hj ⊢
    nlinarith

theorem modularFailure_probability_eq :
    eventProbability (sparseRademacherMatrix 192 dimension)
        (LInfUpperFailure parameters modulus witness) =
      eventProbability (sparseRademacherMatrix 192 dimension)
        (fun J => ∃ j, rowBad (J j)) := by
  change eventProbability (sparseRademacherMatrix 192 dimension)
      (fun J : Fin 192 → Fin dimension → ℤ =>
        LInfUpperFailure parameters modulus witness J) =
    eventProbability (sparseRademacherMatrix 192 dimension)
      (fun J => ∃ j, rowBad (J j))
  rw [sparseRademacherMatrix_eq_map_uniformSeed]
  exact eventProbability_map_congr _ _ _ _ _ failure_iff_rowBad

/-- Explicit finite balanced-ternary obstruction at the `487/50` threshold:
the failure probability of the 500-sidelength all-ones witness is greater
than `2^-134`. -/
theorem ternaryUpper487Over50Rows192Bits134Counterexample_internal :
    failureTarget 134 <
      eventProbability (parameters.distribution.matrixPMF parameters.rows dimension)
        (LInfUpperFailure parameters modulus witness) := by
  change failureTarget 134 <
    eventProbability (sparseRademacherMatrix 192 dimension)
      (LInfUpperFailure parameters modulus witness)
  rw [modularFailure_probability_eq]
  exact matrixRowBad_probability_gt_failureTarget134

/-- Consequently, the `487/50`, 192-row balanced-ternary upper-tail statement
is false at a 134-bit budget. -/
theorem ternaryUpper487Over50Rows192Bits134_false :
    ¬ LInfUpperTailAt parameters (failureTarget 134) := by
  intro h
  have hclaimed := h modulus dimension witness
  exact (not_lt_of_ge
    ternaryUpper487Over50Rows192Bits134Counterexample_internal.le) hclaimed

end Counterexamples.TernaryLInfUpperRows192

/-- Public finite witness for the 192-row `487/50` infinity-upper security
ceiling. -/
theorem ternaryLInfUpperRows192Threshold487Over50Bits134Counterexample :
    failureTarget 134 <
      eventProbability
        (Counterexamples.TernaryLInfUpperRows192.parameters.distribution.matrixPMF
          Counterexamples.TernaryLInfUpperRows192.parameters.rows
          Counterexamples.TernaryLInfUpperRows192.dimension)
        (LInfUpperFailure
          Counterexamples.TernaryLInfUpperRows192.parameters
          Counterexamples.TernaryLInfUpperRows192.modulus
          Counterexamples.TernaryLInfUpperRows192.witness) :=
  Counterexamples.TernaryLInfUpperRows192.ternaryUpper487Over50Rows192Bits134Counterexample_internal

end CertifiedJL
