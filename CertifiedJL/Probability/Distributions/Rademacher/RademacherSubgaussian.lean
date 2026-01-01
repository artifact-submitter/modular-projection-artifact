/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Distributions.BalancedTernary.Duplication
import CertifiedJL.Probability.Distributions.Rademacher.BiasedSignProduct
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Probability.Moments.Basic

/-!
# Subgaussian tails for finite Rademacher sums

This module combines the exact product-cosh moment generating function with
exponential Markov. It provides one- and two-sided bounds for arbitrary finite
coefficient profiles, then transfers the two-sided result through sparse-row
duplication. No modular arithmetic is used here.
-/

open scoped BigOperators ENNReal

open MeasureTheory ProbabilityTheory Set

namespace CertifiedJL
namespace Probability

universe u

/-- The moment generating function of a weighted Rademacher sum is a product of coshes. -/
theorem rademacherSum_integral_exp_eq_prod_cosh
    {ι : Type u} [Fintype ι] (a : ι → ℝ) (t : ℝ) :
    ∫ bits, Real.exp (t * rademacherSum a bits)
        ∂(rademacherPMF ι).toMeasure =
      ∏ i, Real.cosh (t * a i) := by
  have h := rademacherIntegral_exp_mul_eq_biasedSignProduct
    t a (fun _ => (1 : ℝ))
  simpa using h

/-- The standard subgaussian MGF bound for a finite weighted Rademacher sum. -/
theorem rademacherSum_mgf_le_exp_sum_sq
    {ι : Type u} [Fintype ι] (a : ι → ℝ) (t : ℝ) :
    mgf (rademacherSum a) (rademacherPMF ι).toMeasure t ≤
      Real.exp (t ^ 2 * (∑ i, a i ^ 2) / 2) := by
  rw [mgf, rademacherSum_integral_exp_eq_prod_cosh]
  exact prod_cosh_le_exp_sum_sq t a

/--
Optimized one-sided subgaussian tail for a profile of positive squared mass
`variance`.
-/
theorem rademacherSum_upperTail_toReal_le_exp_neg_sq_div_two
    {ι : Type u} [Fintype ι] (a : ι → ℝ) {x variance : ℝ}
    (hx : 0 ≤ x) (hvariance : 0 < variance)
    (hsq : ∑ i, a i ^ 2 = variance) :
    (eventProbability (rademacherPMF ι)
      (fun bits => x < rademacherSum a bits)).toReal ≤
        Real.exp (-(x ^ 2 / (2 * variance))) := by
  let t := x / variance
  have ht : 0 ≤ t := div_nonneg hx hvariance.le
  have hmarkov := measure_ge_le_exp_mul_mgf
    (μ := (rademacherPMF ι).toMeasure)
    (X := rademacherSum a) x ht (Integrable.of_finite)
  have hmgf : mgf (rademacherSum a) (rademacherPMF ι).toMeasure t ≤
      Real.exp (t ^ 2 * variance / 2) := by
    simpa only [hsq] using rademacherSum_mgf_le_exp_sum_sq a t
  rw [eventProbability_eq_toMeasure]
  calc
    (rademacherPMF ι).toMeasure.real
        {bits | x < rademacherSum a bits} ≤
      (rademacherPMF ι).toMeasure.real
        {bits | x ≤ rademacherSum a bits} := by
        apply measureReal_mono
        · intro bits hbits
          change x < rademacherSum a bits at hbits
          change x ≤ rademacherSum a bits
          exact hbits.le
        · exact measure_ne_top _ _
    _ ≤ Real.exp (-t * x) *
          mgf (rademacherSum a) (rademacherPMF ι).toMeasure t := hmarkov
    _ ≤ Real.exp (-t * x) * Real.exp (t ^ 2 * variance / 2) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
    _ = Real.exp (-(x ^ 2 / (2 * variance))) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [t]
      field_simp [hvariance.ne']
      ring

/-- Convert the finite-PMF union bound to real-valued probabilities. -/
theorem eventProbability_or_toReal_le
    {Ω : Type u} [Countable Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (p : PMF Ω) (A B : Ω → Prop) :
    (eventProbability p (fun x => A x ∨ B x)).toReal ≤
      (eventProbability p A).toReal + (eventProbability p B).toReal := by
  have h := eventProbability_or_le p A B
  have htop : eventProbability p A + eventProbability p B ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩
  have hreal := ENNReal.toReal_mono htop h
  exact hreal.trans_eq (ENNReal.toReal_add
    (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))

/-- Optimized two-sided subgaussian tail for a weighted Rademacher sum. -/
theorem rademacherSum_absTail_toReal_le_two_mul_exp_neg_sq_div_two
    {ι : Type u} [Fintype ι] (a : ι → ℝ) {x variance : ℝ}
    (hx : 0 ≤ x) (hvariance : 0 < variance)
    (hsq : ∑ i, a i ^ 2 = variance) :
    (eventProbability (rademacherPMF ι)
      (fun bits => |rademacherSum a bits| > x)).toReal ≤
        2 * Real.exp (-(x ^ 2 / (2 * variance))) := by
  have hupper :=
    rademacherSum_upperTail_toReal_le_exp_neg_sq_div_two
      a hx hvariance hsq
  have hlower :
      (eventProbability (rademacherPMF ι)
        (fun bits => rademacherSum a bits < -x)).toReal ≤
          Real.exp (-(x ^ 2 / (2 * variance))) := by
    rw [rademacherSum_strict_tail_symmetry]
    exact hupper
  have habs : (fun bits => |rademacherSum a bits| > x) =
      (fun bits => rademacherSum a bits < -x ∨
        x < rademacherSum a bits) := by
    funext bits
    apply propext
    constructor
    · intro hs
      by_cases hleft : rademacherSum a bits < -x
      · exact Or.inl hleft
      · right
        by_contra hright
        exact (not_le_of_gt hs) ((abs_le).2
          ⟨le_of_not_gt hleft, le_of_not_gt hright⟩)
    · rintro (hleft | hright)
      · simpa only [neg_neg] using
          (neg_lt_neg hleft).trans_le
            (neg_le_abs (rademacherSum a bits))
      · exact hright.trans_le (le_abs_self (rademacherSum a bits))
  rw [habs]
  calc
    _ ≤ _ + _ := eventProbability_or_toReal_le _ _ _
    _ ≤ Real.exp (-(x ^ 2 / (2 * variance))) +
        Real.exp (-(x ^ 2 / (2 * variance))) := add_le_add hlower hupper
    _ = _ := by ring

/-- The exact numerical tail budget used by the SparseLInf diffuse regime. -/
theorem two_mul_exp_neg_twentyfive_div_four_lt_one_fortieth :
    2 * Real.exp (-(25 : ℝ) / 4) < 1 / 40 := by
  have h1 : Real.exp (-1) < (3 : ℝ) / 8 :=
    Real.exp_neg_one_lt_d9.trans (by norm_num)
  have hmono : Real.exp (-(25 : ℝ) / 4) < Real.exp (-6) := by
    rw [Real.exp_lt_exp]
    norm_num
  have hpow : Real.exp (-6) = Real.exp (-1) ^ 6 := by
    norm_num [← Real.exp_nat_mul]
  rw [hpow] at hmono
  have hpowlt : Real.exp (-1) ^ 6 < ((3 : ℝ) / 8) ^ 6 :=
    pow_lt_pow_left₀ h1 (Real.exp_nonneg _) (by norm_num)
  nlinarith

/-- The two unnormalized sign copies have total squared mass `2 * ‖w‖²`. -/
theorem sum_sq_duplicatedCoefficient_eq_two_mul_norm_sq
    {d : ℕ} (w : EuclideanSpace ℝ (Fin d)) :
    ∑ p : Fin d × Fin 2, w p.1 ^ 2 = 2 * ‖w‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  calc
    ∑ i, (w i ^ 2 + w i ^ 2) = 2 * ∑ i, w i ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 2 * ‖w‖ ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq]

/--
The doubled sparse-row dot product has exactly the law of the unnormalized
duplicated Rademacher sum.
-/
theorem sparseRademacherRow_two_mul_probability_eq_rademacher
    {d : ℕ} (w : EuclideanSpace ℝ (Fin d)) (x : ℝ) :
    eventProbability (sparseRademacherRow d)
        (fun row => |2 * euclideanRowDot row w| > x) =
      eventProbability (rademacherPMF (Fin d × Fin 2))
        (fun bits => |rademacherSum (fun p => w p.1) bits| > x) := by
  rw [sparseRademacherRow_eq_map_uniformRowSeed]
  calc
    eventProbability
        ((PMF.uniformOfFintype (SparseRowSeed d)).map sparseRow)
        (fun row => |2 * euclideanRowDot row w| > x) =
      eventProbability
        ((PMF.uniformOfFintype (SparseRowSeed d)).map sparseRowSeedSigns)
        (fun bits => |rademacherSum (fun p => w p.1) bits| > x) := by
      apply eventProbability_map_congr
      intro seed
      rw [← duplicatedSparseSignSum_eq_two_mul]
      rfl
    _ = _ := by
      rw [map_uniformSparseSeed_signs]
      unfold rademacherPMF
      rw [uniformPiPMF_eq_uniformOfFintype]

/--
SparseLInf diffuse-regime tail: the doubled sparse-row sum exceeds `5 ‖w‖`
with probability strictly below `1/40`.
-/
theorem sparseRademacherRow_two_mul_abs_gt_five_norm_lt_one_fortieth
    {d : ℕ} (w : EuclideanSpace ℝ (Fin d)) (hw : w ≠ 0) :
    eventProbability (sparseRademacherRow d)
        (fun row => |2 * euclideanRowDot row w| > 5 * ‖w‖) <
      (1 : ℝ≥0∞) / 40 := by
  rw [sparseRademacherRow_two_mul_probability_eq_rademacher]
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hv : 0 < 2 * ‖w‖ ^ 2 :=
    mul_pos (by norm_num) (sq_pos_of_pos hn)
  have htail :=
    rademacherSum_absTail_toReal_le_two_mul_exp_neg_sq_div_two
      (fun p : Fin d × Fin 2 => w p.1)
      (x := 5 * ‖w‖) (variance := 2 * ‖w‖ ^ 2)
      (mul_nonneg (by norm_num) (norm_nonneg w)) hv
      (sum_sq_duplicatedCoefficient_eq_two_mul_norm_sq w)
  have hexponent :
      -((5 * ‖w‖) ^ 2 / (2 * (2 * ‖w‖ ^ 2))) =
        -(25 : ℝ) / 4 := by
    field_simp [hn.ne']
    ring
  rw [hexponent] at htail
  have hreal :
      (eventProbability (rademacherPMF (Fin d × Fin 2))
        (fun bits =>
          |rademacherSum (fun p => w p.1) bits| > 5 * ‖w‖)).toReal <
        (1 : ℝ) / 40 :=
    htail.trans_lt two_mul_exp_neg_twentyfive_div_four_lt_one_fortieth
  apply (ENNReal.toReal_lt_toReal
    (PMF.apply_ne_top _ _) (by norm_num)).mp
  convert hreal using 1
  · rfl
  · norm_num only [ENNReal.toReal_div, ENNReal.toReal_one,
      ENNReal.toReal_ofNat]

end Probability
end CertifiedJL
