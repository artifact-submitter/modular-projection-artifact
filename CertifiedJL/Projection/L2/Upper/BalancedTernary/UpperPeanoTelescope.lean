/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperPeanoHybridProducts
import CertifiedJL.Analysis.SmoothBounds.JensenSquare

/-! # Mixed partial-sum laws for the concrete sparse upper Peano telescope -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology NNReal

namespace CertifiedJL

private theorem one_le_centeredGaussianEvenMoment_one (ell : ℕ) :
    1 ≤ centeredGaussianEvenMoment 1 ell := by
  have hsecond : (∫ y : ℝ, y ^ 2 ∂gaussianReal 0 1) = 1 := by
    rw [standardGaussianRademacher_equalMoments.equal 2 (by norm_num),
      standardRademacherMeasure_second_moment]
  have heq (v : ℝ) (hv : v ∈ Ici (0 : ℝ)) :
      (1 * Real.sqrt v) ^ (2 * ell) = v ^ ell := by
    rw [one_mul, pow_mul, Real.sq_sqrt hv]
  have hgi : Integrable
      (fun y : ℝ => (1 * Real.sqrt (y ^ 2)) ^ (2 * ell))
      (gaussianReal 0 1) := by
    convert integrable_standardGaussian_pow (2 * ell) using 1
    funext y
    rw [one_mul, Real.sqrt_sq_eq_abs, pow_mul, sq_abs]
    exact (pow_mul y 2 ell).symm
  have hj := convexSquareExpectation_le
    (μ := gaussianReal 0 1) (fun u : ℝ => u ^ (2 * ell)) 1
    ((convexOn_pow ell).congr (fun v hv => (heq v hv).symm))
    ((continuousOn_pow ell).congr (fun v hv => heq v hv)) hsecond
    (integrable_standardGaussian_pow 2) hgi
  change 1 ≤ ∫ y : ℝ, |y| ^ (2 * ell) ∂gaussianReal 0 1
  rw [show (∫ y : ℝ, |y| ^ (2 * ell) ∂gaussianReal 0 1) =
      ∫ y : ℝ, (1 * Real.sqrt (y ^ 2)) ^ (2 * ell)
        ∂gaussianReal 0 1 by
    apply integral_congr_ae
    filter_upwards [] with y
    rw [one_mul, Real.sqrt_sq_eq_abs]]
  simpa using hj

/-- The explicit Rademacher law is dominated in every even moment by the
variance-one centered Gaussian. -/
theorem standardRademacher_evenMomentDomination :
    GaussianEvenMomentDomination standardRademacherMeasure 1 1 := by
  refine ⟨by norm_num, inferInstance, ?_, ?_, ?_⟩
  · unfold standardRademacherMeasure
    rw [Measure.map_add]
    · simp only [Measure.map_smul, Measure.map_dirac, neg_neg]
      rw [add_comm]
    · fun_prop
  · intro n
    simpa only [Real.norm_eq_abs, abs_pow] using
      (integrable_standardRademacher_pow n).norm
  · intro ell
    have hR : (∫ y : ℝ, |y| ^ (2 * ell)
        ∂standardRademacherMeasure) = 1 := by
      calc
        _ = ∫ y : ℝ, y ^ (2 * ell) ∂standardRademacherMeasure := by
          apply integral_congr_ae
          filter_upwards [] with y
          rw [pow_mul, pow_mul, sq_abs]
        _ = 1 := by
          rw [integral_standardRademacher_pow]
          norm_num [pow_mul]
    rw [hR, one_mul]
    exact one_le_centeredGaussianEvenMoment_one ell

/-- A recursively associated independent weighted sum. -/
noncomputable def weightedIndependentSumLaw :
    {n : ℕ} → (Fin n → ℝ) → (Fin n → Measure ℝ) → Measure ℝ
  | 0, _, _ => Measure.dirac 0
  | n + 1, b, μ => independentAffineSumMeasure
      (weightedIndependentSumLaw (fun i : Fin n => b i.succ)
        (fun i : Fin n => μ i.succ)) (μ 0) (b 0)

/-- The matching recursively associated variance. -/
def weightedIndependentSumVariance : {n : ℕ} → (Fin n → ℝ) → NNReal
  | 0, _ => 0
  | n + 1, b => weightedIndependentSumVariance (fun i : Fin n => b i.succ) +
      scaledVariance (b 0) 1

/-- Coordinatewise variance-one domination propagates to the complete mixed
partial-sum law. -/
theorem weightedIndependentSumLaw_evenMomentDomination :
    ∀ {n : ℕ} (b : Fin n → ℝ) (μ : Fin n → Measure ℝ),
      (∀ i, GaussianEvenMomentDomination (μ i) 1 1) →
      GaussianEvenMomentDomination (weightedIndependentSumLaw b μ) 1
        (weightedIndependentSumVariance b)
  | 0, b, μ, hμ => by
      simpa [weightedIndependentSumLaw, weightedIndependentSumVariance] using
        centeredGaussian_evenMomentDomination 0
  | n + 1, b, μ, hμ => by
      have htail := weightedIndependentSumLaw_evenMomentDomination
        (fun i : Fin n => b i.succ) (fun i : Fin n => μ i.succ)
        (fun i => hμ i.succ)
      simpa [weightedIndependentSumLaw, weightedIndependentSumVariance] using
        htail.independentAffineSum (hμ 0) (b 0)

/-- The recursive variance is exactly the sum of squared coefficients. -/
theorem coe_weightedIndependentSumVariance :
    ∀ {n : ℕ} (b : Fin n → ℝ),
      (weightedIndependentSumVariance b : ℝ) = ∑ i, b i ^ 2
  | 0, b => by simp [weightedIndependentSumVariance]
  | n + 1, b => by
      rw [Fin.sum_univ_succ]
      simp only [weightedIndependentSumVariance, NNReal.coe_add,
        scaledVariance, NNReal.coe_mk, mul_one]
      rw [coe_weightedIndependentSumVariance]
      ring

theorem upperPeanoHybridCoordinateLaw_evenMomentDomination
    {n : ℕ} (k : ℕ) (i : Fin n) :
    GaussianEvenMomentDomination (upperPeanoHybridCoordinateLaw k i) 1 1 := by
  unfold upperPeanoHybridCoordinateLaw
  split_ifs
  · exact standardRademacher_evenMomentDomination
  · exact centeredGaussian_evenMomentDomination 1

/-- Every mixed hybrid weighted sum has the same Gaussian moment variance as
the squared coefficient sum. -/
theorem upperPeanoHybridSum_evenMomentDomination
    {n : ℕ} (b : Fin n → ℝ) (k : ℕ) :
    GaussianEvenMomentDomination
      (weightedIndependentSumLaw b (upperPeanoHybridCoordinateLaw k)) 1
      (weightedIndependentSumVariance b) :=
  weightedIndependentSumLaw_evenMomentDomination b _
    (upperPeanoHybridCoordinateLaw_evenMomentDomination k)

/-- Every duplicated sparse coefficient lies in the sharp scaled strip. -/
theorem sparseUpperDuplicatedCoefficient_sq_le_quarter
    {d : ℕ} (a : Fin d → ℝ) (hsq : ∑ i, a i ^ 2 = 1)
    (p : Fin d × Fin 2) :
    sparseUpperDuplicatedCoefficient a p ^ 2 ≤ 1 / 4 := by
  have hai : a p.1 ^ 2 ≤ 1 := by
    rw [← hsq]
    exact Finset.single_le_sum (fun i _ => sq_nonneg (a i))
      (Finset.mem_univ p.1)
  simp only [sparseUpperDuplicatedCoefficient]
  nlinarith

theorem sparseUpperDuplicatedCoefficient_scaled_strip
    {d : ℕ} (a : Fin d → ℝ) (hsq : ∑ i, a i ^ 2 = 1)
    {s : ℂ} (hs_nonneg : 0 ≤ s.re) (hs_lt_one : s.re < 1)
    (p : Fin d × Fin 2) :
    2 * sparseUpperDuplicatedCoefficient a p ^ 2 * s.re < 1 := by
  have hsre : 0 ≤ s.re := hs_nonneg
  have hp := sparseUpperDuplicatedCoefficient_sq_le_quarter a hsq p
  nlinarith [hsre]

/-- Split an arbitrary finite product integral at one selected coordinate. -/
theorem integral_pi_split_coordinate
    {n : ℕ} (μ : Fin (n + 1) → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] (i : Fin (n + 1))
    (f : (Fin (n + 1) → ℝ) → ℂ)
    (hf : Integrable f (Measure.pi μ)) :
    ∫ x, f x ∂Measure.pi μ =
      ∫ y, ∫ rest,
        f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
          (y, rest))
        ∂Measure.pi (fun j => μ (i.succAbove j)) ∂μ i := by
  have he := measurePreserving_piFinSuccAbove μ i
  rw [← he.symm.integral_comp']
  rw [integral_prod]
  exact he.symm.integrable_comp_of_integrable hf

/-- The weighted coordinate sum splits into the selected coordinate and the
remaining `succAbove` sum. -/
theorem weightedSum_piFinSuccAbove_symm
    {n : ℕ} (b : Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (y : ℝ) (rest : Fin n → ℝ) :
    (∑ j, b j *
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
        (y, rest)) j) =
      b i * y + ∑ j, b (i.succAbove j) * rest j := by
  rw [Fin.sum_univ_succAbove _ i]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove]

/-- The recursively associated weighted-sum law is the pushforward of the
finite product distribution. -/
theorem map_weightedSum_pi_eq_weightedIndependentSumLaw
    {n : ℕ} (b : Fin n → ℝ) (μ : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] :
    Measure.map (fun x : Fin n → ℝ => ∑ i, b i * x i) (Measure.pi μ) =
      weightedIndependentSumLaw b μ := by
  induction n with
  | zero => simp [weightedIndependentSumLaw]
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      let tailSum : (Fin n → ℝ) → ℝ :=
        fun x => ∑ i, b i.succ * x i
      let (i : Fin n) : SigmaFinite (μ i.succ) := inferInstance
      have he := (measurePreserving_piFinSuccAbove μ 0).map_eq
      have he' : Measure.map e (Measure.pi μ) =
          (μ 0).prod (Measure.pi fun i : Fin n => μ i.succ) := by
        simpa [e] using he
      have htail := ih (fun i : Fin n => b i.succ)
        (fun i : Fin n => μ i.succ)
      unfold weightedIndependentSumLaw
      unfold independentAffineSumMeasure
      rw [← htail, ← (Measure.map_id : Measure.map id (μ 0) = μ 0),
        Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
      rw [← Measure.prod_swap, ← he']
      rw [Measure.map_map (by fun_prop) (by fun_prop),
        Measure.map_map (by fun_prop) (by fun_prop),
        Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext x
      rw [Fin.sum_univ_succ]
      simp [e, MeasurableEquiv.piFinSuccAbove_apply, Fin.tail]
      ring

end CertifiedJL
