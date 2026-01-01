/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperPeanoAdjacentConcrete
import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperPeanoTelescope
import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperPeanoGaussianEndpoints
import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperPeanoHybrid

/-! # Unconditional sparse upper Peano hybrid -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace CertifiedJL

/-- Every concrete mixed product has the quadratic-exponential integrability
needed to isolate any coordinate in the positive strip. -/
theorem integrable_upperPeanoHybridValue_integrand
    {n : ℕ} (b : Fin n → ℝ) (k : ℕ)
    (hsq : ∑ i, b i ^ 2 = (1 / 2 : ℝ))
    {s : ℂ} (hs_nonneg : 0 ≤ s.re) (hs_lt_one : s.re < 1) :
    Integrable (fun x : Fin n → ℝ =>
      complexQuadraticExp s (∑ i, b i * x i))
      (Measure.pi (upperPeanoHybridCoordinateLaw k)) := by
  let (i : Fin n) : IsProbabilityMeasure
      (upperPeanoHybridCoordinateLaw k i) := by
    unfold upperPeanoHybridCoordinateLaw
    split <;> infer_instance
  let μ := weightedIndependentSumLaw b (upperPeanoHybridCoordinateLaw k)
  have hdom := upperPeanoHybridSum_evenMomentDomination b k
  have hvariance : weightedIndependentSumVariance b ≤ (2 : NNReal)⁻¹ := by
    apply NNReal.coe_le_coe.mp
    rw [coe_weightedIndependentSumVariance, hsq]
    norm_num
  have htilt := tiltedEvenMoment_le_of_gaussianEvenMomentDomination
    hdom hvariance 0 hs_nonneg hs_lt_one
  have hμ : Integrable (complexQuadraticExp s) μ := by
    refine Integrable.mono' htilt.1
      (contDiff_complexQuadraticExp s).continuous.aestronglyMeasurable ?_
    filter_upwards [] with x
    simp only [complexQuadraticExp, Complex.norm_exp]
    rw [Complex.mul_re]
    norm_num [pow_two, Complex.mul_re, Complex.mul_im]
  dsimp [μ] at hμ
  rw [← map_weightedSum_pi_eq_weightedIndependentSumLaw b
    (upperPeanoHybridCoordinateLaw k)] at hμ
  have hsum : Continuous (fun x : Fin n → ℝ => ∑ i, b i * x i) := by
    apply continuous_finsetSum
    intro i hi
    exact continuous_const.mul (continuous_apply i)
  exact (integrable_map_measure
    (f := fun x : Fin n → ℝ => ∑ i, b i * x i)
    (g := complexQuadraticExp s)
      (contDiff_complexQuadraticExp s).continuous.aestronglyMeasurable
      hsum.measurable.aemeasurable).mp hμ

/-- Half-variance Gaussian moment domination gives integrability of every
quadratic-exponential derivative throughout the U7 strip. -/
theorem integrable_iteratedDeriv_complexQuadraticExp_of_halfDomination
    {μ : Measure ℝ} {mass : ℝ} {variance : NNReal}
    (hμ : GaussianEvenMomentDomination μ mass variance)
    (hvariance : variance ≤ (2 : NNReal)⁻¹) (j : ℕ)
    {s : ℂ} (hs_nonneg : 0 ≤ s.re) (hs_lt_one : s.re < 1) :
    Integrable (iteratedDeriv j (complexQuadraticExp s)) μ := by
  let p := complexQuadraticExpDerivativePolynomial s j
  have hpow (n : ℕ) : Integrable (fun x : ℝ =>
      |x| ^ n * Real.exp (s.re * x ^ 2)) μ := by
    have h0 := (tiltedEvenMoment_le_of_gaussianEvenMomentDomination
      hμ hvariance 0 hs_nonneg hs_lt_one).1
    have hn := (tiltedEvenMoment_le_of_gaussianEvenMomentDomination
      hμ hvariance n hs_nonneg hs_lt_one).1
    have hmajor := h0.add hn
    refine Integrable.mono' hmajor (by fun_prop) ?_
    filter_upwards [] with x
    have hx : |x| ^ n ≤ 1 + |x| ^ (2 * n) := by
      by_cases h : |x| ≤ 1
      · exact (pow_le_one₀ (abs_nonneg _) h).trans
          (le_add_of_nonneg_right (pow_nonneg (abs_nonneg _) _))
      · exact (pow_le_pow_right₀ (le_of_not_ge h) (by omega : n ≤ 2 * n)).trans
          (le_add_of_nonneg_left (by norm_num))
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (pow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le)]
    simp only [Pi.add_apply]
    calc
      |x| ^ n * Real.exp (s.re * x ^ 2) ≤
          (1 + |x| ^ (2 * n)) * Real.exp (s.re * x ^ 2) :=
        mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
      _ = |x| ^ (2 * 0) * Real.exp (s.re * x ^ 2) +
          |x| ^ (2 * n) * Real.exp (s.re * x ^ 2) := by ring
  have hmajor : Integrable (fun x : ℝ =>
      ∑ n ∈ p.support, ‖p.coeff n‖ *
        (|x| ^ n * Real.exp (s.re * x ^ 2))) μ := by
    apply integrable_finsetSum
    intro n hn
    exact (hpow n).const_mul _
  have hcont : Continuous (iteratedDeriv j (complexQuadraticExp s)) := by
    rw [show iteratedDeriv j (complexQuadraticExp s) = fun x : ℝ =>
        p.eval (x : ℂ) * complexQuadraticExp s x by
      funext x
      exact iteratedDeriv_complexQuadraticExp j s x]
    have hp : Continuous (fun x : ℝ => p.eval (x : ℂ)) := by fun_prop
    exact hp.mul (contDiff_complexQuadraticExp s).continuous
  refine Integrable.mono' hmajor hcont.aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [iteratedDeriv_complexQuadraticExp, Polynomial.eval_eq_sum,
    Polynomial.sum_def, Finset.sum_mul]
  calc
    ‖∑ n ∈ p.support, p.coeff n * (x : ℂ) ^ n *
        complexQuadraticExp s x‖ ≤
      ∑ n ∈ p.support, ‖p.coeff n * (x : ℂ) ^ n *
        complexQuadraticExp s x‖ := norm_sum_le _ _
    _ = ∑ n ∈ p.support, ‖p.coeff n‖ *
        (|x| ^ n * Real.exp (s.re * x ^ 2)) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        complexQuadraticExp, Complex.norm_exp]
      have hexp : (s * ((x : ℂ) ^ 2)).re = s.re * x ^ 2 := by
        rw [Complex.mul_re]
        norm_num [pow_two, Complex.mul_re, Complex.mul_im]
      rw [hexp]
      ring

theorem upperPeanoHybridRestSum_evenMomentDomination
    {m : ℕ} (b : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    GaussianEvenMomentDomination (upperPeanoAdjacentRestSumLaw b i) 1
      (weightedIndependentSumVariance
        (fun j : Fin m => b (i.succAbove j))) := by
  let (j : Fin m) : IsProbabilityMeasure
      (upperPeanoHybridRestCoordinateLaw i j) := by
    unfold upperPeanoHybridRestCoordinateLaw upperPeanoHybridCoordinateLaw
    split <;> infer_instance
  unfold upperPeanoAdjacentRestSumLaw
  rw [map_weightedSum_pi_eq_weightedIndependentSumLaw]
  apply weightedIndependentSumLaw_evenMomentDomination
  intro j
  unfold upperPeanoHybridRestCoordinateLaw
  exact upperPeanoHybridCoordinateLaw_evenMomentDomination i.val (i.succAbove j)

theorem integrable_upperPeanoHybridRest_outer_iteratedDeriv_four
    {m : ℕ} (b : Fin (m + 1) → ℝ) (i : Fin (m + 1))
    {ν : Measure ℝ} (hν : GaussianEvenMomentDomination ν 1 1)
    (hvariance : weightedIndependentSumVariance
        (fun j : Fin m => b (i.succAbove j)) + scaledVariance (b i) 1 ≤
      (2 : NNReal)⁻¹)
    {s : ℂ} (hs_nonneg : 0 ≤ s.re) (hs_lt_one : s.re < 1) :
    Integrable (fun w => ∫ y : ℝ,
      iteratedDeriv 4 (complexQuadraticExp s) (w + b i * y) ∂ν)
      (upperPeanoAdjacentRestSumLaw b i) := by
  let : IsFiniteMeasure ν := hν.isFiniteMeasure
  have htotal := (upperPeanoHybridRestSum_evenMomentDomination b i).independentAffineSum
    hν (b i)
  have htotalInt := integrable_iteratedDeriv_complexQuadraticExp_of_halfDomination
    htotal hvariance 4 hs_nonneg hs_lt_one
  unfold independentAffineSumMeasure at htotalInt
  rw [integrable_map_measure (by fun_prop) (by fun_prop)] at htotalInt
  exact htotalInt.integral_prod_left

/-- The exact `11/15` Gaussian-to-K estimate for one concrete hybrid rest
sum, with all integrability and variance premises discharged internally. -/
theorem norm_upperPeanoHybridRest_gaussian_sub_peanoK_le
    {m : ℕ} (b : Fin (m + 1) → ℝ) (i : Fin (m + 1))
    (hsq : ∑ j, b j ^ 2 = (1 / 2 : ℝ))
    {s : ℂ} (hs_nonneg : 0 ≤ s.re) (hs_lt_one : s.re < 1)
    (hscale : 2 * b i ^ 2 * s.re < 1) :
    ‖(∫ w, ∫ y : ℝ, iteratedDeriv 4 (complexQuadraticExp s)
          (w + b i * y) ∂gaussianReal 0 1
          ∂upperPeanoAdjacentRestSumLaw b i) -
        ∫ w, ∫ y : ℝ, iteratedDeriv 4 (complexQuadraticExp s)
          (w + b i * y) ∂peanoKMeasure
          ∂upperPeanoAdjacentRestSumLaw b i‖ ≤
      (11 / 15 : ℝ) * b i ^ 2 *
        quadraticExpDerivativeMajorant 6 ‖s‖ s.re := by
  let bRest : Fin m → ℝ := fun j => b (i.succAbove j)
  have hvariance : weightedIndependentSumVariance bRest +
      scaledVariance (b i) 1 ≤ (2 : NNReal)⁻¹ := by
    apply le_of_eq
    apply NNReal.eq
    rw [NNReal.coe_add, coe_weightedIndependentSumVariance]
    simp only [bRest, scaledVariance, NNReal.coe_mk,
      mul_one, NNReal.coe_inv, NNReal.coe_ofNat]
    norm_num [inv_eq_one_div]
    rw [← hsq, Fin.sum_univ_succAbove (fun j => b j ^ 2) i]
    ring
  have hG := integrable_upperPeanoHybridRest_outer_iteratedDeriv_four b i
    (centeredGaussian_evenMomentDomination 1) hvariance hs_nonneg hs_lt_one
  have hK := integrable_upperPeanoHybridRest_outer_iteratedDeriv_four b i
    peanoK_evenMomentDomination hvariance hs_nonneg hs_lt_one
  exact
    norm_partialSum_secondPeanoDifference_standardGaussian_peanoKMeasure_le_unconditional
      s (b i) hG hK (upperPeanoHybridRestSum_evenMomentDomination b i)
        hvariance hs_nonneg hs_lt_one hscale

noncomputable def upperPeanoHybridKFourValue {m : ℕ}
    (b : Fin (m + 1) → ℝ) (s : ℂ) (i : Fin (m + 1)) : ℂ :=
  ∫ w, ∫ k : ℝ, iteratedDeriv 4 (complexQuadraticExp s) (w + b i * k)
    ∂peanoKMeasure ∂upperPeanoAdjacentRestSumLaw b i

/-- The concrete finite product telescope has the exact fourth-Peano `hfirst`
identity, with all adjacent-step integrability discharged internally. -/
theorem upperPeanoHybridValue_hfirst
    {m : ℕ} (b : Fin (m + 1) → ℝ)
    (hsq : ∑ i, b i ^ 2 = (1 / 2 : ℝ))
    {s : ℂ} (hs_nonneg : 0 ≤ s.re) (hs_lt_one : s.re < 1)
    (hscale : ∀ i, 2 * b i ^ 2 * s.re < 1) :
    upperPeanoHybridValue b s 0 - upperPeanoHybridValue b s (m + 1) =
      ∑ i, (b i ^ 4 / 12 : ℝ) • upperPeanoHybridKFourValue b s i := by
  apply upperPeanoHybridValue_sub_eq_sum_fourthPeano
  intro i
  exact upperPeanoHybridValue_adjacent_hfirst b s i (hscale i)
    (integrable_upperPeanoHybridValue_integrand b i.val hsq hs_nonneg hs_lt_one)
    (integrable_upperPeanoHybridValue_integrand b (i.val + 1) hsq
      hs_nonneg hs_lt_one)

theorem norm_integral_integral_iteratedDeriv_eight_le
    {ρ ν : Measure ℝ} {varianceW : NNReal}
    (hW : GaussianEvenMomentDomination ρ 1 varianceW)
    (hν : GaussianEvenMomentDomination ν 1 1) (c : ℝ)
    (hvariance : varianceW + scaledVariance c 1 ≤ (2 : NNReal)⁻¹)
    (s : ℂ) (hs_nonneg : 0 ≤ s.re) (hs_lt_one : s.re < 1) :
    ‖∫ w, ∫ y : ℝ, iteratedDeriv 8 (complexQuadraticExp s) (w + c * y)
        ∂ν ∂ρ‖ ≤ quadraticExpDerivativeMajorant 8 ‖s‖ s.re := by
  let : IsFiniteMeasure ρ := hW.isFiniteMeasure
  let : IsFiniteMeasure ν := hν.isFiniteMeasure
  let μ := independentAffineSumMeasure ρ ν c
  have hμdom : GaussianEvenMomentDomination μ 1
      (varianceW + scaledVariance c 1) := by
    simpa [μ] using hW.independentAffineSum hν c
  have hμint := integrable_iteratedDeriv_complexQuadraticExp_of_halfDomination
    hμdom hvariance 8 hs_nonneg hs_lt_one
  have hjoint : Integrable (fun p : ℝ × ℝ =>
      iteratedDeriv 8 (complexQuadraticExp s) (p.1 + c * p.2)) (ρ.prod ν) := by
    change Integrable (iteratedDeriv 8 (complexQuadraticExp s))
      (independentAffineSumMeasure ρ ν c) at hμint
    unfold independentAffineSumMeasure at hμint
    rw [integrable_map_measure (by fun_prop) (by fun_prop)] at hμint
    exact hμint
  have heq : (∫ w, ∫ y : ℝ, iteratedDeriv 8 (complexQuadraticExp s)
        (w + c * y) ∂ν ∂ρ) =
      ∫ z, iteratedDeriv 8 (complexQuadraticExp s) z ∂μ := by
    dsimp [μ]
    unfold independentAffineSumMeasure
    rw [integral_map (by fun_prop) (by fun_prop), integral_prod _ hjoint]
  rw [heq]
  exact (norm_integral_le_integral_norm _).trans
    (integral_norm_iteratedDeriv_eight_complexQuadraticExp_le_of_evenMomentDomination
      (hμdom.gaussianHalf hvariance) s hs_nonneg hs_lt_one)

private theorem upperPeanoHybridRest_totalVariance_le
    {m : ℕ} (b : Fin (m + 1) → ℝ) (i : Fin (m + 1))
    (hsq : ∑ j, b j ^ 2 = (1 / 2 : ℝ)) :
    weightedIndependentSumVariance (fun j : Fin m => b (i.succAbove j)) +
        scaledVariance (b i) 1 ≤ (2 : NNReal)⁻¹ := by
  apply le_of_eq
  apply NNReal.eq
  rw [NNReal.coe_add, coe_weightedIndependentSumVariance]
  simp only [scaledVariance, NNReal.coe_mk,
    mul_one, NNReal.coe_inv, NNReal.coe_ofNat]
  norm_num [inv_eq_one_div]
  calc
    (∑ x, b (i.succAbove x) ^ 2) + b i ^ 2 =
        b i ^ 2 + ∑ x, b (i.succAbove x) ^ 2 := add_comm _ _
    _ = ∑ j, b j ^ 2 :=
      (Fin.sum_univ_succAbove (fun j => b j ^ 2) i).symm
    _ = 1 / 2 := hsq

/-- Every derivative-four mixed stage is bounded from the all-Gaussian stage
by the exact accumulated derivative-eight fourth-Peano correction. -/
theorem norm_upperPeanoHybridDerivFourValue_sub_zero_le_unconditional
    {m : ℕ} (b : Fin (m + 1) → ℝ)
    (hsq : ∑ j, b j ^ 2 = (1 / 2 : ℝ))
    {s : ℂ} (hs_nonneg : 0 ≤ s.re) (hs_lt_one : s.re < 1)
    (hscale : ∀ i, 2 * b i ^ 2 * s.re < 1) (i : Fin (m + 1)) :
    ‖upperPeanoHybridDerivFourValue b s i.val -
        upperPeanoHybridDerivFourValue b s 0‖ ≤
      ((∑ j, b j ^ 4) / 12 : ℝ) *
        quadraticExpDerivativeMajorant 8 ‖s‖ s.re := by
  apply norm_upperPeanoHybridDerivFourValue_sub_zero_le b s i _
    (quadraticExpDerivativeMajorant_nonneg (norm_nonneg _) hs_lt_one)
  intro j
  let ρ := upperPeanoHGGRestSumLaw b j
  have hvar := upperPeanoHybridRest_totalVariance_le b j hsq
  have hrest : GaussianEvenMomentDomination ρ 1
      (weightedIndependentSumVariance
        (fun k : Fin m => b (j.succAbove k))) := by
    simpa [ρ, upperPeanoHGGRestSumLaw, upperPeanoAdjacentRestSumLaw] using
      upperPeanoHybridRestSum_evenMomentDomination b j
  have hG : Integrable (fun w => ∫ y : ℝ,
      iteratedDeriv 4 (complexQuadraticExp s) (w + b j * y)
        ∂gaussianReal 0 1) ρ := by
    simpa [ρ, upperPeanoHGGRestSumLaw, upperPeanoAdjacentRestSumLaw] using
      integrable_upperPeanoHybridRest_outer_iteratedDeriv_four b j
        (centeredGaussian_evenMomentDomination 1) hvar hs_nonneg hs_lt_one
  have hR : Integrable (fun w => ∫ y : ℝ,
      iteratedDeriv 4 (complexQuadraticExp s) (w + b j * y)
        ∂standardRademacherMeasure) ρ := by
    simpa [ρ, upperPeanoHGGRestSumLaw, upperPeanoAdjacentRestSumLaw] using
      integrable_upperPeanoHybridRest_outer_iteratedDeriv_four b j
        standardRademacher_evenMomentDomination hvar hs_nonneg hs_lt_one
  have hbefore := upperPeanoHybridDerivFourValue_split_before b s j
    (integrable_upperPeanoHybridDerivFourValue_integrand b j.val hsq
      hs_nonneg hs_lt_one)
  have hafter := upperPeanoHybridDerivFourValue_split_after b s j
    (integrable_upperPeanoHybridDerivFourValue_integrand b (j.val + 1) hsq
      hs_nonneg hs_lt_one)
  let K8 : ℂ := ∫ w, ∫ k : ℝ,
    iteratedDeriv 8 (complexQuadraticExp s) (w + b j * k)
      ∂peanoKMeasure ∂ρ
  have hstep : upperPeanoHybridDerivFourValue b s j.val -
      upperPeanoHybridDerivFourValue b s (j.val + 1) =
        (b j ^ 4 / 12 : ℝ) • K8 := by
    exact upperPeanoHybridDerivFourValue_adjacent b s j ρ (hscale j)
      hG hR hbefore hafter
  have hK8 : ‖K8‖ ≤ quadraticExpDerivativeMajorant 8 ‖s‖ s.re := by
    exact norm_integral_integral_iteratedDeriv_eight_le hrest
      peanoK_evenMomentDomination (b j) hvar s hs_nonneg hs_lt_one
  exact norm_upperPeanoHybridDerivFourValue_adjacent_le b s j _ K8 hstep hK8

/-- The exact unconditional U7 estimate for a nonempty finite list of
variance-`1/2` coefficients. -/
theorem norm_upperPeanoHybridRemainder_le
    {m : ℕ} (b : Fin (m + 1) → ℝ)
    (hsq : ∑ j, b j ^ 2 = (1 / 2 : ℝ))
    {s : ℂ} (hs_nonneg : 0 ≤ s.re) (hs_lt_one : s.re < 1)
    (hscale : ∀ i, 2 * b i ^ 2 * s.re < 1) :
    ‖upperPeanoHybridValue b s 0 - upperPeanoHybridValue b s (m + 1) -
        ((∑ i, b i ^ 4) / 12 : ℝ) •
          upperPeanoHybridDerivFourValue b s 0‖ ≤
      (∑ i, b i ^ 4) ^ 2 / 144 *
          quadraticExpDerivativeMajorant 8 ‖s‖ s.re +
        11 * (∑ i, b i ^ 6) / 180 *
          quadraticExpDerivativeMajorant 6 ‖s‖ s.re := by
  apply norm_fourthPeanoHybridRemainder_le b
    (upperPeanoHybridValue b s 0) (upperPeanoHybridValue b s (m + 1))
    (upperPeanoHybridDerivFourValue b s 0)
    (upperPeanoHybridKFourValue b s)
    (fun i => upperPeanoHybridDerivFourValue b s i.val)
    (quadraticExpDerivativeMajorant 6 ‖s‖ s.re)
    (quadraticExpDerivativeMajorant 8 ‖s‖ s.re)
  · exact upperPeanoHybridValue_hfirst b hsq hs_nonneg hs_lt_one hscale
  · intro i
    rw [upperPeanoHybridDerivFourValue_split_before b s i
      (integrable_upperPeanoHybridDerivFourValue_integrand b i.val hsq
        hs_nonneg hs_lt_one)]
    simpa [upperPeanoHybridKFourValue, upperPeanoHGGRestSumLaw,
      upperPeanoAdjacentRestSumLaw] using
      norm_upperPeanoHybridRest_gaussian_sub_peanoK_le b i hsq
        hs_nonneg hs_lt_one (hscale i)
  · intro i
    exact norm_upperPeanoHybridDerivFourValue_sub_zero_le_unconditional
      b hsq hs_nonneg hs_lt_one hscale i

/-- The unconditional finite hybrid remainder, including the empty index
case. -/
theorem norm_upperPeanoHybridRemainder_le_all
    {n : ℕ} (b : Fin n → ℝ)
    (hsq : ∑ j, b j ^ 2 = (1 / 2 : ℝ))
    {s : ℂ} (hs_nonneg : 0 ≤ s.re) (hs_lt_one : s.re < 1)
    (hscale : ∀ i, 2 * b i ^ 2 * s.re < 1) :
    ‖upperPeanoHybridValue b s 0 - upperPeanoHybridValue b s n -
        ((∑ i, b i ^ 4) / 12 : ℝ) •
          upperPeanoHybridDerivFourValue b s 0‖ ≤
      (∑ i, b i ^ 4) ^ 2 / 144 *
          quadraticExpDerivativeMajorant 8 ‖s‖ s.re +
        11 * (∑ i, b i ^ 6) / 180 *
          quadraticExpDerivativeMajorant 6 ‖s‖ s.re := by
  cases n with
  | zero => simp
  | succ m =>
      exact norm_upperPeanoHybridRemainder_le (s := s) b hsq
        hs_nonneg hs_lt_one hscale

private theorem integral_pi_reindex
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (b : ι → ℝ) (s : ℂ) (nu : Measure ℝ) [SigmaFinite nu] :
    (∫ x : κ → ℝ, complexQuadraticExp s
        (∑ i, b (e.symm i) * x i) ∂Measure.pi (fun _ : κ => nu)) =
      ∫ x : ι → ℝ, complexQuadraticExp s
        (∑ i, b i * x i) ∂Measure.pi (fun _ : ι => nu) := by
  let E := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e.symm
  rw [← (measurePreserving_piCongrLeft (fun _ : ι => nu) e.symm).integral_comp']
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [e.symm_apply_apply]
  congr 1
  change x (e i) = (Equiv.piCongrLeft (fun _ : ι => ℝ) e.symm) x i
  rw [show i = e.symm (e i) by simp, Equiv.piCongrLeft_apply_apply]
  simp

/-- The unconditional U7 estimate for the actual sparse-row distribution. -/
theorem sparseUpper_hybrid
    {d : ℕ} (a : Fin d → ℝ)
    (hsq : ∑ i, a i ^ 2 = 1)
    {s : ℂ} (hs_nonneg : 0 ≤ s.re) (hs_lt_one : s.re < 1) :
    ‖(1 - s) ^ (-1 / 2 : ℂ) -
        quadraticComplexMGF (fun row : Fin d → ℤ => realRowDot row a)
          (sparseRademacherRow d).toMeasure s -
        ((∑ p : Fin d × Fin 2,
            sparseUpperDuplicatedCoefficient a p ^ 4) / 12 : ℂ) *
          (∫ x : ℝ, iteratedDeriv 4 (complexQuadraticExp s) x
            ∂gaussianReal 0 (2 : NNReal)⁻¹)‖ ≤
      (∑ p : Fin d × Fin 2,
          sparseUpperDuplicatedCoefficient a p ^ 4) ^ 2 / 144 *
        quadraticExpDerivativeMajorant 8 ‖s‖ s.re +
      11 * (∑ p : Fin d × Fin 2,
          sparseUpperDuplicatedCoefficient a p ^ 6) / 180 *
        quadraticExpDerivativeMajorant 6 ‖s‖ s.re := by
  let e : Fin d × Fin 2 ≃ Fin (d * 2) := finProdFinEquiv
  let b : Fin (d * 2) → ℝ :=
    fun i => sparseUpperDuplicatedCoefficient a (e.symm i)
  have hsqb : ∑ i, b i ^ 2 = (1 / 2 : ℝ) := by
    rw [show (∑ i, b i ^ 2) = ∑ p : Fin d × Fin 2,
        sparseUpperDuplicatedCoefficient a p ^ 2 by
      simpa [b] using
        (e.sum_comp (fun i : Fin (d * 2) => b i ^ 2)).symm]
    simpa [sparseNormalizedVariance] using
      sum_sq_sparseUpperDuplicatedCoefficient a hsq
  have hscale (i : Fin (d * 2)) : 2 * b i ^ 2 * s.re < 1 := by
    exact sparseUpperDuplicatedCoefficient_scaled_strip a hsq hs_nonneg
      hs_lt_one (e.symm i)
  have h := norm_upperPeanoHybridRemainder_le_all b hsqb
    hs_nonneg hs_lt_one hscale
  have hzero : upperPeanoHybridValue b s 0 =
      (1 - s) ^ (-1 / 2 : ℂ) :=
    upperPeanoHybridValue_zero_eq_gaussianHalf_quadraticMGF b hsqb hs_lt_one
  have hfour : upperPeanoHybridDerivFourValue b s 0 =
      ∫ x : ℝ, iteratedDeriv 4 (complexQuadraticExp s) x
        ∂gaussianReal 0 (2 : NNReal)⁻¹ :=
    upperPeanoHybridDerivFourValue_zero_eq_gaussianHalf b s hsqb
  have hcard : upperPeanoHybridValue b s (d * 2) =
      quadraticComplexMGF (fun row : Fin d → ℤ => realRowDot row a)
        (sparseRademacherRow d).toMeasure s := by
    rw [upperPeanoHybridValue_card]
    calc
      (∫ x : Fin (d * 2) → ℝ, complexQuadraticExp s
          (∑ i, b i * x i)
          ∂Measure.pi (fun _ : Fin (d * 2) => standardRademacherMeasure)) =
          ∫ x : Fin d × Fin 2 → ℝ, complexQuadraticExp s
            (∑ p, sparseUpperDuplicatedCoefficient a p * x p)
            ∂Measure.pi (fun _ : Fin d × Fin 2 =>
              standardRademacherMeasure) := by
        exact integral_pi_reindex e (sparseUpperDuplicatedCoefficient a) s
          standardRademacherMeasure
      _ = _ := (quadraticComplexMGF_sparseRow_eq_pi_standardRademacher a s).symm
  have hpow4 : (∑ i, b i ^ 4) = ∑ p : Fin d × Fin 2,
      sparseUpperDuplicatedCoefficient a p ^ 4 := by
    simpa [b] using
      (e.sum_comp (fun i : Fin (d * 2) => b i ^ 4)).symm
  have hpow6 : (∑ i, b i ^ 6) = ∑ p : Fin d × Fin 2,
      sparseUpperDuplicatedCoefficient a p ^ 6 := by
    simpa [b] using
      (e.sum_comp (fun i : Fin (d * 2) => b i ^ 6)).symm
  rw [hzero, hcard, hfour, hpow4, hpow6] at h
  rw [Complex.real_smul, show
    ((((∑ p : Fin d × Fin 2,
      sparseUpperDuplicatedCoefficient a p ^ 4) / 12 : ℝ) : ℂ)) =
        (((∑ p : Fin d × Fin 2,
          sparseUpperDuplicatedCoefficient a p ^ 4 : ℝ) : ℂ) / 12) by
            norm_num] at h
  exact h

/-- The literal unconditional fourth-order sparse-row comparison. -/
theorem sparseUpper_fourthOrder
    {d : ℕ} (a : Fin d → ℝ)
    (hsq : ∑ i, a i ^ 2 = 1)
    {s : ℂ} (hs_nonneg : 0 ≤ s.re) (hs_lt_one : s.re < 1) :
    ‖quadraticComplexMGF (fun row : Fin d → ℤ => realRowDot row a)
          (sparseRademacherRow d).toMeasure s -
        (1 - s) ^ (-1 / 2 : ℂ) +
        ((sparseProfileFourthMoment a / 8 : ℝ) : ℂ) * s ^ 2 *
          (1 - s) ^ (-5 / 2 : ℂ)‖ ≤
      sparseProfileFourthMoment a ^ 2 / 9216 *
          quadraticExpDerivativeMajorant 8 ‖s‖ s.re +
        11 * (sparseProfileFourthMoment a *
          Real.sqrt (sparseProfileFourthMoment a)) / 5760 *
            quadraticExpDerivativeMajorant 6 ‖s‖ s.re := by
  exact sparseUpper_fourthOrder_of_hybrid a _ hs_lt_one
    (sparseUpper_hybrid a hsq hs_nonneg hs_lt_one)

end CertifiedJL
