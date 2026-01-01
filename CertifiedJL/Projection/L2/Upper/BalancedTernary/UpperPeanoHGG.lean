/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperPeanoHybridProducts
import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperPeanoTelescope
import CertifiedJL.Analysis.Peano.PeanoGaussianRademacherScaled

/-! # The derivative-four Gaussian endpoint bound in the upper Peano hybrid -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CertifiedJL

/-- The derivative-four expectation at a concrete mixed-product stage. -/
noncomputable def upperPeanoHybridDerivFourValue {n : ℕ}
    (b : Fin n → ℝ) (s : ℂ) (k : ℕ) : ℂ :=
  ∫ x : Fin n → ℝ,
    iteratedDeriv 4 (complexQuadraticExp s) (∑ i, b i * x i)
      ∂Measure.pi (upperPeanoHybridCoordinateLaw k)

/-- The pushforward law of the weighted coordinates other than `i`, used only
by the derivative-four hGG telescope. -/
noncomputable def upperPeanoHGGRestSumLaw {m : ℕ}
    (b : Fin (m + 1) → ℝ) (i : Fin (m + 1)) : Measure ℝ :=
  Measure.map (fun x : Fin m → ℝ => ∑ j, b (i.succAbove j) * x j)
    (Measure.pi (upperPeanoHybridRestCoordinateLaw i))

private theorem integrable_iteratedDeriv_of_halfDomination
    {mu : Measure ℝ} {mass : ℝ} {variance : NNReal}
    (hmu : GaussianEvenMomentDomination mu mass variance)
    (hvariance : variance ≤ (2 : NNReal)⁻¹)
    (j : ℕ) {s : ℂ} (hs_nonneg : 0 ≤ s.re) (hs_lt_one : s.re < 1) :
    Integrable (iteratedDeriv j (complexQuadraticExp s)) mu := by
  let p := complexQuadraticExpDerivativePolynomial s j
  have hpow (n : ℕ) : Integrable (fun x : ℝ =>
      |x| ^ n * Real.exp (s.re * x ^ 2)) mu := by
    have h0 := (tiltedEvenMoment_le_of_gaussianEvenMomentDomination
      hmu hvariance 0 hs_nonneg hs_lt_one).1
    have hn := (tiltedEvenMoment_le_of_gaussianEvenMomentDomination
      hmu hvariance n hs_nonneg hs_lt_one).1
    have hmajor := h0.add hn
    refine Integrable.mono' hmajor (by fun_prop) ?_
    filter_upwards [] with x
    have hx : |x| ^ n ≤ 1 + |x| ^ (2 * n) := by
      by_cases h : |x| ≤ 1
      · exact (pow_le_one₀ (abs_nonneg _) h).trans
          (le_add_of_nonneg_right (pow_nonneg (abs_nonneg _) _))
      · exact (pow_le_pow_right₀ (le_of_not_ge h)
          (by omega : n ≤ 2 * n)).trans
          (le_add_of_nonneg_left (by norm_num))
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (pow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le)]
    calc
      |x| ^ n * Real.exp (s.re * x ^ 2) ≤
          (1 + |x| ^ (2 * n)) * Real.exp (s.re * x ^ 2) :=
        mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
      _ = 1 * Real.exp (s.re * x ^ 2) +
          |x| ^ (2 * n) * Real.exp (s.re * x ^ 2) := by ring
  have hmajor : Integrable (fun x : ℝ =>
      ∑ n ∈ p.support, ‖p.coeff n‖ *
        (|x| ^ n * Real.exp (s.re * x ^ 2))) mu := by
    apply integrable_finsetSum
    intro n hn
    exact (hpow n).const_mul _
  have hcont : Continuous (iteratedDeriv j (complexQuadraticExp s)) :=
    ((contDiff_omega_complexQuadraticExp s).of_le (by simp)).continuous_iteratedDeriv' j
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

/-- Normalized mixed products integrate the derivative-four quadratic
exponential throughout the positive U7 strip. -/
theorem integrable_upperPeanoHybridDerivFourValue_integrand
    {n : ℕ} (b : Fin n → ℝ) (k : ℕ)
    (hsq : ∑ i, b i ^ 2 = (1 / 2 : ℝ))
    {s : ℂ} (hs_nonneg : 0 ≤ s.re) (hs_lt_one : s.re < 1) :
    Integrable (fun x : Fin n → ℝ =>
      iteratedDeriv 4 (complexQuadraticExp s) (∑ i, b i * x i))
      (Measure.pi (upperPeanoHybridCoordinateLaw k)) := by
  let (i : Fin n) : IsProbabilityMeasure
      (upperPeanoHybridCoordinateLaw k i) := by
    unfold upperPeanoHybridCoordinateLaw
    split <;> infer_instance
  have hdom := upperPeanoHybridSum_evenMomentDomination b k
  have hvariance : weightedIndependentSumVariance b ≤ (2 : NNReal)⁻¹ := by
    apply NNReal.coe_le_coe.mp
    rw [coe_weightedIndependentSumVariance, hsq]
    norm_num
  have hμ := integrable_iteratedDeriv_of_halfDomination
    hdom hvariance 4 hs_nonneg hs_lt_one
  rw [← map_weightedSum_pi_eq_weightedIndependentSumLaw b
    (upperPeanoHybridCoordinateLaw k)] at hμ
  have hsum : Continuous (fun x : Fin n → ℝ => ∑ i, b i * x i) := by
    apply continuous_finsetSum
    intro i hi
    exact continuous_const.mul (continuous_apply i)
  exact (integrable_map_measure
    (f := fun x : Fin n → ℝ => ∑ i, b i * x i)
    (g := iteratedDeriv 4 (complexQuadraticExp s))
    hμ.aestronglyMeasurable hsum.measurable.aemeasurable).mp hμ

private theorem upperPeanoHybridIntegral_split
    {m : ℕ} (b : Fin (m + 1) → ℝ) (i : Fin (m + 1)) (k : ℕ)
    (nu : Measure ℝ) [SFinite nu] (phi : ℝ → ℂ) (hphi : Continuous phi)
    (hmap : Measure.map
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i)
        (Measure.pi (upperPeanoHybridCoordinateLaw k)) =
      nu.prod (Measure.pi (upperPeanoHybridRestCoordinateLaw i)))
    (hint : Integrable (fun x : Fin (m + 1) → ℝ =>
      phi (∑ j, b j * x j))
      (Measure.pi (upperPeanoHybridCoordinateLaw k))) :
    Integrable (fun w => ∫ y : ℝ, phi (w + b i * y) ∂nu)
        (upperPeanoHGGRestSumLaw b i) ∧
    ((∫ x : Fin (m + 1) → ℝ, phi (∑ j, b j * x j)
        ∂Measure.pi (upperPeanoHybridCoordinateLaw k)) =
      ∫ w, ∫ y : ℝ, phi (w + b i * y) ∂nu
        ∂upperPeanoHGGRestSumLaw b i) := by
  let (j : Fin (m + 1)) : IsProbabilityMeasure
      (upperPeanoHybridCoordinateLaw k j) := by
    unfold upperPeanoHybridCoordinateLaw
    split <;> infer_instance
  let (j : Fin m) : IsProbabilityMeasure
      (upperPeanoHybridRestCoordinateLaw i j) := by
    unfold upperPeanoHybridRestCoordinateLaw upperPeanoHybridCoordinateLaw
    split <;> infer_instance
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i
  let F : (Fin (m + 1) → ℝ) → ℂ := fun x => phi (∑ j, b j * x j)
  let g : ℝ × (Fin m → ℝ) → ℂ := fun p => F (e.symm p)
  let restSum : (Fin m → ℝ) → ℝ :=
    fun x => ∑ j, b (i.succAbove j) * x j
  let J : ℝ → ℂ := fun w => ∫ y : ℝ, phi (w + b i * y) ∂nu
  have hFcont : Continuous F := by
    apply hphi.comp
    apply continuous_finsetSum
    intro j hj
    exact continuous_const.mul (continuous_apply j)
  have hgmeas : AEStronglyMeasurable g
      (Measure.map e (Measure.pi (upperPeanoHybridCoordinateLaw k))) :=
    (hFcont.measurable.comp e.symm.measurable).aestronglyMeasurable
  have hgmap : Integrable g
      (Measure.map e (Measure.pi (upperPeanoHybridCoordinateLaw k))) := by
    apply (integrable_map_measure (g := g) (f := e)
      hgmeas e.measurable.aemeasurable).mpr
    convert hint using 1
    funext x
    exact congrArg F (e.symm_apply_apply x)
  rw [hmap] at hgmap
  have hJcomp : Integrable (J ∘ restSum)
      (Measure.pi (upperPeanoHybridRestCoordinateLaw i)) := by
    refine hgmap.integral_prod_right.congr (ae_of_all _ fun x => ?_)
    apply integral_congr_ae
    filter_upwards [] with y
    rw [show g (y, x) = phi (restSum x + b i * y) by
      simp only [g, F, e, restSum]
      rw [weightedSum_piFinSuccAbove_symm b i]
      congr 1
      ring]
  have hJmeas : AEStronglyMeasurable J (upperPeanoHGGRestSumLaw b i) := by
    have hjoint : AEStronglyMeasurable
        (fun p : ℝ × ℝ => phi (p.1 + b i * p.2))
        ((upperPeanoHGGRestSumLaw b i).prod nu) :=
      (hphi.comp (continuous_fst.add
        (continuous_const.mul continuous_snd))).aestronglyMeasurable
    simpa [J] using hjoint.integral_prod_right'
  have hJ : Integrable J (upperPeanoHGGRestSumLaw b i) := by
    unfold upperPeanoHGGRestSumLaw
    have hrest : AEMeasurable restSum
        (Measure.pi (upperPeanoHybridRestCoordinateLaw i)) := by
      apply Continuous.aemeasurable
      dsimp [restSum]
      apply continuous_finsetSum
      intro j hj
      exact continuous_const.mul (continuous_apply j)
    exact (integrable_map_measure (g := J) (f := restSum)
      hJmeas hrest).mpr hJcomp
  refine ⟨hJ, ?_⟩
  calc
    (∫ x, F x ∂Measure.pi (upperPeanoHybridCoordinateLaw k)) =
        ∫ p, g p ∂Measure.map e
          (Measure.pi (upperPeanoHybridCoordinateLaw k)) := by
      rw [integral_map (by fun_prop) (by fun_prop)]
      apply integral_congr_ae
      filter_upwards [] with x
      exact congrArg F (e.symm_apply_apply x).symm
    _ = ∫ p, g p ∂nu.prod
          (Measure.pi (upperPeanoHybridRestCoordinateLaw i)) := by rw [hmap]
    _ = ∫ x, J (restSum x)
          ∂Measure.pi (upperPeanoHybridRestCoordinateLaw i) := by
      rw [integral_prod_symm _ hgmap]
      apply integral_congr_ae
      filter_upwards [] with x
      apply integral_congr_ae
      filter_upwards [] with y
      rw [show g (y, x) = phi (restSum x + b i * y) by
        simp only [g, F, e, restSum]
        rw [weightedSum_piFinSuccAbove_symm b i]
        congr 1
        ring]
    _ = ∫ w, J w ∂upperPeanoHGGRestSumLaw b i := by
      unfold upperPeanoHGGRestSumLaw
      have hrest : AEMeasurable restSum
          (Measure.pi (upperPeanoHybridRestCoordinateLaw i)) := by
        apply Continuous.aemeasurable
        dsimp [restSum]
        apply continuous_finsetSum
        intro j hj
        exact continuous_const.mul (continuous_apply j)
      rw [integral_map hrest hJ.aestronglyMeasurable]

private theorem continuous_iteratedDeriv_four_complexQuadraticExp (s : ℂ) :
    Continuous (iteratedDeriv 4 (complexQuadraticExp s)) :=
  (contDiff_complexQuadraticExp s).continuous_iteratedDeriv' 4

/-- The derivative-four hybrid immediately before a coordinate replacement
splits over the concrete common rest-sum law and a Gaussian coordinate. -/
theorem upperPeanoHybridDerivFourValue_split_before
    {m : ℕ} (b : Fin (m + 1) → ℝ) (s : ℂ) (i : Fin (m + 1))
    (hint : Integrable (fun x : Fin (m + 1) → ℝ =>
      iteratedDeriv 4 (complexQuadraticExp s) (∑ j, b j * x j))
      (Measure.pi (upperPeanoHybridCoordinateLaw i.val))) :
    upperPeanoHybridDerivFourValue b s i.val =
      ∫ w, ∫ y : ℝ,
        iteratedDeriv 4 (complexQuadraticExp s) (w + b i * y)
          ∂gaussianReal 0 1 ∂upperPeanoHGGRestSumLaw b i := by
  unfold upperPeanoHybridDerivFourValue
  exact (upperPeanoHybridIntegral_split b i i.val (gaussianReal 0 1)
    _ (continuous_iteratedDeriv_four_complexQuadraticExp s)
    (upperPeanoHybridMeasure_before_map_piFinSuccAbove i) hint).2

/-- The derivative-four hybrid immediately after a coordinate replacement
splits over the same rest-sum law and a Rademacher coordinate. -/
theorem upperPeanoHybridDerivFourValue_split_after
    {m : ℕ} (b : Fin (m + 1) → ℝ) (s : ℂ) (i : Fin (m + 1))
    (hint : Integrable (fun x : Fin (m + 1) → ℝ =>
      iteratedDeriv 4 (complexQuadraticExp s) (∑ j, b j * x j))
      (Measure.pi (upperPeanoHybridCoordinateLaw (i.val + 1)))) :
    upperPeanoHybridDerivFourValue b s (i.val + 1) =
      ∫ w, ∫ y : ℝ,
        iteratedDeriv 4 (complexQuadraticExp s) (w + b i * y)
          ∂standardRademacherMeasure ∂upperPeanoHGGRestSumLaw b i := by
  unfold upperPeanoHybridDerivFourValue
  exact (upperPeanoHybridIntegral_split b i (i.val + 1)
    standardRademacherMeasure _
    (continuous_iteratedDeriv_four_complexQuadraticExp s)
    (upperPeanoHybridMeasure_after_map_piFinSuccAbove i) hint).2

/-- The derivative-offset fourth-Peano identity gives one exact adjacent step
after both product integrals are split over their common rest-sum law. -/
theorem upperPeanoHybridDerivFourValue_adjacent
    {n : ℕ} (b : Fin n → ℝ) (s : ℂ) (i : Fin n) (ρ : Measure ℝ)
    (hscale : 2 * b i ^ 2 * s.re < 1)
    (hG : Integrable (fun w => ∫ y : ℝ,
      iteratedDeriv 4 (complexQuadraticExp s) (w + b i * y)
        ∂gaussianReal 0 1) ρ)
    (hR : Integrable (fun w => ∫ y : ℝ,
      iteratedDeriv 4 (complexQuadraticExp s) (w + b i * y)
        ∂standardRademacherMeasure) ρ)
    (hbefore : upperPeanoHybridDerivFourValue b s i.val =
      ∫ w, ∫ y : ℝ,
        iteratedDeriv 4 (complexQuadraticExp s) (w + b i * y)
          ∂gaussianReal 0 1 ∂ρ)
    (hafter : upperPeanoHybridDerivFourValue b s (i.val + 1) =
      ∫ w, ∫ y : ℝ,
        iteratedDeriv 4 (complexQuadraticExp s) (w + b i * y)
          ∂standardRademacherMeasure ∂ρ) :
    upperPeanoHybridDerivFourValue b s i.val -
        upperPeanoHybridDerivFourValue b s (i.val + 1) =
      (b i ^ 4 / 12 : ℝ) • ∫ w, ∫ k : ℝ,
        iteratedDeriv 8 (complexQuadraticExp s) (w + b i * k)
          ∂peanoKMeasure ∂ρ := by
  rw [hbefore, hafter]
  exact
    peanoIdentity4_partialSum_standardGaussianRademacher_scaled_iteratedDeriv_four
      (b i) hscale hG hR

/-- A uniform derivative-eight bound turns an exact adjacent replacement into
the corresponding norm estimate. -/
theorem norm_upperPeanoHybridDerivFourValue_adjacent_le
    {n : ℕ} (b : Fin n → ℝ) (s : ℂ) (i : Fin n) (D8 : ℝ)
    (K8 : ℂ)
    (hstep : upperPeanoHybridDerivFourValue b s i.val -
        upperPeanoHybridDerivFourValue b s (i.val + 1) =
      (b i ^ 4 / 12 : ℝ) • K8)
    (hK8 : ‖K8‖ ≤ D8) :
    ‖upperPeanoHybridDerivFourValue b s (i.val + 1) -
        upperPeanoHybridDerivFourValue b s i.val‖ ≤
      (b i ^ 4 / 12 : ℝ) * D8 := by
  rw [← norm_neg (upperPeanoHybridDerivFourValue b s (i.val + 1) -
    upperPeanoHybridDerivFourValue b s i.val)]
  have hneg : -(upperPeanoHybridDerivFourValue b s (i.val + 1) -
      upperPeanoHybridDerivFourValue b s i.val) =
      upperPeanoHybridDerivFourValue b s i.val -
        upperPeanoHybridDerivFourValue b s (i.val + 1) := by ring
  rw [hneg, hstep, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (by positivity) (by norm_num))]
  exact mul_le_mul_of_nonneg_left hK8
    (div_nonneg (by positivity) (by norm_num))

/-- Telescoping the adjacent derivative-four replacements bounds every mixed
stage by the all-Gaussian derivative-four endpoint with the exact U7
coefficient. -/
theorem norm_upperPeanoHybridDerivFourValue_sub_zero_le
    {n : ℕ} (b : Fin n → ℝ) (s : ℂ) (i : Fin n) (D8 : ℝ)
    (hD8 : 0 ≤ D8)
    (hadj : ∀ j : Fin n,
      ‖upperPeanoHybridDerivFourValue b s (j.val + 1) -
          upperPeanoHybridDerivFourValue b s j.val‖ ≤
        (b j ^ 4 / 12 : ℝ) * D8) :
    ‖upperPeanoHybridDerivFourValue b s i.val -
        upperPeanoHybridDerivFourValue b s 0‖ ≤
      ((∑ j, b j ^ 4) / 12 : ℝ) * D8 := by
  let V : ℕ → ℂ := upperPeanoHybridDerivFourValue b s
  let c : ℕ → ℝ := fun j =>
    if hj : j < n then (b ⟨j, hj⟩ ^ 4 / 12 : ℝ) * D8 else 0
  have hc (j : ℕ) (hj : j < n) : 0 ≤ c j := by
    simp only [c, dif_pos hj]
    positivity
  have hadj' (j : ℕ) (hj : j < n) :
      ‖V (j + 1) - V j‖ ≤ c j := by
    simpa only [V, c, dif_pos hj] using hadj ⟨j, hj⟩
  rw [← Finset.sum_range_sub V i.val]
  calc
    ‖∑ j ∈ Finset.range i.val, (V (j + 1) - V j)‖ ≤
        ∑ j ∈ Finset.range i.val, ‖V (j + 1) - V j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range i.val, c j := by
      apply Finset.sum_le_sum
      intro j hj
      exact hadj' j (lt_trans (Finset.mem_range.mp hj) i.isLt)
    _ ≤ ∑ j ∈ Finset.range n, c j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.le_of_lt i.isLt))
      intro j hj hn
      exact hc j (Finset.mem_range.mp hj)
    _ = ((∑ j, b j ^ 4) / 12 : ℝ) * D8 := by
      rw [← Fin.sum_univ_eq_sum_range c n]
      simp_rw [c, dif_pos (Fin.isLt _)]
      rw [← Finset.sum_mul, ← Finset.sum_div]

end CertifiedJL
