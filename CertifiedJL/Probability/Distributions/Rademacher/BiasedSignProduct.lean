/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Finite.UniformPiBridge
import CertifiedJL.Probability.Distributions.Rademacher.BiasedSign
import CertifiedJL.Probability.Distributions.Rademacher.Rademacher
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Probability.Moments.Variance

/-!
# Finite products of exponentially biased signs

This module packages the one-coordinate tilted Rademacher law from
`CertifiedJL.Probability.Distributions.Rademacher.BiasedSign` as an actual finite PMF and constructs
its coordinatewise product.  The point-mass and finite-expectation APIs are
kept explicit so that later Esscher and Berry--Esseen arguments can move
between exact finite experiments and product measures without an implicit
probabilistic bridge.
-/

open scoped BigOperators ENNReal

open MeasureTheory ProbabilityTheory

namespace CertifiedJL
namespace Probability

universe u

/-- The `ENNReal` point mass of one exponentially biased sign bit. -/
noncomputable def biasedSignMass (u : ℝ) (b : Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (biasedSignWeight u b)

@[simp]
theorem biasedSignMass_false (u : ℝ) :
    biasedSignMass u false = ENNReal.ofReal (biasedSignNegWeight u) := rfl

@[simp]
theorem biasedSignMass_true (u : ℝ) :
    biasedSignMass u true = ENNReal.ofReal (biasedSignPosWeight u) := rfl

theorem biasedSignMass_sum (u : ℝ) :
    ∑ b : Bool, biasedSignMass u b = 1 := by
  rw [Fintype.sum_bool]
  change ENNReal.ofReal (biasedSignPosWeight u) +
      ENNReal.ofReal (biasedSignNegWeight u) = 1
  rw [← ENNReal.ofReal_add (biasedSignPosWeight_nonneg u)
    (biasedSignNegWeight_nonneg u)]
  rw [add_comm, biasedSign_weights_sum]
  simp

/-- The PMF of one Rademacher sign exponentially tilted by `u`. -/
noncomputable def biasedSignPMF (u : ℝ) : PMF Bool :=
  PMF.ofFintype (biasedSignMass u) (biasedSignMass_sum u)

@[simp]
theorem biasedSignPMF_apply (u : ℝ) (b : Bool) :
    biasedSignPMF u b = biasedSignMass u b := rfl

theorem biasedSignPMF_toReal_apply (u : ℝ) (b : Bool) :
    (biasedSignPMF u b).toReal = biasedSignWeight u b := by
  rw [biasedSignPMF_apply, biasedSignMass]
  exact ENNReal.toReal_ofReal (by
    cases b
    · exact biasedSignNegWeight_nonneg u
    · exact biasedSignPosWeight_nonneg u)

/-- The product point mass of coordinatewise exponentially biased signs. -/
noncomputable def biasedSignProductMass {ι : Type u} [Fintype ι]
    (u : ι → ℝ) (bits : ι → Bool) : ℝ≥0∞ :=
  ∏ i, biasedSignMass (u i) (bits i)

/-- The product masses sum to one. -/
theorem biasedSignProductMass_hasSum {ι : Type u} [Fintype ι]
    (u : ι → ℝ) :
    HasSum (biasedSignProductMass u) 1 := by
  classical
  have hsum : ∑ bits : ι → Bool, biasedSignProductMass u bits = 1 := by
    change (∑ bits : ι → Bool,
      ∏ i, biasedSignMass (u i) (bits i)) = 1
    calc
      (∑ bits : ι → Bool,
          ∏ i, biasedSignMass (u i) (bits i)) =
          ∏ i, ∑ b : Bool, biasedSignMass (u i) b :=
        (Fintype.prod_sum
          (fun i b => biasedSignMass (u i) b)).symm
      _ = 1 := by simp only [biasedSignMass_sum, Finset.prod_const_one]
  exact hsum ▸ hasSum_fintype (biasedSignProductMass u)

/-- The independent finite product of exponentially biased sign bits. -/
noncomputable def biasedSignProductPMF {ι : Type u} [Fintype ι]
    (u : ι → ℝ) : PMF (ι → Bool) :=
  ⟨biasedSignProductMass u, biasedSignProductMass_hasSum u⟩

@[simp]
theorem biasedSignProductPMF_apply {ι : Type u} [Fintype ι]
    (u : ι → ℝ) (bits : ι → Bool) :
    biasedSignProductPMF u bits = biasedSignProductMass u bits := rfl

theorem biasedSignProductPMF_toReal_apply {ι : Type u} [Fintype ι]
    (u : ι → ℝ) (bits : ι → Bool) :
    (biasedSignProductPMF u bits).toReal =
      ∏ i, biasedSignWeight (u i) (bits i) := by
  rw [biasedSignProductPMF_apply, biasedSignProductMass, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact biasedSignPMF_toReal_apply (u i) (bits i)

/--
The finite biased-sign PMF is exactly the product of its one-coordinate
measures.
-/
theorem biasedSignProductPMF_toMeasure {ι : Type u} [Fintype ι]
    (u : ι → ℝ) :
    (biasedSignProductPMF u).toMeasure =
      Measure.pi (fun i => (biasedSignPMF (u i)).toMeasure) := by
  classical
  apply Measure.ext_of_singleton
  intro bits
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton bits)]
  rw [Measure.pi_singleton]
  apply Finset.prod_congr rfl
  intro i _
  rw [PMF.toMeasure_apply_singleton _ _
    (measurableSet_singleton (bits i))]
  rfl

/-- Every coordinate has the prescribed exponentially biased marginal. -/
theorem biasedSignProductPMF_marginal {ι : Type u} [Fintype ι]
    (u : ι → ℝ) (i : ι) :
    (biasedSignProductPMF u).map (fun bits => bits i) =
      biasedSignPMF (u i) := by
  classical
  apply PMF.ext
  intro b
  calc
    ((biasedSignProductPMF u).map (fun bits => bits i)) b =
        ((biasedSignProductPMF u).map
          (fun bits => bits i)).toMeasure {b} := by
      rw [PMF.toMeasure_apply_singleton _ _
        (measurableSet_singleton b)]
    _ = (biasedSignProductPMF u).toMeasure
          ((fun bits => bits i) ⁻¹' {b}) := by
      rw [PMF.toMeasure_map_apply _ _ _ (measurable_pi_apply i)
        (measurableSet_singleton b)]
    _ = Measure.pi
          (fun j => (biasedSignPMF (u j)).toMeasure)
          ((fun bits => bits i) ⁻¹' {b}) := by
      rw [biasedSignProductPMF_toMeasure]
    _ = (Measure.pi
          (fun j => (biasedSignPMF (u j)).toMeasure)).map
          (fun bits => bits i) {b} := by
      rw [Measure.map_apply (measurable_pi_apply i)
        (measurableSet_singleton b)]
    _ = (biasedSignPMF (u i)).toMeasure {b} := by
      rw [(measurePreserving_eval
        (fun j => (biasedSignPMF (u j)).toMeasure) i).map_eq]
    _ = biasedSignPMF (u i) b := by
      rw [PMF.toMeasure_apply_singleton _ _
        (measurableSet_singleton b)]

/-- The coordinate projections of the biased product law are independent. -/
theorem biasedSignProductPMF_iIndep {ι : Type u} [Fintype ι]
    (u : ι → ℝ) :
    iIndepFun (fun i bits => bits i)
      (biasedSignProductPMF u).toMeasure := by
  classical
  rw [biasedSignProductPMF_toMeasure]
  simpa using
    (iIndepFun_pi
      (μ := fun i => (biasedSignPMF (u i)).toMeasure)
      (X := fun _ => id) (fun _ => aemeasurable_id))

/--
The centered weighted coordinate summands remain mutually independent under
the biased product law.
-/
theorem biasedSignProduct_centeredWeighted_iIndep
    {ι : Type u} [Fintype ι] (u a : ι → ℝ) :
    iIndepFun
      (fun i bits =>
        a i * (biasedSignValue (bits i) - Real.tanh (u i)))
      (biasedSignProductPMF u).toMeasure := by
  have h := (biasedSignProductPMF_iIndep u).comp
    (fun i b =>
      a i * (biasedSignValue b - Real.tanh (u i)))
    (fun i => measurable_of_finite _)
  convert h using 1
  funext i bits
  rfl

/-- Finite expectation under the independent biased-sign product law. -/
noncomputable def biasedSignProductExpectation {ι : Type u} [Fintype ι]
    (u : ι → ℝ) (f : (ι → Bool) → ℝ) : ℝ :=
  ∑' bits, (biasedSignProductPMF u bits).toReal * f bits

/--
Expectations of coordinatewise products factor into the one-coordinate
expectations.
-/
theorem biasedSignProductExpectation_prod {ι : Type u} [Fintype ι]
    (u : ι → ℝ) (f : ι → ℝ → ℝ) :
    biasedSignProductExpectation u
        (fun bits => ∏ i, f i (biasedSignValue (bits i))) =
      ∏ i, biasedSignExpectation (u i) (f i) := by
  classical
  unfold biasedSignProductExpectation
  rw [tsum_fintype]
  simp_rw [biasedSignProductPMF_toReal_apply]
  simp_rw [← Finset.prod_mul_distrib]
  calc
    (∑ bits : ι → Bool,
        ∏ i, biasedSignWeight (u i) (bits i) *
          f i (biasedSignValue (bits i))) =
        ∏ i, ∑ b : Bool,
          biasedSignWeight (u i) b * f i (biasedSignValue b) :=
      (Fintype.prod_sum (fun i b =>
        biasedSignWeight (u i) b * f i (biasedSignValue b))).symm
    _ = ∏ i, biasedSignExpectation (u i) (f i) := by
      apply Finset.prod_congr rfl
      intro i _
      rfl

/-- The finite-sum expectation agrees with the corresponding PMF integral. -/
theorem biasedSignProductExpectation_eq_integral
    {ι : Type u} [Fintype ι] (u : ι → ℝ)
    (f : (ι → Bool) → ℝ) :
    biasedSignProductExpectation u f =
      ∫ bits, f bits ∂(biasedSignProductPMF u).toMeasure := by
  classical
  rw [finitePMF_integral_eq_sum]
  unfold biasedSignProductExpectation
  rw [tsum_fintype]
  simp only [smul_eq_mul]

/-- A one-coordinate observable has its one-coordinate expectation. -/
theorem biasedSignProductExpectation_coord
    {ι : Type u} [Fintype ι] (u : ι → ℝ) (i : ι)
    (g : Bool → ℝ) :
    biasedSignProductExpectation u (fun bits => g (bits i)) =
      ∑ b : Bool, biasedSignWeight (u i) b * g b := by
  rw [biasedSignProductExpectation_eq_integral]
  rw [← integral_map (μ := (biasedSignProductPMF u).toMeasure)
    (measurable_pi_apply i).aemeasurable
    (measurable_of_finite g).aestronglyMeasurable]
  rw [PMF.toMeasure_map _ _ (measurable_pi_apply i)]
  rw [biasedSignProductPMF_marginal]
  rw [finitePMF_integral_eq_sum]
  simp only [biasedSignPMF_toReal_apply, smul_eq_mul]

/-- Pulling a real scalar through the elementary biased-sign expectation. -/
theorem biasedSignExpectation_const_mul (u c : ℝ) (f : ℝ → ℝ) :
    biasedSignExpectation u (fun x => c * f x) =
      c * biasedSignExpectation u f := by
  rw [biasedSignExpectation_apply, biasedSignExpectation_apply]
  ring

/-- The centered weighted `i`-th sign summand has mean zero. -/
theorem biasedSignProduct_centeredWeightedMean {ι : Type u} [Fintype ι]
    (u a : ι → ℝ) (i : ι) :
    biasedSignProductExpectation u
        (fun bits =>
          a i * (biasedSignValue (bits i) - Real.tanh (u i))) = 0 := by
  change biasedSignProductExpectation u
      (fun bits => (fun b : Bool =>
        a i * (biasedSignValue b - Real.tanh (u i))) (bits i)) = 0
  calc
    biasedSignProductExpectation u
        (fun bits => (fun b : Bool =>
          a i * (biasedSignValue b - Real.tanh (u i))) (bits i)) =
        ∑ b : Bool, biasedSignWeight (u i) b *
          (a i * (biasedSignValue b - Real.tanh (u i))) :=
      biasedSignProductExpectation_coord u i
        (g := fun b : Bool =>
          a i * (biasedSignValue b - Real.tanh (u i)))
    _ = 0 := by
      change biasedSignExpectation (u i)
          (fun x => a i * (x - Real.tanh (u i))) = 0
      rw [biasedSignExpectation_const_mul]
      rw [biasedSignExpectation_apply]
      unfold biasedSignNegWeight biasedSignPosWeight
      ring

/-- The centered second moment of the weighted `i`-th sign summand. -/
theorem biasedSignProduct_centeredWeightedVariance
    {ι : Type u} [Fintype ι] (u a : ι → ℝ) (i : ι) :
    biasedSignProductExpectation u
        (fun bits =>
          (a i * (biasedSignValue (bits i) - Real.tanh (u i))) ^ 2) =
      a i ^ 2 * (1 - Real.tanh (u i) ^ 2) := by
  change biasedSignProductExpectation u
      (fun bits => (fun b : Bool =>
        (a i * (biasedSignValue b - Real.tanh (u i))) ^ 2) (bits i)) =
    a i ^ 2 * (1 - Real.tanh (u i) ^ 2)
  calc
    biasedSignProductExpectation u
        (fun bits => (fun b : Bool =>
          (a i * (biasedSignValue b - Real.tanh (u i))) ^ 2) (bits i)) =
        ∑ b : Bool, biasedSignWeight (u i) b *
          (a i * (biasedSignValue b - Real.tanh (u i))) ^ 2 :=
      biasedSignProductExpectation_coord u i
        (g := fun b : Bool =>
          (a i * (biasedSignValue b - Real.tanh (u i))) ^ 2)
    _ = a i ^ 2 * (1 - Real.tanh (u i) ^ 2) := by
      change biasedSignExpectation (u i)
          (fun x => (a i * (x - Real.tanh (u i))) ^ 2) =
        a i ^ 2 * (1 - Real.tanh (u i) ^ 2)
      simp_rw [mul_pow]
      rw [biasedSignExpectation_const_mul]
      rw [biasedSign_centeredVariance]

/-- The third absolute centered moment of the weighted `i`-th sign summand. -/
theorem biasedSignProduct_thirdAbsoluteCenteredMoment
    {ι : Type u} [Fintype ι] (u a : ι → ℝ) (i : ι) :
    biasedSignProductExpectation u
        (fun bits =>
          |a i * (biasedSignValue (bits i) - Real.tanh (u i))| ^ 3) =
      |a i| ^ 3 * (1 - Real.tanh (u i) ^ 4) := by
  change biasedSignProductExpectation u
      (fun bits => (fun b : Bool =>
        |a i * (biasedSignValue b - Real.tanh (u i))| ^ 3) (bits i)) =
    |a i| ^ 3 * (1 - Real.tanh (u i) ^ 4)
  calc
    biasedSignProductExpectation u
        (fun bits => (fun b : Bool =>
          |a i * (biasedSignValue b - Real.tanh (u i))| ^ 3) (bits i)) =
        ∑ b : Bool, biasedSignWeight (u i) b *
          |a i * (biasedSignValue b - Real.tanh (u i))| ^ 3 :=
      biasedSignProductExpectation_coord u i
        (g := fun b : Bool =>
          |a i * (biasedSignValue b - Real.tanh (u i))| ^ 3)
    _ = |a i| ^ 3 * (1 - Real.tanh (u i) ^ 4) := by
      change biasedSignExpectation (u i)
          (fun x => |a i * (x - Real.tanh (u i))| ^ 3) =
        |a i| ^ 3 * (1 - Real.tanh (u i) ^ 4)
      simp_rw [abs_mul, mul_pow]
      rw [biasedSignExpectation_const_mul]
      rw [biasedSign_thirdAbsoluteCenteredMoment]

/-- The real sign realization agrees with the repository's integer sign bit. -/
@[simp]
theorem biasedSignValue_eq_signBit (b : Bool) :
    biasedSignValue b = (signBit b : ℝ) := by
  cases b <;> norm_num [biasedSignValue, signBit]

/-- A one-sign tilted mass as a uniform mass times its likelihood ratio. -/
theorem biasedSignWeight_eq_uniform_mul_likelihood (u : ℝ) (b : Bool) :
    biasedSignWeight u b =
      (2 : ℝ)⁻¹ * Real.exp (u * biasedSignValue b) / Real.cosh u := by
  cases b
  · rw [show u * biasedSignValue false = -u by
      simp [biasedSignValue]]
    change biasedSignNegWeight u =
      (2 : ℝ)⁻¹ * Real.exp (-u) / Real.cosh u
    rw [biasedSignNegWeight_eq_exp_neg_div_cosh]
    ring
  · rw [show u * biasedSignValue true = u by
      simp [biasedSignValue]]
    change biasedSignPosWeight u =
      (2 : ℝ)⁻¹ * Real.exp u / Real.cosh u
    rw [biasedSignPosWeight_eq_exp_div_cosh]
    ring

/-- Every uniform Rademacher bit vector has mass `∏ i, 1/2`. -/
theorem rademacherPMF_toReal_apply_eq_prod_inv_two
    {ι : Type u} [Fintype ι] (bits : ι → Bool) :
    (rademacherPMF ι bits).toReal = ∏ _i : ι, (2 : ℝ)⁻¹ := by
  classical
  have hmass :
      rademacherPMF ι bits = ∏ _i : ι, (2 : ℝ≥0∞)⁻¹ := by
    unfold rademacherPMF
    calc
      uniformPiPMF (fun _ : ι => Bool) bits =
          (uniformPiPMF
            (fun _ : ι => Bool)).toMeasure {bits} := by
        rw [PMF.toMeasure_apply_singleton _ _
          (measurableSet_singleton bits)]
      _ = Measure.pi
            (fun _i : ι =>
              (PMF.uniformOfFintype Bool).toMeasure) {bits} := by
        rw [uniformPiPMF_toMeasure]
      _ = ∏ i,
            (PMF.uniformOfFintype Bool).toMeasure {bits i} := by
        rw [Measure.pi_singleton]
      _ = ∏ _i : ι, (2 : ℝ≥0∞)⁻¹ := by
        apply Finset.prod_congr rfl
        intro i _
        rw [PMF.toMeasure_apply_singleton _ _
          (measurableSet_singleton (bits i))]
        rw [PMF.uniformOfFintype_apply]
        norm_num
  rw [hmass, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  norm_num

/--
Exact pointwise likelihood ratio of the biased product law against the
uniform Rademacher law.
-/
theorem biasedSignProductPMF_likelihoodRatio
    {ι : Type u} [Fintype ι] (u : ι → ℝ) (bits : ι → Bool) :
    (biasedSignProductPMF u bits).toReal =
      (rademacherPMF ι bits).toReal *
        Real.exp (∑ i, u i * biasedSignValue (bits i)) /
        ∏ i, Real.cosh (u i) := by
  rw [biasedSignProductPMF_toReal_apply]
  rw [rademacherPMF_toReal_apply_eq_prod_inv_two]
  simp_rw [biasedSignWeight_eq_uniform_mul_likelihood]
  rw [Finset.prod_div_distrib]
  rw [Finset.prod_mul_distrib]
  rw [← Real.exp_sum]

/--
Likelihood ratio at scalar tilt `x` for a Rademacher sum with coefficients
`a`.
-/
theorem biasedSignProductPMF_likelihoodRatio_rademacherSum
    {ι : Type u} [Fintype ι] (x : ℝ) (a : ι → ℝ)
    (bits : ι → Bool) :
    (biasedSignProductPMF (fun i => x * a i) bits).toReal =
      (rademacherPMF ι bits).toReal *
        Real.exp (x * rademacherSum a bits) /
        ∏ i, Real.cosh (x * a i) := by
  rw [biasedSignProductPMF_likelihoodRatio]
  congr 3
  rw [rademacherSum]
  simp_rw [biasedSignValue_eq_signBit]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact Esscher change of measure for an arbitrary integrand of a finite
Rademacher sum. -/
theorem rademacherIntegral_exp_mul_eq_biasedSignProduct
    {ι : Type u} [Fintype ι] (x : ℝ) (a : ι → ℝ)
    (f : (ι → Bool) → ℝ) :
    ∫ bits, Real.exp (x * rademacherSum a bits) * f bits
        ∂(rademacherPMF ι).toMeasure =
      (∏ i, Real.cosh (x * a i)) *
        ∫ bits, f bits
          ∂(biasedSignProductPMF (fun i => x * a i)).toMeasure := by
  classical
  rw [finitePMF_integral_eq_sum, finitePMF_integral_eq_sum]
  rw [Finset.mul_sum]
  simp only [smul_eq_mul]
  apply Finset.sum_congr rfl
  intro bits hbits
  rw [biasedSignProductPMF_likelihoodRatio_rademacherSum]
  have hprod : ∏ i, Real.cosh (x * a i) ≠ 0 := by positivity
  field_simp [hprod]

/-- The exact Esscher normalizer has the standard sub-Gaussian bound. -/
theorem prod_cosh_le_exp_sum_sq
    {ι : Type u} [Fintype ι] (x : ℝ) (a : ι → ℝ) :
    ∏ i, Real.cosh (x * a i) ≤
      Real.exp (x ^ 2 * (∑ i, a i ^ 2) / 2) := by
  calc
    ∏ i, Real.cosh (x * a i) ≤
        ∏ i, Real.exp ((x * a i) ^ 2 / 2) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        exact Real.cosh_le_exp_half_sq _
    _ = Real.exp (x ^ 2 * (∑ i, a i ^ 2) / 2) := by
      rw [← Real.exp_sum]
      congr 1
      calc
        ∑ i, (x * a i) ^ 2 / 2 =
            ∑ i, x ^ 2 * a i ^ 2 / 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (∑ i, x ^ 2 * a i ^ 2) / 2 := by rw [Finset.sum_div]
        _ = (x ^ 2 * ∑ i, a i ^ 2) / 2 := by rw [Finset.mul_sum]

/-- Exact variance of the complete centered weighted biased-sign sum. -/
theorem biasedSignProduct_centeredWeightedSumVariance
    {ι : Type u} [Fintype ι] (tilt coeff : ι → ℝ) :
    ∫ bits,
        (∑ i, coeff i *
          (biasedSignValue (bits i) - Real.tanh (tilt i))) ^ 2
      ∂(biasedSignProductPMF tilt).toMeasure =
    ∑ i, coeff i ^ 2 * (1 - Real.tanh (tilt i) ^ 2) := by
  classical
  let μ : Measure (ι → Bool) := (biasedSignProductPMF tilt).toMeasure
  let Y : ι → (ι → Bool) → ℝ := fun i bits =>
    coeff i * (biasedSignValue (bits i) - Real.tanh (tilt i))
  have hmean (i : ι) : ∫ bits, Y i bits ∂μ = 0 := by
    rw [← biasedSignProductExpectation_eq_integral]
    exact biasedSignProduct_centeredWeightedMean tilt coeff i
  have hsum_mean : ∫ bits, (∑ i, Y i bits) ∂μ = 0 := by
    rw [integral_finsetSum]
    · simp only [hmean, Finset.sum_const_zero]
    · intro i hi
      exact Integrable.of_finite
  have hmemLp (i : ι) : MemLp (Y i) 2 μ := by
    apply MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable
      (2 * |coeff i|)
    filter_upwards [] with bits
    have ht : |Real.tanh (tilt i)| ≤ 1 :=
      (abs_le).2 ⟨(Real.neg_one_lt_tanh (tilt i)).le,
        (Real.tanh_lt_one (tilt i)).le⟩
    have hsign : |biasedSignValue (bits i)| = 1 := by
      cases bits i <;> norm_num [biasedSignValue]
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |coeff i| *
          |biasedSignValue (bits i) - Real.tanh (tilt i)| ≤
          |coeff i| *
            (|biasedSignValue (bits i)| + |Real.tanh (tilt i)|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
      _ ≤ |coeff i| * 2 := by
        gcongr
        rw [hsign]
        linarith
      _ = 2 * |coeff i| := by ring
  have hindep := biasedSignProduct_centeredWeighted_iIndep tilt coeff
  have hpairwise : Set.Pairwise (↑(Finset.univ : Finset ι) : Set ι)
      (fun i j => IndepFun (Y i) (Y j) μ) := by
    intro i hi j hj hij
    exact hindep.indepFun hij
  have hvar := ProbabilityTheory.IndepFun.variance_sum
    (μ := μ) (X := Y) (s := Finset.univ)
    (fun i _ => hmemLp i) hpairwise
  have hsum_mean' : ∫ bits, (∑ i, Y i) bits ∂μ = 0 := by
    simpa only [Finset.sum_apply] using hsum_mean
  rw [ProbabilityTheory.variance_of_integral_eq_zero
    (measurable_of_finite _).aemeasurable hsum_mean'] at hvar
  calc
    ∫ bits, (∑ i, coeff i *
        (biasedSignValue (bits i) - Real.tanh (tilt i))) ^ 2 ∂μ =
        ∫ bits, (∑ i, Y i) bits ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with bits
      simp only [Y, Finset.sum_apply]
    _ = ∑ i, ProbabilityTheory.variance (Y i) μ := hvar
    _ = ∑ i, coeff i ^ 2 * (1 - Real.tanh (tilt i) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ProbabilityTheory.variance_of_integral_eq_zero
        (measurable_of_finite _).aemeasurable (hmean i)]
      rw [← biasedSignProductExpectation_eq_integral]
      exact biasedSignProduct_centeredWeightedVariance tilt coeff i

/--
The fourth centered moment of any partial weighted biased-sign sum is at most
three times the square of its un-tilted coefficient mass.  The estimate is
uniform in the coordinate tilts; it is the finite-product moment bound used by
the shifted dominant-row argument.
-/
theorem biasedSignProduct_centeredWeightedFourthMoment_le
    {ι : Type u} [Fintype ι] (tilt coeff : ι → ℝ) (S : Finset ι) :
    ∫ bits,
        (∑ i ∈ S,
          coeff i *
            (biasedSignValue (bits i) - Real.tanh (tilt i))) ^ 4
      ∂(biasedSignProductPMF tilt).toMeasure ≤
    3 * (∑ i ∈ S, coeff i ^ 2) ^ 2 := by
  classical
  let μ : Measure (ι → Bool) := (biasedSignProductPMF tilt).toMeasure
  let Y : ι → (ι → Bool) → ℝ := fun i bits =>
    coeff i * (biasedSignValue (bits i) - Real.tanh (tilt i))
  have hfinite (f : (ι → Bool) → ℝ) : Integrable f μ :=
    Integrable.of_finite
  have hmemLp (i : ι) : MemLp (Y i) 2 μ := by
    apply MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable
      (2 * |coeff i|)
    filter_upwards [] with bits
    have ht : |Real.tanh (tilt i)| ≤ 1 :=
      (abs_le).2 ⟨(Real.neg_one_lt_tanh (tilt i)).le,
        (Real.tanh_lt_one (tilt i)).le⟩
    have hsign : |biasedSignValue (bits i)| = 1 := by
      cases bits i <;> norm_num [biasedSignValue]
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |coeff i| *
          |biasedSignValue (bits i) - Real.tanh (tilt i)| ≤
          |coeff i| *
            (|biasedSignValue (bits i)| + |Real.tanh (tilt i)|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
      _ ≤ |coeff i| * 2 := by
        gcongr
        rw [hsign]
        linarith
      _ = 2 * |coeff i| := by ring
  have hmean (i : ι) : ∫ bits, Y i bits ∂μ = 0 := by
    rw [← biasedSignProductExpectation_eq_integral]
    exact biasedSignProduct_centeredWeightedMean tilt coeff i
  have hsecond (i : ι) :
      ∫ bits, (Y i bits) ^ 2 ∂μ =
        coeff i ^ 2 * (1 - Real.tanh (tilt i) ^ 2) := by
    rw [← biasedSignProductExpectation_eq_integral]
    exact biasedSignProduct_centeredWeightedVariance tilt coeff i
  have hsecond_le (i : ι) :
      ∫ bits, (Y i bits) ^ 2 ∂μ ≤ coeff i ^ 2 := by
    rw [hsecond]
    have ht : 0 ≤ Real.tanh (tilt i) ^ 2 := sq_nonneg _
    nlinarith [sq_nonneg (coeff i)]
  have hfourth (i : ι) :
      ∫ bits, (Y i bits) ^ 4 ∂μ ≤ 3 * coeff i ^ 4 := by
    rw [← biasedSignProductExpectation_eq_integral]
    calc
      biasedSignProductExpectation tilt (fun bits => Y i bits ^ 4) =
          ∑ b : Bool, biasedSignWeight (tilt i) b *
            (coeff i *
              (biasedSignValue b - Real.tanh (tilt i))) ^ 4 :=
        biasedSignProductExpectation_coord tilt i
          (fun b => (coeff i *
            (biasedSignValue b - Real.tanh (tilt i))) ^ 4)
      _ ≤ 3 * coeff i ^ 4 := by
        rw [Fintype.sum_bool]
        simp only [biasedSignWeight, biasedSignValue]
        unfold biasedSignNegWeight biasedSignPosWeight
        have ht_upper : Real.tanh (tilt i) ^ 2 ≤ 1 :=
          (Real.tanh_sq_lt_one (tilt i)).le
        have ht_nonneg : 0 ≤ Real.tanh (tilt i) ^ 2 := sq_nonneg _
        ring_nf
        nlinarith [sq_nonneg (coeff i ^ 2),
          mul_nonneg (sq_nonneg (coeff i ^ 2)) ht_nonneg]
  have hindep := biasedSignProduct_centeredWeighted_iIndep tilt coeff
  change (∫ bits, (∑ i ∈ S, Y i bits) ^ 4 ∂μ) ≤ _
  induction S using Finset.induction with
  | empty => simp
  | @insert i S hi ih =>
      let A : (ι → Bool) → ℝ := fun bits => ∑ j ∈ S, Y j bits
      have hAY : IndepFun A (Y i) μ := by
        have h := hindep.indepFun_finsetSum_of_notMem
          (fun _ => measurable_of_finite _) hi
        convert h using 1
        funext bits
        simp only [A, Y, Finset.sum_apply]
      have hAmean : ∫ bits, A bits ∂μ = 0 := by
        dsimp [A]
        rw [integral_finsetSum]
        · simp only [hmean, Finset.sum_const_zero]
        · intro j hj
          exact hfinite (Y j)
      have hA3Y : ∫ bits, A bits ^ 3 * Y i bits ∂μ = 0 := by
        have hfactor :=
          (hAY.comp (measurable_id.pow_const 3) measurable_id).integral_mul_eq_mul_integral
          (measurable_of_finite _).aestronglyMeasurable
          (measurable_of_finite _).aestronglyMeasurable
        simpa only [Function.comp_apply, Pi.mul_apply, id_eq, hmean,
          mul_zero] using hfactor
      have hAY3 : ∫ bits, A bits * Y i bits ^ 3 ∂μ = 0 := by
        have hfactor :=
          (hAY.comp measurable_id (measurable_id.pow_const 3)).integral_mul_eq_mul_integral
          (measurable_of_finite _).aestronglyMeasurable
          (measurable_of_finite _).aestronglyMeasurable
        simpa only [Function.comp_apply, Pi.mul_apply, id_eq, hAmean,
          zero_mul] using hfactor
      have hA2Y2 :
          ∫ bits, A bits ^ 2 * Y i bits ^ 2 ∂μ =
            (∫ bits, A bits ^ 2 ∂μ) *
              ∫ bits, Y i bits ^ 2 ∂μ := by
        exact (hAY.comp (measurable_id.pow_const 2)
          (measurable_id.pow_const 2)).integral_mul_eq_mul_integral
            (measurable_of_finite _).aestronglyMeasurable
            (measurable_of_finite _).aestronglyMeasurable
      have hA2_nonneg : 0 ≤ ∫ bits, A bits ^ 2 ∂μ := by positivity
      have hA2_le :
          ∫ bits, A bits ^ 2 ∂μ ≤ ∑ j ∈ S, coeff j ^ 2 := by
        have hpairwise : Set.Pairwise (↑S : Set ι)
            (fun j k => IndepFun (Y j) (Y k) μ) := by
          intro j hj k hk hjk
          exact hindep.indepFun hjk
        have hvar := ProbabilityTheory.IndepFun.variance_sum
          (μ := μ) (X := Y) (s := S)
          (fun j _ => hmemLp j) hpairwise
        have hAeq : A = ∑ j ∈ S, Y j := by
          funext bits
          simp only [A, Finset.sum_apply]
        calc
          ∫ bits, A bits ^ 2 ∂μ = ProbabilityTheory.variance A μ :=
            (ProbabilityTheory.variance_of_integral_eq_zero
              (measurable_of_finite _).aemeasurable hAmean).symm
          _ = ProbabilityTheory.variance (∑ j ∈ S, Y j) μ := by rw [hAeq]
          _ = ∑ j ∈ S, ProbabilityTheory.variance (Y j) μ := hvar
          _ ≤ ∑ j ∈ S, coeff j ^ 2 := by
            apply Finset.sum_le_sum
            intro j hj
            rw [ProbabilityTheory.variance_of_integral_eq_zero
              (measurable_of_finite _).aemeasurable (hmean j)]
            exact hsecond_le j
      rw [Finset.sum_insert hi]
      simp only [Finset.sum_insert hi]
      have hexpand :
          (∫ bits, (A bits + Y i bits) ^ 4 ∂μ) =
            (∫ bits, A bits ^ 4 ∂μ) +
              4 * (∫ bits, A bits ^ 3 * Y i bits ∂μ) +
              6 * (∫ bits, A bits ^ 2 * Y i bits ^ 2 ∂μ) +
              4 * (∫ bits, A bits * Y i bits ^ 3 ∂μ) +
              ∫ bits, Y i bits ^ 4 ∂μ := by
        rw [show (fun bits => (A bits + Y i bits) ^ 4) =
            fun bits => A bits ^ 4 + 4 * (A bits ^ 3 * Y i bits) +
              6 * (A bits ^ 2 * Y i bits ^ 2) +
              4 * (A bits * Y i bits ^ 3) + Y i bits ^ 4 by
          funext bits
          ring]
        simp only [integral_add (hfinite _) (hfinite _),
          integral_const_mul]
      rw [show (fun bits => (Y i bits + ∑ j ∈ S, Y j bits) ^ 4) =
          fun bits => (A bits + Y i bits) ^ 4 by
        funext bits
        dsimp [A]
        congr 1
        ring]
      rw [hexpand, hA3Y, hAY3, hA2Y2]
      have hcross := mul_le_mul hA2_le (hsecond_le i)
        (by positivity : 0 ≤ ∫ bits, Y i bits ^ 2 ∂μ)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      nlinarith [ih, hfourth i, hcross,
        sq_nonneg (∑ j ∈ S, coeff j ^ 2), sq_nonneg (coeff i ^ 2)]

end Probability
end CertifiedJL
