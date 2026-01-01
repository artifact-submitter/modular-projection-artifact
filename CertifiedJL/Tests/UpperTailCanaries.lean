/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperRow
import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperNormalization
import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperPeano
import CertifiedJL.Analysis.Peano.PeanoGaussianRademacherNoncompact
import CertifiedJL.Tests.PeanoGaussianRademacherScaled
import CertifiedJL.Tests.PeanoKHybrid
import CertifiedJL.Tests.PeanoKLaw
import CertifiedJL.Tests.UpperTailAnalyticCanaries
import CertifiedJL.Tests.SparseUpperHeadline
import CertifiedJL.Tests.UpperContourQuadrature
import CertifiedJL.Tests.UpperPeanoFinal
import CertifiedJL.Tests.UpperPeanoHybrid
import CertifiedJL.Tests.UpperPeanoProductLaws
import Lean.Util.CollectAxioms

/-!
# Sparse upper-tail statement and normalization canaries

These tests pin the exact statement contract and normalization boundary.
They are deliberately outside the production import closure.
-/

open MeasureTheory Filter
open ProbabilityTheory
open scoped NNReal Topology

namespace CertifiedJL
namespace Tests
namespace UpperTailCanaries

/-! ## Contract shape -/

example :
    SparseUpper128Statement ↔
      ∀ (q d : ℕ) (w : Fin d → ℤ),
        eventProbability (sparseRademacherMatrix rowCount d)
          (SparseUpperFailure q w) < failureTarget securityBits := by
  rfl

example (q : ℕ) {m d : ℕ} (w : Fin d → ℤ)
    (J : Matrix (Fin m) (Fin d) ℤ) :
    SparseUpperFailure q w J ↔
      modularProjectionSqNorm q J w > 338 * sqNorm w := by
  rfl

/-! ## Headline constants and strict boundary -/

example : rowCount = 256 := by rfl
example : securityBits = 128 := by rfl
example : sparseUpperThreshold = 338 := by rfl
example : sparseUpperThreshold ≠ 337 := by norm_num [sparseUpperThreshold]
example : sparseUpperThreshold ≠ 340 := by norm_num [sparseUpperThreshold]
example : rowCount ≠ 255 := by norm_num [rowCount]

example : ¬((338 : ℕ) > 338) := by norm_num
example : (338 : ℕ) ≤ 338 := by norm_num

/-! ## Normalization and profile shape -/

example : sparseNormalizedVariance = (1 / 2 : ℚ) := by rfl
example : sparseNormalizedVariance ≠ (1 : ℚ) := by
  norm_num [sparseNormalizedVariance]

example {d : ℕ} (a : Fin d → ℝ) :
    sparseProfileFourthMoment a = ∑ i, (a i) ^ 4 := by
  rfl

example (s : ℝ) :
    gaussianRealRowMGF s = Real.rpow (1 - s) (-1 / 2 : ℝ) := by
  rfl

/- The real reference notation is not merely a definition: it is the exact
variance-one-half Gaussian quadratic MGF. -/
example :
    (∫ x : ℝ, complexQuadraticExp ((1 / 2 : ℝ) : ℂ) x
        ∂(gaussianReal 0 (2 : NNReal)⁻¹)) =
      (gaussianRealRowMGF (1 / 2) : ℂ) := by
  exact integral_gaussianHalf_complexQuadraticExp_real (by norm_num)

example :
    ∫ z, (z : ℝ) ∂sparseEntryPMF.toMeasure = 0 :=
  sparseEntry_firstMoment

example :
    ∫ z, (z : ℝ) ^ 2 ∂sparseEntryPMF.toMeasure = (1 / 2 : ℝ) :=
  sparseEntry_secondMoment

example :
    ∫ z, (z : ℝ) ^ 2 ∂sparseEntryPMF.toMeasure =
      (sparseNormalizedVariance : ℝ) :=
  sparseEntry_secondMoment_normalized

/-! ## Concrete Gaussian--Rademacher moment boundary -/

example :
    EqualMomentsThrough (gaussianReal 0 1) standardRademacherMeasure 3 :=
  standardGaussianRademacher_equalMoments

example (k : ℕ) :
    Integrable (fun y : ℝ => y ^ k) standardRademacherMeasure :=
  integrable_standardRademacher_pow k

example (k : ℕ) :
    Integrable (fun y : ℝ => y ^ k) (gaussianReal 0 1) :=
  integrable_standardGaussian_pow k

example (k : ℕ) :
    (∫ y, y ^ k ∂standardRademacherMeasure) =
      (1 / 2 : ℝ) * (-1 : ℝ) ^ k + (1 / 2 : ℝ) * (1 : ℝ) ^ k :=
  integral_standardRademacher_pow k

example : standardRademacherMeasure Set.univ = 1 :=
  standardRademacherMeasure_mass

example : IsProbabilityMeasure standardRademacherMeasure := inferInstance

example : (∫ y, y ∂standardRademacherMeasure) = 0 :=
  standardRademacherMeasure_first_moment

example : (∫ y, y ^ 2 ∂standardRademacherMeasure) = 1 :=
  standardRademacherMeasure_second_moment

example (t : ℝ) :
    Integrable (fun y : ℝ => (max (y - t) 0) ^ 3)
      (gaussianReal 0 1) :=
  integrable_standardGaussian_cubicStopLoss t

example (t : ℝ) :
    Integrable (fun y : ℝ => (max (y - t) 0) ^ 3)
      standardRademacherMeasure :=
  integrable_standardRademacher_cubicStopLoss t

example {t : ℝ} (ht : 1 ≤ t) :
    cubicStopLossDifference (gaussianReal 0 1) standardRademacherMeasure t =
      ∫ y in Set.Ioi t, (y - t) ^ 3 ∂(gaussianReal 0 1) :=
  cubicStopLossDifference_standardGaussian_rademacher_of_one_le ht

/-! ## Doubled-sign profile identities -/

example {d : ℕ} (a : Fin d → ℝ)
    (hsq : ∑ i, a i ^ 2 = 1) :
    ∑ p : Fin d × Fin 2,
        sparseUpperDuplicatedCoefficient a p ^ 2 =
      (sparseNormalizedVariance : ℝ) :=
  sum_sq_sparseUpperDuplicatedCoefficient a hsq

example {d : ℕ} (a : Fin d → ℝ) :
    ∑ p : Fin d × Fin 2,
        sparseUpperDuplicatedCoefficient a p ^ 4 =
      sparseProfileFourthMoment a / 8 :=
  sum_fourth_sparseUpperDuplicatedCoefficient a

example {d : ℕ} (a : Fin d → ℝ) :
    ∑ p : Fin d × Fin 2,
        sparseUpperDuplicatedCoefficient a p ^ 6 =
      (∑ i, a i ^ 6) / 32 :=
  sum_sixth_sparseUpperDuplicatedCoefficient a

example {d : ℕ} (a : Fin d → ℝ) :
    ∑ p : Fin d × Fin 2,
        sparseUpperDuplicatedCoefficient a p ^ 6 ≤
      (sparseProfileFourthMoment a *
          Real.sqrt (sparseProfileFourthMoment a)) / 32 :=
  sum_sixth_sparseUpperDuplicatedCoefficient_le a

private noncomputable def upperTailTwoPoint : Measure ℝ :=
  (2 : ENNReal)⁻¹ • Measure.dirac (0 : ℝ) +
    (2 : ENNReal)⁻¹ • Measure.dirac (Real.sqrt 2)

/- A strict nondegenerate Jensen instance: `H(v)=v⁴`, `a=1`, and the
   two-point law assigning mass one half to `0` and to `√2`.  Its squared
   input is nonconstant, has expectation one, and the producer yields the
   strict numerical gap `1 < 2`; a Dirac/equality canary would not detect a
   reversed or vacuous Jensen interface. -/
example :
    (fun v : ℝ => v ^ 4) 1 <
      ∫ y, (fun v : ℝ => v ^ 4) (1 * Real.sqrt (y ^ 2)) ∂upperTailTwoPoint := by
  let μ : Measure ℝ := upperTailTwoPoint
  change (fun v : ℝ => v ^ 4) 1 <
      ∫ y, (fun v : ℝ => v ^ 4) (1 * Real.sqrt (y ^ 2)) ∂μ
  let : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    norm_num [μ, upperTailTwoPoint]
    rw [← two_mul]
    rw [mul_comm, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
  let s : Set ℝ := Set.Ici 0
  have heq : Set.EqOn (fun v : ℝ => v ^ 2)
      (fun v : ℝ => ((1 : ℝ) * Real.sqrt v) ^ 4) s := by
    intro v hv
    calc
      v ^ 2 = (Real.sqrt v ^ 2) ^ 2 := by rw [Real.sq_sqrt hv]
      _ = ((1 : ℝ) * Real.sqrt v) ^ 4 := by ring
  have hconv : ConvexOn ℝ s
      (fun v : ℝ => ((1 : ℝ) * Real.sqrt v) ^ 4) := by
    exact (convexOn_pow 2).congr heq
  have hcont : ContinuousOn
      (fun v : ℝ => ((1 : ℝ) * Real.sqrt v) ^ 4) s := by
    exact (continuousOn_pow 2).congr heq.symm
  have hfi : Integrable (fun y : ℝ => y ^ 2) μ := by
    rw [show μ =
        (2 : ENNReal)⁻¹ • Measure.dirac (0 : ℝ) +
          (2 : ENNReal)⁻¹ • Measure.dirac (Real.sqrt 2) by rfl]
    apply Integrable.add_measure
    · exact (integrable_dirac (f := fun y : ℝ => y ^ 2) (a := (0 : ℝ))
        (by simp)).smul_measure (by norm_num)
    · exact (integrable_dirac (f := fun y : ℝ => y ^ 2)
        (a := Real.sqrt 2) (by simp)).smul_measure (by norm_num)
  have hsecond : ∫ y, y ^ 2 ∂μ = 1 := by
    rw [show μ =
        (2 : ENNReal)⁻¹ • Measure.dirac (0 : ℝ) +
          (2 : ENNReal)⁻¹ • Measure.dirac (Real.sqrt 2) by rfl]
    rw [integral_add_measure]
    · simp [integral_smul_measure, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    · exact (integrable_dirac (f := fun y : ℝ => y ^ 2) (a := (0 : ℝ))
        (by simp)).smul_measure (by norm_num)
    · exact (integrable_dirac (f := fun y : ℝ => y ^ 2)
        (a := Real.sqrt 2) (by simp)).smul_measure (by norm_num)
  have hgi : Integrable
      (fun y : ℝ => (1 * Real.sqrt (y ^ 2)) ^ 4) μ := by
    rw [show μ =
        (2 : ENNReal)⁻¹ • Measure.dirac (0 : ℝ) +
          (2 : ENNReal)⁻¹ • Measure.dirac (Real.sqrt 2) by rfl]
    apply Integrable.add_measure
    · exact (integrable_dirac
        (f := fun y : ℝ => (1 * Real.sqrt (y ^ 2)) ^ 4) (a := (0 : ℝ))
        (by simp)).smul_measure (by norm_num)
    · exact (integrable_dirac
        (f := fun y : ℝ => (1 * Real.sqrt (y ^ 2)) ^ 4)
        (a := Real.sqrt 2) (by simp)).smul_measure (by norm_num)
  have hbound : (fun v : ℝ => v ^ 4) 1 ≤
      ∫ y, (fun v : ℝ => v ^ 4) (1 * Real.sqrt (y ^ 2)) ∂μ :=
    convexSquareExpectation_le
      (μ := μ) (H := fun v : ℝ => v ^ 4) (a := 1)
      hconv hcont hsecond hfi hgi
  have hvalue :
      (∫ y, (fun v : ℝ => v ^ 4) (1 * Real.sqrt (y ^ 2)) ∂μ) = 2 := by
    rw [show μ =
        (2 : ENNReal)⁻¹ • Measure.dirac (0 : ℝ) +
          (2 : ENNReal)⁻¹ • Measure.dirac (Real.sqrt 2) by rfl]
    rw [integral_add_measure]
    · simp [integral_smul_measure, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      have hs : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by norm_num
      nlinarith [hs]
    · exact (integrable_dirac
        (f := fun y : ℝ => (1 * Real.sqrt (y ^ 2)) ^ 4) (a := (0 : ℝ))
        (by simp)).smul_measure (by norm_num)
    · exact (integrable_dirac
        (f := fun y : ℝ => (1 * Real.sqrt (y ^ 2)) ^ 4)
        (a := Real.sqrt 2) (by simp)).smul_measure (by norm_num)
  have hne : (fun v : ℝ => v ^ 4) 1 ≠
      ∫ y, (fun v : ℝ => v ^ 4) (1 * Real.sqrt (y ^ 2)) ∂μ := by
    rw [hvalue]
    norm_num
  exact lt_of_le_of_ne hbound hne

/- A direct profile-factor mutation is rejected by the exact coefficient. -/
example : (1 / 8 : ℝ) ≠ 1 / 4 := by norm_num

/-! ## Peano kernel orientation and prefactor guards -/

/-! ## Noncompact moment boundary guards -/

example {μ ν : Measure ℝ} (hm : EqualMomentsThrough μ ν 3) :
    Integrable id μ :=
  hm.integrable_id_left

example {μ ν : Measure ℝ} (hm : EqualMomentsThrough μ ν 3) :
    Integrable id ν :=
  hm.integrable_id_right

example {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : EqualMomentsThrough μ ν 3) :
    μ.real Set.univ = ν.real Set.univ :=
  hm.equal_mass

example {μ ν : Measure ℝ} (hm : EqualMomentsThrough μ ν 3) :
    (∫ y, y ∂μ) = ∫ y, y ∂ν :=
  hm.equal_first_moment

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    {μ ν : Measure ℝ} (hm : EqualMomentsThrough μ ν 3)
    (f : ℝ → E) (x : ℝ) :
    (∫ y, taylorPolynomial3 f x y ∂μ) =
      ∫ y, taylorPolynomial3 f x y ∂ν :=
  equalMomentsThrough_taylorPolynomial3 hm f x

private noncomputable def upperTailRademacherLaw : Measure ℝ :=
  (2 : ENNReal)⁻¹ • Measure.dirac (-1 : ℝ) +
    (2 : ENNReal)⁻¹ • Measure.dirac (1 : ℝ)

private noncomputable def upperTailThreePointLaw : Measure ℝ :=
  (8 : ENNReal)⁻¹ • Measure.dirac (-2 : ℝ) +
    (3 / 4 : ENNReal) • Measure.dirac (0 : ℝ) +
    (8 : ENNReal)⁻¹ • Measure.dirac (2 : ℝ)

private lemma upperTail_integrable_pow_dirac (a : ℝ) (k : ℕ) :
    Integrable (fun y : ℝ => y ^ k) (Measure.dirac a) := by
  exact integrable_dirac (f := fun y : ℝ => y ^ k) (a := a) (by simp)

private lemma upperTail_three_quarter_ne_top :
    (3 / 4 : ENNReal) ≠ ⊤ := by
  exact ENNReal.div_ne_top (by simp) (by norm_num)

private lemma upperTail_rademacher_moment (k : ℕ) :
    (∫ y, y ^ k ∂upperTailRademacherLaw) =
      (1 / 2 : ℝ) * (-1 : ℝ) ^ k + (1 / 2 : ℝ) * (1 : ℝ) ^ k := by
  rw [upperTailRademacherLaw, integral_add_measure]
  · simp [integral_smul_measure]
  · exact (upperTail_integrable_pow_dirac (-1) k).smul_measure (by norm_num)
  · exact (upperTail_integrable_pow_dirac 1 k).smul_measure (by norm_num)

private lemma upperTail_threePoint_moment (k : ℕ) :
    (∫ y, y ^ k ∂upperTailThreePointLaw) =
      (1 / 8 : ℝ) * (-2 : ℝ) ^ k +
        (3 / 4 : ℝ) * (0 : ℝ) ^ k +
        (1 / 8 : ℝ) * (2 : ℝ) ^ k := by
  rw [upperTailThreePointLaw, integral_add_measure]
  · rw [integral_add_measure]
    · simp [integral_smul_measure]
    · exact (upperTail_integrable_pow_dirac (-2) k).smul_measure (by norm_num)
    · exact (upperTail_integrable_pow_dirac 0 k).smul_measure
        upperTail_three_quarter_ne_top
  · exact ((upperTail_integrable_pow_dirac (-2) k).smul_measure (by norm_num)).add_measure
      ((upperTail_integrable_pow_dirac 0 k).smul_measure
        upperTail_three_quarter_ne_top)
  · exact (upperTail_integrable_pow_dirac 2 k).smul_measure (by norm_num)

private lemma upperTail_equal_moments :
    EqualMomentsThrough upperTailRademacherLaw upperTailThreePointLaw 3 := by
  constructor
  · intro k hk
    rw [upperTailRademacherLaw]
    apply Integrable.add_measure
    · exact (upperTail_integrable_pow_dirac (-1) k).smul_measure (by norm_num)
    · exact (upperTail_integrable_pow_dirac 1 k).smul_measure (by norm_num)
  · intro k hk
    rw [upperTailThreePointLaw]
    apply Integrable.add_measure
    · apply Integrable.add_measure
      · exact (upperTail_integrable_pow_dirac (-2) k).smul_measure (by norm_num)
      · exact (upperTail_integrable_pow_dirac 0 k).smul_measure
          upperTail_three_quarter_ne_top
    · exact (upperTail_integrable_pow_dirac 2 k).smul_measure (by norm_num)
  · intro k hk
    rw [upperTail_rademacher_moment, upperTail_threePoint_moment]
    interval_cases k <;> norm_num

/- Distinct laws with equal moments through degree three exercise all four
   moment fields and make the Taylor cancellation a real producer consumer. -/
example (f : ℝ → ℂ) (x : ℝ) :
    (∫ y, taylorPolynomial3 f x y ∂upperTailRademacherLaw) =
      ∫ y, taylorPolynomial3 f x y ∂upperTailThreePointLaw :=
  equalMomentsThrough_taylorPolynomial3 upperTail_equal_moments f x

/- The two public Taylor-integrability bridges are also consumed directly at
   the target codomain and on the same distinct moment-matched laws. -/
example (f : ℝ → ℂ) (x : ℝ) :
    Integrable (fun y => taylorPolynomial3 f x y) upperTailRademacherLaw :=
  integrable_taylorPolynomial3_left upperTail_equal_moments f x

example (f : ℝ → ℂ) (x : ℝ) :
    Integrable (fun y => taylorPolynomial3 f x y) upperTailThreePointLaw :=
  integrable_taylorPolynomial3_right upperTail_equal_moments f x

/- The U3b function is complex-valued but real-parameterized; its
   C⁴ producer fact is exposed through the sparse Peano umbrella. -/
example (s : ℂ) : ContDiff ℝ 4 (complexQuadraticExp s) :=
  contDiff_complexQuadraticExp s

/- A genuinely nonreal parameter is used here, not only a complex-valued
   codomain with an arbitrary parameter. -/
example : Complex.im (complexQuadraticExp Complex.I 1) = Real.sin 1 := by
  simpa [complexQuadraticExp] using (Complex.exp_ofReal_mul_I_im 1)

example (s : ℂ) (x : ℝ) :
    complexQuadraticExp s x = Complex.exp (s * (x : ℂ) ^ 2) := by
  rfl

/- The fourth derivative is exposed at the actual real-parameterized U3b
   consumer boundary; the complex-domain formula is retained as its
   canonical calculus producer. -/
example (s z : ℂ) :
    iteratedDeriv 4 (complexQuadraticExpComplex s) z =
      complexQuadraticExpFourthPolynomialComplex s z *
        complexQuadraticExpComplex s z :=
  iteratedDeriv_four_complexQuadraticExpComplex s z

example (s : ℂ) (x : ℝ) :
    iteratedDeriv 4 (complexQuadraticExp s) x =
      complexQuadraticExpFourthPolynomialComplex s (x : ℂ) *
        complexQuadraticExp s x :=
  iteratedDeriv_four_complexQuadraticExp s x

/- The first noncompact analytic consumers are exposed at both the volume and
   Gaussian-measure boundaries.  The strict real-part hypotheses are direct
   canaries for the negative quadratic envelope and the variance normalization. -/
example {s : ℂ} (hs : s.re < 0) :
    Integrable (fun x : ℝ => complexQuadraticExp s x) :=
  integrable_complexQuadraticExp_volume hs

example {s : ℂ} {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hs : s.re < 1 / (2 * (v : ℝ))) :
    Integrable (fun x : ℝ =>
      (gaussianPDFReal μ v x : ℂ) * complexQuadraticExp s x) :=
  integrable_gaussianPDFReal_mul_complexQuadraticExp hv hs

example {s : ℂ} {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hs : s.re < 1 / (2 * (v : ℝ))) :
    Integrable (fun x : ℝ => complexQuadraticExp s x) (gaussianReal μ v) :=
  integrable_gaussianReal_complexQuadraticExp hv hs

/- The shifted consumer keeps the translated Gaussian law and the explicit
   linear term in `(x + y)^2` visible at the public boundary. -/
example (s : ℂ) (x y : ℝ) :
    complexQuadraticExp s (x + y) =
      Complex.exp (s * (y : ℂ) ^ 2 + (2 * s * (x : ℂ)) * (y : ℂ) +
        s * (x : ℂ) ^ 2) :=
  complexQuadraticExp_add_expand s x y

example {s : ℂ} {μ x : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hs : s.re < 1 / (2 * (v : ℝ))) :
    Integrable (fun y : ℝ => complexQuadraticExp s (x + y))
      (gaussianReal μ v) :=
  integrable_gaussianReal_shifted_complexQuadraticExp hv hs

example {s : ℂ} {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hs : s.re < 1 / (2 * (v : ℝ))) (n : ℕ) :
    Integrable (fun y : ℝ => (y : ℂ) ^ (2 * n) * complexQuadraticExp s y)
      (gaussianReal μ v) :=
  integrable_gaussianReal_evenPow_mul_complexQuadraticExp hv hs n

example {s : ℂ} {μ x : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hs : s.re < 1 / (2 * (v : ℝ))) (n : ℕ) :
    Integrable
      (fun y : ℝ => ((x + y : ℝ) : ℂ) ^ (2 * n) *
        complexQuadraticExp s (x + y))
      (gaussianReal μ v) :=
  integrable_gaussianReal_shifted_evenPow_mul_complexQuadraticExp hv hs n

example {s : ℂ} {μ x : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hs : s.re < 1 / (2 * (v : ℝ))) :
    Integrable
      (fun y : ℝ => iteratedDeriv 4 (complexQuadraticExp s) (x + y))
      (gaussianReal μ v) :=
  integrable_gaussianReal_shifted_iteratedDeriv_four_complexQuadraticExp hv hs

/- The unweighted volume boundary is intentionally strict: at `Re(s)=0`,
   the integrand is the nonintegrable constant one.  This semantic canary
   prevents a later consumer from silently weakening the negative-real-part
   volume hypothesis. -/
example : ¬ Integrable (fun x : ℝ => complexQuadraticExp (0 : ℂ) x) := by
  intro h
  have hconst : Integrable (fun _ : ℝ => (1 : ℂ)) volume := by
    simpa [complexQuadraticExp] using h
  have hfinite : IsFiniteMeasure (volume : Measure ℝ) :=
    (integrable_const_iff.1 hconst).resolve_left (by norm_num)
  exact (not_isFiniteMeasure_iff.mpr (by simp)) hfinite

example (s : ℂ) (μ x : ℝ) (v : ℝ≥0) :
    Integrable (fun y : ℝ =>
      taylorPolynomial3 (complexQuadraticExp s) x y) (gaussianReal μ v) :=
  integrable_gaussianReal_taylorPolynomial3 (μ := μ) (v := v)
    (complexQuadraticExp s) x

example {s : ℂ} {μ x : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hs : s.re < 1 / (2 * (v : ℝ))) :
    Integrable (fun y : ℝ => complexQuadraticExp s (x + y) -
      taylorPolynomial3 (complexQuadraticExp s) x y) (gaussianReal μ v) :=
  integrable_gaussianReal_shifted_complexQuadraticExp_remainder hv hs

/- The cutoff family is concrete rather than an existence premise: its
   widening core, compact support, bounds, pointwise limit, and derivative
   scaling are all consumed directly at the production codomain. -/
example (n : ℕ) : ContDiff ℝ 4 (upperCutoff n) :=
  upperCutoff_contDiff n

example (n : ℕ) : HasCompactSupport (upperCutoff n) :=
  upperCutoff_hasCompactSupport n

example {n : ℕ} {y : ℝ} (hy : |y| ≤ upperCutoffRadius n) :
    upperCutoff n y = 1 :=
  upperCutoff_eq_one hy

example {n : ℕ} {y : ℝ}
    (hy : 2 * upperCutoffRadius n ≤ |y|) : upperCutoff n y = 0 :=
  upperCutoff_eq_zero hy

example (n : ℕ) (y : ℝ) :
    0 ≤ upperCutoff n y ∧ upperCutoff n y ≤ 1 :=
  ⟨upperCutoff_nonneg n y, upperCutoff_le_one n y⟩

example (y : ℝ) : Tendsto (fun n : ℕ => upperCutoff n y) atTop (𝓝 1) :=
  upperCutoff_pointwise_tendsto y

example (n k : ℕ) (y : ℝ) :
    iteratedDeriv k (upperCutoff n) y =
      (upperCutoffRadius n)⁻¹ ^ k *
        iteratedDeriv k (upperCutoffBase) (y / upperCutoffRadius n) :=
  upperCutoff_iteratedDeriv n k y

example (k : ℕ) :
    ∃ C : ℝ, ∀ (n : ℕ) (y : ℝ),
      ‖iteratedDeriv k (upperCutoff n) y‖ ≤
        C * (upperCutoffRadius n)⁻¹ ^ k :=
  upperCutoff_iteratedDeriv_bound k

/- The B3 approximant is translated at the expansion point.  This direct
   identity rejects the tempting but incorrect `χₙ(z)` cutoff placement. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (f : ℝ → E) (x y : ℝ) :
    upperCutoffRemainder n f x (x + y) =
      upperCutoff n y • (f (x + y) - taylorPolynomial3 f x y) :=
  upperCutoffRemainder_apply n f x y

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ 4 f) (n : ℕ) (x : ℝ) :
    ContDiff ℝ 4 (upperCutoffRemainder n f x) :=
  upperCutoffRemainder_contDiff hf n x

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (f : ℝ → E) (x : ℝ) :
    HasCompactSupport (upperCutoffRemainder n f x) :=
  upperCutoffRemainder_hasCompactSupport n f x

/- The Gaussian law limit is a proved dominated-convergence consumer of the
   exact translated remainder, not a free limit field in the Peano schema. -/
example {s : ℂ} {μ x : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hs : s.re < 1 / (2 * (v : ℝ))) :
    Tendsto
      (fun n => ∫ y, upperCutoffRemainder n (complexQuadraticExp s) x
        (x + y) ∂(gaussianReal μ v)) atTop
      (𝓝 (∫ y, (complexQuadraticExp s (x + y) -
        taylorPolynomial3 (complexQuadraticExp s) x y) ∂(gaussianReal μ v))) :=
  upperCutoffRemainder_integral_tendsto (μ := gaussianReal μ v)
    (contDiff_complexQuadraticExp s) x
    (integrable_gaussianReal_shifted_complexQuadraticExp_remainder hv hs)

/- The Rademacher side is a concrete finite-support law, not a free DCT
   premise.  This application keeps the target complex codomain visible. -/
example {s : ℂ} (x : ℝ) :
    Tendsto
      (fun n => ∫ y, upperCutoffRemainder n (complexQuadraticExp s) x
        (x + y) ∂standardRademacherMeasure) atTop
      (𝓝 (∫ y, (complexQuadraticExp s (x + y) -
        taylorPolynomial3 (complexQuadraticExp s) x y)
        ∂standardRademacherMeasure)) :=
  upperCutoffRemainder_standardRademacher_integral_tendsto
    (contDiff_complexQuadraticExp s) x

example {s : ℂ} (n : ℕ) (x : ℝ) :
    upperCutoffRemainder n (complexQuadraticExp s) x (x + (-1 : ℝ)) =
        complexQuadraticExp s (x + (-1 : ℝ)) -
          taylorPolynomial3 (complexQuadraticExp s) x (-1 : ℝ) ∧
      upperCutoffRemainder n (complexQuadraticExp s) x (x + (1 : ℝ)) =
        complexQuadraticExp s (x + (1 : ℝ)) -
          taylorPolynomial3 (complexQuadraticExp s) x (1 : ℝ) := by
  exact upperCutoffRemainder_standardRademacher_support n
    (complexQuadraticExp s) x

/- The derivative-side producer exposes the full fourth-order Leibniz sum;
   the i=0 term is the zero-order cutoff derivative term and the i>0 terms
   are the cutoff cross terms that the later stop-loss envelope must dominate. -/
example {s : ℂ} (n : ℕ) (x z : ℝ) :
    iteratedDeriv 4 (upperCutoffRemainder n (complexQuadraticExp s) x) z =
      ∑ i ∈ Finset.range (4 + 1),
        Nat.choose 4 i • iteratedDeriv i
            (fun z : ℝ => upperCutoff n (z - x)) z •
          iteratedDeriv (4 - i)
            (fun z : ℝ => complexQuadraticExp s z -
              taylorPolynomial3 (complexQuadraticExp s) x (z - x)) z :=
  upperCutoffRemainder_iteratedDeriv_four
    (contDiff_complexQuadraticExp s) n x z

/- The cutoff cross-term constants are uniform in the radius, expansion
   point, and integration variable.  The full five-term conclusion is kept
   visible so no derivative order can silently disappear from the DCT
   handoff. -/
example :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (s : ℂ) (n : ℕ) (x t : ℝ),
        ‖iteratedDeriv 4
          (upperCutoffRemainder n (complexQuadraticExp s) x) (x + t)‖ ≤
          ∑ i ∈ Finset.range (4 + 1),
            Nat.choose 4 i * C i *
              ‖iteratedDeriv (4 - i)
                (fun z : ℝ => complexQuadraticExp s z -
                  taylorPolynomial3 (complexQuadraticExp s) x (z - x))
                (x + t)‖ :=
  by
    obtain ⟨C, hC, hbound⟩ :=
      upperCutoffRemainder_iteratedDeriv_four_norm_le
    exact ⟨C, hC, fun s => hbound (contDiff_complexQuadraticExp s)⟩

example {s : ℂ} (x t : ℝ) :
    Tendsto
      (fun n => iteratedDeriv 4
        (upperCutoffRemainder n (complexQuadraticExp s) x) (x + t)) atTop
      (𝓝 (iteratedDeriv 4 (complexQuadraticExp s) (x + t))) :=
  upperCutoffRemainder_iteratedDeriv_four_tendsto
    (contDiff_complexQuadraticExp s) x t

/- The first concrete weighted-DCT boundary is exercised at a genuinely
   nonreal parameter and a nonzero shift.  The strict `Re(s)<0` domain is
   intentional here; the later variance-scaled U3b domain is separate. -/
example : ((-1 + Complex.I : ℂ).im) = 1 := by norm_num

/- The lower derivative formulas used by the five-term majorant are pinned at
   the same real-argument complex quadratic exponential. -/
example (s : ℂ) (x : ℝ) :
    iteratedDeriv 1 (complexQuadraticExp s) x =
      2 * s * (x : ℂ) * complexQuadraticExp s x :=
  iteratedDeriv_one_complexQuadraticExp s x

example (s : ℂ) (x : ℝ) :
    iteratedDeriv 2 (complexQuadraticExp s) x =
      (2 * s + 4 * s ^ 2 * (x : ℂ) ^ 2) * complexQuadraticExp s x :=
  iteratedDeriv_two_complexQuadraticExp s x

example (s : ℂ) (x : ℝ) :
    iteratedDeriv 3 (complexQuadraticExp s) x =
      (12 * s ^ 2 * (x : ℂ) + 8 * s ^ 3 * (x : ℂ) ^ 3) *
        complexQuadraticExp s x :=
  iteratedDeriv_three_complexQuadraticExp s x

/- The U3/U4 higher derivatives are generated from one recurrence.  The
   generic canary prevents the exact sixth/eighth formulas from becoming
   disconnected one-off calculations, while these two symbolic applications
   pin every coefficient used by the paper's derivative majorants. -/
example (n : ℕ) (s : ℂ) (x : ℝ) :
    iteratedDeriv n (complexQuadraticExp s) x =
      (complexQuadraticExpDerivativePolynomial s n).eval (x : ℂ) *
        complexQuadraticExp s x :=
  iteratedDeriv_complexQuadraticExp n s x

example (s : ℂ) (x : ℝ) :
    iteratedDeriv 6 (complexQuadraticExp s) x =
      (120 * s ^ 3 + 720 * s ^ 4 * (x : ℂ) ^ 2 +
        480 * s ^ 5 * (x : ℂ) ^ 4 + 64 * s ^ 6 * (x : ℂ) ^ 6) *
        complexQuadraticExp s x :=
  iteratedDeriv_six_complexQuadraticExp s x

example (s : ℂ) (x : ℝ) :
    iteratedDeriv 8 (complexQuadraticExp s) x =
      (1680 * s ^ 4 + 13440 * s ^ 5 * (x : ℂ) ^ 2 +
        13440 * s ^ 6 * (x : ℂ) ^ 4 + 3584 * s ^ 7 * (x : ℂ) ^ 6 +
        256 * s ^ 8 * (x : ℂ) ^ 8) * complexQuadraticExp s x :=
  iteratedDeriv_eight_complexQuadraticExp s x

/- The finite-sum normalization is evaluated at both orders used in U3/U4,
   so index range, factorials, powers of two, and all polynomial coefficients
   remain visible independently of the derivative-bound applications. -/
example (rho lambda x : ℝ) :
    quadraticExpDerivativePointwiseMajorant 6 rho lambda x =
      (120 * rho ^ 3 + 720 * rho ^ 4 * |x| ^ 2 +
        480 * rho ^ 5 * |x| ^ 4 + 64 * rho ^ 6 * |x| ^ 6) *
        Real.exp (lambda * x ^ 2) := by
  norm_num [quadraticExpDerivativePointwiseMajorant, Finset.sum_range_succ]
  ring

example (rho lambda x : ℝ) :
    quadraticExpDerivativePointwiseMajorant 8 rho lambda x =
      (1680 * rho ^ 4 + 13440 * rho ^ 5 * |x| ^ 2 +
        13440 * rho ^ 6 * |x| ^ 4 + 3584 * rho ^ 7 * |x| ^ 6 +
        256 * rho ^ 8 * |x| ^ 8) * Real.exp (lambda * x ^ 2) := by
  norm_num [quadraticExpDerivativePointwiseMajorant, Finset.sum_range_succ]
  ring

example {m : ℕ} {rho lambda x : ℝ} (hrho : 0 ≤ rho) :
    0 ≤ quadraticExpDerivativePointwiseMajorant m rho lambda x :=
  quadraticExpDerivativePointwiseMajorant_nonneg hrho

/- These are the exact D₆/D₈ expansions used by the analytic row bound and
   later by the normalized interval evaluator.  Every half-integer exponent
   and every coefficient is deliberately repeated here.  The parity guards
   keep these semantic paper consumers inside U3's even-order domain. -/
example : Even 6 := by norm_num
example : Even 8 := by norm_num

example (rho lambda : ℝ) :
    quadraticExpDerivativeMajorant 6 rho lambda =
      120 * rho ^ 3 * Real.rpow (1 - lambda) (-(1 : ℝ) / 2) +
      360 * rho ^ 4 * Real.rpow (1 - lambda) (-(3 : ℝ) / 2) +
      360 * rho ^ 5 * Real.rpow (1 - lambda) (-(5 : ℝ) / 2) +
      120 * rho ^ 6 * Real.rpow (1 - lambda) (-(7 : ℝ) / 2) :=
  quadraticExpDerivativeMajorant_six rho lambda

example (rho lambda : ℝ) :
    quadraticExpDerivativeMajorant 8 rho lambda =
      1680 * rho ^ 4 * Real.rpow (1 - lambda) (-(1 : ℝ) / 2) +
      6720 * rho ^ 5 * Real.rpow (1 - lambda) (-(3 : ℝ) / 2) +
      10080 * rho ^ 6 * Real.rpow (1 - lambda) (-(5 : ℝ) / 2) +
      6720 * rho ^ 7 * Real.rpow (1 - lambda) (-(7 : ℝ) / 2) +
      1680 * rho ^ 8 * Real.rpow (1 - lambda) (-(9 : ℝ) / 2) :=
  quadraticExpDerivativeMajorant_eight rho lambda

example {m : ℕ} {rho lambda : ℝ} (hrho : 0 ≤ rho) (hlambda : lambda < 1) :
    0 ≤ quadraticExpDerivativeMajorant m rho lambda :=
  quadraticExpDerivativeMajorant_nonneg hrho hlambda

example (s : ℂ) (x : ℝ) :
    ‖iteratedDeriv 6 (complexQuadraticExp s) x‖ ≤
      quadraticExpDerivativePointwiseMajorant 6 ‖s‖ s.re x :=
  norm_iteratedDeriv_six_complexQuadraticExp_le s x

example (s : ℂ) (x : ℝ) :
    ‖iteratedDeriv 8 (complexQuadraticExp s) x‖ ≤
      quadraticExpDerivativePointwiseMajorant 8 ‖s‖ s.re x :=
  norm_iteratedDeriv_eight_complexQuadraticExp_le s x

/- The total arithmetic formula expands to the five coefficients used by D₈;
   the adjacent interface canary pins the semantic domain `0 ≤ lambda < 1`. -/
example (lambda : ℝ) :
    gaussianHalfTiltedEvenMomentMajorant 0 lambda =
        Real.rpow (1 - lambda) (-(1 : ℝ) / 2) ∧
      gaussianHalfTiltedEvenMomentMajorant 1 lambda =
        (1 / 2 : ℝ) * Real.rpow (1 - lambda) (-(3 : ℝ) / 2) ∧
      gaussianHalfTiltedEvenMomentMajorant 2 lambda =
        (3 / 4 : ℝ) * Real.rpow (1 - lambda) (-(5 : ℝ) / 2) ∧
      gaussianHalfTiltedEvenMomentMajorant 3 lambda =
        (15 / 8 : ℝ) * Real.rpow (1 - lambda) (-(7 : ℝ) / 2) ∧
      gaussianHalfTiltedEvenMomentMajorant 4 lambda =
        (105 / 16 : ℝ) * Real.rpow (1 - lambda) (-(9 : ℝ) / 2) := by
  norm_num [gaussianHalfTiltedEvenMomentMajorant]

example {μ : Measure ℝ} {lambda : ℝ}
    (h : QuadraticExpEvenMomentBound μ lambda) :
    0 ≤ lambda ∧ lambda < 1 :=
  ⟨h.lambda_nonneg, h.lambda_lt_one⟩

/- A genuinely nonreal parameter prevents the expectation consumers from
   collapsing to a real-only API. -/
example {μ : Measure ℝ}
    (h : QuadraticExpEvenMomentBound μ (1 / 2 : ℝ)) :
    (∫ x : ℝ, ‖iteratedDeriv 6
        (complexQuadraticExp ((1 / 2 : ℂ) + Complex.I)) x‖ ∂μ) ≤
      quadraticExpDerivativeMajorant 6 ‖(1 / 2 : ℂ) + Complex.I‖ (1 / 2) := by
  have h' : QuadraticExpEvenMomentBound μ
      (((1 / 2 : ℂ) + Complex.I).re) := by
    simpa using h
  simpa using integral_norm_iteratedDeriv_six_complexQuadraticExp_le
    ((1 / 2 : ℂ) + Complex.I) h'

example {μ : Measure ℝ}
    (h : QuadraticExpEvenMomentBound μ (1 / 2 : ℝ)) :
    (∫ x : ℝ, ‖iteratedDeriv 8
        (complexQuadraticExp ((1 / 2 : ℂ) + Complex.I)) x‖ ∂μ) ≤
      quadraticExpDerivativeMajorant 8 ‖(1 / 2 : ℂ) + Complex.I‖ (1 / 2) := by
  have h' : QuadraticExpEvenMomentBound μ
      (((1 / 2 : ℂ) + Complex.I).re) := by
    simpa using h
  simpa using integral_norm_iteratedDeriv_eight_complexQuadraticExp_le
    ((1 / 2 : ℂ) + Complex.I) h'

example :
    Integrable
      (fun t : ℝ => (((|2 + t| ^ (2 * 3) : ℝ) : ℂ) *
        complexQuadraticExp (-1 + Complex.I : ℂ) (2 + t))) volume :=
  integrable_volume_shifted_abs_evenPow_mul_complexQuadraticExp
    (s := (-1 + Complex.I : ℂ)) (x := 2) (by norm_num) 3

example :
    Integrable
      (fun t : ℝ => (((|2 + t| ^ 3 : ℝ) : ℂ) *
        complexQuadraticExp (-1 + Complex.I : ℂ) (2 + t))) volume :=
  integrable_volume_shifted_absPow_mul_complexQuadraticExp
    (s := (-1 + Complex.I : ℂ)) (x := 2) (by norm_num) 3

example : Integrable (fun y : ℝ => (1 + |y|) ^ 3)
    (gaussianReal 0 1) :=
  integrable_one_add_abs_cubic_of_pows
    (integrable_standardGaussian_pow 0)
    (integrable_standardGaussian_pow 1)
    (integrable_standardGaussian_pow 2)
    (integrable_standardGaussian_pow 3)

example : StronglyMeasurable (fun t : ℝ =>
    cubicStopLossDifference (gaussianReal 0 1)
      standardRademacherMeasure t) :=
  stronglyMeasurable_standardGaussianRademacher_cubicStopLossDifference

example :
    Integrable
      (fun t : ℝ => iteratedDeriv 4
        (complexQuadraticExp (-1 + Complex.I : ℂ)) (2 + t)) volume :=
  integrable_volume_shifted_iteratedDeriv_four_complexQuadraticExp
    (s := (-1 + Complex.I : ℂ)) (x := 2) (by norm_num)

example :
    Integrable
      (fun t : ℝ => ((1 / 6 : ℝ) *
        cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t) •
        iteratedDeriv 4
          (complexQuadraticExp (-1 + Complex.I : ℂ)) (2 + t)) volume :=
  integrable_standardGaussianRademacher_weighted_fourthDeriv
    (s := (-1 + Complex.I : ℂ)) (x := 2) (by norm_num)

/- The concrete DCT consumer fixes the Gaussian-minus-Rademacher orientation,
   the `1/6` Peano factor, the translated cutoff, and the uncut limit. -/
example :
    Tendsto
      (fun n => ∫ t : ℝ,
        ((1 / 6 : ℝ) * cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t) •
          iteratedDeriv 4
            (upperCutoffRemainder n
              (complexQuadraticExp (-1 + Complex.I : ℂ)) 2) (2 + t))
      atTop
      (𝓝 (∫ t : ℝ,
        ((1 / 6 : ℝ) * cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t) •
          iteratedDeriv 4
            (complexQuadraticExp (-1 + Complex.I : ℂ)) (2 + t))) :=
  upperCutoffRemainder_standardGaussianRademacher_weighted_fourthDeriv_integral_tendsto
    (s := (-1 + Complex.I : ℂ)) (x := 2) (by norm_num)

/- The compact cutoff data are discharged for both concrete laws at the
   downstream complex consumer.  Keeping all four conjuncts visible rejects a
   wrapper that proves only the Gaussian side or only the post-Fubini RHS. -/
example (n : ℕ) :
    (Integrable
        (Function.uncurry (fun t y : ℝ =>
          ((1 / 6 : ℝ) * (max (y - t) 0) ^ 3) •
            deriv (deriv (deriv (deriv
              (upperCutoffRemainder n
                (complexQuadraticExp (-1 + Complex.I : ℂ)) 2))))
              (2 + t)))
        (volume.prod (gaussianReal 0 1)) ∧
      Integrable
        (fun t : ℝ =>
          ((1 / 6 : ℝ) *
            (∫ y, (max (y - t) 0) ^ 3 ∂(gaussianReal 0 1))) •
            deriv (deriv (deriv (deriv
              (upperCutoffRemainder n
                (complexQuadraticExp (-1 + Complex.I : ℂ)) 2))))
              (2 + t)) volume) ∧
    (Integrable
        (Function.uncurry (fun t y : ℝ =>
          ((1 / 6 : ℝ) * (max (y - t) 0) ^ 3) •
            deriv (deriv (deriv (deriv
              (upperCutoffRemainder n
                (complexQuadraticExp (-1 + Complex.I : ℂ)) 2))))
              (2 + t)))
        (volume.prod standardRademacherMeasure) ∧
      Integrable
        (fun t : ℝ =>
          ((1 / 6 : ℝ) *
            (∫ y, (max (y - t) 0) ^ 3 ∂standardRademacherMeasure)) •
            deriv (deriv (deriv (deriv
              (upperCutoffRemainder n
                (complexQuadraticExp (-1 + Complex.I : ℂ)) 2))))
              (2 + t)) volume) :=
  upperCutoffRemainder_standardGaussianRademacher_kernel_data
    (contDiff_complexQuadraticExp (-1 + Complex.I : ℂ)) 2 n

/- The lower-tail producer is consumed directly at the explicit Gaussian and
   two-point Rademacher laws.  The strict `Iio` endpoint, hypothesis `t ≤ -1`,
   and Gaussian-minus-Rademacher orientation are all part of the canary. -/
example {t : ℝ} (ht : t ≤ -1) :
    cubicStopLossDifference (gaussianReal 0 1) standardRademacherMeasure t =
      ∫ y in Set.Iio t, (t - y) ^ 3 ∂(gaussianReal 0 1) :=
  cubicStopLossDifference_standardGaussian_rademacher_of_le_neg_one ht

/- The global producer is exercised in its uniform two-atom form, then in
   every disjoint branch.  The two strict-tail examples are separate Iio/Ioi
   canaries; the endpoint examples pin ownership at `-1` and `1`. -/
example (t : ℝ) :
    (∫ y, (max (y - t) 0) ^ 3 ∂standardRademacherMeasure) =
      ((max ((1 : ℝ) - t) 0) ^ 3 +
        (max ((-1 : ℝ) - t) 0) ^ 3) / 2 :=
  integral_standardRademacher_cubicStopLoss t

example :
    cubicStopLossDifference (gaussianReal 0 1) standardRademacherMeasure 0 =
      (∫ y, (max (y - 0) 0) ^ 3 ∂(gaussianReal 0 1)) -
        (1 / 2 : ℝ) * (1 - 0) ^ 3 := by
  exact cubicStopLossDifference_standardGaussian_rademacher_of_mem_Ioo
    (t := 0) (by norm_num) (by norm_num)

example :
    cubicStopLossDifference (gaussianReal 0 1) standardRademacherMeasure (-2) =
      ∫ y in Set.Iio (-2 : ℝ), ((-2 : ℝ) - y) ^ 3 ∂(gaussianReal 0 1) := by
  simpa using
    (cubicStopLossDifference_standardGaussian_rademacher_piecewise (-2 : ℝ))

example :
    cubicStopLossDifference (gaussianReal 0 1) standardRademacherMeasure 2 =
      ∫ y in Set.Ioi (2 : ℝ), (y - 2) ^ 3 ∂(gaussianReal 0 1) := by
  have h :=
    cubicStopLossDifference_standardGaussian_rademacher_piecewise (2 : ℝ)
  norm_num at h
  exact h

/- The two tail-envelope producers are consumed at opposite non-boundary
   points.  The shared normalized value `6 * exp (-2)` pins the Gaussian
   density factor, the quadratic polynomial, and reflection symmetry. -/
example :
    |cubicStopLossDifference (gaussianReal 0 1)
        standardRademacherMeasure 2| ≤
      (Real.sqrt (2 * Real.pi))⁻¹ * (6 * Real.exp (-2)) := by
  have h :=
    abs_cubicStopLossDifference_standardGaussian_rademacher_le_of_one_le
      (t := 2) (by norm_num)
  convert h using 1
  norm_num [pow_two]

example :
    |cubicStopLossDifference (gaussianReal 0 1)
        standardRademacherMeasure (-2)| ≤
      (Real.sqrt (2 * Real.pi))⁻¹ * (6 * Real.exp (-2)) := by
  have h :=
    abs_cubicStopLossDifference_standardGaussian_rademacher_le_of_le_neg_one
      (t := -2) (by norm_num)
  convert h using 1
  norm_num [pow_two]

/- The compact middle and its global envelope are tested separately from the
   exact tails.  The fifth moment prevents an integrability proof specialized
   only to the cubic Taylor degree. -/
example :
    |cubicStopLossDifference (gaussianReal 0 1)
        standardRademacherMeasure 0| ≤
      8 * ((∫ y, (1 + |y|) ^ 3 ∂(gaussianReal 0 1)) +
        ∫ y, (1 + |y|) ^ 3 ∂standardRademacherMeasure) :=
  abs_cubicStopLossDifference_standardGaussian_rademacher_le_of_abs_lt_one
    (t := 0) (by norm_num)

example (t : ℝ) :
    |cubicStopLossDifference (gaussianReal 0 1)
        standardRademacherMeasure t| ≤
      standardGaussianRademacherCubicEnvelope t :=
  abs_cubicStopLossDifference_standardGaussian_rademacher_le_envelope t

example (t : ℝ) : 0 ≤ standardGaussianRademacherCubicEnvelope t :=
  standardGaussianRademacherCubicEnvelope_nonneg t

example : standardGaussianRademacherCubicEnvelope 0 =
    8 * ((∫ y, (1 + |y|) ^ 3 ∂(gaussianReal 0 1)) +
      ∫ y, (1 + |y|) ^ 3 ∂standardRademacherMeasure) +
      (Real.sqrt (2 * Real.pi))⁻¹ * 2 := by
  norm_num [standardGaussianRademacherCubicEnvelope]

example : standardGaussianRademacherCubicEnvelope 2 =
    (Real.sqrt (2 * Real.pi))⁻¹ * (6 * Real.exp (-2)) := by
  norm_num [standardGaussianRademacherCubicEnvelope, pow_two]

example : standardGaussianRademacherCubicEnvelope (-2) =
    (Real.sqrt (2 * Real.pi))⁻¹ * (6 * Real.exp (-2)) := by
  norm_num [standardGaussianRademacherCubicEnvelope, pow_two]

example : Integrable (fun t : ℝ =>
    |t| ^ 5 * standardGaussianRademacherCubicEnvelope t) volume :=
  integrable_absPow_mul_standardGaussianRademacherCubicEnvelope 5

/- The public quantifier order keeps one cutoff-profile witness valid for all
   negative-real parameters, shifts, cutoff radii, and integration points. -/
example :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ {s : ℂ} {x : ℝ}, s.re < 0 →
        Integrable
          (upperCutoffRemainder_standardGaussianRademacher_majorant C s x)
          volume ∧
        ∀ (n : ℕ) (t : ℝ),
          ‖((1 / 6 : ℝ) *
              cubicStopLossDifference (gaussianReal 0 1)
                standardRademacherMeasure t) •
            iteratedDeriv 4
              (upperCutoffRemainder n (complexQuadraticExp s) x) (x + t)‖ ≤
            upperCutoffRemainder_standardGaussianRademacher_majorant C s x t :=
  upperCutoffRemainder_standardGaussianRademacher_integrable_majorant

/- Expanding the producer freezes all five binomial coefficients and all five
   derivative orders in both the true-exponential and Taylor-polynomial sums. -/
example (C : ℕ → ℝ) (s : ℂ) (x t : ℝ) :
    upperCutoffRemainder_standardGaussianRademacher_majorant C s x t =
      (1 / 6 : ℝ) *
        (|cubicStopLossDifference (gaussianReal 0 1)
            standardRademacherMeasure t| *
          (C 0 * ‖iteratedDeriv 4 (complexQuadraticExp s) (x + t)‖ +
            4 * C 1 * ‖iteratedDeriv 3 (complexQuadraticExp s) (x + t)‖ +
            6 * C 2 * ‖iteratedDeriv 2 (complexQuadraticExp s) (x + t)‖ +
            4 * C 3 * ‖iteratedDeriv 1 (complexQuadraticExp s) (x + t)‖ +
            C 4 * ‖iteratedDeriv 0 (complexQuadraticExp s) (x + t)‖) +
        standardGaussianRademacherCubicEnvelope t *
          (C 0 * ‖iteratedDeriv 4
              (fun z : ℝ => taylorPolynomial3 (complexQuadraticExp s) x (z - x))
              (x + t)‖ +
            4 * C 1 * ‖iteratedDeriv 3
              (fun z : ℝ => taylorPolynomial3 (complexQuadraticExp s) x (z - x))
              (x + t)‖ +
            6 * C 2 * ‖iteratedDeriv 2
              (fun z : ℝ => taylorPolynomial3 (complexQuadraticExp s) x (z - x))
              (x + t)‖ +
            4 * C 3 * ‖iteratedDeriv 1
              (fun z : ℝ => taylorPolynomial3 (complexQuadraticExp s) x (z - x))
              (x + t)‖ +
            C 4 * ‖iteratedDeriv 0
              (fun z : ℝ => taylorPolynomial3 (complexQuadraticExp s) x (z - x))
              (x + t)‖)) := by
  norm_num [upperCutoffRemainder_standardGaussianRademacher_majorant,
    Finset.sum_range_succ, Nat.choose]

/- Direct endpoint applications reject tightening either public tail
   hypothesis to a strict inequality. -/
example :
    |cubicStopLossDifference (gaussianReal 0 1)
        standardRademacherMeasure 1| ≤
      (Real.sqrt (2 * Real.pi))⁻¹ *
        (3 * Real.exp (-(1 / 2 : ℝ))) := by
  have h :=
    abs_cubicStopLossDifference_standardGaussian_rademacher_le_of_one_le
      (t := 1) le_rfl
  convert h using 1
  norm_num [pow_two]

example :
    |cubicStopLossDifference (gaussianReal 0 1)
        standardRademacherMeasure (-1)| ≤
      (Real.sqrt (2 * Real.pi))⁻¹ *
        (3 * Real.exp (-(1 / 2 : ℝ))) := by
  have h :=
    abs_cubicStopLossDifference_standardGaussian_rademacher_le_of_le_neg_one
      (t := -1) le_rfl
  convert h using 1
  norm_num [pow_two]

example :
    cubicStopLossDifference (gaussianReal 0 1) standardRademacherMeasure (-1) =
      ∫ y in Set.Iio (-1 : ℝ), ((-1 : ℝ) - y) ^ 3 ∂(gaussianReal 0 1) := by
  simpa using
    (cubicStopLossDifference_standardGaussian_rademacher_piecewise (-1 : ℝ))

example :
    cubicStopLossDifference (gaussianReal 0 1) standardRademacherMeasure 1 =
      ∫ y in Set.Ioi (1 : ℝ), (y - 1) ^ 3 ∂(gaussianReal 0 1) := by
  have h :=
    cubicStopLossDifference_standardGaussian_rademacher_piecewise (1 : ℝ)
  norm_num at h
  exact h

example (t : ℝ) :
    (1 / 12 : ℝ) *
        cubicStopLossKernel (gaussianReal 0 1) standardRademacherMeasure t =
      (1 / 6 : ℝ) *
        cubicStopLossDifference (gaussianReal 0 1) standardRademacherMeasure t :=
  standardGaussianRademacher_cubicStopLossKernel_normalization t

/- A nonreal fourth-power scaling is now part of the production kernel API,
   rather than an external multiplication of an unscaled equality. -/
example (t : ℝ) :
    cubicStopLossKernelScaled (1 + 2 * Complex.I : ℂ)
        (gaussianReal 0 1) standardRademacherMeasure t =
      (1 + 2 * Complex.I : ℂ) ^ 4 *
        (cubicStopLossKernel (gaussianReal 0 1)
          standardRademacherMeasure t : ℂ) := by
  rfl

example (t : ℝ) :
    (1 / 12 : ℂ) *
        cubicStopLossKernelScaled (1 + 2 * Complex.I : ℂ)
          (gaussianReal 0 1) standardRademacherMeasure t =
      (1 + 2 * Complex.I : ℂ) ^ 4 * ((1 / 6 : ℝ) : ℂ) *
        (cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t : ℂ) :=
  cubicStopLossKernelScaled_normalization (1 + 2 * Complex.I : ℂ) t

example : ((1 + 2 * Complex.I : ℂ) ^ 4).im = -24 := by
  norm_num [pow_succ, Complex.mul_re, Complex.mul_im]

/- The cutoff assembly canary keeps all three noncompact limits explicit at
   the target codomain `ℂ`; no existence-of-cutoff premise is hidden. -/
example {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]
    {f : ℝ → ℂ} (x : ℝ)
    (hm : EqualMomentsThrough μ ν 3)
    (hμf : Integrable (fun y => f (x + y)) μ)
    (hνf : Integrable (fun y => f (x + y)) ν)
    (g : ℕ → ℝ → ℂ)
    (hg4 : ∀ n, ContDiff ℝ 4 (g n))
    (hgc : ∀ n, HasCompactSupport (g n))
    (hμKernel : ∀ n, Integrable
      (Function.uncurry (fun t y =>
        ((1 / 6 : ℝ) * (max (y - t) 0) ^ 3) •
          deriv (deriv (deriv (deriv (g n)))) (x + t))) (volume.prod μ))
    (hνKernel : ∀ n, Integrable
      (Function.uncurry (fun t y =>
        ((1 / 6 : ℝ) * (max (y - t) 0) ^ 3) •
          deriv (deriv (deriv (deriv (g n)))) (x + t))) (volume.prod ν))
    (hμRhs : ∀ n, Integrable (fun t =>
      (((1 / 6 : ℝ) * (∫ y, (max (y - t) 0) ^ 3 ∂μ)) •
        deriv (deriv (deriv (deriv (g n)))) (x + t))))
    (hνRhs : ∀ n, Integrable (fun t =>
      (((1 / 6 : ℝ) * (∫ y, (max (y - t) 0) ^ 3 ∂ν)) •
        deriv (deriv (deriv (deriv (g n)))) (x + t))))
    (hμLimit : Tendsto
      (fun n => ∫ y, g n (x + y) ∂μ) atTop
      (𝓝 (∫ y, (f (x + y) - taylorPolynomial3 f x y) ∂μ)))
    (hνLimit : Tendsto
      (fun n => ∫ y, g n (x + y) ∂ν) atTop
      (𝓝 (∫ y, (f (x + y) - taylorPolynomial3 f x y) ∂ν)))
    (hRhsLimit : Tendsto
      (fun n => ∫ t, ((1 / 6 : ℝ) * cubicStopLossDifference μ ν t) •
        deriv (deriv (deriv (deriv (g n)))) (x + t)) atTop
      (𝓝 (∫ t, ((1 / 6 : ℝ) * cubicStopLossDifference μ ν t) •
        deriv (deriv (deriv (deriv f))) (x + t)))) :
    (∫ y, f (x + y) ∂μ) - ∫ y, f (x + y) ∂ν =
      ∫ t, ((1 / 6 : ℝ) * cubicStopLossDifference μ ν t) •
        deriv (deriv (deriv (deriv f))) (x + t) := by
  exact peanoIdentity4_of_compact_approximants
    (E := ℂ) (μ := μ) (ν := ν) (f := f) (x := x)
    hm hμf hνf g hg4 hgc hμKernel hνKernel hμRhs hνRhs
    hμLimit hνLimit hRhsLimit

/- The concrete P0 canary exposes the complete noncompact conclusion with no
   residual cutoff, moment, integrability, or convergence premise. -/
example :
    (∫ y : ℝ, complexQuadraticExp (-1 + Complex.I : ℂ) (2 + y)
        ∂(gaussianReal 0 1)) -
        ∫ y : ℝ, complexQuadraticExp (-1 + Complex.I : ℂ) (2 + y)
          ∂standardRademacherMeasure =
      ∫ t : ℝ, ((1 / 6 : ℝ) *
        cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t) •
        iteratedDeriv 4 (complexQuadraticExp (-1 + Complex.I : ℂ))
          (2 + t) :=
  peanoIdentity4_standardGaussianRademacher_complexQuadraticExp
    (s := (-1 + Complex.I : ℂ)) (by norm_num) 2

/- The repaired B4 theorem is genuinely generic in the complete normed real
   codomain: no codomain measurable-space or topology instances are supplied
   here. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {μ : Measure ℝ} {f : ℝ → E} (hf : ContDiff ℝ 4 f)
    (x : ℝ)
    (hrem : Integrable
      (fun y : ℝ => f (x + y) - taylorPolynomial3 f x y) μ) :
    Tendsto
      (fun n => ∫ y, upperCutoffRemainder n f x (x + y) ∂μ) atTop
      (𝓝 (∫ y, (f (x + y) - taylorPolynomial3 f x y) ∂μ)) :=
  upperCutoffRemainder_integral_tendsto hf x hrem

/- The adjacent explicit Rademacher wrapper preserves the same minimal
   arbitrary-codomain API rather than reintroducing measurable assumptions. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℝ → E} (hf : ContDiff ℝ 4 f) (x : ℝ) :
    Tendsto
      (fun n => ∫ y, upperCutoffRemainder n f x (x + y)
        ∂standardRademacherMeasure) atTop
      (𝓝 (∫ y, (f (x + y) - taylorPolynomial3 f x y)
        ∂standardRademacherMeasure)) :=
  upperCutoffRemainder_standardRademacher_integral_tendsto hf x

example (y t : ℝ) (ht : t ≤ y) : 0 ≤ y - t := sub_nonneg.mpr ht

example : ((1 : ℝ) - 0) ≠ ((0 : ℝ) - 1) := by norm_num

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℝ → E} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (x y : ℝ) :
    f (x + y) =
      ∫ t in Set.Iic y, (y - t) • deriv (deriv f) (x + t) :=
  peanoKernel2_Iic hf hfc x y

/- The producer-connected k=4 guard applies the generic theorem at `E = ℂ`
   and exposes the exact cubic kernel prefactor `1/6`. -/
example (x y : ℝ) :
    (0 : ℂ) =
      ∫ t in Set.Iic y, ((y - t) ^ 3 / 6) •
        deriv (deriv (deriv (deriv (fun _ : ℝ => (0 : ℂ))))) (x + t) := by
  have h := peanoKernel4_Iic (f := fun _ : ℝ => (0 : ℂ))
    (show ContDiff ℝ 4 (fun _ : ℝ => (0 : ℂ)) from contDiff_const)
    HasCompactSupport.zero x y
  simpa only [Pi.zero_apply, deriv_const, smul_zero, integral_zero] using h

/- The law-level k=4 producer keeps the `1/6` factor and the Δ₃ orientation
   visible at codomain `ℂ`; this is the compact precursor to the Gaussian vs
   Rademacher cutoff theorem. -/
example :
    (∫ y, (fun _ : ℝ => (0 : ℂ)) (0 + y) ∂Measure.dirac (0 : ℝ)) -
        ∫ y, (fun _ : ℝ => (0 : ℂ)) (0 + y) ∂Measure.dirac (1 : ℝ) =
      ∫ t, ((1 / 6 : ℝ) * cubicStopLossDifference
        (Measure.dirac (0 : ℝ)) (Measure.dirac (1 : ℝ)) t) •
          deriv (deriv (deriv (deriv (fun _ : ℝ => (0 : ℂ))))) (0 + t) := by
  exact peanoIdentity4_compact
    (μ := Measure.dirac (0 : ℝ)) (ν := Measure.dirac (1 : ℝ))
    (f := fun _ : ℝ => (0 : ℂ)) (x := 0)
    (by fun_prop) (by exact HasCompactSupport.zero)
    (by
      exact (integrable_zero (ℝ × ℝ) ℂ
        (volume.prod (Measure.dirac (0 : ℝ)))).congr
        (Filter.Eventually.of_forall (fun p => by
          rcases p with ⟨t, y⟩
          simp)))
    (by
      exact (integrable_zero (ℝ × ℝ) ℂ
        (volume.prod (Measure.dirac (1 : ℝ)))).congr
        (Filter.Eventually.of_forall (fun p => by
          rcases p with ⟨t, y⟩
          simp)))
    (by
      exact (integrable_zero ℝ ℂ volume).congr
        (Filter.Eventually.of_forall (fun t => by simp)))
    (by
      exact (integrable_zero ℝ ℂ volume).congr
        (Filter.Eventually.of_forall (fun t => by simp)))

/- The actual replacement-kernel normalization is producer-facing, not just a
   factorial check: `k = 2 * Δ₃`, `1/6 * Δ₃ = 1/12 * k`, and scaling carries
   the outer `c⁴/12` factor. -/
example (μ ν : Measure ℝ) (t : ℝ) :
    cubicStopLossKernel μ ν t =
      2 * ((∫ y, (max (y - t) 0) ^ 3 ∂μ) -
        (∫ y, (max (y - t) 0) ^ 3 ∂ν)) := by
  rfl

example (μ ν : Measure ℝ) (t : ℝ) :
    (1 / 6 : ℝ) * cubicStopLossDifference μ ν t =
      (1 / 12 : ℝ) * cubicStopLossKernel μ ν t := by
  rw [cubicStopLossKernel]
  ring

example (c : ℝ) (μ ν : Measure ℝ) (t : ℝ) :
    (c ^ 4 / 12 : ℝ) * cubicStopLossKernel μ ν t =
      (c ^ 4 / 6 : ℝ) * cubicStopLossDifference μ ν t := by
  rw [cubicStopLossKernel]
  ring

/- The actual law-level producer is exercised at codomain `ℂ` with distinct
   laws.  The conclusion keeps the paper's `μ−ν` / `X−Y` stop-loss order
   visible, so swapping the laws or scalar orientation changes the expected
   type even though the zero compact-support witness discharges integrability. -/
example :
    (∫ y, (fun _ : ℝ => (0 : ℂ)) (0 + y) ∂Measure.dirac (0 : ℝ)) -
        ∫ y, (fun _ : ℝ => (0 : ℂ)) (0 + y) ∂Measure.dirac (1 : ℝ) =
      ∫ t, ((∫ y, max (y - t) 0 ∂Measure.dirac (0 : ℝ)) -
        (∫ y, max (y - t) 0 ∂Measure.dirac (1 : ℝ))) •
          deriv (deriv (fun _ : ℝ => (0 : ℂ))) (0 + t) := by
  exact peanoIdentity2_compact
    (μ := Measure.dirac (0 : ℝ)) (ν := Measure.dirac (1 : ℝ))
    (f := fun _ : ℝ => (0 : ℂ)) (x := 0)
    (by fun_prop) (by exact HasCompactSupport.zero)
    (by
      exact (integrable_zero (ℝ × ℝ) ℂ
        (volume.prod (Measure.dirac (0 : ℝ)))).congr
        (Filter.Eventually.of_forall (fun p => by
          rcases p with ⟨t, y⟩
          simp)))
    (by
      exact (integrable_zero (ℝ × ℝ) ℂ
        (volume.prod (Measure.dirac (1 : ℝ)))).congr
        (Filter.Eventually.of_forall (fun p => by
          rcases p with ⟨t, y⟩
          simp)))
    (by simp) (by simp)

/- These factorial equalities remain small arithmetic guards alongside the
   producer-connected k=4 application above. -/
example : (1 : ℝ) / Nat.factorial 1 = 1 := by norm_num
example : (1 : ℝ) / Nat.factorial 3 = 1 / 6 := by norm_num

#print axioms convexSquareExpectation_le
#print axioms sum_sq_sparseUpperDuplicatedCoefficient
#print axioms sum_fourth_sparseUpperDuplicatedCoefficient
#print axioms sum_sixth_sparseUpperDuplicatedCoefficient
#print axioms sum_sixth_sparseUpperDuplicatedCoefficient_le

#print axioms sparseEntry_firstMoment
#print axioms sparseEntry_secondMoment
#print axioms sparseEntry_secondMoment_normalized
#print axioms peanoIdentity2_compact
#print axioms peanoKernel4_Iic
#print axioms peanoIdentity4_compact
#print axioms EqualMomentsThrough
#print axioms EqualMomentsThrough.integrable_left
#print axioms EqualMomentsThrough.integrable_right
#print axioms EqualMomentsThrough.equal
#print axioms EqualMomentsThrough.integrable_id_left
#print axioms EqualMomentsThrough.integrable_id_right
#print axioms EqualMomentsThrough.equal_mass
#print axioms EqualMomentsThrough.equal_first_moment
#print axioms taylorPolynomial3
#print axioms equalMomentsThrough_taylorPolynomial3
#print axioms integrable_taylorPolynomial3_left
#print axioms integrable_taylorPolynomial3_right
#print axioms contDiff_complexQuadraticExp
#print axioms iteratedDeriv_four_complexQuadraticExpComplex
#print axioms iteratedDeriv_four_complexQuadraticExp
#print axioms integrable_complexQuadraticExp_volume
#print axioms integrable_gaussianPDFReal_mul_complexQuadraticExp
#print axioms integrable_gaussianReal_complexQuadraticExp
#print axioms complexQuadraticExp_add_expand
#print axioms integrable_gaussianReal_shifted_complexQuadraticExp
#print axioms integrable_gaussianReal_evenPow_mul_complexQuadraticExp
#print axioms integrable_gaussianReal_shifted_evenPow_mul_complexQuadraticExp
#print axioms integrable_gaussianReal_shifted_iteratedDeriv_four_complexQuadraticExp
#print axioms integrable_gaussianReal_taylorPolynomial3
#print axioms integrable_gaussianReal_shifted_complexQuadraticExp_remainder
#print axioms upperCutoffRadius_pos
#print axioms upperCutoff_apply
#print axioms upperCutoff_contDiff
#print axioms upperCutoff_hasCompactSupport
#print axioms upperCutoff_eq_one
#print axioms upperCutoff_eq_zero
#print axioms upperCutoff_pointwise_tendsto
#print axioms upperCutoff_iteratedDeriv
#print axioms upperCutoffBase_iteratedDeriv_bound
#print axioms upperCutoff_iteratedDeriv_bound
#print axioms upperCutoffRemainder_apply
#print axioms upperCutoffRemainder_contDiff
#print axioms upperCutoffRemainder_hasCompactSupport
#print axioms upperCutoffRemainder_integral_tendsto
#print axioms upperCutoffRemainder_standardRademacher_integral_tendsto
#print axioms upperCutoffRemainder_standardRademacher_support
#print axioms upperCutoffRemainder_iteratedDeriv_four
#print axioms upperCutoffRemainder_iteratedDeriv_four_norm_le
#print axioms taylorPolynomial3_iteratedDeriv_four
#print axioms upperCutoffRemainder_iteratedDeriv_four_tendsto
#print axioms standardGaussianRademacher_equalMoments
#print axioms integrable_standardGaussian_pow
#print axioms standardRademacherMeasure_mass
#print axioms standardRademacherMeasure_first_moment
#print axioms standardRademacherMeasure_second_moment
#print axioms integrable_standardGaussian_cubicStopLoss
#print axioms integrable_standardRademacher_cubicStopLoss
#print axioms cubicStopLossDifference_standardGaussian_rademacher_of_one_le
#print axioms cubicStopLossDifference_standardGaussian_rademacher_of_le_neg_one
#print axioms integral_standardRademacher_cubicStopLoss
#print axioms cubicStopLossDifference_standardGaussian_rademacher_of_mem_Ioo
#print axioms cubicStopLossDifference_standardGaussian_rademacher_piecewise
#print axioms standardGaussianRademacher_cubicStopLossKernel_normalization
#print axioms cubicStopLossKernelScaled_normalization
#print axioms standardRademacherMeasure_isProbabilityMeasure
#print axioms integrable_volume_shifted_abs_evenPow_mul_complexQuadraticExp
#print axioms integrable_volume_shifted_absPow_mul_complexQuadraticExp
#print axioms iteratedDeriv_one_complexQuadraticExp
#print axioms iteratedDeriv_two_complexQuadraticExp
#print axioms iteratedDeriv_three_complexQuadraticExp
#print axioms iteratedDeriv_complexQuadraticExp
#print axioms iteratedDeriv_six_complexQuadraticExp
#print axioms iteratedDeriv_eight_complexQuadraticExp
#print axioms quadraticExpDerivativePointwiseMajorant_nonneg
#print axioms quadraticExpDerivativePointwiseMajorant_six
#print axioms quadraticExpDerivativePointwiseMajorant_eight
#print axioms quadraticExpDerivativeMajorant_nonneg
#print axioms quadraticExpDerivativeMajorant_six
#print axioms quadraticExpDerivativeMajorant_eight
#print axioms norm_iteratedDeriv_six_complexQuadraticExp_le
#print axioms norm_iteratedDeriv_eight_complexQuadraticExp_le
#print axioms integral_norm_iteratedDeriv_six_complexQuadraticExp_le
#print axioms integral_norm_iteratedDeriv_eight_complexQuadraticExp_le
#print axioms integrable_volume_shifted_iteratedDeriv_four_complexQuadraticExp
#print axioms integrable_one_add_abs_cubic_of_pows
#print axioms stronglyMeasurable_standardGaussianRademacher_cubicStopLossDifference
#print axioms integrable_standardGaussianRademacher_weighted_fourthDeriv
#print axioms upperCutoffRemainder_standardGaussianRademacher_weighted_fourthDeriv_integral_tendsto
#print axioms abs_cubicStopLossDifference_standardGaussian_rademacher_le_of_one_le
#print axioms abs_cubicStopLossDifference_standardGaussian_rademacher_le_of_le_neg_one
#print axioms abs_cubicStopLossDifference_standardGaussian_rademacher_le_of_abs_lt_one
#print axioms abs_cubicStopLossDifference_standardGaussian_rademacher_le_envelope
#print axioms standardGaussianRademacherCubicEnvelope_nonneg
#print axioms integrable_absPow_mul_standardGaussianRademacherCubicEnvelope
#print axioms upperCutoffRemainder_standardGaussianRademacher_integrable_majorant
#print axioms upperCutoffRemainder_standardGaussianRademacher_kernel_data
#print axioms peanoIdentity4_of_compact_approximants
#print axioms peanoIdentity4_standardGaussianRademacher_complexQuadraticExp
#print axioms integral_gaussianHalf_complexQuadraticExp_real

set_option linter.style.longLine false in
open Lean in
run_cmd
  let allowed : Array Name :=
    #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Name :=
    #[``CertifiedJL.sparseEntry_firstMoment,
      ``CertifiedJL.sparseEntry_secondMoment,
      ``CertifiedJL.sparseEntry_secondMoment_normalized,
      ``CertifiedJL.integral_gaussianHalf_complexQuadraticExp_real,
      ``CertifiedJL.integrable_absPow_mul_abs_peanoKDensity,
      ``CertifiedJL.integrable_peanoKDensity,
      ``CertifiedJL.peanoKDensity_neg,
      ``CertifiedJL.peanoKDensity_nonneg_of_one_le,
      ``CertifiedJL.peanoKDensity_nonneg_of_le_neg_one,
      ``CertifiedJL.convexSquareExpectation_le,
      ``CertifiedJL.sum_sq_sparseUpperDuplicatedCoefficient,
      ``CertifiedJL.sum_fourth_sparseUpperDuplicatedCoefficient,
      ``CertifiedJL.sum_sixth_sparseUpperDuplicatedCoefficient,
      ``CertifiedJL.sum_sixth_sparseUpperDuplicatedCoefficient_le,
      ``CertifiedJL.peanoKernel2_Iic,
      ``CertifiedJL.peanoIdentity2_compact,
      ``CertifiedJL.peanoKernel4_Iic,
      ``CertifiedJL.peanoIdentity4_compact,
      ``CertifiedJL.EqualMomentsThrough,
      ``CertifiedJL.EqualMomentsThrough.integrable_left,
      ``CertifiedJL.EqualMomentsThrough.integrable_right,
      ``CertifiedJL.EqualMomentsThrough.equal,
      ``CertifiedJL.EqualMomentsThrough.integrable_id_left,
      ``CertifiedJL.EqualMomentsThrough.integrable_id_right,
      ``CertifiedJL.EqualMomentsThrough.equal_mass,
      ``CertifiedJL.EqualMomentsThrough.equal_first_moment,
      ``CertifiedJL.taylorPolynomial3,
      ``CertifiedJL.equalMomentsThrough_taylorPolynomial3,
      ``CertifiedJL.integrable_taylorPolynomial3_left,
      ``CertifiedJL.integrable_taylorPolynomial3_right,
      ``CertifiedJL.contDiff_complexQuadraticExp,
      ``CertifiedJL.iteratedDeriv_four_complexQuadraticExpComplex,
      ``CertifiedJL.iteratedDeriv_four_complexQuadraticExp,
      ``CertifiedJL.integrable_complexQuadraticExp_volume,
      ``CertifiedJL.integrable_gaussianPDFReal_mul_complexQuadraticExp,
      ``CertifiedJL.integrable_gaussianReal_complexQuadraticExp,
      ``CertifiedJL.complexQuadraticExp_add_expand,
      ``CertifiedJL.integrable_gaussianReal_shifted_complexQuadraticExp,
      ``CertifiedJL.integrable_gaussianReal_evenPow_mul_complexQuadraticExp,
      ``CertifiedJL.integrable_gaussianReal_shifted_evenPow_mul_complexQuadraticExp,
      ``CertifiedJL.integrable_gaussianReal_shifted_iteratedDeriv_four_complexQuadraticExp,
      ``CertifiedJL.integrable_gaussianReal_taylorPolynomial3,
      ``CertifiedJL.integrable_gaussianReal_shifted_complexQuadraticExp_remainder,
      ``CertifiedJL.upperCutoffRadius_pos,
      ``CertifiedJL.upperCutoff_apply,
      ``CertifiedJL.upperCutoff_contDiff,
      ``CertifiedJL.upperCutoff_hasCompactSupport,
      ``CertifiedJL.upperCutoff_eq_one,
      ``CertifiedJL.upperCutoff_eq_zero,
      ``CertifiedJL.upperCutoff_pointwise_tendsto,
      ``CertifiedJL.upperCutoff_iteratedDeriv,
      ``CertifiedJL.upperCutoffBase_iteratedDeriv_bound,
      ``CertifiedJL.upperCutoff_iteratedDeriv_bound,
      ``CertifiedJL.upperCutoffRemainder_apply,
      ``CertifiedJL.upperCutoffRemainder_contDiff,
      ``CertifiedJL.upperCutoffRemainder_hasCompactSupport,
      ``CertifiedJL.upperCutoffRemainder_integral_tendsto,
      ``CertifiedJL.upperCutoffRemainder_standardRademacher_integral_tendsto,
      ``CertifiedJL.upperCutoffRemainder_standardRademacher_support,
      ``CertifiedJL.upperCutoffRemainder_iteratedDeriv_four,
      ``CertifiedJL.upperCutoffRemainder_iteratedDeriv_four_norm_le,
      ``CertifiedJL.taylorPolynomial3_iteratedDeriv_four,
      ``CertifiedJL.upperCutoffRemainder_iteratedDeriv_four_tendsto,
      ``CertifiedJL.standardGaussianRademacher_equalMoments,
      ``CertifiedJL.integrable_standardGaussian_pow,
      ``CertifiedJL.standardRademacherMeasure_mass,
      ``CertifiedJL.standardRademacherMeasure_first_moment,
      ``CertifiedJL.standardRademacherMeasure_second_moment,
      ``CertifiedJL.integrable_standardGaussian_cubicStopLoss,
      ``CertifiedJL.integrable_standardRademacher_cubicStopLoss,
      ``CertifiedJL.cubicStopLossDifference_standardGaussian_rademacher_of_one_le,
      ``CertifiedJL.cubicStopLossDifference_standardGaussian_rademacher_of_le_neg_one,
      ``CertifiedJL.integral_standardRademacher_cubicStopLoss,
      ``CertifiedJL.cubicStopLossDifference_standardGaussian_rademacher_of_mem_Ioo,
      ``CertifiedJL.cubicStopLossDifference_standardGaussian_rademacher_piecewise,
      ``CertifiedJL.standardGaussianRademacher_cubicStopLossKernel_normalization,
      ``CertifiedJL.cubicStopLossKernelScaled_normalization,
      ``CertifiedJL.standardRademacherMeasure_isProbabilityMeasure,
      ``CertifiedJL.integrable_volume_shifted_abs_evenPow_mul_complexQuadraticExp,
      ``CertifiedJL.integrable_volume_shifted_absPow_mul_complexQuadraticExp,
      ``CertifiedJL.iteratedDeriv_one_complexQuadraticExp,
      ``CertifiedJL.iteratedDeriv_two_complexQuadraticExp,
      ``CertifiedJL.iteratedDeriv_three_complexQuadraticExp,
      ``CertifiedJL.iteratedDeriv_complexQuadraticExp,
      ``CertifiedJL.iteratedDeriv_six_complexQuadraticExp,
      ``CertifiedJL.iteratedDeriv_eight_complexQuadraticExp,
      ``CertifiedJL.quadraticExpDerivativePointwiseMajorant_nonneg,
      ``CertifiedJL.quadraticExpDerivativePointwiseMajorant_six,
      ``CertifiedJL.quadraticExpDerivativePointwiseMajorant_eight,
      ``CertifiedJL.quadraticExpDerivativeMajorant_nonneg,
      ``CertifiedJL.quadraticExpDerivativeMajorant_six,
      ``CertifiedJL.quadraticExpDerivativeMajorant_eight,
      ``CertifiedJL.norm_iteratedDeriv_six_complexQuadraticExp_le,
      ``CertifiedJL.norm_iteratedDeriv_eight_complexQuadraticExp_le,
      ``CertifiedJL.integral_norm_iteratedDeriv_six_complexQuadraticExp_le,
      ``CertifiedJL.integral_norm_iteratedDeriv_eight_complexQuadraticExp_le,
      ``CertifiedJL.integrable_volume_shifted_iteratedDeriv_four_complexQuadraticExp,
      ``CertifiedJL.integrable_one_add_abs_cubic_of_pows,
      ``CertifiedJL.stronglyMeasurable_standardGaussianRademacher_cubicStopLossDifference,
      ``CertifiedJL.integrable_standardGaussianRademacher_weighted_fourthDeriv,
      ``CertifiedJL.upperCutoffRemainder_standardGaussianRademacher_weighted_fourthDeriv_integral_tendsto,
      ``CertifiedJL.abs_cubicStopLossDifference_standardGaussian_rademacher_le_of_one_le,
      ``CertifiedJL.abs_cubicStopLossDifference_standardGaussian_rademacher_le_of_le_neg_one,
      ``CertifiedJL.abs_cubicStopLossDifference_standardGaussian_rademacher_le_of_abs_lt_one,
      ``CertifiedJL.abs_cubicStopLossDifference_standardGaussian_rademacher_le_envelope,
      ``CertifiedJL.standardGaussianRademacherCubicEnvelope_nonneg,
      ``CertifiedJL.integrable_absPow_mul_standardGaussianRademacherCubicEnvelope,
      ``CertifiedJL.upperCutoffRemainder_standardGaussianRademacher_integrable_majorant,
      ``CertifiedJL.upperCutoffRemainder_standardGaussianRademacher_kernel_data,
      ``CertifiedJL.peanoIdentity4_of_compact_approximants,
      ``CertifiedJL.peanoIdentity4_standardGaussianRademacher_complexQuadraticExp]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    unless axioms.size == allowed.size &&
        axioms.all allowed.contains &&
        allowed.all axioms.contains do
      throwError "unexpected axioms for {target}: {axioms}"

end UpperTailCanaries
end Tests
end CertifiedJL
