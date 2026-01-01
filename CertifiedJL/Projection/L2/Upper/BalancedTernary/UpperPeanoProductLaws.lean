/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperPeanoHybrid
import CertifiedJL.Probability.Finite.UniformPiBridge
import CertifiedJL.Probability.Distributions.Rademacher.Rademacher
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Product-law endpoints for the sparse upper Peano telescope

This file identifies the two endpoint product measures used by the finite
coordinate telescope.  It deliberately contains no hybrid-error algebra.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace CertifiedJL

private theorem uniformBool_realSign_toMeasure :
    ((PMF.uniformOfFintype Bool).map
      (fun bit => (signBit bit : ℝ))).toMeasure =
      standardRademacherMeasure := by
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _)]
  ext s hs
  rw [Measure.map_apply (measurable_of_finite _) hs]
  rw [PMF.toMeasure_apply_fintype]
  rw [standardRademacherMeasure, Measure.add_apply _ _ s,
    Measure.smul_apply _ _ s, Measure.smul_apply _ _ s]
  simp only [Measure.dirac_apply' _ hs]
  rw [Fintype.sum_bool]
  by_cases hneg : (-1 : ℝ) ∈ s <;>
    by_cases hpos : (1 : ℝ) ∈ s <;>
      simp [Set.indicator, hneg, hpos, signBit]

/-- Coordinatewise real signs under the uniform Boolean product PMF have the
product of the standard two-point Rademacher measures. -/
theorem rademacherSigns_toMeasure
    {ι : Type*} [Fintype ι] :
    ((rademacherPMF ι).map
      (fun bits i => (signBit (bits i) : ℝ))).toMeasure =
      Measure.pi (fun _ : ι => standardRademacherMeasure) := by
  change (uniformPiMap
    (fun _ : ι => fun bit => (signBit bit : ℝ))).toMeasure = _
  rw [uniformPiMap_toMeasure _ (fun _ => measurable_of_finite _)]
  congr 1
  funext i
  exact uniformBool_realSign_toMeasure

/-- The pushforward of the finite Rademacher sum is the pushforward of the
coordinate dot product under the explicit product Rademacher measure. -/
theorem rademacherSum_map_eq_map_pi_standardRademacher
    {ι : Type*} [Fintype ι] (b : ι → ℝ) :
    Measure.map (rademacherSum b) (rademacherPMF ι).toMeasure =
      Measure.map (fun x : ι → ℝ => ∑ i, b i * x i)
        (Measure.pi (fun _ : ι => standardRademacherMeasure)) := by
  let signs : (ι → Bool) → (ι → ℝ) :=
    fun bits i => (signBit (bits i) : ℝ)
  let dot : (ι → ℝ) → ℝ := fun x => ∑ i, b i * x i
  have hpoint : rademacherSum b = dot ∘ signs := by
    funext bits
    simp only [rademacherSum, dot, signs, Function.comp_apply]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hpoint, ← Measure.map_map (by fun_prop : Measurable dot)
    (measurable_of_finite signs)]
  rw [PMF.toMeasure_map signs (rademacherPMF ι)
    (measurable_of_finite signs)]
  rw [show ((rademacherPMF ι).map signs).toMeasure =
      Measure.pi (fun _ : ι => standardRademacherMeasure) by
    simpa only [signs] using (rademacherSigns_toMeasure (ι := ι))]

private noncomputable def weightedGaussianVariance
    {ι : Type*} [Fintype ι] (b : ι → ℝ) : NNReal :=
  ⟨∑ i, b i ^ 2, Finset.sum_nonneg fun _ _ => sq_nonneg _⟩

/-- A weighted sum of independent standard Gaussians is the centered Gaussian
whose variance is the sum of the squared weights. -/
theorem map_weightedSum_pi_gaussianReal
    {ι : Type*} [Fintype ι] (b : ι → ℝ) :
    Measure.map (fun x : ι → ℝ => ∑ i, b i * x i)
        (Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      gaussianReal 0 (weightedGaussianVariance b) := by
  let scale : (ι → ℝ) → (ι → ℝ) := fun x i => b i * x i
  let total : (ι → ℝ) → ℝ := fun x => ∑ i, x i
  have hfun : (fun x : ι → ℝ => ∑ i, b i * x i) = total ∘ scale := by
    rfl
  rw [hfun, ← Measure.map_map (by fun_prop : Measurable total)
    (by fun_prop : Measurable scale)]
  have hpi : Measure.map scale (Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      Measure.pi (fun i : ι => gaussianReal 0 (scaledVariance (b i) 1)) := by
    calc
      Measure.map scale (Measure.pi (fun _ : ι => gaussianReal 0 1)) =
          Measure.pi (fun i : ι =>
            Measure.map (fun x : ℝ => b i * x) (gaussianReal 0 1)) := by
        exact Measure.pi_map_pi (fun i => (by fun_prop :
          AEMeasurable (fun x : ℝ => b i * x) (gaussianReal 0 1)))
      _ = _ := by
        congr 1
        funext i
        simpa [scaledVariance] using
          (gaussianReal_map_const_mul (μ := 0) (v := (1 : NNReal)) (b i))
  rw [hpi]
  apply Measure.ext_of_charFun
  rw [charFun_map_sum_pi_eq_prod]
  funext t
  rw [Finset.prod_apply]
  simp_rw [charFun_gaussianReal t]
  rw [← Complex.exp_sum]
  congr 1
  have hscaled (i : ι) :
      ((scaledVariance (b i) 1 : NNReal) : ℝ) = b i ^ 2 := by
    simp [scaledVariance]
  have hvar : ((weightedGaussianVariance b : NNReal) : ℝ) =
      ∑ i, b i ^ 2 := rfl
  simp_rw [hscaled]
  rw [hvar]
  norm_num
  calc
    (∑ x, (b x : ℂ) ^ 2 * (t : ℂ) ^ 2 / 2) =
        ∑ x, (b x : ℂ) ^ 2 * ((t : ℂ) ^ 2 / 2) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
    _ = (∑ x, (b x : ℂ) ^ 2) * ((t : ℂ) ^ 2 / 2) := by
      rw [Finset.sum_mul]
    _ = _ := by ring

/-- Under squared-weight normalization `1/2`, the weighted Gaussian product
endpoint is exactly the Gaussian-half reference law used by U7. -/
theorem map_weightedSum_pi_gaussianReal_eq_gaussianHalf
    {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (hsq : ∑ i, b i ^ 2 = (1 / 2 : ℝ)) :
    Measure.map (fun x : ι → ℝ => ∑ i, b i * x i)
        (Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      gaussianReal 0 (2 : NNReal)⁻¹ := by
  rw [map_weightedSum_pi_gaussianReal]
  congr 2
  apply NNReal.eq
  change (∑ i, b i ^ 2) = (((2 : NNReal)⁻¹ : NNReal) : ℝ)
  norm_num at hsq ⊢
  exact hsq

end CertifiedJL
