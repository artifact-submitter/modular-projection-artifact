/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.NormalApproximation.Shared.CDFMetric
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Exponential layer-cake transfer

This file proves the exact bounded-variation estimate used after the
Berry--Esseen step in the sparse one-row Esscher argument.  We avoid a
general Stieltjes integration theory.  Instead, Tonelli/Fubini is applied
directly to the identity

`exp (-t y) = ∫ z in Set.Ici y, t * exp (-t z)`

for `t > 0`.  For the strict event `a < y`, the inner section after swapping
the integrals is precisely `Set.Ioc a z`.  Its probability is
`cdf μ z - cdf μ a`; consequently a uniform CDF error `ε` contributes at
most `2 ε`, one copy at each endpoint.
-/

open MeasureTheory ProbabilityTheory Set

namespace CertifiedJL
namespace Probability

/-- The decreasing exponential density used in the layer-cake identity. -/
noncomputable def exponentialLayerDensity (t z : ℝ) : ℝ :=
  t * Real.exp (-t * z)

/--
The two-variable nonnegative kernel whose two iterated integrals give the
exponentially weighted strict upper tail.
-/
noncomputable def exponentialLayerKernel (a t : ℝ) (p : ℝ × ℝ) : ℝ :=
  if a < p.1 ∧ p.1 ≤ p.2 then exponentialLayerDensity t p.2 else 0

theorem exponentialLayerDensity_nonneg {t : ℝ} (ht : 0 ≤ t) (z : ℝ) :
    0 ≤ exponentialLayerDensity t z := by
  exact mul_nonneg ht (Real.exp_nonneg _)

theorem exponentialLayerDensity_integrableOn_Ioi {t : ℝ} (ht : 0 < t)
    (y : ℝ) :
    IntegrableOn (exponentialLayerDensity t) (Ioi y) := by
  have h :=
    (integrableOn_exp_mul_Ioi (a := -t) (by linarith) y).const_mul t
  change Integrable
    (fun z : ℝ => t * Real.exp (-t * z))
    (volume.restrict (Ioi y))
  simpa only [neg_mul] using h

theorem exponentialLayerDensity_integrableOn_Ici {t : ℝ} (ht : 0 < t)
    (y : ℝ) :
    IntegrableOn (exponentialLayerDensity t) (Ici y) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact exponentialLayerDensity_integrableOn_Ioi ht y

theorem integral_Ioi_exponentialLayerDensity {t : ℝ} (ht : 0 < t)
    (y : ℝ) :
    (∫ z in Ioi y, exponentialLayerDensity t z) =
      Real.exp (-t * y) := by
  unfold exponentialLayerDensity
  rw [integral_const_mul, integral_exp_mul_Ioi (a := -t) (by linarith)]
  field_simp

theorem integral_Ici_exponentialLayerDensity {t : ℝ} (ht : 0 < t)
    (y : ℝ) :
    (∫ z in Ici y, exponentialLayerDensity t z) =
      Real.exp (-t * y) := by
  rw [integral_Ici_eq_integral_Ioi,
    integral_Ioi_exponentialLayerDensity ht y]

theorem measurable_exponentialLayerDensity (t : ℝ) :
    Measurable (exponentialLayerDensity t) := by
  unfold exponentialLayerDensity
  fun_prop

theorem measurable_exponentialLayerKernel (a t : ℝ) :
    Measurable (exponentialLayerKernel a t) := by
  unfold exponentialLayerKernel
  apply Measurable.ite
  · exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_snd)
  · exact (measurable_exponentialLayerDensity t).comp measurable_snd
  · exact measurable_const

theorem exponentialLayerKernel_nonneg {a t : ℝ} (ht : 0 ≤ t)
    (p : ℝ × ℝ) :
    0 ≤ exponentialLayerKernel a t p := by
  unfold exponentialLayerKernel
  split_ifs
  · exact exponentialLayerDensity_nonneg ht p.2
  · exact le_rfl

theorem exponentialLayerKernel_integrable_prod
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a t : ℝ} (ht : 0 < t) :
    Integrable (exponentialLayerKernel a t) (μ.prod volume) := by
  have hmeas :
      AEStronglyMeasurable (exponentialLayerKernel a t)
        (μ.prod volume) :=
    (measurable_exponentialLayerKernel a t).aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards with y
    by_cases hay : a < y
    · have hfun :
          (fun z => exponentialLayerKernel a t (y, z)) =
            (Ici y).indicator (exponentialLayerDensity t) := by
        funext z
        simp only [exponentialLayerKernel, hay, true_and]
        by_cases hyz : y ≤ z <;> simp [hyz]
      rw [hfun]
      exact (exponentialLayerDensity_integrableOn_Ici ht y).integrable_indicator
        measurableSet_Ici
    · have hfun :
          (fun z => exponentialLayerKernel a t (y, z)) = 0 := by
        funext z
        simp [exponentialLayerKernel, hay]
      rw [hfun]
      exact integrable_zero ℝ ℝ volume
  · have hinner :
        (fun y =>
            ∫ z, ‖exponentialLayerKernel a t (y, z)‖) =
          fun y => if a < y then Real.exp (-t * y) else 0 := by
      funext y
      rw [show (fun z => ‖exponentialLayerKernel a t (y, z)‖) =
          fun z => exponentialLayerKernel a t (y, z) by
        funext z
        rw [Real.norm_eq_abs, abs_of_nonneg
          (exponentialLayerKernel_nonneg ht.le (y, z))]]
      by_cases hay : a < y
      · simp only [hay, if_true]
        rw [show (fun z => exponentialLayerKernel a t (y, z)) =
            (Ici y).indicator (exponentialLayerDensity t) by
          funext z
          simp only [exponentialLayerKernel, hay, true_and]
          by_cases hyz : y ≤ z <;> simp [hyz]]
        rw [integral_indicator measurableSet_Ici]
        exact integral_Ici_exponentialLayerDensity ht y
      · simp only [hay, if_false]
        have hzero :
            (fun z => exponentialLayerKernel a t (y, z)) = 0 := by
          funext z
          simp [exponentialLayerKernel, hay]
        rw [hzero]
        simp
    rw [hinner]
    have hbounded :
        ∀ y, ‖if a < y then Real.exp (-t * y) else 0‖ ≤
          Real.exp (-t * a) := by
      intro y
      by_cases hay : a < y
      · rw [if_pos hay, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (by nlinarith)
      · simp only [if_neg hay, norm_zero]
        exact Real.exp_nonneg _
    exact Integrable.mono'
      (integrable_const (c := Real.exp (-t * a)))
      (Measurable.ite
        (measurableSet_lt measurable_const measurable_id)
        (by fun_prop) measurable_const).aestronglyMeasurable
      (ae_of_all μ hbounded)

/--
Direct exponential layer-cake identity for a strict upper tail.

The interval on the right is `Ioc a z`, not `Ioo a z`: this is the exact
endpoint convention produced by integrating `z` over `Ici y`.  The choice is
what makes the formula use the ordinary closed-half-line CDF without any
atom correction.
-/
theorem integral_exponential_strictUpper_eq_integral_Ioc
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a t : ℝ} (ht : 0 < t) :
    (∫ y in Ioi a, Real.exp (-t * y) ∂μ) =
      ∫ z in Ioi a,
        exponentialLayerDensity t z * μ.real (Ioc a z) := by
  have hk := exponentialLayerKernel_integrable_prod μ (a := a) ht
  have hk' :
      Integrable
        (Function.uncurry
          (fun y z => exponentialLayerKernel a t (y, z)))
        (μ.prod volume) := by
    have heq :
        Function.uncurry
            (fun y z => exponentialLayerKernel a t (y, z)) =
          exponentialLayerKernel a t := by
      funext p
      rcases p with ⟨y, z⟩
      rfl
    rw [heq]
    exact hk
  have hswap := integral_integral_swap hk'
  have hleft :
      (fun y => ∫ z, exponentialLayerKernel a t (y, z)) =
        fun y => (Ioi a).indicator (fun y => Real.exp (-t * y)) y := by
    funext y
    by_cases hay : a < y
    · simp only [Set.indicator_apply, mem_Ioi, hay, if_true]
      rw [show (fun z => exponentialLayerKernel a t (y, z)) =
          (Ici y).indicator (exponentialLayerDensity t) by
        funext z
        simp only [exponentialLayerKernel, hay, true_and]
        by_cases hyz : y ≤ z <;> simp [hyz]]
      rw [integral_indicator measurableSet_Ici]
      exact integral_Ici_exponentialLayerDensity ht y
    · simp only [Set.indicator_apply, mem_Ioi, hay, if_false]
      have hzero :
          (fun z => exponentialLayerKernel a t (y, z)) = 0 := by
        funext z
        simp [exponentialLayerKernel, hay]
      rw [hzero]
      simp
  have hright :
      (fun z => ∫ y, exponentialLayerKernel a t (y, z) ∂μ) =
        fun z =>
          exponentialLayerDensity t z * μ.real (Ioc a z) := by
    funext z
    rw [show (fun y => exponentialLayerKernel a t (y, z)) =
        (Ioc a z).indicator
          (fun _ => exponentialLayerDensity t z) by
      funext y
      simp only [exponentialLayerKernel]
      by_cases hy : a < y ∧ y ≤ z <;> simp [hy]]
    rw [integral_indicator measurableSet_Ioc, setIntegral_const]
    simp only [smul_eq_mul]
    ring
  rw [hleft, hright] at hswap
  have hwhole :
      (∫ z, exponentialLayerDensity t z * μ.real (Ioc a z)) =
        ∫ z in Ioi a,
          exponentialLayerDensity t z * μ.real (Ioc a z) := by
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with z
    by_cases haz : a < z
    · simp only [Set.indicator_apply, mem_Ioi, haz, if_true]
    · simp only [Set.indicator_apply, mem_Ioi, haz, if_false]
      have hempty : Ioc a z = ∅ := by
        ext y
        simp only [mem_Ioc, mem_empty_iff_false, iff_false]
        intro hy
        exact haz (hy.1.trans_le hy.2)
      rw [hempty]
      simp
  rw [hwhole] at hswap
  simpa only [integral_indicator measurableSet_Ioi] using hswap

/-- An interval probability is a difference of two closed-half-line CDFs. -/
theorem probability_Ioc_eq_cdf_sub
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a z : ℝ} (haz : a ≤ z) :
    μ.real (Ioc a z) = cdf μ z - cdf μ a := by
  have hset : Ioc a z = Iic z \ Iic a := by
    ext y
    simp only [mem_Ioc, mem_sdiff, mem_Iic]
    constructor
    · intro hy
      exact ⟨hy.2, not_le.mpr hy.1⟩
    · intro hy
      exact ⟨lt_of_not_ge hy.2, hy.1⟩
  rw [hset, measureReal_sdiff (Iic_subset_Iic.mpr haz)
    measurableSet_Iic, cdf_eq_real, cdf_eq_real]

/--
Uniform CDF control gives the exact `2 ε` control of every interval
`(a,z]`: one error occurs at `z` and one at `a`.
-/
theorem probability_Ioc_sub_le_two_mul
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    {ε a z : ℝ} (haz : a ≤ z)
    (hKol : ∀ x, |cdf μ x - cdf ν x| ≤ ε) :
    |μ.real (Ioc a z) - ν.real (Ioc a z)| ≤ 2 * ε := by
  rw [probability_Ioc_eq_cdf_sub μ haz,
    probability_Ioc_eq_cdf_sub ν haz]
  calc
    |(cdf μ z - cdf μ a) - (cdf ν z - cdf ν a)| =
        |(cdf μ z - cdf ν z) - (cdf μ a - cdf ν a)| := by
      ring_nf
    _ ≤ |cdf μ z - cdf ν z| + |cdf μ a - cdf ν a| :=
      abs_sub _ _
    _ ≤ ε + ε := add_le_add (hKol z) (hKol a)
    _ = 2 * ε := by ring

/--
The exponentially weighted strict upper-tail expectations of two
probability laws differ by at most the exponential threshold times twice
their uniform CDF error.

No atom assumption is needed.  Strictness is handled exactly by the
`Ioc` section in `integral_exponential_strictUpper_eq_integral_Ioc`.
-/
theorem abs_integral_exponential_strictUpper_sub_le
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    {ε a t : ℝ} (ht : 0 < t)
    (hKol : ∀ x, |cdf μ x - cdf ν x| ≤ ε) :
    |(∫ y in Ioi a, Real.exp (-t * y) ∂μ) -
        (∫ y in Ioi a, Real.exp (-t * y) ∂ν)| ≤
      2 * ε * Real.exp (-t * a) := by
  rw [integral_exponential_strictUpper_eq_integral_Ioc μ ht,
    integral_exponential_strictUpper_eq_integral_Ioc ν ht]
  let w : ℝ → ℝ := fun z => exponentialLayerDensity t z
  let fμ : ℝ → ℝ := fun z => w z * μ.real (Ioc a z)
  let fν : ℝ → ℝ := fun z => w z * ν.real (Ioc a z)
  have hw_nonneg : ∀ z, 0 ≤ w z :=
    fun z => exponentialLayerDensity_nonneg ht.le z
  have hw_int : IntegrableOn w (Ioi a) :=
    exponentialLayerDensity_integrableOn_Ioi ht a
  have hfμ_int : IntegrableOn fμ (Ioi a) := by
    have hkμ :=
      exponentialLayerKernel_integrable_prod μ (a := a) ht
    have hint :
        Integrable
          (fun z => ∫ y, exponentialLayerKernel a t (y, z) ∂μ)
          volume :=
      hkμ.integral_prod_right
    have heq :
        (fun z => ∫ y, exponentialLayerKernel a t (y, z) ∂μ) =
          fμ := by
      funext z
      rw [show (fun y => exponentialLayerKernel a t (y, z)) =
          (Ioc a z).indicator
            (fun _ => exponentialLayerDensity t z) by
        funext y
        simp only [exponentialLayerKernel]
        by_cases hy : a < y ∧ y ≤ z <;> simp [hy]]
      rw [integral_indicator measurableSet_Ioc, setIntegral_const]
      simp only [fμ, w, smul_eq_mul]
      ring
    rw [heq] at hint
    exact hint.integrableOn
  have hfν_int : IntegrableOn fν (Ioi a) := by
    have hkν :=
      exponentialLayerKernel_integrable_prod ν (a := a) ht
    have hint :
        Integrable
          (fun z => ∫ y, exponentialLayerKernel a t (y, z) ∂ν)
          volume :=
      hkν.integral_prod_right
    have heq :
        (fun z => ∫ y, exponentialLayerKernel a t (y, z) ∂ν) =
          fν := by
      funext z
      rw [show (fun y => exponentialLayerKernel a t (y, z)) =
          (Ioc a z).indicator
            (fun _ => exponentialLayerDensity t z) by
        funext y
        simp only [exponentialLayerKernel]
        by_cases hy : a < y ∧ y ≤ z <;> simp [hy]]
      rw [integral_indicator measurableSet_Ioc, setIntegral_const]
      simp only [fν, w, smul_eq_mul]
      ring
    rw [heq] at hint
    exact hint.integrableOn
  change |(∫ z in Ioi a, fμ z) - ∫ z in Ioi a, fν z| ≤ _
  rw [← integral_sub hfμ_int hfν_int]
  calc
    |∫ z in Ioi a, fμ z - fν z| ≤
        ∫ z in Ioi a, |fμ z - fν z| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z in Ioi a, 2 * ε * w z := by
      apply setIntegral_mono_on
      · exact (hfμ_int.sub hfν_int).abs
      · exact hw_int.const_mul (2 * ε)
      · exact measurableSet_Ioi
      · intro z hz
        have hinterval :=
          probability_Ioc_sub_le_two_mul μ ν hz.le hKol
        rw [show fμ z - fν z =
            w z * (μ.real (Ioc a z) - ν.real (Ioc a z)) by
          simp only [fμ, fν]
          ring]
        rw [abs_mul, abs_of_nonneg (hw_nonneg z)]
        simpa [mul_comm] using
          mul_le_mul_of_nonneg_left hinterval (hw_nonneg z)
    _ = 2 * ε * Real.exp (-t * a) := by
      rw [integral_const_mul, integral_Ioi_exponentialLayerDensity ht a]

/--
Kolmogorov-distance form of the exponential layer-cake transfer.
-/
theorem abs_integral_exponential_strictUpper_sub_le_kolmogorovDistance
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    {a t : ℝ} (ht : 0 < t) :
    |(∫ y in Ioi a, Real.exp (-t * y) ∂μ) -
        (∫ y in Ioi a, Real.exp (-t * y) ∂ν)| ≤
      2 * kolmogorovDistance μ ν * Real.exp (-t * a) := by
  apply abs_integral_exponential_strictUpper_sub_le
    (μ := μ) (ν := ν) ht
  intro x
  simpa [cdfAbsoluteDiscrepancy, cdfDiscrepancy] using
    cdfAbsoluteDiscrepancy_le_kolmogorovDistance μ ν x

end Probability
end CertifiedJL
