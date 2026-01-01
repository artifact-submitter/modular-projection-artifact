/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.NormalApproximation.Rademacher.TiltedRademacherMoments
import CertifiedJL.Probability.Distributions.Gaussian.StandardGaussian
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A distribution-free large-Lyapunov branch

This file proves an elementary replacement for the vacuous `d_K ≤ 1`
branch.  A finite law of mean zero and second moment one lies within `3/5`
in Kolmogorov distance of the standard Gaussian.  Consequently the desired
`d_K ≤ (3/5) L` estimate is automatic as soon as `L ≥ 11/12`.

The proof is deliberately self-contained.  It combines the one-sided
second-moment inequality

`P[X > t], P[X ≤ -t] ≤ 1 / (1 + t²)`

with the elementary density bound `φ ≤ 2/5`.  No quantitative
Berry--Esseen estimate is assumed.
-/

open scoped BigOperators ENNReal

open MeasureTheory ProbabilityTheory Set

namespace CertifiedJL
namespace Probability

section FiniteCantelli

universe u

variable {Ω : Type u} [Fintype Ω] [MeasurableSpace Ω]
  [MeasurableSingletonClass Ω]

/-- Real-valued expectation of a function under a finite PMF. -/
noncomputable def finitePMFExpectation
    (p : PMF Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, (p ω).toReal * X ω

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem finitePMFExpectation_const
    (p : PMF Ω) (c : ℝ) :
    finitePMFExpectation p (fun _ => c) = c := by
  classical
  unfold finitePMFExpectation
  rw [← Finset.sum_mul]
  have hsum : ∑ ω : Ω, (p ω).toReal = 1 := by
    rw [← ENNReal.toReal_sum]
    · have hp := p.tsum_coe
      rw [tsum_fintype] at hp
      rw [hp]
      norm_num
    · intro ω _
      exact p.apply_ne_top ω
  rw [hsum, one_mul]

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem finitePMFExpectation_add
    (p : PMF Ω) (X Y : Ω → ℝ) :
    finitePMFExpectation p (fun ω => X ω + Y ω) =
      finitePMFExpectation p X + finitePMFExpectation p Y := by
  classical
  unfold finitePMFExpectation
  simp_rw [mul_add]
  exact Finset.sum_add_distrib

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem finitePMFExpectation_const_mul
    (p : PMF Ω) (c : ℝ) (X : Ω → ℝ) :
    finitePMFExpectation p (fun ω => c * X ω) =
      c * finitePMFExpectation p X := by
  classical
  unfold finitePMFExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem finitePMFExpectation_eq_integral
    (p : PMF Ω) (X : Ω → ℝ) :
    finitePMFExpectation p X = ∫ ω, X ω ∂p.toMeasure := by
  rw [finitePMF_integral_eq_sum]
  unfold finitePMFExpectation
  apply Finset.sum_congr rfl
  intro ω _
  simp only [smul_eq_mul]

omit [Fintype Ω] in
theorem cdf_map_finitePMF_eq_eventProbability [Finite Ω]
    (p : PMF Ω) (X : Ω → ℝ) (x : ℝ) :
    cdf (p.toMeasure.map X) x =
      (eventProbability p (fun ω => X ω ≤ x)).toReal := by
  let : IsProbabilityMeasure (p.toMeasure.map X) :=
    Measure.isProbabilityMeasure_map
      (measurable_of_finite X).aemeasurable
  rw [cdf_eq_real]
  rw [Measure.real]
  rw [Measure.map_apply (measurable_of_finite X) measurableSet_Iic]
  rw [eventProbability_eq_toMeasure]
  congr 2

/--
The closed upper-tail half of Cantelli's inequality, proved directly by
squaring `tX + 1` and summing over the finite sample space.
-/
theorem finitePMF_upper_le_one_div_one_add_sq
    (p : PMF Ω) (X : Ω → ℝ)
    (hmean : finitePMFExpectation p X = 0)
    (hsecond : finitePMFExpectation p (fun ω => X ω ^ 2) = 1)
    {t : ℝ} (ht : 0 < t) :
    (eventProbability p (fun ω => t ≤ X ω)).toReal ≤
      1 / (1 + t ^ 2) := by
  classical
  rw [eventProbability_toReal_eq_sum]
  have hpoint (ω : Ω) :
      (1 + t ^ 2) ^ 2 *
          (if t ≤ X ω then (p ω).toReal else 0) ≤
        (p ω).toReal * (t * X ω + 1) ^ 2 := by
    split_ifs with hω
    · have hw : 0 ≤ (p ω).toReal := ENNReal.toReal_nonneg
      have hbase : 1 + t ^ 2 ≤ t * X ω + 1 := by
        nlinarith
      have hleft : 0 ≤ 1 + t ^ 2 := by positivity
      have hright : 0 ≤ t * X ω + 1 := hleft.trans hbase
      calc
        (1 + t ^ 2) ^ 2 * (p ω).toReal =
            (p ω).toReal * (1 + t ^ 2) ^ 2 := by ring
        _ ≤ (p ω).toReal * (t * X ω + 1) ^ 2 :=
          mul_le_mul_of_nonneg_left
            ((sq_le_sq₀ hleft hright).2 hbase) hw
    · simp only [mul_zero]
      exact mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  have hsum :
      (1 + t ^ 2) ^ 2 *
          ∑ ω, (if t ≤ X ω then (p ω).toReal else 0) ≤
        ∑ ω, (p ω).toReal * (t * X ω + 1) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun ω _ => hpoint ω
  have hexpect :
      ∑ ω, (p ω).toReal * (t * X ω + 1) ^ 2 =
        1 + t ^ 2 := by
    calc
      ∑ ω, (p ω).toReal * (t * X ω + 1) ^ 2 =
          t ^ 2 * finitePMFExpectation p (fun ω => X ω ^ 2) +
            2 * t * finitePMFExpectation p X +
            finitePMFExpectation p (fun _ => 1) := by
        unfold finitePMFExpectation
        rw [Finset.mul_sum, Finset.mul_sum]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ω _
        ring
      _ = 1 + t ^ 2 := by
        rw [hmean, hsecond, finitePMFExpectation_const]
        ring
  rw [hexpect] at hsum
  have hpos : 0 < 1 + t ^ 2 := by positivity
  rw [div_eq_mul_inv]
  apply (le_div_iff₀ hpos).2
  have hcancel :
      (1 + t ^ 2) *
          ∑ ω, (if t ≤ X ω then (p ω).toReal else 0) ≤ 1 := by
    nlinarith
  simpa [mul_comm] using hcancel

/--
The closed lower-tail half of Cantelli's inequality.
-/
theorem finitePMF_lower_le_one_div_one_add_sq
    (p : PMF Ω) (X : Ω → ℝ)
    (hmean : finitePMFExpectation p X = 0)
    (hsecond : finitePMFExpectation p (fun ω => X ω ^ 2) = 1)
    {t : ℝ} (ht : 0 < t) :
    (eventProbability p (fun ω => X ω ≤ -t)).toReal ≤
      1 / (1 + t ^ 2) := by
  let Y : Ω → ℝ := fun ω => -X ω
  have hmeanY : finitePMFExpectation p Y = 0 := by
    rw [show Y = fun ω => (-1 : ℝ) * X ω by funext ω; simp [Y]]
    rw [finitePMFExpectation_const_mul, hmean]
    norm_num
  have hsecondY :
      finitePMFExpectation p (fun ω => Y ω ^ 2) = 1 := by
    simpa only [Y, neg_sq] using hsecond
  simpa only [Y, le_neg] using
    finitePMF_upper_le_one_div_one_add_sq
      p Y hmeanY hsecondY ht

end FiniteCantelli

section GaussianElementary

/-- The standard Gaussian density is even. -/
theorem standardGaussianDensity_neg (x : ℝ) :
    standardGaussianDensity (-x) = standardGaussianDensity x := by
  simp [standardGaussianDensity]

/-- The standard Gaussian upper tail at zero is exactly one half. -/
theorem standardGaussianTail_zero :
    standardGaussianTail 0 = 1 / 2 := by
  have heven :
      (fun x : ℝ => standardGaussianDensity |x|) =
        standardGaussianDensity := by
    funext x
    rw [← standardGaussianDensity_neg x]
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx, standardGaussianDensity_neg]
    · rw [abs_of_neg (lt_of_not_ge hx)]
  have htotal : ∫ x : ℝ, standardGaussianDensity x = 1 := by
    rw [standardGaussianDensity_eq_gaussianPDFReal]
    exact ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 (by norm_num)
  have hsplit := integral_comp_abs (f := standardGaussianDensity)
  rw [heven, htotal] at hsplit
  unfold standardGaussianTail
  linarith

/-- The elementary global density estimate `φ(x) ≤ 2/5`. -/
theorem standardGaussianDensity_le_two_fifths (x : ℝ) :
    standardGaussianDensity x ≤ 2 / 5 := by
  have hpi : (25 : ℝ) / 8 < Real.pi := by
    linarith [Real.pi_gt_d2]
  have hsqrt : (5 : ℝ) / 2 < √(2 * Real.pi) := by
    rw [Real.lt_sqrt (by norm_num : 0 ≤ (5 : ℝ) / 2)]
    nlinarith
  have hinv : (√(2 * Real.pi))⁻¹ < (2 : ℝ) / 5 := by
    rw [inv_lt_iff_one_lt_mul₀ (by positivity :
      0 < √(2 * Real.pi))]
    nlinarith
  unfold standardGaussianDensity
  calc
    (√(2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) ≤
        (√(2 * Real.pi))⁻¹ * 1 := by
      gcongr
      exact Real.exp_le_one_iff.mpr (by
        nlinarith [sq_nonneg x])
    _ ≤ 2 / 5 := by simpa using hinv.le

/--
For `t ≥ 0`, the standard Gaussian upper tail stays above the tangent-line
bound `1/2 - (2/5)t`.
-/
theorem standardGaussianTail_ge_half_sub_two_fifths_mul
    {t : ℝ} (ht : 0 ≤ t) :
    1 / 2 - (2 / 5 : ℝ) * t ≤ standardGaussianTail t := by
  have hdecomp :
      standardGaussianTail 0 =
        (∫ x : ℝ in Set.Ioc 0 t, standardGaussianDensity x) +
          standardGaussianTail t := by
    unfold standardGaussianTail
    have hdisjoint : Disjoint (Set.Ioc (0 : ℝ) t) (Set.Ioi t) := by
      exact Set.disjoint_left.2 fun x hx hxt => (not_lt_of_ge hx.2) hxt
    have hunion : Set.Ioc (0 : ℝ) t ∪ Set.Ioi t = Set.Ioi 0 := by
      ext x
      simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
      constructor
      · rintro (hx | hx)
        · exact hx.1
        · exact lt_of_le_of_lt ht hx
      · intro hx
        by_cases hxt : x ≤ t
        · exact Or.inl ⟨hx, hxt⟩
        · exact Or.inr (lt_of_not_ge hxt)
    rw [← setIntegral_union hdisjoint measurableSet_Ioi
      (integrable_standardGaussianDensity.integrableOn)
      (integrable_standardGaussianDensity.integrableOn), hunion]
  have hinterval :
      (∫ x : ℝ in Set.Ioc 0 t, standardGaussianDensity x) ≤
        (2 / 5 : ℝ) * t := by
    calc
      (∫ x : ℝ in Set.Ioc 0 t, standardGaussianDensity x) ≤
          ∫ _x : ℝ in Set.Ioc 0 t, (2 / 5 : ℝ) := by
        apply setIntegral_mono_on
          integrable_standardGaussianDensity.integrableOn
          (integrableOn_const
            (hs := by
              rw [Real.volume_Ioc]
              exact ENNReal.ofReal_ne_top) :
            IntegrableOn (fun _x : ℝ => (2 / 5 : ℝ)) (Set.Ioc 0 t))
          measurableSet_Ioc
        intro x _
        exact standardGaussianDensity_le_two_fifths x
      _ = (2 / 5 : ℝ) * t := by
        rw [setIntegral_const]
        simp only [smul_eq_mul, Measure.real, Real.volume_Ioc,
          sub_zero]
        rw [ENNReal.toReal_ofReal ht]
        ring
  rw [standardGaussianTail_zero] at hdecomp
  linarith

/-- On the nonnegative half-line, the Gaussian upper tail is at most one half. -/
theorem standardGaussianTail_le_half {t : ℝ} (ht : 0 ≤ t) :
    standardGaussianTail t ≤ 1 / 2 := by
  rw [← standardGaussianTail_zero]
  unfold standardGaussianTail
  refine setIntegral_mono_set
    integrable_standardGaussianDensity.integrableOn ?_ ?_
  · exact ae_restrict_of_forall_mem measurableSet_Ioi fun x _ =>
      standardGaussianDensity_nonneg x
  · exact .of_forall <| Set.Ioi_subset_Ioi ht

/-- The standard Gaussian CDF is one minus its strict upper tail. -/
theorem cdf_standardGaussian_eq_one_sub_tail (x : ℝ) :
    cdf (gaussianReal 0 1) x = 1 - standardGaussianTail x := by
  rw [cdf_eq_real]
  have hIic :
      (gaussianReal 0 1).real (Set.Iic x) =
        ∫ y : ℝ in Set.Iic x, standardGaussianDensity y := by
    rw [Measure.real, gaussianReal_apply_eq_integral 0 (by norm_num)]
    rw [ENNReal.toReal_ofReal]
    · rw [standardGaussianDensity_eq_gaussianPDFReal]
    · exact setIntegral_nonneg measurableSet_Iic
        (fun y _ => ProbabilityTheory.gaussianPDFReal_nonneg 0 1 y)
  rw [hIic]
  have hsplit :
      (∫ y : ℝ in Set.Iic x, standardGaussianDensity y) +
          standardGaussianTail x = 1 := by
    unfold standardGaussianTail
    rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl)
      measurableSet_Ioi
      integrable_standardGaussianDensity.integrableOn
      integrable_standardGaussianDensity.integrableOn]
    rw [Iic_union_Ioi, Measure.restrict_univ]
    rw [standardGaussianDensity_eq_gaussianPDFReal]
    exact ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 (by norm_num)
  linarith

/-- Reflection identifies the Gaussian CDF at `-t` with the upper tail at `t`. -/
theorem cdf_standardGaussian_neg_eq_tail (t : ℝ) :
    cdf (gaussianReal 0 1) (-t) = standardGaussianTail t := by
  rw [cdf_eq_real]
  have hIic :
      (gaussianReal 0 1).real (Set.Iic (-t)) =
        ∫ y : ℝ in Set.Iic (-t), standardGaussianDensity y := by
    rw [Measure.real, gaussianReal_apply_eq_integral 0 (by norm_num)]
    rw [ENNReal.toReal_ofReal]
    · rw [standardGaussianDensity_eq_gaussianPDFReal]
    · exact setIntegral_nonneg measurableSet_Iic
        (fun y _ => ProbabilityTheory.gaussianPDFReal_nonneg 0 1 y)
  rw [hIic]
  unfold standardGaussianTail
  calc
    (∫ y : ℝ in Set.Iic (-t), standardGaussianDensity y) =
        ∫ y : ℝ in Set.Iic (-t), standardGaussianDensity (-y) := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro y _
      exact (standardGaussianDensity_neg y).symm
    _ = ∫ y : ℝ in Set.Ioi t, standardGaussianDensity y := by
      have h := integral_comp_neg_Iic (-t) standardGaussianDensity
      rw [neg_neg] at h
      exact h

end GaussianElementary

section UniversalThreeFifths

universe u

variable {Ω : Type u} [Fintype Ω] [MeasurableSpace Ω]
  [MeasurableSingletonClass Ω]

omit [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem eventProbability_toReal_le_one
    (p : PMF Ω) (event : Ω → Prop) :
    (eventProbability p event).toReal ≤ 1 := by
  unfold eventProbability
  rw [← ENNReal.toReal_one]
  exact (ENNReal.toReal_le_toReal
    ((p.map event).apply_ne_top True) ENNReal.one_ne_top).2
      ((p.map event).coe_le_one True)

/--
Every finite mean-zero, unit-second-moment law is within `11/20` of the
standard Gaussian in Kolmogorov distance.
-/
theorem kolmogorovDistance_finitePMF_standardGaussian_le_eleven_twentieths
    (p : PMF Ω) (X : Ω → ℝ)
    (hmean : finitePMFExpectation p X = 0)
    (hsecond : finitePMFExpectation p (fun ω => X ω ^ 2) = 1) :
    kolmogorovDistance (p.toMeasure.map X) (gaussianReal 0 1) ≤
      (11 : ℝ) / 20 := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  rw [cdfAbsoluteDiscrepancy, cdfDiscrepancy, abs_le]
  rw [cdf_map_finitePMF_eq_eventProbability]
  by_cases hx : 0 ≤ x
  · have htail :
        standardGaussianTail x ≤ (11 : ℝ) / 20 :=
      (standardGaussianTail_le_half hx).trans (by norm_num)
    have hupper :
        (eventProbability p (fun ω => X ω ≤ x)).toReal -
            cdf (gaussianReal 0 1) x ≤ 11 / 20 := by
      rw [cdf_standardGaussian_eq_one_sub_tail]
      have hprob :
          (eventProbability p (fun ω => X ω ≤ x)).toReal ≤ 1 := by
        exact eventProbability_toReal_le_one p _
      linarith
    constructor
    · have hlow :
          -(11 / 20 : ℝ) ≤
            (eventProbability p (fun ω => X ω ≤ x)).toReal -
              cdf (gaussianReal 0 1) x := by
        rw [cdf_standardGaussian_eq_one_sub_tail]
        have hpartition :
            (eventProbability p (fun ω => X ω ≤ x)).toReal +
                (eventProbability p (fun ω => x < X ω)).toReal = 1 := by
          have hsum :
              ∑ ω : Ω, (p ω).toReal = 1 := by
            rw [← ENNReal.toReal_sum]
            · have hp := p.tsum_coe
              rw [tsum_fintype] at hp
              rw [hp]
              norm_num
            · intro ω _
              exact p.apply_ne_top ω
          rw [eventProbability_toReal_eq_sum,
            eventProbability_toReal_eq_sum, ← Finset.sum_add_distrib,
            ← hsum]
          apply Finset.sum_congr rfl
          intro ω _
          by_cases hω : X ω ≤ x
          · simp [hω, not_lt_of_ge hω]
          · simp [hω, lt_of_not_ge hω]
        have htailLower :
            1 / 2 - (2 / 5 : ℝ) * x ≤ standardGaussianTail x :=
          standardGaussianTail_ge_half_sub_two_fifths_mul hx
        by_cases hx1 : 1 ≤ x
        · have hstrict :
              (eventProbability p (fun ω => x < X ω)).toReal ≤ 1 / 2 := by
            calc
              _ ≤ 1 / (1 + x ^ 2) :=
                calc
                  _ ≤ (eventProbability p (fun ω => x ≤ X ω)).toReal := by
                    rw [eventProbability_toReal_eq_sum,
                      eventProbability_toReal_eq_sum]
                    apply Finset.sum_le_sum
                    intro ω _
                    by_cases hω : x < X ω
                    · simp [hω, hω.le]
                    · simp only [hω, if_false]
                      by_cases hle : x ≤ X ω
                      · rw [if_pos hle]
                        exact ENNReal.toReal_nonneg
                      · rw [if_neg hle]
                  _ ≤ 1 / (1 + x ^ 2) :=
                    finitePMF_upper_le_one_div_one_add_sq
                      p X hmean hsecond
                        (lt_of_lt_of_le zero_lt_one hx1)
              _ ≤ 1 / 2 := by
                gcongr
                nlinarith
          linarith [standardGaussianTail_nonneg x]
        · have hxlt : x < 1 := lt_of_not_ge hx1
          have hstrict :
              (eventProbability p (fun ω => x < X ω)).toReal ≤
                1 / (1 + x ^ 2) := by
            by_cases hx0 : x = 0
            · subst x
              exact (eventProbability_toReal_le_one p _).trans (by norm_num)
            · calc
                _ ≤ (eventProbability p (fun ω => x ≤ X ω)).toReal := by
                  rw [eventProbability_toReal_eq_sum,
                    eventProbability_toReal_eq_sum]
                  apply Finset.sum_le_sum
                  intro ω _
                  by_cases hω : x < X ω
                  · simp [hω, hω.le]
                  · simp only [hω, if_false]
                    by_cases hle : x ≤ X ω
                    · rw [if_pos hle]
                      exact ENNReal.toReal_nonneg
                    · rw [if_neg hle]
                _ ≤ 1 / (1 + x ^ 2) :=
                  finitePMF_upper_le_one_div_one_add_sq
                    p X hmean hsecond
                      (lt_of_le_of_ne hx (Ne.symm hx0))
          have hnumeric :
              1 / (1 + x ^ 2) -
                  (1 / 2 - (2 / 5 : ℝ) * x) ≤ 11 / 20 := by
            have hden : 0 < 1 + x ^ 2 := by positivity
            have hcubic : x ^ 3 ≤ x ^ 2 := by
              nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hxlt.le)]
            have hsquare := sq_nonneg (7 * x - 2)
            have hquot :
                1 / (1 + x ^ 2) ≤
                  (11 / 20 : ℝ) +
                    (1 / 2 - (2 / 5 : ℝ) * x) := by
              apply (div_le_iff₀ hden).2
              by_cases hxhalf : x ≤ 1 / 2
              · have hfactor : 0 ≤ 5 - 8 * x := by nlinarith
                nlinarith [mul_nonneg (sq_nonneg x) hfactor,
                  sq_nonneg (1 - 4 * x)]
              · have hfactor :
                    0 ≤ -8 * x ^ 2 + 17 * x + 1 / 2 := by
                  have hx2 : x ^ 2 ≤ x := by nlinarith
                  nlinarith
                have hprod :
                    0 ≤ (x - 1 / 2) *
                      (-8 * x ^ 2 + 17 * x + 1 / 2) :=
                  mul_nonneg (by nlinarith) hfactor
                nlinarith
            linarith
          linarith
      exact hlow
    · exact hupper
  · have hxneg : x < 0 := lt_of_not_ge hx
    let t : ℝ := -x
    have ht : 0 < t := neg_pos.mpr hxneg
    have hupper :
        (eventProbability p (fun ω => X ω ≤ x)).toReal -
            cdf (gaussianReal 0 1) x ≤ 11 / 20 := by
      have hleft :
          (eventProbability p (fun ω => X ω ≤ x)).toReal ≤
            1 / (1 + t ^ 2) := by
        simpa only [t, neg_neg] using
          finitePMF_lower_le_one_div_one_add_sq
            p X hmean hsecond ht
      have hgauss :
          cdf (gaussianReal 0 1) x = standardGaussianTail t := by
        simpa only [t, neg_neg] using cdf_standardGaussian_neg_eq_tail t
      rw [hgauss]
      have htailLower :
          1 / 2 - (2 / 5 : ℝ) * t ≤ standardGaussianTail t :=
        standardGaussianTail_ge_half_sub_two_fifths_mul ht.le
      by_cases ht1 : 1 ≤ t
      · have hrat : 1 / (1 + t ^ 2) ≤ 1 / 2 := by
          gcongr
          nlinarith
        linarith [standardGaussianTail_nonneg t]
      · have htlt : t < 1 := lt_of_not_ge ht1
        have hnumeric :
            1 / (1 + t ^ 2) -
                (1 / 2 - (2 / 5 : ℝ) * t) ≤ 11 / 20 := by
          have hden : 0 < 1 + t ^ 2 := by positivity
          have hcubic : t ^ 3 ≤ t ^ 2 := by
            nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr htlt.le)]
          have hsquare := sq_nonneg (7 * t - 2)
          have hquot :
              1 / (1 + t ^ 2) ≤
                (11 / 20 : ℝ) +
                  (1 / 2 - (2 / 5 : ℝ) * t) := by
            apply (div_le_iff₀ hden).2
            by_cases hthalf : t ≤ 1 / 2
            · have hfactor : 0 ≤ 5 - 8 * t := by nlinarith
              nlinarith [mul_nonneg (sq_nonneg t) hfactor,
                sq_nonneg (1 - 4 * t)]
            · have hfactor :
                  0 ≤ -8 * t ^ 2 + 17 * t + 1 / 2 := by
                have ht2 : t ^ 2 ≤ t := by nlinarith
                nlinarith
              have hprod :
                  0 ≤ (t - 1 / 2) *
                    (-8 * t ^ 2 + 17 * t + 1 / 2) :=
                mul_nonneg (by nlinarith) hfactor
              nlinarith
          linarith
        linarith
    have hlower :
        -(11 / 20 : ℝ) ≤
          (eventProbability p (fun ω => X ω ≤ x)).toReal -
            cdf (gaussianReal 0 1) x := by
      have hprob :
          0 ≤ (eventProbability p (fun ω => X ω ≤ x)).toReal :=
        ENNReal.toReal_nonneg
      have hgaussHalf :
          cdf (gaussianReal 0 1) x ≤ 1 / 2 := by
        exact (monotone_cdf (gaussianReal 0 1) hxneg.le).trans_eq
          (by
            rw [cdf_standardGaussian_eq_one_sub_tail,
              standardGaussianTail_zero]
            norm_num)
      linarith
    exact ⟨hlower, hupper⟩

/-- A convenient weakened form of the `11/20` universal estimate. -/
theorem kolmogorovDistance_finitePMF_standardGaussian_le_three_fifths
    (p : PMF Ω) (X : Ω → ℝ)
    (hmean : finitePMFExpectation p X = 0)
    (hsecond : finitePMFExpectation p (fun ω => X ω ^ 2) = 1) :
    kolmogorovDistance (p.toMeasure.map X) (gaussianReal 0 1) ≤
      (3 : ℝ) / 5 :=
  (kolmogorovDistance_finitePMF_standardGaussian_le_eleven_twentieths
    p X hmean hsecond).trans (by norm_num)

/--
The elementary large-Lyapunov branch: the desired linear estimate follows
as soon as the Lyapunov parameter is at least one.
-/
theorem kolmogorovDistance_finitePMF_le_threeFifths_mul_of_one_le
    (p : PMF Ω) (X : Ω → ℝ)
    (hmean : finitePMFExpectation p X = 0)
    (hsecond : finitePMFExpectation p (fun ω => X ω ^ 2) = 1)
    {L : ℝ} (hL : 1 ≤ L) :
    kolmogorovDistance (p.toMeasure.map X) (gaussianReal 0 1) ≤
      (3 / 5 : ℝ) * L := by
  exact
    (kolmogorovDistance_finitePMF_standardGaussian_le_three_fifths
      p X hmean hsecond).trans (by nlinarith)

/--
The sharper universal estimate closes the `(3/5)L` branch already at
`L ≥ 11/12`.
-/
theorem kolmogorovDistance_finitePMF_le_threeFifths_mul_of_eleven_twelfths_le
    (p : PMF Ω) (X : Ω → ℝ)
    (hmean : finitePMFExpectation p X = 0)
    (hsecond : finitePMFExpectation p (fun ω => X ω ^ 2) = 1)
    {L : ℝ} (hL : (11 : ℝ) / 12 ≤ L) :
    kolmogorovDistance (p.toMeasure.map X) (gaussianReal 0 1) ≤
      (3 / 5 : ℝ) * L := by
  exact
    (kolmogorovDistance_finitePMF_standardGaussian_le_eleven_twentieths
      p X hmean hsecond).trans (by nlinarith)

end UniversalThreeFifths

section TiltedRademacherLargeLyapunov

universe u

variable {ι : Type u} [Fintype ι]

/-- The standardized tilted Rademacher sum has exact mean zero. -/
theorem biasedSignProductExpectation_standardizedTiltedRademacher_eq_zero
    (u a : ι → ℝ) :
    biasedSignProductExpectation u
        (standardizedTiltedRademacherSum u a) = 0 := by
  let s : ℝ := tiltedRademacherStdDev u a
  let X : ι → (ι → Bool) → ℝ :=
    fun i bits =>
      (a i / s) *
        (biasedSignValue (bits i) - Real.tanh (u i))
  have hcoordinate (i : ι) :
      biasedSignProductExpectation u (X i) = 0 := by
    exact biasedSignProduct_centeredWeightedMean
      u (fun i => a i / s) i
  have hsum :
      biasedSignProductExpectation u
          (fun bits => ∑ i, X i bits) =
        ∑ i, biasedSignProductExpectation u (X i) := by
    classical
    unfold biasedSignProductExpectation
    simp only [tsum_fintype]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  have hrepr :
      standardizedTiltedRademacherSum u a =
        fun bits => ∑ i, X i bits := by
    rfl
  rw [hrepr]
  rw [hsum]
  simp only [hcoordinate, Finset.sum_const_zero]

/-- Exact variance of one centered weighted coordinate under the product law. -/
theorem variance_centeredWeightedBiasedSign
    (u a : ι → ℝ) (i : ι) :
    variance
        (fun bits : ι → Bool =>
          a i * (biasedSignValue (bits i) - Real.tanh (u i)))
        (biasedSignProductPMF u).toMeasure =
      a i ^ 2 * (1 - Real.tanh (u i) ^ 2) := by
  let X : (ι → Bool) → ℝ :=
    fun bits =>
      a i * (biasedSignValue (bits i) - Real.tanh (u i))
  have hmean :
      ∫ bits, X bits ∂(biasedSignProductPMF u).toMeasure = 0 := by
    rw [← biasedSignProductExpectation_eq_integral]
    exact biasedSignProduct_centeredWeightedMean u a i
  rw [variance_eq_integral (measurable_of_finite X).aemeasurable]
  rw [hmean]
  simp only [sub_zero]
  rw [← biasedSignProductExpectation_eq_integral]
  exact biasedSignProduct_centeredWeightedVariance u a i

/--
The centered tilted sum divided by its standard deviation has variance one.
-/
theorem variance_standardizedTiltedRademacherSum_eq_one
    (u a : ι → ℝ) (ha : ∃ i, a i ≠ 0) :
    variance (standardizedTiltedRademacherSum u a)
        (biasedSignProductPMF u).toMeasure = 1 := by
  let s : ℝ := tiltedRademacherStdDev u a
  let c : ι → ℝ := fun i => a i / s
  let X : ι → (ι → Bool) → ℝ :=
    fun i bits =>
      c i * (biasedSignValue (bits i) - Real.tanh (u i))
  have hmem (i : ι) :
      MemLp (X i) 2 (biasedSignProductPMF u).toMeasure :=
    MemLp.of_discrete
  have hindep : iIndepFun X (biasedSignProductPMF u).toMeasure := by
    exact biasedSignProduct_centeredWeighted_iIndep u c
  have hvar :
      variance (∑ i, X i)
          (biasedSignProductPMF u).toMeasure =
        ∑ i, variance (X i) (biasedSignProductPMF u).toMeasure := by
    exact IndepFun.variance_sum
      (s := Finset.univ)
      (fun i _ => hmem i)
      (fun i _ j _ hij => hindep.indepFun hij)
  have hsum :
      ∑ i, variance (X i) (biasedSignProductPMF u).toMeasure = 1 := by
    rw [show (∑ i, variance (X i)
        (biasedSignProductPMF u).toMeasure) =
        ∑ i, c i ^ 2 * (1 - Real.tanh (u i) ^ 2) by
      apply Finset.sum_congr rfl
      intro i _
      exact variance_centeredWeightedBiasedSign u c i]
    exact standardizedTiltedRademacherVariance_eq_one u a ha
  have hrepr :
      standardizedTiltedRademacherSum u a =
        ∑ i, X i := by
    funext bits
    simp only [standardizedTiltedRademacherSum, X, c, s,
      Finset.sum_apply]
  rw [hrepr, hvar, hsum]

/-- Exact unit second moment of the standardized tilted Rademacher sum. -/
theorem standardizedTiltedRademacher_finitePMFSecondMoment_eq_one
    (u a : ι → ℝ) (ha : ∃ i, a i ≠ 0) :
    letI : Fintype (ι → Bool) := Fintype.ofFinite (ι → Bool)
    finitePMFExpectation (biasedSignProductPMF u)
        (fun bits => standardizedTiltedRademacherSum u a bits ^ 2) = 1 := by
  let : Fintype (ι → Bool) := Fintype.ofFinite (ι → Bool)
  let S := standardizedTiltedRademacherSum u a
  have hmean :
      ∫ bits, S bits ∂(biasedSignProductPMF u).toMeasure = 0 := by
    rw [← biasedSignProductExpectation_eq_integral]
    exact biasedSignProductExpectation_standardizedTiltedRademacher_eq_zero
      u a
  have hvar :
      variance S (biasedSignProductPMF u).toMeasure = 1 :=
    variance_standardizedTiltedRademacherSum_eq_one u a ha
  rw [finitePMFExpectation_eq_integral]
  change (∫ bits, S bits ^ 2 ∂(biasedSignProductPMF u).toMeasure) = 1
  rw [← hvar]
  rw [variance_eq_integral (measurable_of_finite S).aemeasurable]
  rw [hmean]
  simp only [sub_zero]

/--
The distribution-free `3/5` bound instantiated for a standardized tilted
Rademacher sum.
-/
theorem kolmogorovDistance_standardizedTiltedRademacher_le_eleven_twentieths
    (u a : ι → ℝ) (ha : ∃ i, a i ≠ 0) :
    kolmogorovDistance
        (standardizedTiltedRademacherPMF u a).toMeasure
        (gaussianReal 0 1) ≤ (11 : ℝ) / 20 := by
  let : Fintype (ι → Bool) := Fintype.ofFinite (ι → Bool)
  have hmean :
      finitePMFExpectation (biasedSignProductPMF u)
          (standardizedTiltedRademacherSum u a) = 0 := by
    have h :=
      biasedSignProductExpectation_standardizedTiltedRademacher_eq_zero u a
    unfold finitePMFExpectation
    unfold biasedSignProductExpectation at h
    rw [tsum_fintype] at h
    exact h
  have hsecond :
      finitePMFExpectation (biasedSignProductPMF u)
          (fun bits => standardizedTiltedRademacherSum u a bits ^ 2) = 1 :=
    standardizedTiltedRademacher_finitePMFSecondMoment_eq_one u a ha
  rw [standardizedTiltedRademacherPMF_toMeasure]
  exact
    kolmogorovDistance_finitePMF_standardGaussian_le_eleven_twentieths
    (biasedSignProductPMF u) (standardizedTiltedRademacherSum u a)
    hmean hsecond

/-- A convenient weakened form of the tilted-law universal estimate. -/
theorem kolmogorovDistance_standardizedTiltedRademacher_le_three_fifths
    (u a : ι → ℝ) (ha : ∃ i, a i ≠ 0) :
    kolmogorovDistance
        (standardizedTiltedRademacherPMF u a).toMeasure
        (gaussianReal 0 1) ≤ (3 : ℝ) / 5 :=
  (kolmogorovDistance_standardizedTiltedRademacher_le_eleven_twentieths
    u a ha).trans (by norm_num)

/--
For the Esscher-standardized Rademacher law, `L ≥ 11/12` closes the desired
`(3/5)L` branch without Berry--Esseen.
-/
theorem rademacherTiltedStandardizedLaw_le_threeFifths_mul_of_elevenTwelfths_le
    (b : ι → ℝ) (x : ℝ) (hnorm : ∑ i, b i ^ 2 = 1)
    (hL : (11 : ℝ) / 12 ≤ rademacherLyapunovRatio b x) :
    kolmogorovDistance
        (rademacherTiltedStandardizedLaw b x)
        (gaussianReal 0 1) ≤
      (3 / 5 : ℝ) * rademacherLyapunovRatio b x := by
  have ha : ∃ i, b i ≠ 0 := by
    by_contra h
    push Not at h
    have hb : b = 0 := by
      funext i
      exact h i
    subst b
    simp at hnorm
  have hbase :=
    kolmogorovDistance_standardizedTiltedRademacher_le_eleven_twentieths
      (fun i => x * b i) b ha
  rw [standardizedTiltedRademacherPMF_toMeasure_specialize] at hbase
  exact hbase.trans (by nlinarith)

/--
For the Esscher-standardized Rademacher law, `L ≥ 1` closes the desired
`(3/5)L` branch without Berry--Esseen.
-/
theorem rademacherTiltedStandardizedLaw_le_threeFifths_mul_of_one_le
    (b : ι → ℝ) (x : ℝ) (hnorm : ∑ i, b i ^ 2 = 1)
    (hL : 1 ≤ rademacherLyapunovRatio b x) :
    kolmogorovDistance
        (rademacherTiltedStandardizedLaw b x)
        (gaussianReal 0 1) ≤
      (3 / 5 : ℝ) * rademacherLyapunovRatio b x := by
  exact
    rademacherTiltedStandardizedLaw_le_threeFifths_mul_of_elevenTwelfths_le
      b x hnorm (by nlinarith)

end TiltedRademacherLargeLyapunov

end Probability
end CertifiedJL
