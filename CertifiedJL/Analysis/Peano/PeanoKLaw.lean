/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author.
-/

import CertifiedJL.Analysis.Peano.PeanoGaussianRademacherDCT
import CertifiedJL.Analysis.SmoothBounds.JensenSquare
import CertifiedJL.Analysis.Gaussian.GaussianEvenMomentDomination
import CertifiedJL.Analysis.Peano.PositiveStopLossGaussianization
import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpGaussianHalfMoment
import CertifiedJL.Probability.Distributions.Gaussian.StandardGaussian
import Mathlib.Analysis.Convex.Piecewise
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The positive fourth-order Peano density

This module owns the real density that appears in the fourth-order
Gaussian--Rademacher replacement law.  The density is oriented exactly as in
the paper: twice the Gaussian cubic stop-loss minus the Rademacher cubic
stop-loss.  The probability measure itself is deliberately not defined until
global nonnegativity and total mass one have been proved.
-/

open Filter MeasureTheory Set
open ProbabilityTheory
open scoped Interval Topology

namespace CertifiedJL

/-! ### Rational Mills certificate for U6b -/

private noncomputable def peanoMillsNumerator (t : ℝ) : ℝ :=
  t ^ 4 + 9 * t ^ 2 - 2

private noncomputable def peanoMillsDenominator (t : ℝ) : ℝ :=
  t ^ 5 + 10 * t ^ 3 + 5 * t

private noncomputable def peanoMillsRatio (t : ℝ) : ℝ :=
  peanoMillsNumerator t / peanoMillsDenominator t

private theorem peanoMillsDenominator_pos {t : ℝ} (ht : 0 < t) :
    0 < peanoMillsDenominator t := by
  unfold peanoMillsDenominator
  nlinarith [sq_nonneg (t ^ 2), sq_nonneg t]

private theorem tendsto_peanoMillsRatio_atTop :
    Tendsto peanoMillsRatio atTop (𝓝 0) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hnum : Tendsto
      (fun x : ℝ => x⁻¹ + 9 * x⁻¹ ^ 3 - 2 * x⁻¹ ^ 5) atTop (𝓝 0) := by
    simpa using hinv.add ((hinv.pow 3).const_mul 9) |>.sub ((hinv.pow 5).const_mul 2)
  have hden : Tendsto
      (fun x : ℝ => 1 + 10 * x⁻¹ ^ 2 + 5 * x⁻¹ ^ 4) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add ((hinv.pow 2).const_mul 10)).add
      ((hinv.pow 4).const_mul 5)
  have hquot := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have hquot' : Tendsto
      ((fun x : ℝ => x⁻¹ + 9 * x⁻¹ ^ 3 - 2 * x⁻¹ ^ 5) /
        fun x : ℝ => 1 + 10 * x⁻¹ ^ 2 + 5 * x⁻¹ ^ 4) atTop (𝓝 0) := by
    simpa only [zero_div] using hquot
  apply hquot'.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
  dsimp only [Pi.div_apply]
  unfold peanoMillsRatio peanoMillsNumerator peanoMillsDenominator
  field_simp [hx]

private theorem tendsto_standardGaussianDensity_mul_peanoMillsRatio :
    Tendsto (fun t => Probability.standardGaussianDensity t * peanoMillsRatio t)
      atTop (𝓝 0) := by
  have hquad : Tendsto (fun t : ℝ => (1 / 2 : ℝ) * t ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop (by norm_num)
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t ^ 2))
      atTop (𝓝 0) := by
    apply (Real.tendsto_exp_neg_atTop_nhds_zero.comp hquad).congr'
    filter_upwards [] with t
    simp only [Function.comp_apply]
    congr 1
    ring
  have hdensity : Tendsto Probability.standardGaussianDensity atTop (𝓝 0) := by
    have hscaled : Tendsto
        (fun t : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-(1 / 2 : ℝ) * t ^ 2)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hexp.const_mul (Real.sqrt (2 * Real.pi))⁻¹
    apply hscaled.congr'
    filter_upwards [] with t
    unfold Probability.standardGaussianDensity
    congr 2
    ring
  simpa only [zero_mul] using hdensity.mul tendsto_peanoMillsRatio_atTop

private theorem hasDerivAt_standardGaussianTail (t : ℝ) :
    HasDerivAt Probability.standardGaussianTail
      (-Probability.standardGaussianDensity t) t := by
  have hfun : Probability.standardGaussianTail =
      (fun _ => Probability.standardGaussianTail t) -
        fun u => ∫ x in t..u, Probability.standardGaussianDensity x := by
    funext u
    unfold Probability.standardGaussianTail
    have h := intervalIntegral.integral_Ioi_sub_Ioi'
      Probability.integrable_standardGaussianDensity.integrableOn
      Probability.integrable_standardGaussianDensity.integrableOn
      (a := t) (b := u)
    dsimp only [Pi.sub_apply]
    linarith
  rw [hfun]
  have hcont : Continuous Probability.standardGaussianDensity := by
    unfold Probability.standardGaussianDensity
    fun_prop
  simpa only [zero_sub] using
    (hasDerivAt_const t (Probability.standardGaussianTail t)).sub
    (intervalIntegral.integral_hasDerivAt_right
      Probability.integrable_standardGaussianDensity.intervalIntegrable
      hcont.stronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt)

private theorem hasDerivAt_standardGaussianDensity (t : ℝ) :
    HasDerivAt Probability.standardGaussianDensity
      (-t * Probability.standardGaussianDensity t) t := by
  have hinner : HasDerivAt (fun x : ℝ => -x ^ 2 / 2) (-t) t := by
    convert ((hasDerivAt_id t).pow 2).neg.div_const 2 using 1
    all_goals first | rfl | (simp only [id_eq]; ring)
  unfold Probability.standardGaussianDensity
  change HasDerivAt
    (fun z : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-z ^ 2 / 2))
    (-t * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2))) t
  have hraw := hinner.exp.const_mul (Real.sqrt (2 * Real.pi))⁻¹
  convert hraw using 1
  all_goals first | rfl | ring

private theorem hasDerivAt_peanoMillsRatio {t : ℝ}
    (ht : 0 < t) : HasDerivAt peanoMillsRatio
      (((4 * t ^ 3 + 18 * t) * peanoMillsDenominator t -
        peanoMillsNumerator t * (5 * t ^ 4 + 30 * t ^ 2 + 5)) /
          peanoMillsDenominator t ^ 2) t := by
  have hdenNe := (peanoMillsDenominator_pos ht).ne'
  have hnum : HasDerivAt (fun x : ℝ => x ^ 4 + 9 * x ^ 2 - 2)
      (4 * t ^ 3 + 18 * t) t := by
    have hraw := (((hasDerivAt_id t).pow 4).add
      (((hasDerivAt_id t).pow 2).const_mul 9)).sub_const 2
    convert hraw using 1
    all_goals first | rfl | (simp only [id_eq]; ring)
  have hden : HasDerivAt (fun x : ℝ => x ^ 5 + 10 * x ^ 3 + 5 * x)
      (5 * t ^ 4 + 30 * t ^ 2 + 5) t := by
    have hraw := (((hasDerivAt_id t).pow 5).add
      (((hasDerivAt_id t).pow 3).const_mul 10)).add
        ((hasDerivAt_id t).const_mul 5)
    convert hraw using 1
    all_goals first | rfl | (simp only [id_eq]; ring)
  unfold peanoMillsRatio peanoMillsNumerator peanoMillsDenominator
  exact hnum.div hden hdenNe

private noncomputable def peanoMillsGap (t : ℝ) : ℝ :=
  Probability.standardGaussianTail t -
    Probability.standardGaussianDensity t * peanoMillsRatio t

private noncomputable def peanoMillsGapDeriv (t : ℝ) : ℝ :=
  -Probability.standardGaussianDensity t *
    (10 * (t ^ 4 + 14 * t ^ 2 + 1) / peanoMillsDenominator t ^ 2)

private theorem hasDerivAt_peanoMillsGap {t : ℝ} (ht : 0 < t) :
    HasDerivAt peanoMillsGap (peanoMillsGapDeriv t) t := by
  have hden := (peanoMillsDenominator_pos ht).ne'
  unfold peanoMillsGap peanoMillsGapDeriv
  convert (hasDerivAt_standardGaussianTail t).sub
    ((hasDerivAt_standardGaussianDensity t).mul
      (hasDerivAt_peanoMillsRatio ht)) using 1
  all_goals try rfl
  unfold peanoMillsRatio peanoMillsNumerator peanoMillsDenominator
  field_simp [hden]
  ring

private theorem peanoMillsGapDeriv_nonpos {t : ℝ} :
    peanoMillsGapDeriv t ≤ 0 := by
  unfold peanoMillsGapDeriv
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (Probability.standardGaussianDensity_nonneg t))
    (div_nonneg (mul_nonneg (by norm_num)
      (by nlinarith [sq_nonneg (t ^ 2), sq_nonneg t])) (sq_nonneg _))

private theorem tendsto_peanoMillsGap_atTop :
    Tendsto peanoMillsGap atTop (𝓝 0) := by
  unfold peanoMillsGap
  have htail : Tendsto Probability.standardGaussianTail atTop (𝓝 0) := by
    unfold Probability.standardGaussianTail
    simpa using tendsto_integral_Ioi_zero (f := Probability.standardGaussianDensity)
      (b := fun t : ℝ => t) tendsto_id
  simpa only [sub_zero] using
    htail.sub tendsto_standardGaussianDensity_mul_peanoMillsRatio

/-- The rational Mills lower bound used in the second Peano kernel proof. -/
theorem standardGaussian_rational_mills_lower {t : ℝ} (ht : 0 < t) :
    Probability.standardGaussianDensity t * (t ^ 4 + 9 * t ^ 2 - 2) ≤
      Probability.standardGaussianTail t * (t ^ 5 + 10 * t ^ 3 + 5 * t) := by
  have hderiv : ∀ x ∈ Ici t,
      HasDerivAt peanoMillsGap (peanoMillsGapDeriv x) x := by
    intro x hx
    exact hasDerivAt_peanoMillsGap (ht.trans_le hx)
  have hnonpos : ∀ x ∈ Ioi t, peanoMillsGapDeriv x ≤ 0 := by
    intro x hx
    exact peanoMillsGapDeriv_nonpos
  have hftc := integral_Ioi_of_hasDerivAt_of_nonpos' hderiv hnonpos
    tendsto_peanoMillsGap_atTop
  have hintNonpos : (∫ x in Ioi t, peanoMillsGapDeriv x) ≤ 0 :=
    integral_nonpos_of_ae (ae_restrict_mem measurableSet_Ioi |>.mono fun x hx =>
      hnonpos x hx)
  have hgap : 0 ≤ peanoMillsGap t := by linarith
  have hden := peanoMillsDenominator_pos ht
  unfold peanoMillsGap peanoMillsRatio at hgap
  change Probability.standardGaussianDensity t * peanoMillsNumerator t ≤
    Probability.standardGaussianTail t * peanoMillsDenominator t
  apply (div_le_iff₀ hden).mp
  calc
    Probability.standardGaussianDensity t * peanoMillsNumerator t /
        peanoMillsDenominator t =
      Probability.standardGaussianDensity t *
        (peanoMillsNumerator t / peanoMillsDenominator t) := by ring
    _ ≤ Probability.standardGaussianTail t := sub_nonneg.mp hgap

/-- The candidate density of the fourth-order Peano replacement law. -/
noncomputable def peanoKDensity (t : ℝ) : ℝ :=
  cubicStopLossKernel (gaussianReal 0 1) standardRademacherMeasure t

/-- The defining orientation of the Peano K density. -/
theorem peanoKDensity_eq_two_mul_cubicStopLossDifference (t : ℝ) :
    peanoKDensity t = 2 *
      cubicStopLossDifference (gaussianReal 0 1)
        standardRademacherMeasure t := by
  rfl

/-- The Peano K density is strongly measurable. -/
theorem stronglyMeasurable_peanoKDensity :
    StronglyMeasurable peanoKDensity := by
  change StronglyMeasurable (fun t : ℝ => 2 *
    cubicStopLossDifference (gaussianReal 0 1)
      standardRademacherMeasure t)
  exact
    stronglyMeasurable_standardGaussianRademacher_cubicStopLossDifference.const_mul 2

/-- Every polynomial weight is integrable against the absolute value of the
candidate K density. -/
theorem integrable_absPow_mul_abs_peanoKDensity (m : ℕ) :
    Integrable (fun t : ℝ => |t| ^ m * |peanoKDensity t|) volume := by
  have hmajor :=
    (integrable_absPow_mul_standardGaussianRademacherCubicEnvelope m).const_mul 2
  refine Integrable.mono' hmajor ?_ ?_
  · exact ((continuous_abs.pow m).stronglyMeasurable.mul
      stronglyMeasurable_peanoKDensity.norm).aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (abs_nonneg t) m)
    (abs_nonneg (peanoKDensity t)))]
  rw [peanoKDensity_eq_two_mul_cubicStopLossDifference, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hΔ :=
    abs_cubicStopLossDifference_standardGaussian_rademacher_le_envelope t
  have ht : 0 ≤ |t| ^ m := pow_nonneg (abs_nonneg t) m
  calc
    |t| ^ m * (2 *
        |cubicStopLossDifference (gaussianReal 0 1)
          standardRademacherMeasure t|) ≤
        |t| ^ m * (2 * standardGaussianRademacherCubicEnvelope t) := by
      gcongr
    _ = 2 * (|t| ^ m * standardGaussianRademacherCubicEnvelope t) := by ring

/-- In particular, the candidate K density is Lebesgue integrable. -/
theorem integrable_peanoKDensity : Integrable peanoKDensity volume := by
  have h := integrable_absPow_mul_abs_peanoKDensity 0
  apply (integrable_norm_iff
    stronglyMeasurable_peanoKDensity.aestronglyMeasurable).mp
  simpa only [pow_zero, one_mul, Real.norm_eq_abs] using h

/-! ### Convexity of the squared positive-part cubic -/

/-- The scalar profile used to compare a symmetric law with a Rademacher
variable by applying Jensen's inequality to its square. -/
noncomputable def peanoCubicSquareProfile (t v : ℝ) : ℝ :=
  (max (Real.sqrt v - t) 0) ^ 3

private noncomputable def peanoCubicSquareProfileDeriv (t v : ℝ) : ℝ :=
  3 * (Real.sqrt v - t) ^ 2 / (2 * Real.sqrt v)

private noncomputable def peanoCubicSquareProfileDeriv2 (t v : ℝ) : ℝ :=
  3 * (v - t ^ 2) / (4 * v * Real.sqrt v)

private theorem hasDerivAt_peanoCubicSquareProfile_right
    {t v : ℝ} (hv : t ^ 2 < v) :
    HasDerivAt (fun z : ℝ => (Real.sqrt z - t) ^ 3)
      (peanoCubicSquareProfileDeriv t v) v := by
  have hv0 : v ≠ 0 := ne_of_gt (lt_of_le_of_lt (sq_nonneg t) hv)
  convert (((Real.hasDerivAt_sqrt hv0).sub_const t).pow 3) using 1 <;> try rfl
  norm_num [peanoCubicSquareProfileDeriv]
  field_simp [Real.sqrt_ne_zero'.mpr (lt_of_le_of_lt (sq_nonneg t) hv)]

private theorem hasDerivAt_peanoCubicSquareProfileDeriv_right
    {t v : ℝ} (hv : t ^ 2 < v) :
    HasDerivAt (peanoCubicSquareProfileDeriv t)
      (peanoCubicSquareProfileDeriv2 t v) v := by
  have hvpos : 0 < v := lt_of_le_of_lt (sq_nonneg t) hv
  have hv0 : v ≠ 0 := ne_of_gt hvpos
  have hsqrt0 : Real.sqrt v ≠ 0 := Real.sqrt_ne_zero'.mpr hvpos
  have hraw := (((Real.hasDerivAt_sqrt hv0).sub_const t).pow 2).const_mul 3 |>.div
    ((Real.hasDerivAt_sqrt hv0).const_mul 2) (by positivity)
  convert hraw using 1 <;> try rfl
  norm_num [peanoCubicSquareProfileDeriv, peanoCubicSquareProfileDeriv2]
  field_simp [hsqrt0, hv0]
  nlinarith [Real.sq_sqrt hvpos.le]

private theorem convexOn_peanoCubicSquareProfile_right (t : ℝ) :
    ConvexOn ℝ (Ici (t ^ 2)) (fun v : ℝ => (Real.sqrt v - t) ^ 3) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici (t ^ 2))
  · exact ((Real.continuous_sqrt.sub continuous_const).pow 3).continuousOn
  · intro v hv
    exact (hasDerivAt_peanoCubicSquareProfile_right
      (by simpa only [interior_Ici, mem_Ioi] using hv)).hasDerivWithinAt
  · intro v hv
    exact (hasDerivAt_peanoCubicSquareProfileDeriv_right
      (by simpa only [interior_Ici, mem_Ioi] using hv)).hasDerivWithinAt
  · intro v hv
    have hv' : t ^ 2 < v := by simpa only [interior_Ici, mem_Ioi] using hv
    unfold peanoCubicSquareProfileDeriv2
    exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hv'.le))
      (mul_nonneg (mul_nonneg (by norm_num) (lt_of_le_of_lt (sq_nonneg t) hv').le)
        (Real.sqrt_nonneg v))

private theorem monotoneOn_peanoCubicSquareProfile_right
    {t : ℝ} (ht : 0 < t) :
    MonotoneOn (fun v : ℝ => (Real.sqrt v - t) ^ 3) (Ici (t ^ 2)) := by
  intro a ha b hb hab
  have hsqrt := Real.sqrt_le_sqrt hab
  have hta : t ≤ Real.sqrt a := by
    calc
      t = Real.sqrt (t ^ 2) := by rw [Real.sqrt_sq_eq_abs, abs_of_pos ht]
      _ ≤ Real.sqrt a := Real.sqrt_le_sqrt ha
  have htb : t ≤ Real.sqrt b := hta.trans hsqrt
  exact pow_le_pow_left₀ (sub_nonneg.mpr hta) (sub_le_sub_right hsqrt t) 3

/-- For every nonnegative threshold, the positive-part cubic after a square
root is convex on the nonnegative axis. -/
theorem convexOn_peanoCubicSquareProfile {t : ℝ} (ht : 0 ≤ t) :
    ConvexOn ℝ (Ici 0) (peanoCubicSquareProfile t) := by
  rcases ht.eq_or_lt with rfl | ht
  · apply (convexOn_rpow (p := (3 / 2 : ℝ)) (by norm_num)).congr
    intro v hv
    rw [peanoCubicSquareProfile, sub_zero, max_eq_left (Real.sqrt_nonneg v),
      ← Real.rpow_natCast]
    rw [show (3 : ℝ) = 2 * (3 / 2 : ℝ) by norm_num, Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul hv]
    norm_num
  · let g : ℝ → ℝ := fun v => (Real.sqrt v - t) ^ 3
    have hpiece : peanoCubicSquareProfile t =
        (Iic (t ^ 2)).piecewise 0 g := by
      funext v
      by_cases hv : v ≤ t ^ 2
      · rw [Set.piecewise_eq_of_mem (s := Iic (t ^ 2))
          (f := 0) (g := g) hv]
        have hsqrt : Real.sqrt v ≤ t := by
          calc
            Real.sqrt v ≤ Real.sqrt (t ^ 2) := Real.sqrt_le_sqrt hv
            _ = t := by rw [Real.sqrt_sq_eq_abs, abs_of_pos ht]
        simp [peanoCubicSquareProfile, hsqrt]
      · rw [Set.piecewise_eq_of_notMem (s := Iic (t ^ 2))
          (f := 0) (g := g) hv]
        have hsqrt : t ≤ Real.sqrt v := by
          calc
            t = Real.sqrt (t ^ 2) := by rw [Real.sqrt_sq_eq_abs, abs_of_pos ht]
            _ ≤ Real.sqrt v := Real.sqrt_le_sqrt (le_of_not_ge hv)
        simp [peanoCubicSquareProfile, g, max_eq_left (sub_nonneg.mpr hsqrt)]
    rw [hpiece]
    exact (convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici
      (convexOn_const 0 (convex_Iic (t ^ 2)))
      (convexOn_peanoCubicSquareProfile_right t)
      antitoneOn_const (monotoneOn_peanoCubicSquareProfile_right ht)
      (by simp [Real.sqrt_sq_eq_abs, abs_of_pos ht])).subset
        (subset_univ _) (convex_Ici 0)

private theorem peanoCubicSquareProfile_sq_eq_add (t y : ℝ) (ht : 0 ≤ t) :
    peanoCubicSquareProfile t (y ^ 2) =
      (max (y - t) 0) ^ 3 + (max (-y - t) 0) ^ 3 := by
  rw [peanoCubicSquareProfile, Real.sqrt_sq_eq_abs]
  by_cases hy : 0 ≤ y
  · rw [abs_of_nonneg hy, max_eq_right (by linarith : -y - t ≤ 0)]
    ring
  · have hy' : y ≤ 0 := le_of_not_ge hy
    rw [abs_of_nonpos hy', max_eq_right (by linarith : y - t ≤ 0)]
    ring

private theorem cubicStopLossDifference_standardGaussian_rademacher_nonneg_of_nonneg
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ cubicStopLossDifference (gaussianReal 0 1)
      standardRademacherMeasure t := by
  let f : ℝ → ℝ := fun y => (max (y - t) 0) ^ 3
  have hf : Integrable f (gaussianReal 0 1) :=
    integrable_standardGaussian_cubicStopLoss t
  have hmap : Measure.map (fun y : ℝ => -y) (gaussianReal 0 1) =
      gaussianReal 0 1 := by
    simpa using (gaussianReal_map_neg (μ := 0) (v := 1))
  have hfmap : AEStronglyMeasurable f
      (Measure.map (fun y : ℝ => -y) (gaussianReal 0 1)) := by
    rw [hmap]
    exact hf.aestronglyMeasurable
  have hfneg : Integrable (fun y : ℝ => f (-y)) (gaussianReal 0 1) := by
    exact (integrable_map_measure hfmap (by fun_prop)).mp (by simpa [hmap] using hf)
  have hreflect : (∫ y, f (-y) ∂(gaussianReal 0 1)) =
      ∫ y, f y ∂(gaussianReal 0 1) := by
    calc
      (∫ y, f (-y) ∂(gaussianReal 0 1)) =
          ∫ y, f y ∂(Measure.map (fun y : ℝ => -y) (gaussianReal 0 1)) := by
        exact (integral_map (μ := gaussianReal 0 1) (φ := fun y : ℝ => -y)
          (by fun_prop) hfmap).symm
      _ = ∫ y, f y ∂(gaussianReal 0 1) := by rw [hmap]
  have hprofileInt : Integrable
      (fun y : ℝ => peanoCubicSquareProfile t (y ^ 2)) (gaussianReal 0 1) := by
    refine (hf.add hfneg).congr (ae_of_all _ fun y => ?_)
    change f y + f (-y) = peanoCubicSquareProfile t (y ^ 2)
    simpa only [f, neg_neg] using (peanoCubicSquareProfile_sq_eq_add t y ht).symm
  have hsecond : (∫ y : ℝ, y ^ 2 ∂(gaussianReal 0 1)) = 1 := by
    rw [standardGaussianRademacher_equalMoments.equal 2 (by norm_num),
      standardRademacherMeasure_second_moment]
  have hprofileInt' : Integrable
      (fun y : ℝ => (max (1 * Real.sqrt (y ^ 2) - t) 0) ^ 3)
      (gaussianReal 0 1) := by
    refine hprofileInt.congr (ae_of_all _ fun y => ?_)
    simp [peanoCubicSquareProfile]
  have hjensen := convexSquareExpectation_le
    (μ := gaussianReal 0 1) (fun u : ℝ => (max (u - t) 0) ^ 3) 1
    (by
      apply (convexOn_peanoCubicSquareProfile ht).congr
      intro v hv
      simp [peanoCubicSquareProfile])
    (by fun_prop) hsecond (integrable_standardGaussian_pow 2) hprofileInt'
  have hprofileIntegral :
      (∫ y : ℝ, peanoCubicSquareProfile t (y ^ 2) ∂(gaussianReal 0 1)) =
        2 * ∫ y, f y ∂(gaussianReal 0 1) := by
    calc
      _ = ∫ y, f y + f (-y) ∂(gaussianReal 0 1) := by
        apply integral_congr_ae
        exact ae_of_all _ fun y => by
          simpa only [f, neg_neg] using peanoCubicSquareProfile_sq_eq_add t y ht
      _ = (∫ y, f y ∂(gaussianReal 0 1)) +
          ∫ y, f (-y) ∂(gaussianReal 0 1) := integral_add hf hfneg
      _ = 2 * ∫ y, f y ∂(gaussianReal 0 1) := by rw [hreflect]; ring
  have hR : (∫ y, (max (y - t) 0) ^ 3 ∂standardRademacherMeasure) =
      (max (1 - t) 0) ^ 3 / 2 := by
    rw [integral_standardRademacher_cubicStopLoss,
      max_eq_right (by linarith : (-1 : ℝ) - t ≤ 0)]
    ring
  have hjensen' : (max (1 - t) 0) ^ 3 ≤
      ∫ y : ℝ, peanoCubicSquareProfile t (y ^ 2) ∂(gaussianReal 0 1) := by
    simpa [peanoCubicSquareProfile] using hjensen
  rw [hprofileIntegral] at hjensen'
  unfold cubicStopLossDifference
  rw [hR]
  dsimp only [f] at hjensen'
  linarith

private theorem peanoK_taylorPolynomial3_cube (t y : ℝ) :
    taylorPolynomial3 (fun z : ℝ => z ^ 3) (-t) y = (y - t) ^ 3 := by
  have hderiv1 : deriv (fun z : ℝ => z ^ 3) =
      (fun z : ℝ => 3 * z ^ 2) := by
    funext z
    convert ((hasDerivAt_id z).pow 3).deriv using 1 <;> simp [id_eq]
  have hderiv2 : deriv (fun z : ℝ => 3 * z ^ 2) =
      (fun z : ℝ => 6 * z) := by
    funext z
    convert ((hasDerivAt_const z 3).mul ((hasDerivAt_id z).pow 2)).deriv
      using 1 <;> (simp [id_eq] <;> ring)
  have hderiv3 : deriv (fun z : ℝ => 6 * z) =
      (fun _ : ℝ => 6) := by
    funext z
    convert ((hasDerivAt_const z 6).mul (hasDerivAt_id z)).deriv
      using 1 <;> simp [id_eq]
  have h1val : deriv (fun z : ℝ => z ^ 3) (-t) =
      3 * (-t) ^ 2 := congrFun hderiv1 (-t)
  have h2val : deriv (deriv (fun z : ℝ => z ^ 3)) (-t) =
      6 * (-t) := by
    rw [hderiv1]
    exact congrFun hderiv2 (-t)
  have h3val : deriv (deriv (deriv (fun z : ℝ => z ^ 3))) (-t) = 6 := by
    rw [hderiv1, hderiv2]
    exact congrFun hderiv3 (-t)
  simp only [taylorPolynomial3]
  rw [h1val, h2val, h3val]
  ring

private theorem integral_shifted_cube_standardGaussian_rademacher_eq_K (t : ℝ) :
    (∫ y, (y - t) ^ 3 ∂(gaussianReal 0 1)) =
      ∫ y, (y - t) ^ 3 ∂standardRademacherMeasure := by
  have h := equalMomentsThrough_taylorPolynomial3
    (hm := standardGaussianRademacher_equalMoments)
    (f := fun z : ℝ => z ^ 3) (-t)
  simpa only [peanoK_taylorPolynomial3_cube] using h

private theorem integrable_shifted_cube_standardGaussian_rademacher_K (t : ℝ) :
    Integrable (fun y => (y - t) ^ 3) (gaussianReal 0 1) ∧
      Integrable (fun y => (y - t) ^ 3) standardRademacherMeasure := by
  constructor
  · have h := integrable_taylorPolynomial3_left
      (hm := standardGaussianRademacher_equalMoments)
      (f := fun z : ℝ => z ^ 3) (-t)
    simpa only [peanoK_taylorPolynomial3_cube] using h
  · have h := integrable_taylorPolynomial3_right
      (hm := standardGaussianRademacher_equalMoments)
      (f := fun z : ℝ => z ^ 3) (-t)
    simpa only [peanoK_taylorPolynomial3_cube] using h

private theorem peanoK_cubic_stoploss_decompose (y t : ℝ) :
    (max (y - t) 0) ^ 3 =
      (y - t) ^ 3 + (max (t - y) 0) ^ 3 := by
  by_cases h : t ≤ y
  · rw [max_eq_left (sub_nonneg.mpr h),
      max_eq_right (sub_nonpos.mpr h)]
    ring
  · have h' : y ≤ t := le_of_lt (lt_of_not_ge h)
    rw [max_eq_right (sub_nonpos.mpr h'),
      max_eq_left (sub_nonneg.mpr h')]
    ring

private theorem standardRademacherMeasure_map_neg :
    Measure.map (fun y : ℝ => -y) standardRademacherMeasure =
      standardRademacherMeasure := by
  unfold standardRademacherMeasure
  rw [Measure.map_add]
  · simp only [Measure.map_smul, Measure.map_dirac, neg_neg]
    rw [add_comm]
  · fun_prop

private theorem integral_cubic_stoploss_neg_eq_lower
    (μ : Measure ℝ) (hmap : Measure.map (fun y : ℝ => -y) μ = μ)
    (t : ℝ) (hint : Integrable (fun y : ℝ => (max (y + t) 0) ^ 3) μ) :
    (∫ y, (max (y + t) 0) ^ 3 ∂μ) =
      ∫ y, (max (t - y) 0) ^ 3 ∂μ := by
  let f : ℝ → ℝ := fun y => (max (y + t) 0) ^ 3
  have hfmap : Integrable f (Measure.map (fun y : ℝ => -y) μ) := by
    rw [hmap]
    exact hint
  calc
    (∫ y, (max (y + t) 0) ^ 3 ∂μ) =
        ∫ y, f y ∂(Measure.map (fun y : ℝ => -y) μ) := by
      rw [hmap]
    _ = ∫ y, f (-y) ∂μ :=
      integral_map (μ := μ) (φ := fun y : ℝ => -y)
        (by fun_prop) hfmap.aestronglyMeasurable
    _ = ∫ y, (max (t - y) 0) ^ 3 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [f]
      congr 2
      ring

/-- The candidate K density is an even function. -/
theorem peanoKDensity_neg (t : ℝ) : peanoKDensity (-t) = peanoKDensity t := by
  have hGupper := integrable_standardGaussian_cubicStopLoss t
  have hRupper := integrable_standardRademacher_cubicStopLoss t
  have hpoly := integrable_shifted_cube_standardGaussian_rademacher_K t
  have hGlower : Integrable (fun y : ℝ => (max (t - y) 0) ^ 3)
      (gaussianReal 0 1) := by
    refine (hGupper.sub hpoly.1).congr
      (Filter.Eventually.of_forall fun y => ?_)
    change (max (y - t) 0) ^ 3 - (y - t) ^ 3 =
      (max (t - y) 0) ^ 3
    rw [peanoK_cubic_stoploss_decompose]
    ring
  have hRlower : Integrable (fun y : ℝ => (max (t - y) 0) ^ 3)
      standardRademacherMeasure := by
    refine (hRupper.sub hpoly.2).congr
      (Filter.Eventually.of_forall fun y => ?_)
    change (max (y - t) 0) ^ 3 - (y - t) ^ 3 =
      (max (t - y) 0) ^ 3
    rw [peanoK_cubic_stoploss_decompose]
    ring
  have hGdecomp :
      (∫ y, (max (y - t) 0) ^ 3 ∂(gaussianReal 0 1)) =
        (∫ y, (y - t) ^ 3 ∂(gaussianReal 0 1)) +
          ∫ y, (max (t - y) 0) ^ 3 ∂(gaussianReal 0 1) := by
    calc
      _ = ∫ y, (y - t) ^ 3 + (max (t - y) 0) ^ 3
          ∂(gaussianReal 0 1) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => peanoK_cubic_stoploss_decompose y t
      _ = _ := integral_add hpoly.1 hGlower
  have hRdecomp :
      (∫ y, (max (y - t) 0) ^ 3 ∂standardRademacherMeasure) =
        (∫ y, (y - t) ^ 3 ∂standardRademacherMeasure) +
          ∫ y, (max (t - y) 0) ^ 3 ∂standardRademacherMeasure := by
    calc
      _ = ∫ y, (y - t) ^ 3 + (max (t - y) 0) ^ 3
          ∂standardRademacherMeasure := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => peanoK_cubic_stoploss_decompose y t
      _ = _ := integral_add hpoly.2 hRlower
  have hGreflect :
      (∫ y, (max (y + t) 0) ^ 3 ∂(gaussianReal 0 1)) =
        ∫ y, (max (t - y) 0) ^ 3 ∂(gaussianReal 0 1) := by
    apply integral_cubic_stoploss_neg_eq_lower
      (μ := gaussianReal 0 1) (t := t)
    · simpa using (gaussianReal_map_neg (μ := 0) (v := 1))
    · simpa only [sub_neg_eq_add] using
        integrable_standardGaussian_cubicStopLoss (-t)
  have hRreflect :
      (∫ y, (max (y + t) 0) ^ 3 ∂standardRademacherMeasure) =
        ∫ y, (max (t - y) 0) ^ 3 ∂standardRademacherMeasure := by
    apply integral_cubic_stoploss_neg_eq_lower
      (μ := standardRademacherMeasure) (t := t)
    · exact standardRademacherMeasure_map_neg
    · simpa only [sub_neg_eq_add] using
        integrable_standardRademacher_cubicStopLoss (-t)
  rw [peanoKDensity_eq_two_mul_cubicStopLossDifference,
    peanoKDensity_eq_two_mul_cubicStopLossDifference]
  unfold cubicStopLossDifference
  simp only [sub_neg_eq_add]
  rw [hGreflect, hRreflect, hGdecomp, hRdecomp,
    integral_shifted_cube_standardGaussian_rademacher_eq_K]
  ring

/-- The fourth-order Peano replacement density is globally nonnegative. -/
theorem peanoKDensity_nonneg (t : ℝ) : 0 ≤ peanoKDensity t := by
  by_cases ht : 0 ≤ t
  · rw [peanoKDensity_eq_two_mul_cubicStopLossDifference]
    exact mul_nonneg (by norm_num)
      (cubicStopLossDifference_standardGaussian_rademacher_nonneg_of_nonneg ht)
  · rw [← peanoKDensity_neg t]
    rw [peanoKDensity_eq_two_mul_cubicStopLossDifference]
    exact mul_nonneg (by norm_num)
      (cubicStopLossDifference_standardGaussian_rademacher_nonneg_of_nonneg
        (neg_nonneg.mpr (le_of_not_ge ht)))

/-- On the right tail, the K density is twice a strict Gaussian upper-tail
cubic integral. -/
theorem peanoKDensity_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    peanoKDensity t =
      2 * ∫ y in Ioi t, (y - t) ^ 3 ∂(gaussianReal 0 1) := by
  rw [peanoKDensity_eq_two_mul_cubicStopLossDifference,
    cubicStopLossDifference_standardGaussian_rademacher_of_one_le ht]

/-- On the left tail, the K density is twice a strict Gaussian lower-tail
cubic integral. -/
theorem peanoKDensity_of_le_neg_one {t : ℝ} (ht : t ≤ -1) :
    peanoKDensity t =
      2 * ∫ y in Iio t, (t - y) ^ 3 ∂(gaussianReal 0 1) := by
  rw [peanoKDensity_eq_two_mul_cubicStopLossDifference,
    cubicStopLossDifference_standardGaussian_rademacher_of_le_neg_one ht]

/-- The candidate density is nonnegative on and beyond the right endpoint. -/
theorem peanoKDensity_nonneg_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ peanoKDensity t := by
  rw [peanoKDensity_of_one_le ht]
  exact mul_nonneg (by norm_num) <|
    integral_nonneg_of_ae (ae_restrict_mem measurableSet_Ioi |>.mono fun y hy => by
      exact pow_nonneg (sub_nonneg.mpr hy.le) 3)

/-- The candidate density is nonnegative on and beyond the left endpoint. -/
theorem peanoKDensity_nonneg_of_le_neg_one {t : ℝ} (ht : t ≤ -1) :
    0 ≤ peanoKDensity t := by
  rw [peanoKDensity_of_le_neg_one ht]
  exact mul_nonneg (by norm_num) <|
    integral_nonneg_of_ae (ae_restrict_mem measurableSet_Iio |>.mono fun y hy => by
      exact pow_nonneg (sub_nonneg.mpr hy.le) 3)

/-! ### Exact mass and polynomial moments -/

noncomputable def peanoBetaCoeff (m : ℕ) : ℝ :=
  6 / ((m + 1 : ℝ) * (m + 2) * (m + 3) * (m + 4))

private theorem intervalIntegral_pow_mul_sub_cube (m : ℕ) (y : ℝ) :
    (∫ t in (0 : ℝ)..y, t ^ m * (y - t) ^ 3) =
      peanoBetaCoeff m * y ^ (m + 4) := by
  have hfun : (fun t : ℝ => t ^ m * (y - t) ^ 3) =
      fun t => y ^ 3 * t ^ m - 3 * y ^ 2 * t ^ (m + 1) +
        3 * y * t ^ (m + 2) - t ^ (m + 3) := by
    funext t
    ring
  rw [hfun]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_add,
    intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_pow, integral_pow, integral_pow, integral_pow]
  · unfold peanoBetaCoeff
    push_cast
    field_simp
    ring
  all_goals (apply Continuous.intervalIntegrable; fun_prop)

theorem integral_Ici_absPow_mul_cubicStopLoss (m : ℕ) (y : ℝ) :
    (∫ t in Ici (0 : ℝ), |t| ^ m * (max (y - t) 0) ^ 3) =
      peanoBetaCoeff m * (max y 0) ^ (m + 4) := by
  by_cases hy : 0 ≤ y
  · calc
      (∫ t in Ici (0 : ℝ), |t| ^ m * (max (y - t) 0) ^ 3) =
          ∫ t in Ioc (0 : ℝ) y, t ^ m * (y - t) ^ 3 := by
        rw [← integral_indicator measurableSet_Ici,
          ← integral_indicator measurableSet_Ioc]
        apply integral_congr_ae
        filter_upwards [volume.ae_ne 0] with t htne
        by_cases ht0 : 0 ≤ t
        · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htne)
          by_cases hty : t ≤ y
          · simp [ht0, htpos, hty, abs_of_nonneg ht0]
          · have hyt : y - t ≤ 0 := sub_nonpos.mpr (le_of_not_ge hty)
            simp [ht0, htpos, hty, hyt]
        · have htneg : t < 0 := lt_of_not_ge ht0
          rw [Set.indicator_of_notMem (s := Ioc (0 : ℝ) y) (f := fun t =>
            t ^ m * (y - t) ^ 3) (by
              intro hmem
              exact (not_lt_of_ge htneg.le) hmem.1)]
          simp [ht0]
      _ = ∫ t in (0 : ℝ)..y, t ^ m * (y - t) ^ 3 :=
        (intervalIntegral.integral_of_le hy).symm
      _ = peanoBetaCoeff m * y ^ (m + 4) :=
        intervalIntegral_pow_mul_sub_cube m y
      _ = peanoBetaCoeff m * (max y 0) ^ (m + 4) := by rw [max_eq_left hy]
  · have hy' : y ≤ 0 := le_of_not_ge hy
    calc
      (∫ t in Ici (0 : ℝ), |t| ^ m * (max (y - t) 0) ^ 3) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
        rw [max_eq_right (sub_nonpos.mpr (hy'.trans ht))]
        simp
      _ = peanoBetaCoeff m * (max y 0) ^ (m + 4) := by simp [max_eq_right hy']

private theorem integrableOn_Ici_absPow_mul_cubicStopLoss (m : ℕ) (y : ℝ) :
    IntegrableOn (fun t : ℝ => |t| ^ m * (max (y - t) 0) ^ 3) (Ici 0) := by
  let g : ℝ → ℝ := fun t => |t| ^ m * (max (y - t) 0) ^ 3
  have hcompact : IntegrableOn g (Icc 0 (max y 0)) :=
    ContinuousOn.integrableOn_compact isCompact_Icc (by
      dsimp only [g]
      fun_prop)
  have hind : Integrable ((Icc 0 (max y 0)).indicator g) volume :=
    hcompact.integrable_indicator measurableSet_Icc
  have hindRest : Integrable ((Icc 0 (max y 0)).indicator g)
      (volume.restrict (Ici 0)) := hind.mono_measure Measure.restrict_le_self
  refine hindRest.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  by_cases hty : t ≤ max y 0
  · rw [Set.indicator_of_mem (s := Icc 0 (max y 0)) (f := g)
      (show t ∈ Icc 0 (max y 0) from ⟨ht, hty⟩)]
  · rw [Set.indicator_of_notMem (s := Icc 0 (max y 0)) (f := g)
      (by simp only [mem_Icc, not_and_or]; exact Or.inr hty)]
    rw [max_eq_right]
    · simp
    · exact sub_nonpos.mpr ((le_max_left y 0).trans (le_of_not_ge hty))

private theorem integrable_maxPow_standardGaussian (n : ℕ) :
    Integrable (fun y : ℝ => (max y 0) ^ n) (gaussianReal 0 1) := by
  have habs : Integrable (fun y : ℝ => |y| ^ n) (gaussianReal 0 1) := by
    simpa [Real.norm_eq_abs, abs_pow] using (integrable_standardGaussian_pow n).norm
  refine Integrable.mono' habs (by fun_prop) ?_
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_max_right y 0) n)]
  exact pow_le_pow_left₀ (le_max_right y 0) (max_le (le_abs_self y) (abs_nonneg y)) n

theorem integral_Ici_absPow_mul_standardGaussian_cubicStopLoss (m : ℕ) :
    (∫ t in Ici (0 : ℝ), |t| ^ m *
        (∫ y, (max (y - t) 0) ^ 3 ∂(gaussianReal 0 1))) =
      peanoBetaCoeff m *
        ∫ y, (max y 0) ^ (m + 4) ∂(gaussianReal 0 1) := by
  let F : ℝ → ℝ → ℝ := fun t y => |t| ^ m * (max (y - t) 0) ^ 3
  have hFsm : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Ici 0)).prod (gaussianReal 0 1)) := by
    exact (by fun_prop : StronglyMeasurable (Function.uncurry F)).aestronglyMeasurable
  have hFint : Integrable (Function.uncurry F)
      ((volume.restrict (Ici 0)).prod (gaussianReal 0 1)) := by
    apply (integrable_prod_iff' hFsm).mpr
    constructor
    · exact ae_of_all _ fun y => integrableOn_Ici_absPow_mul_cubicStopLoss m y
    · have houter := (integrable_maxPow_standardGaussian (m + 4)).const_mul
          (peanoBetaCoeff m)
      refine houter.congr (ae_of_all _ fun y => ?_)
      change peanoBetaCoeff m * (max y 0) ^ (m + 4) =
        ∫ t in Ici (0 : ℝ), ‖|t| ^ m * (max (y - t) 0) ^ 3‖
      rw [show (fun t : ℝ => ‖|t| ^ m * (max (y - t) 0) ^ 3‖) =
          fun t => |t| ^ m * (max (y - t) 0) ^ 3 by
        funext t
        rw [Real.norm_eq_abs, abs_of_nonneg]
        exact mul_nonneg (pow_nonneg (abs_nonneg t) _)
          (pow_nonneg (le_max_right _ _) _)]
      exact (integral_Ici_absPow_mul_cubicStopLoss m y).symm
  calc
    (∫ t in Ici (0 : ℝ), |t| ^ m *
        (∫ y, (max (y - t) 0) ^ 3 ∂(gaussianReal 0 1))) =
        ∫ t in Ici (0 : ℝ), ∫ y, F t y ∂(gaussianReal 0 1) := by
      apply integral_congr_ae
      filter_upwards [] with t
      change |t| ^ m * (∫ y, (max (y - t) 0) ^ 3 ∂(gaussianReal 0 1)) =
        ∫ y, |t| ^ m * (max (y - t) 0) ^ 3 ∂(gaussianReal 0 1)
      rw [integral_const_mul]
    _ = ∫ y, (∫ t in Ici (0 : ℝ), F t y) ∂(gaussianReal 0 1) :=
      by
        convert integral_integral_swap (μ := volume.restrict (Ici 0))
          (ν := gaussianReal 0 1) hFint using 1
    _ = ∫ y, peanoBetaCoeff m * (max y 0) ^ (m + 4)
        ∂(gaussianReal 0 1) := by
      congr 1
      funext y
      change (∫ t in Ici (0 : ℝ), |t| ^ m * (max (y - t) 0) ^ 3) =
        peanoBetaCoeff m * (max y 0) ^ (m + 4)
      exact integral_Ici_absPow_mul_cubicStopLoss m y
    _ = peanoBetaCoeff m *
        ∫ y, (max y 0) ^ (m + 4) ∂(gaussianReal 0 1) :=
      integral_const_mul _ _

theorem integral_standardGaussian_abs_evenPow (ell : ℕ) :
    (∫ x : ℝ, |x| ^ (2 * ell) ∂(gaussianReal 0 1)) =
      (Nat.doubleFactorial (2 * ell - 1) : ℝ) := by
  have hhalf := integral_gaussianHalf_abs_evenPow_mul_exp_sq ell
    (lambda := 0) (by norm_num)
  simp only [zero_mul, Real.exp_zero, mul_one] at hhalf
  have hscale := centeredGaussianEvenMoment_scaled (Real.sqrt 2)
    (2 : NNReal)⁻¹ ell
  have hvariance : scaledVariance (Real.sqrt 2) (2 : NNReal)⁻¹ = 1 := by
    ext
    simp [scaledVariance, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hvariance] at hscale
  unfold centeredGaussianEvenMoment at hscale
  rw [hscale, hhalf]
  unfold gaussianHalfTiltedEvenMomentMajorant
  rw [abs_of_nonneg (Real.sqrt_nonneg 2)]
  rw [pow_mul]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp [Real.one_rpow]
  field_simp

theorem integral_standardGaussian_max_evenPow (ell : ℕ) (hell : 0 < ell) :
    (∫ x : ℝ, (max x 0) ^ (2 * ell) ∂(gaussianReal 0 1)) =
      (Nat.doubleFactorial (2 * ell - 1) : ℝ) / 2 := by
  let f : ℝ → ℝ := fun x => (max x 0) ^ (2 * ell)
  have hf := integrable_maxPow_standardGaussian (2 * ell)
  have hmap : Measure.map (fun x : ℝ => -x) (gaussianReal 0 1) =
      gaussianReal 0 1 := by
    simpa using (gaussianReal_map_neg (μ := 0) (v := 1))
  have hreflect : (∫ x, f (-x) ∂(gaussianReal 0 1)) =
      ∫ x, f x ∂(gaussianReal 0 1) := by
    have hfmap : AEStronglyMeasurable f
        (Measure.map (fun x : ℝ => -x) (gaussianReal 0 1)) := by
      rw [hmap]
      exact hf.aestronglyMeasurable
    calc
      _ = ∫ x, f x ∂(Measure.map (fun x : ℝ => -x) (gaussianReal 0 1)) := by
        exact (integral_map (μ := gaussianReal 0 1) (φ := fun x : ℝ => -x)
          (by fun_prop) hfmap).symm
      _ = _ := by rw [hmap]
  have hfneg : Integrable (fun x => f (-x)) (gaussianReal 0 1) := by
    have hfmap : Integrable f
        (Measure.map (fun x : ℝ => -x) (gaussianReal 0 1)) := by
      rw [hmap]
      exact hf
    exact (integrable_map_measure hfmap.aestronglyMeasurable (by fun_prop)).mp hfmap
  have hsum : (∫ x : ℝ, |x| ^ (2 * ell) ∂(gaussianReal 0 1)) =
      (∫ x, f x ∂(gaussianReal 0 1)) + ∫ x, f (-x) ∂(gaussianReal 0 1) := by
    rw [← integral_add hf hfneg]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp only [f]
    by_cases hx : 0 ≤ x
    · simp [hx, hell.ne', pow_mul, sq_abs]
    · have hx' : x ≤ 0 := le_of_not_ge hx
      simp [hx', hell.ne', pow_mul, sq_abs]
  rw [integral_standardGaussian_abs_evenPow, hreflect] at hsum
  dsimp only [f] at hsum ⊢
  linarith

private theorem integrableOn_Ici_absPow_mul_standardRademacher_cubicStopLoss
    (m : ℕ) : IntegrableOn (fun t : ℝ => |t| ^ m *
      (∫ y, (max (y - t) 0) ^ 3 ∂standardRademacherMeasure)) (Ici 0) := by
  have h := (integrableOn_Ici_absPow_mul_cubicStopLoss m 1).const_mul (1 / 2 : ℝ)
  refine h.congr (ae_restrict_mem measurableSet_Ici |>.mono fun t ht => ?_)
  dsimp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have ht0 : 0 ≤ t := ht
  have hneg : max ((-1 : ℝ) - t) 0 = 0 :=
    max_eq_right (sub_nonpos.mpr (by linarith))
  rw [integral_standardRademacher_cubicStopLoss, hneg]
  ring

theorem integral_Ici_absPow_mul_standardRademacher_cubicStopLoss (m : ℕ) :
    (∫ t in Ici (0 : ℝ), |t| ^ m *
        (∫ y, (max (y - t) 0) ^ 3 ∂standardRademacherMeasure)) =
      peanoBetaCoeff m / 2 := by
  calc
    _ = (1 / 2 : ℝ) * ∫ t in Ici (0 : ℝ),
        |t| ^ m * (max ((1 : ℝ) - t) 0) ^ 3 := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      have ht0 : 0 ≤ t := ht
      have hneg : max ((-1 : ℝ) - t) 0 = 0 :=
        max_eq_right (sub_nonpos.mpr (by linarith))
      rw [integral_standardRademacher_cubicStopLoss, hneg]
      ring
    _ = peanoBetaCoeff m / 2 := by
      rw [integral_Ici_absPow_mul_cubicStopLoss m 1]
      norm_num
      ring

private theorem integrableOn_Ici_absPow_mul_peanoKDensity (m : ℕ) :
    IntegrableOn (fun t : ℝ => |t| ^ m * peanoKDensity t) (Ici 0) := by
  have h : Integrable (fun t : ℝ => |t| ^ m * |peanoKDensity t|)
      (volume.restrict (Ici 0)) :=
    (integrable_absPow_mul_abs_peanoKDensity m).mono_measure
      Measure.restrict_le_self
  refine h.congr (ae_restrict_mem measurableSet_Ici |>.mono fun t _ => ?_)
  dsimp only
  rw [abs_of_nonneg (peanoKDensity_nonneg t)]

private theorem integrableOn_Ici_absPow_mul_standardGaussian_cubicStopLoss
    (m : ℕ) : IntegrableOn (fun t : ℝ => |t| ^ m *
      (∫ y, (max (y - t) 0) ^ 3 ∂(gaussianReal 0 1))) (Ici 0) := by
  have hk := (integrableOn_Ici_absPow_mul_peanoKDensity m).const_mul (1 / 2 : ℝ)
  have hr := integrableOn_Ici_absPow_mul_standardRademacher_cubicStopLoss m
  refine (hk.add hr).congr (ae_restrict_mem measurableSet_Ici |>.mono fun t _ => ?_)
  dsimp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [peanoKDensity_eq_two_mul_cubicStopLossDifference]
  unfold cubicStopLossDifference
  ring

theorem integral_Ici_absPow_mul_peanoKDensity (m : ℕ) :
    (∫ t in Ici (0 : ℝ), |t| ^ m * peanoKDensity t) =
      2 * peanoBetaCoeff m *
        ((∫ y, (max y 0) ^ (m + 4) ∂(gaussianReal 0 1)) - 1 / 2) := by
  have hg := integrableOn_Ici_absPow_mul_standardGaussian_cubicStopLoss m
  have hr := integrableOn_Ici_absPow_mul_standardRademacher_cubicStopLoss m
  calc
    _ = 2 * ((∫ t in Ici (0 : ℝ), |t| ^ m *
          (∫ y, (max (y - t) 0) ^ 3 ∂(gaussianReal 0 1))) -
        ∫ t in Ici (0 : ℝ), |t| ^ m *
          (∫ y, (max (y - t) 0) ^ 3 ∂standardRademacherMeasure)) := by
      rw [← integral_sub hg hr, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      rw [peanoKDensity_eq_two_mul_cubicStopLossDifference]
      unfold cubicStopLossDifference
      ring
    _ = _ := by
      rw [integral_Ici_absPow_mul_standardGaussian_cubicStopLoss,
        integral_Ici_absPow_mul_standardRademacher_cubicStopLoss]
      ring

theorem integral_absPow_mul_peanoKDensity (m : ℕ) :
    (∫ t : ℝ, |t| ^ m * peanoKDensity t) =
      4 * peanoBetaCoeff m *
        ((∫ y, (max y 0) ^ (m + 4) ∂(gaussianReal 0 1)) - 1 / 2) := by
  calc
    (∫ t : ℝ, |t| ^ m * peanoKDensity t) =
        ∫ t : ℝ, |t| ^ m * peanoKDensity |t| := by
      apply integral_congr_ae
      filter_upwards [] with t
      by_cases ht : 0 ≤ t
      · rw [abs_of_nonneg ht]
      · rw [abs_of_nonpos (le_of_not_ge ht), peanoKDensity_neg]
    _ = 2 * ∫ t in Ioi (0 : ℝ), t ^ m * peanoKDensity t := by
      simpa only using integral_comp_abs
        (f := fun t : ℝ => t ^ m * peanoKDensity t)
    _ = 2 * ∫ t in Ici (0 : ℝ), |t| ^ m * peanoKDensity t := by
      rw [integral_Ici_eq_integral_Ioi]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [abs_of_pos ht]
    _ = _ := by rw [integral_Ici_absPow_mul_peanoKDensity]; ring

theorem integral_abs_evenPow_mul_peanoKDensity (ell : ℕ) :
    (∫ t : ℝ, |t| ^ (2 * ell) * peanoKDensity t) =
      2 * peanoBetaCoeff (2 * ell) *
        ((Nat.doubleFactorial (2 * (ell + 2) - 1) : ℝ) - 1) := by
  rw [integral_absPow_mul_peanoKDensity,
    show 2 * ell + 4 = 2 * (ell + 2) by omega,
    integral_standardGaussian_max_evenPow (ell + 2) (by omega)]
  ring

theorem integral_peanoKDensity : (∫ t : ℝ, peanoKDensity t) = 1 := by
  have h := integral_abs_evenPow_mul_peanoKDensity 0
  norm_num [peanoBetaCoeff] at h ⊢
  exact h

/-! ### Exact odd absolute moments -/


theorem integral_standardGaussian_max_oddPow (q : ℕ) :
    (∫ x : ℝ, (max x 0) ^ (2 * q + 1) ∂(gaussianReal 0 1)) =
      2 ^ q * Nat.factorial q / Real.sqrt (2 * Real.pi) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [smul_eq_mul, gaussianPDFReal]
  have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  calc
    _ = ∫ x in Ioi (0 : ℝ), (Real.sqrt (2 * Real.pi))⁻¹ *
        (x ^ (2 * q + 1) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : 0 < x
      · rw [Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx), max_eq_left hx.le]
        simp only [NNReal.coe_one, mul_one, sub_zero]
        field_simp [hsqrt]
      · have hx' : x ≤ 0 := le_of_not_gt hx
        rw [Set.indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx), max_eq_right hx']
        simp
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
        ∫ x in Ioi (0 : ℝ), x ^ (2 * q + 1) *
          Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
      rw [integral_const_mul]
    _ = _ := by
      rw [show (∫ x in Ioi (0 : ℝ), x ^ (2 * q + 1) *
          Real.exp (-(1 / 2 : ℝ) * x ^ 2)) =
          (1 / 2 : ℝ) ^ (-(((2 * q + 1 : ℕ) : ℝ) + 1) / 2) *
            (1 / 2 : ℝ) * Real.Gamma ((((2 * q + 1 : ℕ) : ℝ) + 1) / 2) by
        simpa only [Real.rpow_natCast, Real.rpow_two] using
          (integral_rpow_mul_exp_neg_mul_rpow (p := (2 : ℝ))
            (q := ((2 * q + 1 : ℕ) : ℝ)) (b := (1 / 2 : ℝ))
            (by norm_num)
            (by
              have hnonneg : 0 ≤ (((2 * q + 1 : ℕ) : ℝ)) := by positivity
              exact (by linarith : (-1 : ℝ) < ((2 * q + 1 : ℕ) : ℝ)))
            (by norm_num))]
      rw [show (((2 * q + 1 : ℕ) : ℝ) + 1) / 2 = (q : ℝ) + 1 by
        push_cast; ring]
      rw [Real.Gamma_nat_eq_factorial]
      rw [show -(((2 * q + 1 : ℕ) : ℝ) + 1) / 2 = -(q : ℝ) - 1 by
        push_cast; ring]
      rw [show -(q : ℝ) - 1 = -((q : ℝ) + 1) by ring]
      have hneg : (1 / 2 : ℝ) ^ (-((q : ℝ) + 1)) =
          ((1 / 2 : ℝ) ^ ((q : ℝ) + 1))⁻¹ :=
        Real.rpow_neg (x := (1 / 2 : ℝ)) (by norm_num) ((q : ℝ) + 1)
      rw [hneg]
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2)]
      simp only [Real.rpow_natCast]
      field_simp [hsqrt]
      norm_num
      ring_nf
      rw [← mul_pow]
      norm_num

theorem integral_abs_pow_eleven_mul_peanoKDensity :
    (∫ t : ℝ, |t| ^ 11 * peanoKDensity t) =
      (645120 / Real.sqrt (2 * Real.pi) - 1 / 2) / 1365 := by
  rw [integral_absPow_mul_peanoKDensity,
    show 11 + 4 = 2 * 7 + 1 by norm_num,
    integral_standardGaussian_max_oddPow 7]
  norm_num [peanoBetaCoeff]
  ring

theorem integral_abs_pow_fifteen_mul_peanoKDensity :
    (∫ t : ℝ, |t| ^ 15 * peanoKDensity t) =
      (185794560 / Real.sqrt (2 * Real.pi) - 1 / 2) / 3876 := by
  rw [integral_absPow_mul_peanoKDensity,
    show 15 + 4 = 2 * 9 + 1 by norm_num,
    integral_standardGaussian_max_oddPow 9]
  norm_num [peanoBetaCoeff]
  ring



/-! ### Probability-measure packaging -/

/-- The fourth-order Peano replacement probability measure. -/
noncomputable def peanoKMeasure : Measure ℝ :=
  positiveDensityMeasure peanoKDensity

instance peanoKMeasure_isProbabilityMeasure :
    IsProbabilityMeasure peanoKMeasure := by
  rw [isProbabilityMeasure_iff_real]
  have h := integral_positiveDensityMeasure peanoKDensity
    stronglyMeasurable_peanoKDensity.measurable peanoKDensity_nonneg
    (fun _ : ℝ => (1 : ℝ))
  change (∫ _ : ℝ, (1 : ℝ) ∂peanoKMeasure) = _ at h
  rw [integral_const] at h
  simpa [Measure.real, smul_eq_mul, integral_peanoKDensity] using h

/-! ### Gaussian even-moment domination -/

theorem peanoKMeasure_map_neg :
    peanoKMeasure.map (fun x : ℝ => -x) = peanoKMeasure := by
  ext s hs
  let e : ℝ ≃ᵐ ℝ := MeasurableEquiv.neg ℝ
  have hmap := e.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul'
    (g := peanoKDensity) hs (f' := fun _ => (-1 : ℝ))
    (fun x => (hasDerivAt_neg x))
    (ae_of_all _ peanoKDensity_nonneg) integrable_peanoKDensity
  change peanoKMeasure.map (fun x : ℝ => -x) s = _
  rw [show peanoKMeasure.map (fun x : ℝ => -x) s =
      ENNReal.ofReal (∫ x in s, |(-1 : ℝ)| * peanoKDensity (-x)) by
    simpa [peanoKMeasure, positiveDensityMeasure, e] using hmap]
  unfold peanoKMeasure positiveDensityMeasure
  rw [withDensity_apply _ hs]
  rw [← ofReal_integral_eq_lintegral_ofReal integrable_peanoKDensity.integrableOn
    (ae_restrict_mem hs |>.mono fun x _ => peanoKDensity_nonneg x)]
  congr 1
  apply setIntegral_congr_fun hs
  intro x _
  simp [peanoKDensity_neg]

theorem integrable_absPow_peanoKMeasure (n : ℕ) :
    Integrable (fun x : ℝ => |x| ^ n) peanoKMeasure := by
  unfold peanoKMeasure positiveDensityMeasure
  rw [integrable_withDensity_iff_integrable_smul'
    stronglyMeasurable_peanoKDensity.measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine (integrable_absPow_mul_abs_peanoKDensity n).congr (ae_of_all _ fun x => ?_)
  simp only [ENNReal.toReal_ofReal (peanoKDensity_nonneg x), smul_eq_mul]
  rw [abs_of_nonneg (peanoKDensity_nonneg x)]
  ring

theorem integral_absPow_peanoKMeasure (n : ℕ) :
    (∫ x : ℝ, |x| ^ n ∂peanoKMeasure) =
      ∫ x : ℝ, |x| ^ n * peanoKDensity x := by
  unfold peanoKMeasure
  rw [integral_positiveDensityMeasure peanoKDensity
    stronglyMeasurable_peanoKDensity.measurable peanoKDensity_nonneg]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul]
  ring

theorem integral_abs_evenPow_peanoKMeasure (ell : ℕ) :
    (∫ x : ℝ, |x| ^ (2 * ell) ∂peanoKMeasure) =
      2 * peanoBetaCoeff (2 * ell) *
        ((Nat.doubleFactorial (2 * (ell + 2) - 1) : ℝ) - 1) := by
  rw [integral_absPow_peanoKMeasure,
    integral_abs_evenPow_mul_peanoKDensity]

private theorem peanoK_evenMoment_le_standardGaussian (ell : ℕ) :
    2 * peanoBetaCoeff (2 * ell) *
        ((Nat.doubleFactorial (2 * (ell + 2) - 1) : ℝ) - 1) ≤
      (Nat.doubleFactorial (2 * ell - 1) : ℝ) := by
  by_cases hell : ell = 0
  · subst ell
    norm_num [peanoBetaCoeff]
  · have hellpos : 0 < ell := Nat.pos_of_ne_zero hell
    have hidx : 2 * (ell + 2) - 1 = (2 * ell - 1) + 2 + 2 := by omega
    rw [hidx, Nat.doubleFactorial_add_two, Nat.doubleFactorial_add_two]
    unfold peanoBetaCoeff
    push_cast
    have hcast : ((2 * ell - 1 : ℕ) : ℝ) = 2 * (ell : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hcast]
    let d : ℝ := Nat.doubleFactorial (2 * ell - 1)
    let D : ℝ := (2 * (ell : ℝ) + 1) * (2 * ell + 2) *
      (2 * ell + 3) * (2 * ell + 4)
    have hd : 0 ≤ d := by positivity
    have hD : 0 < D := by dsimp only [D]; positivity
    have heq :
        2 * (6 / ((2 * (ell : ℝ) + 1) * (2 * ell + 2) *
          (2 * ell + 3) * (2 * ell + 4))) *
            ((2 * ell - 1 + 2 + 2) *
              ((2 * ell - 1 + 2) * d) - 1) =
          (12 * ((2 * ell + 3) * ((2 * ell + 1) * d) - 1)) / D := by
      dsimp only [D]
      ring
    rw [heq]
    change (12 * ((2 * (ell : ℝ) + 3) * ((2 * ell + 1) * d) - 1)) / D ≤ d
    apply (div_le_iff₀ hD).mpr
    dsimp only [D]
    have hcoef : 12 * (2 * (ell : ℝ) + 3) * (2 * ell + 1) ≤
        (2 * ell + 1) * (2 * ell + 2) * (2 * ell + 3) * (2 * ell + 4) := by
      have hellreal : (1 : ℝ) ≤ ell := by exact_mod_cast hellpos
      nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * (ell : ℝ) + 1)
        (mul_nonneg (by linarith : 0 ≤ 2 * (ell : ℝ) + 3)
          (by nlinarith : 0 ≤ (2 * (ell : ℝ) + 2) * (2 * ell + 4) - 12))]
    nlinarith [mul_le_mul_of_nonneg_right hcoef hd]

theorem peanoK_evenMomentDomination :
    GaussianEvenMomentDomination peanoKMeasure 1 1 := by
  refine ⟨by norm_num, inferInstance, peanoKMeasure_map_neg,
    integrable_absPow_peanoKMeasure, ?_⟩
  intro ell
  rw [integral_abs_evenPow_peanoKMeasure]
  unfold centeredGaussianEvenMoment
  rw [integral_standardGaussian_abs_evenPow]
  norm_num
  exact peanoK_evenMoment_le_standardGaussian ell


end CertifiedJL
