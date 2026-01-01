/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Gaussian.GammaInteger
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Even-dimensional half-Gaussian reference measures

The sparse upper counterexample compares a centered binomial lattice with
the density `π⁻¹/² exp (-x²)`, i.e. a Gaussian of variance `1/2`.  This file
develops the radial integral needed to identify the squared norm of `rows`
such coordinates with `Gamma(shape, 1)` whenever `rows = 2 * shape`.
-/

open scoped BigOperators

open MeasureTheory

namespace CertifiedJL
namespace Probability
namespace HalfGaussianEven

variable {rows shape : ℕ}

/-- Scalar density of a centered Gaussian with variance `1/2`. -/
noncomputable def halfGaussianDensity (x : ℝ) : ℝ :=
  (Real.sqrt Real.pi)⁻¹ * Real.exp (-x ^ 2)

/-- The corresponding radial density on a rows-dimensional Euclidean space. -/
noncomputable def halfGaussianRadialDensity
    (x : EuclideanSpace ℝ (Fin rows)) : ℝ :=
  Real.pi⁻¹ ^ shape * Real.exp (-‖x‖ ^ 2)

/-- Product form of the rows-dimensional half-Gaussian density. -/
noncomputable def halfGaussianProductDensity (x : Fin rows → ℝ) : ℝ :=
  ∏ i, halfGaussianDensity (x i)

/-- Squared Euclidean radius in product coordinates. -/
def squaredRadius (x : Fin rows → ℝ) : ℝ :=
  ∑ i, (x i) ^ 2

theorem integrable_halfGaussianDensity :
    Integrable halfGaussianDensity := by
  unfold halfGaussianDensity
  have h :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1))
      |>.const_mul (Real.sqrt Real.pi)⁻¹
  apply h.congr
  filter_upwards with x
  congr 2
  ring

theorem integrable_halfGaussianProductDensity {rows : ℕ} :
    Integrable (halfGaussianProductDensity (rows := rows)) := by
  exact Integrable.fintype_prod
    (μ := fun _ : Fin rows => (volume : Measure ℝ))
    (fun _ => integrable_halfGaussianDensity)

/-- The product and radial presentations agree under the Euclidean isometry. -/
theorem halfGaussianProductDensity_eq_radial
    (hrows : rows = 2 * shape) (x : Fin rows → ℝ) :
    halfGaussianProductDensity x =
      halfGaussianRadialDensity (shape := shape) (WithLp.toLp 2 x) := by
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  unfold halfGaussianProductDensity halfGaussianDensity
    halfGaussianRadialDensity
  rw [Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← Real.exp_sum]
  rw [EuclideanSpace.real_norm_sq_eq]
  have hconst :
      (Real.sqrt Real.pi)⁻¹ ^ rows =
        Real.pi⁻¹ ^ shape := by
    rw [inv_pow, hrows,
      pow_mul, Real.sq_sqrt hpi]
    rw [inv_pow]
  rw [hconst, Finset.sum_neg_distrib]

/-- Explicit exponential form of the product density. -/
theorem halfGaussianProductDensity_eq_exp
    (hrows : rows = 2 * shape) (x : Fin rows → ℝ) :
    halfGaussianProductDensity x =
      Real.pi⁻¹ ^ shape * Real.exp (-squaredRadius x) := by
  rw [halfGaussianProductDensity_eq_radial hrows]
  unfold halfGaussianRadialDensity squaredRadius
  rw [EuclideanSpace.real_norm_sq_eq]

/--
The square substitution at the exact exponent needed for rows Gaussian
coordinates.
-/
theorem integral_pow_even_sub_one_exp_neg_sq_Ioi
    (hrows : rows = 2 * shape) (hshape : 0 < shape)
    {a : ℝ} (ha : 0 ≤ a) :
    (∫ r : ℝ in Set.Ioi (Real.sqrt a),
        r ^ (rows - 1) * Real.exp (-r ^ 2)) =
      (1 / 2 : ℝ) *
        ∫ t : ℝ in Set.Ioi a, t ^ (shape - 1) * Real.exp (-t) := by
  have hrowspos : 0 < rows := by omega
  have hpred : rows - 1 = 2 * (shape - 1) + 1 := by omega
  let f : ℝ → ℝ := fun r => r ^ 2
  let f' : ℝ → ℝ := fun r => 2 * r
  let g : ℝ → ℝ :=
    fun t => (1 / 2 : ℝ) * t ^ (shape - 1) * Real.exp (-t)
  have hf : ContinuousOn f (Set.Ici (Real.sqrt a)) := by
    fun_prop
  have hft : Filter.Tendsto f Filter.atTop Filter.atTop := by
    exact Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hff' :
      ∀ r ∈ Set.Ioi (Real.sqrt a),
        HasDerivWithinAt f (f' r) (Set.Ioi r) r := by
    intro r _
    simpa [f, f'] using (hasDerivAt_pow 2 r).hasDerivWithinAt
  have hg_cont : ContinuousOn g (f '' Set.Ioi (Real.sqrt a)) := by
    apply Continuous.continuousOn
    fun_prop
  have hg_iCi : IntegrableOn g (Set.Ici a) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    have hbase := integrableOn_pow_mul_exp_neg_Ioi (shape - 1) ha
    have hscaled :=
      hbase.const_mul ((((shape - 1) : ℕ).factorial : ℝ) / 2)
    exact IntegrableOn.congr_fun hscaled (fun t _ => by
      simp only [g]
      field_simp) measurableSet_Ioi
  have himage : f '' Set.Ici (Real.sqrt a) ⊆ Set.Ici a := by
    rintro y ⟨r, hr, rfl⟩
    dsimp only [f]
    rw [Set.mem_Ici] at hr ⊢
    nlinarith [Real.sq_sqrt ha, Real.sqrt_nonneg a]
  have hg1 : IntegrableOn g (f '' Set.Ici (Real.sqrt a)) :=
    hg_iCi.mono_set himage
  have hg2 :
      IntegrableOn (fun r => (g ∘ f) r * f' r)
        (Set.Ici (Real.sqrt a)) := by
    have hraw :
        IntegrableOn
          (fun r : ℝ => r ^ ((rows - 1) : ℝ) *
            Real.exp (-(1 : ℝ) * r ^ 2))
          (Set.Ici (Real.sqrt a)) :=
      (integrable_rpow_mul_exp_neg_mul_sq
          (b := (1 : ℝ)) (by norm_num)
          (s := ((rows - 1) : ℝ)) (by
            have hrowsposReal : (0 : ℝ) < rows := by exact_mod_cast hrowspos
            linarith)).integrableOn
    exact hraw.congr_fun (fun r hr => by
      rw [Set.mem_Ici] at hr
      have hr0 : 0 ≤ r := (Real.sqrt_nonneg a).trans hr
      simp only [g, f, f', Function.comp_apply]
      rw [show (rows : ℝ) - 1 = ((rows - 1 : ℕ) : ℝ) by
          rw [Nat.cast_sub (by omega : 1 ≤ rows)]; norm_num,
        Real.rpow_natCast, hpred, pow_succ, pow_mul]
      ring_nf) measurableSet_Ici
  have hchange :=
    integral_comp_mul_deriv_Ioi hf hft hff' hg_cont hg1 hg2
  have hfa : f (Real.sqrt a) = a := by
    simp [f, Real.sq_sqrt ha]
  rw [hfa] at hchange
  calc
    (∫ r : ℝ in Set.Ioi (Real.sqrt a),
        r ^ (rows - 1) * Real.exp (-r ^ 2)) =
        ∫ r : ℝ in Set.Ioi (Real.sqrt a),
          (g ∘ f) r * f' r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hr0 : 0 ≤ r :=
        (Real.sqrt_nonneg a).trans (Set.mem_Ioi.mp hr).le
      simp only [g, f, f', Function.comp_apply]
      rw [hpred, pow_succ, pow_mul]
      ring
    _ = ∫ t : ℝ in Set.Ioi a, g t := hchange
    _ = (1 / 2 : ℝ) *
        ∫ t : ℝ in Set.Ioi a, t ^ (shape - 1) * Real.exp (-t) := by
      simp only [g]
      rw [← MeasureTheory.integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      ring

/-- Exact first-moment Gaussian tail integral. -/
theorem integral_Ioi_mul_exp_neg_mul_sq {c b : ℝ}
    (hc : 0 < c) (hb : 0 ≤ b) :
    (∫ x : ℝ in Set.Ioi b, x * Real.exp (-c * x ^ 2)) =
      Real.exp (-c * b ^ 2) / (2 * c) := by
  let F : ℝ → ℝ :=
    fun x => Real.exp (-c * x ^ 2) / (2 * c)
  let F' : ℝ → ℝ :=
    fun x => -x * Real.exp (-c * x ^ 2)
  have hderiv : ∀ x ∈ Set.Ici b, HasDerivAt F (F' x) x := by
    intro x _
    apply
      (((hasDerivAt_id x).pow 2).const_mul (-c)).exp.div_const
        (2 * c) |>.congr_deriv
    dsimp only [F']
    simp only [Pi.pow_apply, id_eq]
    field_simp [hc.ne']
    norm_num
    ring
  have hnonpos : ∀ x ∈ Set.Ioi b, F' x ≤ 0 := by
    intro x hx
    dsimp only [F']
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (hb.trans hx.le))
      (Real.exp_nonneg _)
  have htendstoExp :
      Filter.Tendsto
        (fun x : ℝ => Real.exp (-c * x ^ 2))
        Filter.atTop (nhds 0) := by
    have htemp :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        ((Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))
          |>.const_mul_atTop hc)
    apply htemp.congr'
    filter_upwards with x
    simp only [Function.comp_apply]
    congr 1
    ring
  have htendsto :
      Filter.Tendsto F Filter.atTop (nhds 0) := by
    simpa only [F, zero_div] using htendstoExp.div_const (2 * c)
  have hnegative :=
    integral_Ioi_of_hasDerivAt_of_nonpos'
      hderiv hnonpos htendsto
  have hnegIntegral :
      (∫ x : ℝ in Set.Ioi b, F' x) =
        -(∫ x : ℝ in Set.Ioi b,
          x * Real.exp (-c * x ^ 2)) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    simp only [F']
    ring
  rw [hnegIntegral, zero_sub] at hnegative
  apply neg_inj.mp
  rw [hnegative]

/--
Mills's inequality in the exact form used by the coordinate truncation.
-/
theorem integral_Ioi_exp_neg_mul_sq_le {c b : ℝ}
    (hc : 0 < c) (hb : 0 < b) :
    (∫ x : ℝ in Set.Ioi b, Real.exp (-c * x ^ 2)) ≤
      Real.exp (-c * b ^ 2) / (2 * c * b) := by
  have hf :
      IntegrableOn (fun x : ℝ => Real.exp (-c * x ^ 2))
        (Set.Ioi b) :=
    (integrable_exp_neg_mul_sq hc).integrableOn
  have hgGlobal :=
    (integrable_mul_exp_neg_mul_sq hc).const_mul b⁻¹
  have hg :
      IntegrableOn
        (fun x : ℝ => b⁻¹ *
          (x * Real.exp (-c * x ^ 2)))
        (Set.Ioi b) :=
    hgGlobal.integrableOn
  calc
    (∫ x : ℝ in Set.Ioi b, Real.exp (-c * x ^ 2)) ≤
        ∫ x : ℝ in Set.Ioi b,
          b⁻¹ * (x * Real.exp (-c * x ^ 2)) := by
      apply setIntegral_mono_on hf hg measurableSet_Ioi
      intro x hx
      have hbx : b ≤ x := (Set.mem_Ioi.mp hx).le
      have hone : 1 ≤ b⁻¹ * x := by
        rw [← div_eq_inv_mul, one_le_div₀ hb]
        exact hbx
      nlinarith [Real.exp_pos (-c * x ^ 2)]
    _ = b⁻¹ *
        ∫ x : ℝ in Set.Ioi b,
          x * Real.exp (-c * x ^ 2) := by
      rw [integral_const_mul]
    _ = Real.exp (-c * b ^ 2) / (2 * c * b) := by
      rw [integral_Ioi_mul_exp_neg_mul_sq hc hb.le]
      field_simp

/-- Two-sided Mills bound for an even Gaussian kernel. -/
theorem integral_abs_ge_exp_neg_mul_sq_le {c b : ℝ}
    (hc : 0 < c) (hb : 0 < b) :
    (∫ x : ℝ in {x | b ≤ |x|},
        Real.exp (-c * x ^ 2)) ≤
      Real.exp (-c * b ^ 2) / (c * b) := by
  let kernel : ℝ → ℝ :=
    fun x => Real.exp (-c * x ^ 2)
  have hset :
      {x : ℝ | b ≤ |x|} =
        Set.Iic (-b) ∪ Set.Ici b := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic,
      Set.mem_Ici, le_abs]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl h
  have hdisjoint : Disjoint (Set.Iic (-b)) (Set.Ici b) := by
    rw [Set.disjoint_left]
    intro x hxLeft hxRight
    rw [Set.mem_Iic] at hxLeft
    rw [Set.mem_Ici] at hxRight
    linarith
  have hint : Integrable kernel :=
    integrable_exp_neg_mul_sq hc
  have heven (x : ℝ) : kernel (-x) = kernel x := by
    simp only [kernel, neg_sq]
  have hleft :
      (∫ x : ℝ in Set.Iic (-b), kernel x) =
        ∫ x : ℝ in Set.Ioi b, kernel x := by
    calc
      (∫ x : ℝ in Set.Iic (-b), kernel x) =
          ∫ x : ℝ in Set.Iic (-b), kernel (-x) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro x _
        exact (heven x).symm
      _ = ∫ x : ℝ in Set.Ioi b, kernel x := by
        simpa only [neg_neg] using integral_comp_neg_Iic (-b) kernel
  rw [hset, setIntegral_union hdisjoint measurableSet_Ici
    hint.integrableOn hint.integrableOn,
    hleft, integral_Ici_eq_integral_Ioi]
  calc
    (∫ x : ℝ in Set.Ioi b, kernel x) +
        ∫ x : ℝ in Set.Ioi b, kernel x ≤
      Real.exp (-c * b ^ 2) / (2 * c * b) +
        Real.exp (-c * b ^ 2) / (2 * c * b) := by
      gcongr <;>
        exact integral_Ioi_exp_neg_mul_sq_le hc hb
    _ = Real.exp (-c * b ^ 2) / (c * b) := by ring

/-- The one-dimensional density after the fixed exponential tilt `λ = 3/5`. -/
noncomputable def tiltedHalfGaussianDensity (x : ℝ) : ℝ :=
  (Real.sqrt Real.pi)⁻¹ *
    Real.exp (-(2 / 5 : ℝ) * x ^ 2)

theorem integrable_tiltedHalfGaussianDensity :
    Integrable tiltedHalfGaussianDensity := by
  exact (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 2 / 5))
    |>.const_mul (Real.sqrt Real.pi)⁻¹

/-- Product form of the fixed tilted density. -/
noncomputable def tiltedHalfGaussianProductDensity
    (x : Fin rows → ℝ) : ℝ :=
  ∏ i, tiltedHalfGaussianDensity (x i)

theorem integrable_tiltedHalfGaussianProductDensity {rows : ℕ} :
    Integrable (tiltedHalfGaussianProductDensity (rows := rows)) := by
  exact Integrable.fintype_prod
    (μ := fun _ : Fin rows => (volume : Measure ℝ))
    (fun _ => integrable_tiltedHalfGaussianDensity)

theorem tiltedHalfGaussianProductDensity_eq_exp
    (hrows : rows = 2 * shape) (x : Fin rows → ℝ) :
    tiltedHalfGaussianProductDensity x =
      Real.pi⁻¹ ^ shape *
        Real.exp (-(2 / 5 : ℝ) * ∑ i, (x i) ^ 2) := by
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  unfold tiltedHalfGaussianProductDensity
    tiltedHalfGaussianDensity
  rw [Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← Real.exp_sum]
  have hconst :
      (Real.sqrt Real.pi)⁻¹ ^ rows =
        Real.pi⁻¹ ^ shape := by
    rw [inv_pow, hrows,
      pow_mul, Real.sq_sqrt hpi]
    rw [inv_pow]
  rw [hconst]
  rw [← Finset.mul_sum]

/--
The original density is the fixed `3/5` exponential tilt of the auxiliary
density.
-/
theorem halfGaussianProductDensity_eq_exp_mul_tilted
    (hrows : rows = 2 * shape) (x : Fin rows → ℝ) :
    halfGaussianProductDensity x =
      Real.exp (-(3 / 5 : ℝ) * squaredRadius x) *
        tiltedHalfGaussianProductDensity x := by
  rw [halfGaussianProductDensity_eq_exp hrows,
    tiltedHalfGaussianProductDensity_eq_exp hrows]
  unfold squaredRadius
  rw [show
      -(∑ i, x i ^ 2) =
        -(3 / 5 : ℝ) * (∑ i, x i ^ 2) +
          -(2 / 5 : ℝ) * (∑ i, x i ^ 2) by ring,
    Real.exp_add]
  ring

/-- Total mass of the tilted one-dimensional density. -/
theorem integral_tiltedHalfGaussianDensity :
    (∫ x : ℝ, tiltedHalfGaussianDensity x) =
      Real.sqrt (5 / 2 : ℝ) := by
  unfold tiltedHalfGaussianDensity
  rw [integral_const_mul, integral_gaussian]
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  rw [show Real.pi / (2 / 5 : ℝ) =
      Real.pi * (5 / 2 : ℝ) by ring,
    Real.sqrt_mul hpi]
  field_simp [Real.sqrt_ne_zero'.mpr Real.pi_pos]

/--
Two-sided tilted coordinate tail, with the final elementary scale
comparison supplied separately.
-/
theorem integral_abs_ge_tiltedHalfGaussianDensity_lt {b : ℝ}
    (hb : 0 < b)
    (hscale :
      (Real.sqrt Real.pi)⁻¹ / ((2 / 5 : ℝ) * b) <
        Real.sqrt (5 / 2 : ℝ)) :
    (∫ x : ℝ in {x | b ≤ |x|},
        tiltedHalfGaussianDensity x) <
      Real.sqrt (5 / 2 : ℝ) *
        Real.exp (-(2 / 5 : ℝ) * b ^ 2) := by
  unfold tiltedHalfGaussianDensity
  rw [integral_const_mul]
  have hmills :=
    integral_abs_ge_exp_neg_mul_sq_le
      (c := (2 / 5 : ℝ)) (by norm_num) hb
  calc
    (Real.sqrt Real.pi)⁻¹ *
        ∫ x : ℝ in {x | b ≤ |x|},
          Real.exp (-(2 / 5 : ℝ) * x ^ 2) ≤
      (Real.sqrt Real.pi)⁻¹ *
        (Real.exp (-(2 / 5 : ℝ) * b ^ 2) /
          ((2 / 5 : ℝ) * b)) := by
      gcongr
    _ = ((Real.sqrt Real.pi)⁻¹ / ((2 / 5 : ℝ) * b)) *
        Real.exp (-(2 / 5 : ℝ) * b ^ 2) := by ring
    _ < Real.sqrt (5 / 2 : ℝ) *
        Real.exp (-(2 / 5 : ℝ) * b ^ 2) :=
      mul_lt_mul_of_pos_right hscale (Real.exp_pos _)

/--
Tilted product density with one coordinate restricted to the two-sided
cutoff tail.
-/
noncomputable def coordinateTiltedTailDensity
    (b : ℝ) (j : Fin rows) (x : Fin rows → ℝ) : ℝ :=
  ∏ i, if i = j then
    {t : ℝ | b ≤ |t|}.indicator tiltedHalfGaussianDensity (x i)
  else tiltedHalfGaussianDensity (x i)

theorem coordinateTiltedTailDensity_nonneg
    (b : ℝ) (j : Fin rows) (x : Fin rows → ℝ) :
    0 ≤ coordinateTiltedTailDensity b j x := by
  apply Finset.prod_nonneg
  intro i _
  by_cases hij : i = j
  · rw [if_pos hij]
    simp only [Set.indicator]
    split_ifs
    · unfold tiltedHalfGaussianDensity
      positivity
    · exact le_rfl
  · rw [if_neg hij]
    unfold tiltedHalfGaussianDensity
    positivity

theorem coordinateTiltedTailDensity_eq_of_mem
    {b : ℝ} {j : Fin rows} {x : Fin rows → ℝ}
    (hj : b ≤ |x j|) :
    coordinateTiltedTailDensity b j x =
      tiltedHalfGaussianProductDensity x := by
  unfold coordinateTiltedTailDensity
    tiltedHalfGaussianProductDensity
  apply Finset.prod_congr rfl
  intro i _
  by_cases hij : i = j
  · subst i
    rw [if_pos rfl]
    simp [hj]
  · rw [if_neg hij]

theorem integrable_coordinateTiltedTailDensity
    (b : ℝ) (j : Fin rows) :
    Integrable (coordinateTiltedTailDensity b j) := by
  unfold coordinateTiltedTailDensity
  rw [MeasureTheory.volume_pi]
  change Integrable
    (fun x : Fin rows → ℝ =>
      ∏ i, (fun t : ℝ => if i = j then
        {s : ℝ | b ≤ |s|}.indicator tiltedHalfGaussianDensity t
      else tiltedHalfGaussianDensity t) (x i))
    (Measure.pi fun _ : Fin rows => (volume : Measure ℝ))
  apply Integrable.fintype_prod
    (f := fun i : Fin rows => fun t : ℝ => if i = j then
      {s : ℝ | b ≤ |s|}.indicator tiltedHalfGaussianDensity t
    else tiltedHalfGaussianDensity t)
    (μ := fun _ : Fin rows => (volume : Measure ℝ))
  intro i
  by_cases hij : i = j
  · simpa [hij] using
      integrable_tiltedHalfGaussianDensity.indicator
        (measurableSet_le measurable_const continuous_abs.measurable)
  · simpa [hij] using integrable_tiltedHalfGaussianDensity

/-- Exact factorization of the one-coordinate tilted tail integral. -/
theorem integral_coordinateTiltedTailDensity
    (b : ℝ) (j : Fin rows) :
    (∫ x : Fin rows → ℝ, coordinateTiltedTailDensity b j x) =
      (∫ t : ℝ in {t | b ≤ |t|},
          tiltedHalfGaussianDensity t) *
        Real.sqrt (5 / 2 : ℝ) ^ (rows - 1) := by
  unfold coordinateTiltedTailDensity
  rw [integral_fintype_prod_volume_eq_prod
    (fun i : Fin rows => fun t : ℝ =>
      if i = j then
        {s : ℝ | b ≤ |s|}.indicator tiltedHalfGaussianDensity t
      else tiltedHalfGaussianDensity t)]
  let factors : Fin rows → ℝ :=
    fun i => ∫ t : ℝ, if i = j then
      {t : ℝ | b ≤ |t|}.indicator tiltedHalfGaussianDensity t
    else tiltedHalfGaussianDensity t
  change (∏ i, factors i) = _
  rw [← Finset.prod_erase_mul (Finset.univ : Finset (Fin rows))
    factors (Finset.mem_univ j)]
  have hj :
      factors j =
        ∫ t : ℝ in {t | b ≤ |t|},
          tiltedHalfGaussianDensity t := by
    simp [factors, integral_indicator
      (measurableSet_le measurable_const continuous_abs.measurable)]
  have hrest :
      ∏ i ∈ (Finset.univ : Finset (Fin rows)).erase j,
          factors i =
        Real.sqrt (5 / 2 : ℝ) ^ (rows - 1) := by
    calc
      ∏ i ∈ (Finset.univ : Finset (Fin rows)).erase j,
          factors i =
        ∏ _i ∈ (Finset.univ : Finset (Fin rows)).erase j,
          Real.sqrt (5 / 2 : ℝ) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hij : i ≠ j := Finset.ne_of_mem_erase hi
        simp [factors, hij, integral_tiltedHalfGaussianDensity]
      _ = Real.sqrt (5 / 2 : ℝ) ^
          ((Finset.univ : Finset (Fin rows)).erase j).card := by
        rw [Finset.prod_const]
      _ = Real.sqrt (5 / 2 : ℝ) ^ (rows - 1) := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ j),
          Finset.card_univ, Fintype.card_fin]
  rw [hj, hrest, mul_comm]

/--
The part of the radial upper tail removed by imposing a coordinate cutoff.
-/
def halfGaussianTruncationSet (a b : ℝ) : Set (Fin rows → ℝ) :=
  {x | a < squaredRadius x ∧ ∃ j, b ≤ |x j|}

theorem measurableSet_halfGaussianTruncationSet
    {rows : ℕ} (a b : ℝ) :
    MeasurableSet (halfGaussianTruncationSet (rows := rows) a b) := by
  unfold halfGaussianTruncationSet squaredRadius
  have hradial :
      MeasurableSet
        {x : Fin rows → ℝ | a < ∑ i, (x i) ^ 2} :=
    measurableSet_lt measurable_const
      (Finset.measurable_sum _ fun i _ =>
        ((measurable_pi_apply i).pow_const 2))
  have hcoordinate :
      MeasurableSet
        (⋃ j : Fin rows, {x : Fin rows → ℝ | b ≤ |x j|}) :=
    MeasurableSet.iUnion fun j =>
      measurableSet_le measurable_const
        (continuous_abs.measurable.comp (measurable_pi_apply j))
  convert hradial.inter hcoordinate using 1
  ext x
  simp

/--
Exponential tilting plus a union bound controls the Gaussian mass discarded
by the coordinate cutoff.

The scale hypothesis is deliberately separated: concrete applications can
discharge it with a short rational estimate and `π > 3`.
-/
theorem integral_halfGaussianTruncationSet_lt
    (hrows : rows = 2 * shape) (hshape : 0 < shape)
    {a b : ℝ} (hb : 0 < b)
    (hscale :
      (Real.sqrt Real.pi)⁻¹ / ((2 / 5 : ℝ) * b) <
        Real.sqrt (5 / 2 : ℝ)) :
    (∫ x : Fin rows → ℝ in halfGaussianTruncationSet a b,
        halfGaussianProductDensity x) <
      rows * (5 / 2 : ℝ) ^ shape *
        Real.exp (-(3 * a + 2 * b ^ 2) / 5) := by
  have hrowspos : 0 < rows := by omega
  let tailSum : (Fin rows → ℝ) → ℝ :=
    fun x => ∑ j, coordinateTiltedTailDensity b j x
  have htailSumIntegrable : Integrable tailSum := by
    exact integrable_finsetSum _ fun j _ =>
      integrable_coordinateTiltedTailDensity b j
  have hleftIntegrable :
      Integrable
        ((halfGaussianTruncationSet a b).indicator
          (halfGaussianProductDensity (rows := rows))) :=
    (integrable_halfGaussianProductDensity (rows := rows)).indicator
      (measurableSet_halfGaussianTruncationSet (rows := rows) a b)
  have hpointwise :
      ∀ x : Fin rows → ℝ,
        (halfGaussianTruncationSet a b).indicator
            halfGaussianProductDensity x ≤
          Real.exp (-(3 / 5 : ℝ) * a) * tailSum x := by
    intro x
    by_cases hx : x ∈ halfGaussianTruncationSet a b
    · rw [Set.indicator_of_mem hx]
      obtain ⟨hradial, j, hj⟩ := hx
      have htiltedNonneg :
          0 ≤ tiltedHalfGaussianProductDensity x := by
        unfold tiltedHalfGaussianProductDensity
        apply Finset.prod_nonneg
        intro i _
        unfold tiltedHalfGaussianDensity
        positivity
      have hexp :
          Real.exp (-(3 / 5 : ℝ) * squaredRadius x) ≤
            Real.exp (-(3 / 5 : ℝ) * a) := by
        rw [Real.exp_le_exp]
        nlinarith
      rw [halfGaussianProductDensity_eq_exp_mul_tilted hrows]
      calc
        Real.exp (-(3 / 5 : ℝ) * squaredRadius x) *
              tiltedHalfGaussianProductDensity x ≤
            Real.exp (-(3 / 5 : ℝ) * a) *
              tiltedHalfGaussianProductDensity x := by
          exact mul_le_mul_of_nonneg_right hexp htiltedNonneg
        _ = Real.exp (-(3 / 5 : ℝ) * a) *
              coordinateTiltedTailDensity b j x := by
          rw [coordinateTiltedTailDensity_eq_of_mem hj]
        _ ≤ Real.exp (-(3 / 5 : ℝ) * a) * tailSum x := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
          exact Finset.single_le_sum
            (fun i _ => coordinateTiltedTailDensity_nonneg b i x)
            (Finset.mem_univ j)
    · simp only [Set.indicator, hx, ↓reduceIte]
      exact mul_nonneg (Real.exp_nonneg _) <|
        Finset.sum_nonneg fun j _ =>
          coordinateTiltedTailDensity_nonneg b j x
  have hintegral :
      (∫ x : Fin rows → ℝ,
          (halfGaussianTruncationSet a b).indicator
            halfGaussianProductDensity x) ≤
        ∫ x : Fin rows → ℝ,
          Real.exp (-(3 / 5 : ℝ) * a) * tailSum x := by
    apply integral_mono hleftIntegrable
      (htailSumIntegrable.const_mul _) hpointwise
  have htailIntegral :
      (∫ x : Fin rows → ℝ, tailSum x) =
        ∑ j : Fin rows,
          ∫ x : Fin rows → ℝ,
            coordinateTiltedTailDensity b j x := by
    exact integral_finsetSum Finset.univ fun j _ =>
      integrable_coordinateTiltedTailDensity b j
  rw [integral_indicator
      (measurableSet_halfGaussianTruncationSet (rows := rows) a b),
    integral_const_mul, htailIntegral] at hintegral
  have hcoordinate (j : Fin rows) :
      (∫ x : Fin rows → ℝ,
          coordinateTiltedTailDensity b j x) <
        (5 / 2 : ℝ) ^ shape *
          Real.exp (-(2 / 5 : ℝ) * b ^ 2) := by
    rw [integral_coordinateTiltedTailDensity]
    have htail :=
      integral_abs_ge_tiltedHalfGaussianDensity_lt hb hscale
    have hsqrtNonneg : 0 ≤ Real.sqrt (5 / 2 : ℝ) :=
      Real.sqrt_nonneg _
    calc
      (∫ t : ℝ in {t | b ≤ |t|},
          tiltedHalfGaussianDensity t) *
            Real.sqrt (5 / 2 : ℝ) ^ (rows - 1) <
          (Real.sqrt (5 / 2 : ℝ) *
              Real.exp (-(2 / 5 : ℝ) * b ^ 2)) *
            Real.sqrt (5 / 2 : ℝ) ^ (rows - 1) := by
        exact mul_lt_mul_of_pos_right htail (by positivity)
      _ = (5 / 2 : ℝ) ^ shape *
          Real.exp (-(2 / 5 : ℝ) * b ^ 2) := by
        rw [mul_assoc, mul_comm (Real.exp _), ← mul_assoc,
          ← pow_succ']
        rw [show (rows - 1) + 1 = rows by omega,
          hrows, pow_mul,
          Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 2)]
  have hsum :
      (∑ j : Fin rows,
          ∫ x : Fin rows → ℝ,
            coordinateTiltedTailDensity b j x) <
        rows * ((5 / 2 : ℝ) ^ shape *
          Real.exp (-(2 / 5 : ℝ) * b ^ 2)) := by
    calc
      (∑ j : Fin rows,
          ∫ x : Fin rows → ℝ,
            coordinateTiltedTailDensity b j x) <
          ∑ _j : Fin rows,
            ((5 / 2 : ℝ) ^ shape *
              Real.exp (-(2 / 5 : ℝ) * b ^ 2)) :=
        Finset.sum_lt_sum_of_nonempty (by
          exact ⟨⟨0, hrowspos⟩, Finset.mem_univ _⟩)
          (fun j _ => hcoordinate j)
      _ = rows * ((5 / 2 : ℝ) ^ shape *
          Real.exp (-(2 / 5 : ℝ) * b ^ 2)) := by
        simp [mul_comm]
  calc
    (∫ x : Fin rows → ℝ in halfGaussianTruncationSet a b,
        halfGaussianProductDensity x) ≤
        Real.exp (-(3 / 5 : ℝ) * a) *
          ∑ j : Fin rows,
            ∫ x : Fin rows → ℝ,
              coordinateTiltedTailDensity b j x := hintegral
    _ < Real.exp (-(3 / 5 : ℝ) * a) *
        (rows * ((5 / 2 : ℝ) ^ shape *
          Real.exp (-(2 / 5 : ℝ) * b ^ 2))) :=
      mul_lt_mul_of_pos_left hsum (Real.exp_pos _)
    _ = rows * (5 / 2 : ℝ) ^ shape *
        Real.exp (-(3 * a + 2 * b ^ 2) / 5) := by
      rw [show
          -(3 * a + 2 * b ^ 2) / 5 =
            -(3 / 5 : ℝ) * a + -(2 / 5 : ℝ) * b ^ 2 by ring,
        Real.exp_add]
      ring

/--
The squared-radius tail of the normalized rows-dimensional half-Gaussian is
the integer-shape `Gamma(shape, 1)` survival function.
-/
theorem integral_halfGaussianRadialDensity_tail
    (hrows : rows = 2 * shape) (hshape : 0 < shape)
    {a : ℝ} (ha : 0 ≤ a) :
    (∫ x : EuclideanSpace ℝ (Fin rows) in
        {x | a < ‖x‖ ^ 2}, halfGaussianRadialDensity (shape := shape) x) =
      gammaSurvivalNat shape a := by
  let : Nonempty (Fin rows) := ⟨⟨0, by omega⟩⟩
  let radial : ℝ → ℝ :=
    fun r =>
      if a < r ^ 2 then
        Real.pi⁻¹ ^ shape * Real.exp (-r ^ 2)
      else 0
  have htailMeas :
      MeasurableSet
        {x : EuclideanSpace ℝ (Fin rows) | a < ‖x‖ ^ 2} := by
    exact measurableSet_lt measurable_const
      (continuous_norm.pow 2).measurable
  rw [← integral_indicator htailMeas]
  have hradial :
      (fun x : EuclideanSpace ℝ (Fin rows) =>
          {x | a < ‖x‖ ^ 2}.indicator
            (halfGaussianRadialDensity (shape := shape)) x) =
        fun x => radial ‖x‖ := by
    funext x
    simp only [Set.indicator, Set.mem_ofPred_eq, radial,
      halfGaussianRadialDensity]
  rw [hradial, integral_fun_norm_addHaar volume radial]
  have hdim :
      Module.finrank ℝ (EuclideanSpace ℝ (Fin rows)) = 2 * shape := by
    simpa using hrows
  have hvol :=
    InnerProductSpace.volume_ball_of_dim_even
      (E := EuclideanSpace ℝ (Fin rows))
      hdim (0 : EuclideanSpace ℝ (Fin rows)) 1
  have hvolReal :
      volume.real
          (Metric.ball (0 : EuclideanSpace ℝ (Fin rows)) 1) =
        Real.pi ^ shape / (shape : ℕ).factorial := by
    rw [Measure.real, hvol]
    norm_num
    positivity
  rw [hdim, hvolReal]
  simp only [nsmul_eq_mul, smul_eq_mul]
  rw [← hrows]
  have hsqrtIff {r : ℝ} (hr : 0 < r) :
      a < r ^ 2 ↔ Real.sqrt a < r := by
    constructor
    · intro har
      nlinarith [Real.sq_sqrt ha, Real.sqrt_nonneg a]
    · intro hsr
      nlinarith [Real.sq_sqrt ha, Real.sqrt_nonneg a]
  have hradialIntegral :
      (∫ r : ℝ in Set.Ioi 0, r ^ (rows - 1) * radial r) =
        Real.pi⁻¹ ^ shape *
          ∫ r : ℝ in Set.Ioi (Real.sqrt a),
            r ^ (rows - 1) * Real.exp (-r ^ 2) := by
    calc
      (∫ r : ℝ in Set.Ioi 0, r ^ (rows - 1) * radial r) =
          ∫ r : ℝ in Set.Ioi 0,
            (Set.Ioi (Real.sqrt a)).indicator
              (fun r =>
                Real.pi⁻¹ ^ shape *
                  (r ^ (rows - 1) * Real.exp (-r ^ 2))) r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        have hr0 := Set.mem_Ioi.mp hr
        simp only [radial]
        simp only [Set.indicator, Set.mem_Ioi]
        by_cases har : a < r ^ 2
        · rw [if_pos har, if_pos ((hsqrtIff hr0).mp har)]
          ring
        · rw [if_neg har, if_neg (not_congr (hsqrtIff hr0) |>.mp har)]
          ring
      _ = ∫ r : ℝ in
          Set.Ioi 0 ∩ Set.Ioi (Real.sqrt a),
            Real.pi⁻¹ ^ shape *
              (r ^ (rows - 1) * Real.exp (-r ^ 2)) := by
        rw [setIntegral_indicator measurableSet_Ioi]
      _ = ∫ r : ℝ in Set.Ioi (Real.sqrt a),
            Real.pi⁻¹ ^ shape *
              (r ^ (rows - 1) * Real.exp (-r ^ 2)) := by
        rw [Set.inter_eq_right.mpr]
        intro r hr
        exact (Real.sqrt_nonneg a).trans_lt (Set.mem_Ioi.mp hr)
      _ = Real.pi⁻¹ ^ shape *
          ∫ r : ℝ in Set.Ioi (Real.sqrt a),
            r ^ (rows - 1) * Real.exp (-r ^ 2) := by
        rw [integral_const_mul]
  rw [hradialIntegral,
    integral_pow_even_sub_one_exp_neg_sq_Ioi hrows hshape ha]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hfactorial :
      (((shape : ℕ).factorial : ℝ)) =
        shape * (((shape - 1) : ℕ).factorial : ℝ) := by
    rw [show (shape : ℕ) = (shape - 1) + 1 by omega,
      Nat.factorial_succ]
    norm_num
  have hgamma :
      (1 / (((shape - 1) : ℕ).factorial : ℝ)) *
          ∫ t : ℝ in Set.Ioi a,
            t ^ (shape - 1) * Real.exp (-t) =
        gammaSurvivalNat shape a := by
    have hbase := integral_pow_mul_exp_neg_Ioi (shape - 1) ha
    calc
      (1 / (((shape - 1) : ℕ).factorial : ℝ)) *
          ∫ t : ℝ in Set.Ioi a,
            t ^ (shape - 1) * Real.exp (-t) =
          ∫ t : ℝ in Set.Ioi a,
            Real.exp (-t) * t ^ (shape - 1) /
              (shape - 1).factorial := by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t _
        ring
      _ = gammaSurvivalNat shape a := by
        simpa [show shape - 1 + 1 = shape by omega] using hbase
  have hpiCancel :
      Real.pi ^ shape * Real.pi⁻¹ ^ shape = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hpi, one_pow]
  rw [← hgamma]
  rw [hrows]
  field_simp [hpi]
  rw [hfactorial]
  ring_nf
  rw [show
      ((↑(shape * 2) * Real.pi ^ shape * Real.pi⁻¹ ^ shape *
          ∫ t : ℝ in Set.Ioi a,
            t ^ (shape - 1) * Real.exp (-t)) *
            ((shape - 1).factorial : ℝ)) =
        (Real.pi ^ shape * Real.pi⁻¹ ^ shape) *
          (↑(shape * 2) *
            (∫ t : ℝ in Set.Ioi a,
              t ^ (shape - 1) * Real.exp (-t)) *
            ((shape - 1).factorial : ℝ)) by ring]
  rw [hpiCancel]
  norm_num [Nat.cast_mul]
  ring

/--
Function-space form of the `Gamma(shape, 1)` radial identity.  This is the
interface consumed by the lattice-cell tensorization.
-/
theorem integral_halfGaussianProductDensity_tail
    (hrows : rows = 2 * shape) (hshape : 0 < shape)
    {a : ℝ} (ha : 0 ≤ a) :
    (∫ x : Fin rows → ℝ in
        {x | a < ∑ i, (x i) ^ 2}, halfGaussianProductDensity x) =
      gammaSurvivalNat shape a := by
  let tailE :
      Set (EuclideanSpace ℝ (Fin rows)) :=
    {x | a < ‖x‖ ^ 2}
  have htailE : MeasurableSet tailE := by
    exact measurableSet_lt measurable_const
      (continuous_norm.pow 2).measurable
  have hcomp :
      (fun x : Fin rows → ℝ =>
          tailE.indicator (halfGaussianRadialDensity (shape := shape))
            (WithLp.toLp 2 x)) =
        fun x =>
          {x | a < ∑ i, (x i) ^ 2}.indicator
            halfGaussianProductDensity x := by
    funext x
    simp only [tailE, Set.indicator, Set.mem_ofPred_eq,
      EuclideanSpace.real_norm_sq_eq,
      halfGaussianProductDensity_eq_radial hrows]
  have htransport :=
    (PiLp.volume_preserving_toLp (Fin rows)).integral_comp
      (MeasurableEquiv.toLp 2 _).measurableEmbedding
      (tailE.indicator (halfGaussianRadialDensity (shape := shape)))
  rw [hcomp, integral_indicator (by
    exact measurableSet_lt measurable_const
      (Finset.measurable_sum _ fun i _ =>
        ((measurable_pi_apply i).pow_const 2))),
    integral_indicator htailE] at htransport
  exact htransport.trans
    (integral_halfGaussianRadialDensity_tail hrows hshape ha)

end HalfGaussianEven
end Probability
end CertifiedJL
