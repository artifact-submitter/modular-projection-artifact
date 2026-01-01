import CertifiedJL.Analysis.Peano.PeanoKLaw

/-!
# Exact second Peano kernel for the Peano K law

This file proves the fifth-stop-loss identity, the closed standard-Gaussian
formula, reflection, and global nonnegativity required by U6a.
-/

open Filter MeasureTheory Set
open ProbabilityTheory
open scoped Interval Topology

namespace CertifiedJL

theorem integral_max_sub_mul_max_sub_cube (t y : ℝ) :
    (∫ x : ℝ, max (x - t) 0 * (max (y - x) 0) ^ 3) =
      (max (y - t) 0) ^ 5 / 20 := by
  let f : ℝ → ℝ := fun u => max u 0 * (max ((y - t) - u) 0) ^ 3
  calc
    (∫ x : ℝ, max (x - t) 0 * (max (y - x) 0) ^ 3) =
        ∫ u : ℝ, f u := by
      have h := (integral_add_right_eq_self
        (fun x : ℝ => max (x - t) 0 * (max (y - x) 0) ^ 3) t
        (μ := volume)).symm
      rw [h]
      apply integral_congr_ae
      filter_upwards [] with u
      dsimp [f]
      rw [add_sub_cancel_right]
      rw [show y - (u + t) = y - t - u by ring]
    _ = ∫ u in Ici (0 : ℝ), |u| ^ 1 * (max ((y - t) - u) 0) ^ 3 := by
      rw [← integral_indicator measurableSet_Ici]
      apply integral_congr_ae
      filter_upwards [] with u
      dsimp [f]
      by_cases hu : 0 ≤ u
      · rw [indicator_of_mem (show u ∈ Ici (0 : ℝ) from hu), max_eq_left hu,
          abs_of_nonneg hu]
        simp
      · rw [indicator_of_notMem (show u ∉ Ici (0 : ℝ) from hu),
          max_eq_right (le_of_not_ge hu)]
        simp
    _ = peanoBetaCoeff 1 * (max (y - t) 0) ^ 5 := by
      simpa using integral_Ici_absPow_mul_cubicStopLoss 1 (y - t)
    _ = (max (y - t) 0) ^ 5 / 20 := by
      norm_num [peanoBetaCoeff]
      ring

private theorem integrable_max_sub_mul_max_sub_cube (t y : ℝ) :
    Integrable (fun x : ℝ => max (x - t) 0 * (max (y - x) 0) ^ 3) := by
  let g : ℝ → ℝ := fun x => max (x - t) 0 * (max (y - x) 0) ^ 3
  have hcompact : IntegrableOn g (Icc t (max y t)) :=
    ContinuousOn.integrableOn_compact isCompact_Icc (by
      dsimp only [g]
      fun_prop)
  have hind : Integrable ((Icc t (max y t)).indicator g) volume :=
    hcompact.integrable_indicator measurableSet_Icc
  refine hind.congr (ae_of_all _ fun x => ?_)
  by_cases hxt : t ≤ x
  · by_cases hxy : x ≤ max y t
    · rw [indicator_of_mem (show x ∈ Icc t (max y t) from ⟨hxt, hxy⟩)]
    · rw [indicator_of_notMem (show x ∉ Icc t (max y t) by simp [hxy])]
      have hyx : y - x ≤ 0 := by linarith [le_max_left y t]
      simp only [max_eq_right hyx, zero_pow (by norm_num : (3 : ℕ) ≠ 0), mul_zero]
  · rw [indicator_of_notMem (show x ∉ Icc t (max y t) by simp [hxt])]
    have hxt' : x - t ≤ 0 := sub_nonpos.mpr (le_of_not_ge hxt)
    simp only [max_eq_right hxt', zero_mul]

private theorem integrable_firstStopLoss_mul_cubicStopLoss
    (μ : Measure ℝ) [SFinite μ] (t : ℝ)
    (hfive : Integrable (fun y : ℝ => (max (y - t) 0) ^ 5) μ) :
    Integrable (fun x : ℝ => max (x - t) 0 *
      (∫ y, (max (y - x) 0) ^ 3 ∂μ)) := by
  let F : ℝ → ℝ → ℝ := fun x y =>
    max (x - t) 0 * (max (y - x) 0) ^ 3
  have hFsm : AEStronglyMeasurable (Function.uncurry F) (volume.prod μ) :=
    (by fun_prop : StronglyMeasurable (Function.uncurry F)).aestronglyMeasurable
  have hFint : Integrable (Function.uncurry F) (volume.prod μ) := by
    apply (integrable_prod_iff' hFsm).mpr
    constructor
    · exact ae_of_all _ fun y => integrable_max_sub_mul_max_sub_cube t y
    · refine (hfive.const_mul (1 / 20 : ℝ)).congr (ae_of_all _ fun y => ?_)
      change (1 / 20 : ℝ) * (max (y - t) 0) ^ 5 =
        ∫ x : ℝ, ‖F x y‖
      rw [show (fun x : ℝ => ‖F x y‖) = (fun x => F x y) by
        funext x
        rw [Real.norm_eq_abs, abs_of_nonneg]
        exact mul_nonneg (le_max_right _ _) (pow_nonneg (le_max_right _ _) _)]
      dsimp only [F]
      rw [integral_max_sub_mul_max_sub_cube]
      ring
  refine hFint.integral_prod_left.congr (ae_of_all _ fun x => ?_)
  dsimp only [Function.uncurry_apply_pair, F]
  rw [integral_const_mul]

private theorem integral_firstStopLoss_mul_cubicStopLoss
    (μ : Measure ℝ) [SFinite μ] (t : ℝ)
    (hfive : Integrable (fun y : ℝ => (max (y - t) 0) ^ 5) μ) :
    (∫ x : ℝ, max (x - t) 0 *
        (∫ y, (max (y - x) 0) ^ 3 ∂μ)) =
      (1 / 20 : ℝ) * ∫ y, (max (y - t) 0) ^ 5 ∂μ := by
  let F : ℝ → ℝ → ℝ := fun x y =>
    max (x - t) 0 * (max (y - x) 0) ^ 3
  have hFsm : AEStronglyMeasurable (Function.uncurry F) (volume.prod μ) :=
    (by fun_prop : StronglyMeasurable (Function.uncurry F)).aestronglyMeasurable
  have hFint : Integrable (Function.uncurry F) (volume.prod μ) := by
    apply (integrable_prod_iff' hFsm).mpr
    constructor
    · exact ae_of_all _ fun y => integrable_max_sub_mul_max_sub_cube t y
    · refine (hfive.const_mul (1 / 20 : ℝ)).congr (ae_of_all _ fun y => ?_)
      change (1 / 20 : ℝ) * (max (y - t) 0) ^ 5 =
        ∫ x : ℝ, ‖F x y‖
      rw [show (fun x : ℝ => ‖F x y‖) = (fun x => F x y) by
        funext x
        rw [Real.norm_eq_abs, abs_of_nonneg]
        exact mul_nonneg (le_max_right _ _) (pow_nonneg (le_max_right _ _) _)]
      dsimp only [F]
      rw [integral_max_sub_mul_max_sub_cube]
      ring
  calc
    (∫ x : ℝ, max (x - t) 0 *
        (∫ y, (max (y - x) 0) ^ 3 ∂μ)) =
        ∫ x, ∫ y, F x y ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      change max (x - t) 0 * (∫ y, (max (y - x) 0) ^ 3 ∂μ) =
        ∫ y, max (x - t) 0 * (max (y - x) 0) ^ 3 ∂μ
      rw [integral_const_mul]
    _ = ∫ y, (∫ x, F x y) ∂μ :=
      integral_integral_swap (μ := volume) (ν := μ) hFint
    _ = ∫ y, (max (y - t) 0) ^ 5 / 20 ∂μ := by
      apply integral_congr_ae (μ := μ)
      exact ae_of_all _ fun y => integral_max_sub_mul_max_sub_cube t y
    _ = (1 / 20 : ℝ) * ∫ y, (max (y - t) 0) ^ 5 ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      ring

private theorem integrable_fifth_stoploss_of_pows
    {μ : Measure ℝ} {t : ℝ}
    (h0 : Integrable (fun _ : ℝ => (1 : ℝ)) μ)
    (h5 : Integrable (fun y : ℝ => y ^ 5) μ) :
    Integrable (fun y : ℝ => (max (y - t) 0) ^ 5) μ := by
  have h5abs : Integrable (fun y : ℝ => |y| ^ 5) μ := by
    simpa [Real.norm_eq_abs, abs_pow] using h5.norm
  have hmajorant : Integrable
      (fun y : ℝ => 16 * (|y| ^ 5 + |t| ^ 5)) μ := by
    refine ((h5abs.add (h0.const_mul (|t| ^ 5))).const_mul 16).congr
      (ae_of_all _ fun y => ?_)
    simp
  refine hmajorant.mono' (by fun_prop) ?_
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_max_right _ _) 5)]
  have hmax : max (y - t) 0 ≤ |y| + |t| :=
    max_le (by linarith [le_abs_self y, neg_le_abs t]) (by positivity)
  calc
    max (y - t) 0 ^ 5 ≤ (|y| + |t|) ^ 5 :=
      pow_le_pow_left₀ (le_max_right _ _) hmax 5
    _ ≤ 2 ^ (5 - 1) * (|y| ^ 5 + |t| ^ 5) :=
      add_pow_le (abs_nonneg y) (abs_nonneg t) 5
    _ = 16 * (|y| ^ 5 + |t| ^ 5) := by norm_num

theorem firstStopLossDifference_standardGaussian_peanoKMeasure_eq_fifth
    (t : ℝ) :
    firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t =
      (∫ y, max (y - t) 0 ∂(gaussianReal 0 1)) -
        (1 / 10 : ℝ) *
          ((∫ y, (max (y - t) 0) ^ 5 ∂(gaussianReal 0 1)) -
            ∫ y, (max (y - t) 0) ^ 5 ∂standardRademacherMeasure) := by
  have hGfive := integrable_fifth_stoploss_of_pows
    (integrable_standardGaussian_pow 0 |>.congr (ae_of_all _ fun y => by simp))
    (integrable_standardGaussian_pow 5)
    (t := t)
  have hRfive := integrable_fifth_stoploss_of_pows
    (integrable_standardRademacher_pow 0 |>.congr (ae_of_all _ fun y => by simp))
    (integrable_standardRademacher_pow 5)
    (t := t)
  have hGprod := integral_firstStopLoss_mul_cubicStopLoss
    (gaussianReal 0 1) t hGfive
  have hRprod := integral_firstStopLoss_mul_cubicStopLoss
    standardRademacherMeasure t hRfive
  unfold firstStopLossDifference
  change (∫ y, max (y - t) 0 ∂(gaussianReal 0 1)) -
      (∫ y, max (y - t) 0 ∂positiveDensityMeasure peanoKDensity) = _
  rw [integral_positiveDensityMeasure peanoKDensity
    stronglyMeasurable_peanoKDensity.measurable peanoKDensity_nonneg]
  change (∫ y, max (y - t) 0 ∂(gaussianReal 0 1)) -
      ∫ x, peanoKDensity x * max (x - t) 0 = _
  rw [show (fun x : ℝ => peanoKDensity x * max (x - t) 0) =
      fun x => 2 * (max (x - t) 0 *
        ((∫ y, (max (y - x) 0) ^ 3 ∂(gaussianReal 0 1)) -
          ∫ y, (max (y - x) 0) ^ 3 ∂standardRademacherMeasure)) by
    funext x
    rw [peanoKDensity_eq_two_mul_cubicStopLossDifference]
    unfold cubicStopLossDifference
    ring]
  rw [show (fun x : ℝ => 2 * (max (x - t) 0 *
      ((∫ y, (max (y - x) 0) ^ 3 ∂(gaussianReal 0 1)) -
        ∫ y, (max (y - x) 0) ^ 3 ∂standardRademacherMeasure))) =
      (fun x => 2 * (max (x - t) 0 *
        (∫ y, (max (y - x) 0) ^ 3 ∂(gaussianReal 0 1))) -
        2 * (max (x - t) 0 *
          (∫ y, (max (y - x) 0) ^ 3 ∂standardRademacherMeasure))) by
    funext x; ring]
  rw [integral_sub]
  · rw [integral_const_mul, integral_const_mul, hGprod, hRprod]
    ring
  · exact (integrable_firstStopLoss_mul_cubicStopLoss
      (gaussianReal 0 1) t hGfive).const_mul 2
  · exact (integrable_firstStopLoss_mul_cubicStopLoss
      standardRademacherMeasure t hRfive).const_mul 2

private theorem integrable_pow_mul_standardGaussianDensity (n : ℕ) :
    Integrable (fun y : ℝ => y ^ n * Probability.standardGaussianDensity y) := by
  have h := integrable_standardGaussian_pow n
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero 0 (by norm_num)] at h
  rw [integrable_withDensity_iff_integrable_smul'
    (ProbabilityTheory.measurable_gaussianPDF 0 1)
    (ae_of_all _ fun _ => ProbabilityTheory.gaussianPDF_lt_top)] at h
  have h' : Integrable (fun y : ℝ =>
      ProbabilityTheory.gaussianPDFReal 0 1 y * y ^ n) := by
    simpa [smul_eq_mul] using h
  refine h'.congr (ae_of_all _ fun y => ?_)
  rw [Probability.standardGaussianDensity_eq_gaussianPDFReal]
  ring

private theorem tendsto_pow_mul_standardGaussianDensity_atTop (n : ℕ) :
    Tendsto (fun y : ℝ => y ^ n * Probability.standardGaussianDensity y)
      atTop (𝓝 0) := by
  have hraw : Tendsto
      (fun y : ℝ => y ^ (n : ℝ) * Real.exp (-(1 / 2 : ℝ) * y ^ 2))
      atTop (𝓝 0) :=
    (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg (by norm_num : (0 : ℝ) < 1 / 2)
      (n : ℝ)).tendsto_zero_of_tendsto
        (Real.tendsto_exp_atBot.comp
          (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-(1 / 2 : ℝ)) < 0)))
  have hpow : Tendsto
      (fun y : ℝ => y ^ n * Real.exp (-(1 / 2 : ℝ) * y ^ 2))
      atTop (𝓝 0) := by
    apply hraw.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [Real.rpow_natCast]
  have hscaled := hpow.const_mul (Real.sqrt (2 * Real.pi))⁻¹
  have heq : (fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
      (y ^ n * Real.exp (-(1 / 2 : ℝ) * y ^ 2))) =ᶠ[atTop]
      (fun y => y ^ n * Probability.standardGaussianDensity y) := by
    filter_upwards [] with y
    unfold Probability.standardGaussianDensity
    ring_nf
  have hscaled' := hscaled.congr' heq
  simpa only [mul_zero] using hscaled'

private theorem hasDerivAt_standardGaussianDensity_u6 (t : ℝ) :
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

private theorem integral_Ioi_standardGaussianDensity_pow_add_two
    (n : ℕ) (t : ℝ) :
    (∫ y in Ioi t, y ^ (n + 2) * Probability.standardGaussianDensity y) =
      t ^ (n + 1) * Probability.standardGaussianDensity t +
        (n + 1 : ℝ) *
          ∫ y in Ioi t, y ^ n * Probability.standardGaussianDensity y := by
  let F : ℝ → ℝ := fun y =>
    -(y ^ (n + 1) * Probability.standardGaussianDensity y)
  have hderiv : ∀ y ∈ Ici t, HasDerivAt F
      (y ^ (n + 2) * Probability.standardGaussianDensity y -
        (n + 1 : ℝ) * (y ^ n * Probability.standardGaussianDensity y)) y := by
    intro y _
    unfold F
    have h := (((hasDerivAt_id y).pow (n + 1)).mul
      (hasDerivAt_standardGaussianDensity_u6 y)).neg
    change HasDerivAt (fun z : ℝ =>
      -(z ^ (n + 1) * Probability.standardGaussianDensity z)) _ y at h
    convert h using 1
    simp only [Pi.pow_apply, id_eq, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring
  have hint : IntegrableOn (fun y : ℝ =>
      y ^ (n + 2) * Probability.standardGaussianDensity y -
        (n + 1 : ℝ) * (y ^ n * Probability.standardGaussianDensity y)) (Ioi t) :=
    (integrable_pow_mul_standardGaussianDensity (n + 2)).integrableOn.sub
      ((integrable_pow_mul_standardGaussianDensity n).const_mul (n + 1 : ℝ)).integrableOn
  have hlim : Tendsto F atTop (𝓝 0) := by
    simpa only [F, neg_zero] using
      (tendsto_pow_mul_standardGaussianDensity_atTop (n + 1)).neg
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  rw [integral_sub
    (integrable_pow_mul_standardGaussianDensity (n + 2)).integrableOn
    ((integrable_pow_mul_standardGaussianDensity n).const_mul (n + 1 : ℝ)).integrableOn,
    integral_const_mul] at hftc
  dsimp only [F] at hftc
  linarith

private theorem integral_Ioi_mul_standardGaussianDensity (t : ℝ) :
    (∫ y in Ioi t, y * Probability.standardGaussianDensity y) =
      Probability.standardGaussianDensity t := by
  have hderiv : ∀ y ∈ Ici t, HasDerivAt
      (fun z : ℝ => -Probability.standardGaussianDensity z)
      (y * Probability.standardGaussianDensity y) y := by
    intro y _
    have h := (hasDerivAt_standardGaussianDensity_u6 y).neg
    change HasDerivAt (fun z : ℝ => -Probability.standardGaussianDensity z) _ y at h
    convert h using 1
    ring
  have hint : IntegrableOn
      (fun y : ℝ => y * Probability.standardGaussianDensity y) (Ioi t) := by
    simpa only [pow_one] using
      (integrable_pow_mul_standardGaussianDensity 1).integrableOn
  have hlim : Tendsto (fun z : ℝ => -Probability.standardGaussianDensity z)
      atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul, neg_zero] using
      (tendsto_pow_mul_standardGaussianDensity_atTop 0).neg
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  simpa using hftc

private theorem integral_Ioi_sq_standardGaussianDensity (t : ℝ) :
    (∫ y in Ioi t, y ^ 2 * Probability.standardGaussianDensity y) =
      t * Probability.standardGaussianDensity t +
        Probability.standardGaussianTail t := by
  rw [integral_Ioi_standardGaussianDensity_pow_add_two 0]
  simp [Probability.standardGaussianTail]

private theorem integral_Ioi_cube_standardGaussianDensity (t : ℝ) :
    (∫ y in Ioi t, y ^ 3 * Probability.standardGaussianDensity y) =
      (t ^ 2 + 2) * Probability.standardGaussianDensity t := by
  rw [integral_Ioi_standardGaussianDensity_pow_add_two 1,
    show (fun y : ℝ => y ^ 1 * Probability.standardGaussianDensity y) =
      fun y => y * Probability.standardGaussianDensity y by funext y; rw [pow_one],
    integral_Ioi_mul_standardGaussianDensity]
  ring

private theorem integral_Ioi_fourth_standardGaussianDensity (t : ℝ) :
    (∫ y in Ioi t, y ^ 4 * Probability.standardGaussianDensity y) =
      (t ^ 3 + 3 * t) * Probability.standardGaussianDensity t +
        3 * Probability.standardGaussianTail t := by
  rw [integral_Ioi_standardGaussianDensity_pow_add_two 2,
    integral_Ioi_sq_standardGaussianDensity]
  ring

private theorem integral_Ioi_fifth_standardGaussianDensity (t : ℝ) :
    (∫ y in Ioi t, y ^ 5 * Probability.standardGaussianDensity y) =
      (t ^ 4 + 4 * t ^ 2 + 8) * Probability.standardGaussianDensity t := by
  rw [integral_Ioi_standardGaussianDensity_pow_add_two 3,
    integral_Ioi_cube_standardGaussianDensity]
  ring

theorem integral_standardGaussian_fifth_stopLoss (t : ℝ) :
    (∫ y, (max (y - t) 0) ^ 5 ∂(gaussianReal 0 1)) =
      (t ^ 4 + 9 * t ^ 2 + 8) * Probability.standardGaussianDensity t -
        (t ^ 5 + 10 * t ^ 3 + 15 * t) * Probability.standardGaussianTail t := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  rw [← Probability.standardGaussianDensity_eq_gaussianPDFReal]
  change (∫ y : ℝ, Probability.standardGaussianDensity y *
      (max (y - t) 0) ^ 5) = _
  calc
    (∫ y : ℝ, Probability.standardGaussianDensity y *
        (max (y - t) 0) ^ 5) =
        ∫ y in Ioi t, (y - t) ^ 5 *
          Probability.standardGaussianDensity y := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hy : t < y
      · rw [indicator_of_mem (show y ∈ Ioi t from hy),
          max_eq_left (sub_nonneg.mpr hy.le)]
        ring
      · rw [indicator_of_notMem (show y ∉ Ioi t from hy),
          max_eq_right (sub_nonpos.mpr (le_of_not_gt hy))]
        simp
    _ = (t ^ 4 + 9 * t ^ 2 + 8) * Probability.standardGaussianDensity t -
        (t ^ 5 + 10 * t ^ 3 + 15 * t) * Probability.standardGaussianTail t := by
      let f0 : ℝ → ℝ := fun y => Probability.standardGaussianDensity y
      let f1 : ℝ → ℝ := fun y => y * Probability.standardGaussianDensity y
      let f2 : ℝ → ℝ := fun y => y ^ 2 * Probability.standardGaussianDensity y
      let f3 : ℝ → ℝ := fun y => y ^ 3 * Probability.standardGaussianDensity y
      let f4 : ℝ → ℝ := fun y => y ^ 4 * Probability.standardGaussianDensity y
      let f5 : ℝ → ℝ := fun y => y ^ 5 * Probability.standardGaussianDensity y
      have h0 : IntegrableOn f0 (Ioi t) := by
        simpa only [f0, pow_zero, one_mul] using
          (integrable_pow_mul_standardGaussianDensity 0).integrableOn
      have h1 : IntegrableOn f1 (Ioi t) := by
        simpa only [f1, pow_one] using
          (integrable_pow_mul_standardGaussianDensity 1).integrableOn
      have h2 : IntegrableOn f2 (Ioi t) :=
        (integrable_pow_mul_standardGaussianDensity 2).integrableOn
      have h3 : IntegrableOn f3 (Ioi t) :=
        (integrable_pow_mul_standardGaussianDensity 3).integrableOn
      have h4 : IntegrableOn f4 (Ioi t) :=
        (integrable_pow_mul_standardGaussianDensity 4).integrableOn
      have h5 : IntegrableOn f5 (Ioi t) :=
        (integrable_pow_mul_standardGaussianDensity 5).integrableOn
      have hpoly : (fun y : ℝ => (y - t) ^ 5 *
          Probability.standardGaussianDensity y) =
          fun y => ((((f5 y + (-5 * t) * f4 y) +
            (10 * t ^ 2) * f3 y) + (-10 * t ^ 3) * f2 y) +
            (5 * t ^ 4) * f1 y) + (-t ^ 5) * f0 y := by
        funext y
        dsimp only [f0, f1, f2, f3, f4, f5]
        ring
      have hc4 := h4.const_mul (-5 * t)
      have hc3 := h3.const_mul (10 * t ^ 2)
      have hc2 := h2.const_mul (-10 * t ^ 3)
      have hc1 := h1.const_mul (5 * t ^ 4)
      have hc0 := h0.const_mul (-t ^ 5)
      let g1 : ℝ → ℝ := fun y => f5 y + (-5 * t) * f4 y
      let g2 : ℝ → ℝ := fun y => g1 y + (10 * t ^ 2) * f3 y
      let g3 : ℝ → ℝ := fun y => g2 y + (-10 * t ^ 3) * f2 y
      let g4 : ℝ → ℝ := fun y => g3 y + (5 * t ^ 4) * f1 y
      have hg1 : IntegrableOn g1 (Ioi t) := by
        refine (h5.add hc4).congr (ae_restrict_mem measurableSet_Ioi |>.mono fun y _ => ?_)
        rfl
      have hg2 : IntegrableOn g2 (Ioi t) := by
        refine (hg1.add hc3).congr (ae_restrict_mem measurableSet_Ioi |>.mono fun y _ => ?_)
        rfl
      have hg3 : IntegrableOn g3 (Ioi t) := by
        refine (hg2.add hc2).congr (ae_restrict_mem measurableSet_Ioi |>.mono fun y _ => ?_)
        rfl
      have hg4 : IntegrableOn g4 (Ioi t) := by
        refine (hg3.add hc1).congr (ae_restrict_mem measurableSet_Ioi |>.mono fun y _ => ?_)
        rfl
      rw [hpoly]
      change (∫ y in Ioi t, g4 y + (-t ^ 5) * f0 y) = _
      rw [integral_add hg4 hc0]
      change (∫ y in Ioi t, g3 y + (5 * t ^ 4) * f1 y) + _ = _
      rw [integral_add hg3 hc1]
      change ((∫ y in Ioi t, g2 y + (-10 * t ^ 3) * f2 y) + _) + _ = _
      rw [integral_add hg2 hc2]
      change (((∫ y in Ioi t, g1 y + (10 * t ^ 2) * f3 y) + _) + _) + _ = _
      rw [integral_add hg1 hc3]
      change (((((∫ y in Ioi t, f5 y + (-5 * t) * f4 y) + _) + _) + _) + _) = _
      rw [integral_add h5 hc4,
        integral_const_mul, integral_const_mul, integral_const_mul,
        integral_const_mul, integral_const_mul]
      dsimp only [f0, f1, f2, f3, f4, f5]
      rw [integral_Ioi_fifth_standardGaussianDensity,
        integral_Ioi_fourth_standardGaussianDensity,
        integral_Ioi_cube_standardGaussianDensity,
        integral_Ioi_sq_standardGaussianDensity,
        integral_Ioi_mul_standardGaussianDensity]
      rw [show (∫ y in Ioi t, Probability.standardGaussianDensity y) =
        Probability.standardGaussianTail t by rfl]
      ring

theorem integral_standardGaussian_first_stopLoss (t : ℝ) :
    (∫ y, max (y - t) 0 ∂(gaussianReal 0 1)) =
      Probability.standardGaussianDensity t -
        t * Probability.standardGaussianTail t := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  rw [← Probability.standardGaussianDensity_eq_gaussianPDFReal]
  change (∫ y : ℝ, Probability.standardGaussianDensity y *
      max (y - t) 0) = _
  calc
    _ = ∫ y in Ioi t, (y - t) * Probability.standardGaussianDensity y := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hy : t < y
      · rw [indicator_of_mem (show y ∈ Ioi t from hy),
          max_eq_left (sub_nonneg.mpr hy.le)]
        ring
      · rw [indicator_of_notMem (show y ∉ Ioi t from hy),
          max_eq_right (sub_nonpos.mpr (le_of_not_gt hy))]
        simp
    _ = _ := by
      have h1 : IntegrableOn
          (fun y : ℝ => y * Probability.standardGaussianDensity y) (Ioi t) := by
        simpa only [pow_one] using
          (integrable_pow_mul_standardGaussianDensity 1).integrableOn
      have h0 : IntegrableOn Probability.standardGaussianDensity (Ioi t) :=
        Probability.integrable_standardGaussianDensity.integrableOn
      rw [show (fun y : ℝ => (y - t) * Probability.standardGaussianDensity y) =
          fun y => y * Probability.standardGaussianDensity y -
            t * Probability.standardGaussianDensity y by funext y; ring,
        integral_sub h1 (h0.const_mul t), integral_const_mul,
        integral_Ioi_mul_standardGaussianDensity]
      rfl

theorem integral_standardRademacher_fifth_stopLoss (t : ℝ) :
    (∫ y, (max (y - t) 0) ^ 5 ∂standardRademacherMeasure) =
      ((max ((1 : ℝ) - t) 0) ^ 5 +
        (max ((-1 : ℝ) - t) 0) ^ 5) / 2 := by
  rw [standardRademacherMeasure, integral_add_measure]
  · simp only [integral_smul_measure, integral_dirac]
    norm_num
    ring
  · exact (integrable_dirac
      (f := fun y : ℝ => (max (y - t) 0) ^ 5) (a := (-1 : ℝ))
      (by simp)).smul_measure (by norm_num)
  · exact (integrable_dirac
      (f := fun y : ℝ => (max (y - t) 0) ^ 5) (a := (1 : ℝ))
      (by simp)).smul_measure (by norm_num)

theorem firstStopLossDifference_standardGaussian_peanoKMeasure_of_nonneg
    {t : ℝ} (ht : 0 ≤ t) :
    firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t =
      (2 - 9 * t ^ 2 - t ^ 4) / 10 * Probability.standardGaussianDensity t +
        (t ^ 5 + 10 * t ^ 3 + 5 * t) / 10 *
          Probability.standardGaussianTail t +
        (max (1 - t) 0) ^ 5 / 20 := by
  rw [firstStopLossDifference_standardGaussian_peanoKMeasure_eq_fifth,
    integral_standardGaussian_first_stopLoss,
    integral_standardGaussian_fifth_stopLoss,
    integral_standardRademacher_fifth_stopLoss]
  rw [max_eq_right (show (-1 : ℝ) - t ≤ 0 by linarith)]
  simp only [zero_pow (by norm_num : (5 : ℕ) ≠ 0), add_zero]
  ring

private theorem integrable_first_stoploss_of_abs
    {μ : Measure ℝ} [IsFiniteMeasure μ] (t : ℝ)
    (habs : Integrable (fun y : ℝ => |y|) μ) :
    Integrable (fun y : ℝ => max (y - t) 0) μ := by
  have hmajorant : Integrable (fun y : ℝ => |y| + |t|) μ :=
    habs.add (integrable_const (|t| : ℝ))
  refine hmajorant.mono' (by fun_prop) ?_
  filter_upwards [] with y
  calc
    ‖max (y - t) 0‖ = max (y - t) 0 := Real.norm_of_nonneg (le_max_right _ _)
    _ ≤ |y| + |t| := max_le
      (by linarith [le_abs_self y, neg_le_abs t])
      (add_nonneg (abs_nonneg y) (abs_nonneg t))

private theorem integral_first_stoploss_neg_eq_lower
    (μ : Measure ℝ) (hmap : Measure.map (fun y : ℝ => -y) μ = μ)
    (t : ℝ) (hint : Integrable (fun y : ℝ => max (y + t) 0) μ) :
    (∫ y, max (y + t) 0 ∂μ) = ∫ y, max (t - y) 0 ∂μ := by
  let f : ℝ → ℝ := fun y => max (y + t) 0
  have hfmap : Integrable f (Measure.map (fun y : ℝ => -y) μ) := by
    rw [hmap]
    exact hint
  calc
    (∫ y, max (y + t) 0 ∂μ) =
        ∫ y, f y ∂(Measure.map (fun y : ℝ => -y) μ) := by rw [hmap]
    _ = ∫ y, f (-y) ∂μ :=
      integral_map (μ := μ) (φ := fun y : ℝ => -y)
        (by fun_prop) hfmap.aestronglyMeasurable
    _ = ∫ y, max (t - y) 0 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with y
      dsimp only [f]
      rw [show -y + t = t - y by ring]

private theorem integral_id_peanoKMeasure :
    (∫ y : ℝ, y ∂peanoKMeasure) = 0 := by
  have hid : Integrable (fun y : ℝ => y) peanoKMeasure := by
    refine (integrable_absPow_peanoKMeasure 1).mono' (by fun_prop) ?_
    filter_upwards [] with y
    simp [Real.norm_eq_abs]
  have hmapInt : (∫ y : ℝ, y ∂peanoKMeasure) =
      ∫ y : ℝ, -y ∂peanoKMeasure := by
    calc
      _ = ∫ y : ℝ, y ∂(peanoKMeasure.map (fun y : ℝ => -y)) := by
        rw [peanoKMeasure_map_neg]
      _ = ∫ y : ℝ, -y ∂peanoKMeasure := by
        rw [integral_map]
        · fun_prop
        · rw [peanoKMeasure_map_neg]
          exact hid.aestronglyMeasurable
  rw [integral_neg] at hmapInt
  linarith

theorem firstStopLossDifference_standardGaussian_peanoKMeasure_neg (t : ℝ) :
    firstStopLossDifference (gaussianReal 0 1) peanoKMeasure (-t) =
      firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t := by
  have hGabs : Integrable (fun y : ℝ => |y|) (gaussianReal 0 1) := by
    simpa [Real.norm_eq_abs] using (integrable_standardGaussian_pow 1).norm
  have hKabs : Integrable (fun y : ℝ => |y|) peanoKMeasure := by
    simpa only [pow_one] using integrable_absPow_peanoKMeasure 1
  have hGid : Integrable (fun y : ℝ => y) (gaussianReal 0 1) :=
    by simpa only [pow_one] using integrable_standardGaussian_pow 1
  have hKid : Integrable (fun y : ℝ => y) peanoKMeasure := by
    refine hKabs.mono' (by fun_prop) ?_
    filter_upwards [] with y
    simp [Real.norm_eq_abs]
  have hGupper := integrable_first_stoploss_of_abs (-t) hGabs
  have hKupper := integrable_first_stoploss_of_abs (-t) hKabs
  have hGlower : Integrable (fun y : ℝ => max (t - y) 0)
      (gaussianReal 0 1) := by
    have hmajorant : Integrable (fun y : ℝ => |y| + |t|)
        (gaussianReal 0 1) := hGabs.add (integrable_const |t|)
    refine hmajorant.mono' (by fun_prop) ?_
    filter_upwards [] with y
    calc
      ‖max (t - y) 0‖ = max (t - y) 0 := Real.norm_of_nonneg (le_max_right _ _)
      _ ≤ |y| + |t| := max_le
        (by linarith [neg_le_abs y, le_abs_self t])
        (add_nonneg (abs_nonneg y) (abs_nonneg t))
  have hKlower : Integrable (fun y : ℝ => max (t - y) 0)
      peanoKMeasure := by
    have hmajorant : Integrable (fun y : ℝ => |y| + |t|) peanoKMeasure :=
      hKabs.add (integrable_const |t|)
    refine hmajorant.mono' (by fun_prop) ?_
    filter_upwards [] with y
    calc
      ‖max (t - y) 0‖ = max (t - y) 0 := Real.norm_of_nonneg (le_max_right _ _)
      _ ≤ |y| + |t| := max_le
        (by linarith [neg_le_abs y, le_abs_self t])
        (add_nonneg (abs_nonneg y) (abs_nonneg t))
  have hGreflect := integral_first_stoploss_neg_eq_lower
    (gaussianReal 0 1) (by simpa using (gaussianReal_map_neg (μ := 0) (v := 1)))
    t (by simpa only [sub_neg_eq_add] using hGupper)
  have hKreflect := integral_first_stoploss_neg_eq_lower
    peanoKMeasure peanoKMeasure_map_neg t
    (by simpa only [sub_neg_eq_add] using hKupper)
  have hdecomp (y : ℝ) : max (t - y) 0 = (t - y) + max (y - t) 0 := by
    by_cases hyt : y ≤ t
    · rw [max_eq_left (sub_nonneg.mpr hyt),
        max_eq_right (sub_nonpos.mpr hyt)]
      ring
    · have hty : t ≤ y := le_of_not_ge hyt
      rw [max_eq_right (sub_nonpos.mpr hty),
        max_eq_left (sub_nonneg.mpr hty)]
      ring
  have hGsum : (∫ y, max (t - y) 0 ∂(gaussianReal 0 1)) =
      t - (∫ y, y ∂(gaussianReal 0 1)) +
        ∫ y, max (y - t) 0 ∂(gaussianReal 0 1) := by
    rw [show (fun y : ℝ => max (t - y) 0) =
      fun y => (t - y) + max (y - t) 0 by funext y; exact hdecomp y]
    calc
      (∫ y, (t - y) + max (y - t) 0 ∂(gaussianReal 0 1)) =
          (∫ y, t - y ∂(gaussianReal 0 1)) +
            ∫ y, max (y - t) 0 ∂(gaussianReal 0 1) :=
        integral_add ((integrable_const t).sub hGid)
          (integrable_first_stoploss_of_abs t hGabs)
      _ = _ := by
        rw [integral_sub (integrable_const t) hGid, integral_const]
        simp
  have hKsum : (∫ y, max (t - y) 0 ∂peanoKMeasure) =
      t - (∫ y, y ∂peanoKMeasure) +
        ∫ y, max (y - t) 0 ∂peanoKMeasure := by
    rw [show (fun y : ℝ => max (t - y) 0) =
      fun y => (t - y) + max (y - t) 0 by funext y; exact hdecomp y]
    calc
      (∫ y, (t - y) + max (y - t) 0 ∂peanoKMeasure) =
          (∫ y, t - y ∂peanoKMeasure) +
            ∫ y, max (y - t) 0 ∂peanoKMeasure :=
        integral_add ((integrable_const t).sub hKid)
          (integrable_first_stoploss_of_abs t hKabs)
      _ = _ := by
        rw [integral_sub (integrable_const t) hKid, integral_const]
        simp
  unfold firstStopLossDifference
  simp only [sub_neg_eq_add]
  rw [hGreflect, hKreflect, hGsum, hKsum,
    integral_id_gaussianReal, integral_id_peanoKMeasure]
  simp

theorem firstStopLossDifference_standardGaussian_peanoKMeasure_nonneg
    (t : ℝ) :
    0 ≤ firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t := by
  have hhalf : ∀ u : ℝ, 0 ≤ u →
      0 ≤ firstStopLossDifference (gaussianReal 0 1) peanoKMeasure u := by
    intro u hu
    rw [firstStopLossDifference_standardGaussian_peanoKMeasure_of_nonneg hu]
    have hlast : 0 ≤ (max (1 - u) 0) ^ 5 / 20 := by positivity
    by_cases hu0 : u = 0
    · subst u
      norm_num
      nlinarith [Probability.standardGaussianDensity_nonneg 0]
    · have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
      have hmills := standardGaussian_rational_mills_lower hupos
      have hcore : 0 ≤
          (2 - 9 * u ^ 2 - u ^ 4) / 10 *
              Probability.standardGaussianDensity u +
            (u ^ 5 + 10 * u ^ 3 + 5 * u) / 10 *
              Probability.standardGaussianTail u := by
        nlinarith
      exact add_nonneg hcore hlast
  by_cases ht : 0 ≤ t
  · exact hhalf t ht
  · rw [← firstStopLossDifference_standardGaussian_peanoKMeasure_neg t]
    exact hhalf (-t) (neg_nonneg.mpr (le_of_not_ge ht))



end CertifiedJL
