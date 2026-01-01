import CertifiedJL.Analysis.Peano.PeanoKStopLoss
import CertifiedJL.Analysis.Peano.PeanoQuadraticExpSecond

/-!
# Moment domination for the positive Peano K stop-loss kernel

This file proves the U6c beta identity and packages the exact second Peano
kernel as a symmetric finite positive measure with Gaussian even-moment
domination constant `11 / 15`.
-/

open Filter MeasureTheory Set
open ProbabilityTheory
open scoped Interval Topology

namespace CertifiedJL

noncomputable def secondPeanoBetaCoeff (m : ℕ) : ℝ :=
  1 / ((m + 1 : ℝ) * (m + 2))

private theorem intervalIntegral_pow_mul_sub (m : ℕ) (y : ℝ) :
    (∫ t in (0 : ℝ)..y, t ^ m * (y - t)) =
      secondPeanoBetaCoeff m * y ^ (m + 2) := by
  rw [show (fun t : ℝ => t ^ m * (y - t)) =
      fun t => y * t ^ m - t ^ (m + 1) by funext t; ring,
    intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    integral_pow, integral_pow]
  · unfold secondPeanoBetaCoeff
    push_cast
    field_simp
    ring
  all_goals (apply Continuous.intervalIntegrable; fun_prop)

theorem integral_Ici_absPow_mul_firstStopLoss (m : ℕ) (y : ℝ) :
    (∫ t in Ici (0 : ℝ), |t| ^ m * max (y - t) 0) =
      secondPeanoBetaCoeff m * (max y 0) ^ (m + 2) := by
  by_cases hy : 0 ≤ y
  · calc
      (∫ t in Ici (0 : ℝ), |t| ^ m * max (y - t) 0) =
          ∫ t in Ioc (0 : ℝ) y, t ^ m * (y - t) := by
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
          rw [indicator_of_notMem (s := Ioc (0 : ℝ) y)
            (f := fun t => t ^ m * (y - t)) (by
              intro hmem
              exact (not_lt_of_ge htneg.le) hmem.1)]
          simp [ht0]
      _ = ∫ t in (0 : ℝ)..y, t ^ m * (y - t) :=
        (intervalIntegral.integral_of_le hy).symm
      _ = secondPeanoBetaCoeff m * y ^ (m + 2) :=
        intervalIntegral_pow_mul_sub m y
      _ = _ := by rw [max_eq_left hy]
  · have hy' : y ≤ 0 := le_of_not_ge hy
    calc
      (∫ t in Ici (0 : ℝ), |t| ^ m * max (y - t) 0) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
        rw [max_eq_right (sub_nonpos.mpr (hy'.trans ht))]
        simp
      _ = _ := by simp [max_eq_right hy']

private theorem integrableOn_Ici_absPow_mul_firstStopLoss
    (m : ℕ) (y : ℝ) :
    IntegrableOn (fun t : ℝ => |t| ^ m * max (y - t) 0) (Ici 0) := by
  let g : ℝ → ℝ := fun t => |t| ^ m * max (y - t) 0
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
  · rw [indicator_of_mem (s := Icc 0 (max y 0)) (f := g) ⟨ht, hty⟩]
  · rw [indicator_of_notMem (s := Icc 0 (max y 0)) (f := g)
      (by simp only [mem_Icc, not_and_or]; exact Or.inr hty)]
    rw [max_eq_right]
    · simp
    · exact sub_nonpos.mpr ((le_max_left y 0).trans (le_of_not_ge hty))

private theorem integrable_maxPow_of_absPow {μ : Measure ℝ} (n : ℕ)
    (habs : Integrable (fun y : ℝ => |y| ^ n) μ) :
    Integrable (fun y : ℝ => (max y 0) ^ n) μ := by
  refine habs.mono' (by fun_prop) ?_
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_max_right _ _) n)]
  exact pow_le_pow_left₀ (le_max_right y 0)
    (max_le (le_abs_self y) (abs_nonneg y)) n

private theorem integrableOn_Ici_absPow_mul_measure_firstStopLoss
    (μ : Measure ℝ) [SFinite μ] (m : ℕ)
    (hmom : Integrable (fun y : ℝ => (max y 0) ^ (m + 2)) μ) :
    IntegrableOn (fun t : ℝ => |t| ^ m *
      (∫ y, max (y - t) 0 ∂μ)) (Ici 0) := by
  let F : ℝ → ℝ → ℝ := fun t y => |t| ^ m * max (y - t) 0
  have hFsm : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Ici 0)).prod μ) :=
    (by fun_prop : StronglyMeasurable (Function.uncurry F)).aestronglyMeasurable
  have hFint : Integrable (Function.uncurry F)
      ((volume.restrict (Ici 0)).prod μ) := by
    apply (integrable_prod_iff' hFsm).mpr
    constructor
    · exact ae_of_all _ fun y => integrableOn_Ici_absPow_mul_firstStopLoss m y
    · refine (hmom.const_mul (secondPeanoBetaCoeff m)).congr
        (ae_of_all _ fun y => ?_)
      change secondPeanoBetaCoeff m * (max y 0) ^ (m + 2) =
        ∫ t in Ici (0 : ℝ), ‖F t y‖
      rw [show (fun t : ℝ => ‖F t y‖) = (fun t => F t y) by
        funext t
        rw [Real.norm_eq_abs, abs_of_nonneg]
        exact mul_nonneg (pow_nonneg (abs_nonneg t) _)
          (le_max_right _ _)]
      exact (integral_Ici_absPow_mul_firstStopLoss m y).symm
  refine hFint.integral_prod_left.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t _
  dsimp only [Function.uncurry_apply_pair, F]
  rw [integral_const_mul]

theorem integral_Ici_absPow_mul_measure_firstStopLoss
    (μ : Measure ℝ) [SFinite μ] (m : ℕ)
    (hmom : Integrable (fun y : ℝ => (max y 0) ^ (m + 2)) μ) :
    (∫ t in Ici (0 : ℝ), |t| ^ m *
        (∫ y, max (y - t) 0 ∂μ)) =
      secondPeanoBetaCoeff m *
        ∫ y, (max y 0) ^ (m + 2) ∂μ := by
  let F : ℝ → ℝ → ℝ := fun t y => |t| ^ m * max (y - t) 0
  have hFsm : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Ici 0)).prod μ) :=
    (by fun_prop : StronglyMeasurable (Function.uncurry F)).aestronglyMeasurable
  have hFint : Integrable (Function.uncurry F)
      ((volume.restrict (Ici 0)).prod μ) := by
    apply (integrable_prod_iff' hFsm).mpr
    constructor
    · exact ae_of_all _ fun y => integrableOn_Ici_absPow_mul_firstStopLoss m y
    · refine (hmom.const_mul (secondPeanoBetaCoeff m)).congr
        (ae_of_all _ fun y => ?_)
      change secondPeanoBetaCoeff m * (max y 0) ^ (m + 2) =
        ∫ t in Ici (0 : ℝ), ‖F t y‖
      rw [show (fun t : ℝ => ‖F t y‖) = (fun t => F t y) by
        funext t
        rw [Real.norm_eq_abs, abs_of_nonneg]
        exact mul_nonneg (pow_nonneg (abs_nonneg t) _)
          (le_max_right _ _)]
      exact (integral_Ici_absPow_mul_firstStopLoss m y).symm
  calc
    (∫ t in Ici (0 : ℝ), |t| ^ m *
        (∫ y, max (y - t) 0 ∂μ)) =
        ∫ t in Ici (0 : ℝ), ∫ y, F t y ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with t
      change |t| ^ m * (∫ y, max (y - t) 0 ∂μ) =
        ∫ y, |t| ^ m * max (y - t) 0 ∂μ
      rw [integral_const_mul]
    _ = ∫ y, (∫ t in Ici (0 : ℝ), F t y) ∂μ := by
      convert integral_integral_swap (μ := volume.restrict (Ici 0)) (ν := μ) hFint using 1
    _ = ∫ y, secondPeanoBetaCoeff m * (max y 0) ^ (m + 2) ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => integral_Ici_absPow_mul_firstStopLoss m y
    _ = _ := integral_const_mul _ _

private theorem integrable_standardGaussian_absPow (n : ℕ) :
    Integrable (fun y : ℝ => |y| ^ n) (gaussianReal 0 1) := by
  simpa [Real.norm_eq_abs, abs_pow] using (integrable_standardGaussian_pow n).norm

private theorem integrableOn_Ici_absPow_mul_firstStopLossDifference
    (m : ℕ) :
    IntegrableOn (fun t : ℝ => |t| ^ m *
      firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t) (Ici 0) := by
  have hGmom := integrable_maxPow_of_absPow (m + 2)
    (integrable_standardGaussian_absPow (m + 2))
  have hKmom := integrable_maxPow_of_absPow (m + 2)
    (integrable_absPow_peanoKMeasure (m + 2))
  have hG := integrableOn_Ici_absPow_mul_measure_firstStopLoss
    (gaussianReal 0 1) m hGmom
  have hK := integrableOn_Ici_absPow_mul_measure_firstStopLoss
    peanoKMeasure m hKmom
  refine (hG.sub hK).congr (ae_restrict_mem measurableSet_Ici |>.mono fun t _ => ?_)
  dsimp only [Pi.sub_apply]
  unfold firstStopLossDifference
  ring

theorem integral_Ici_absPow_mul_firstStopLossDifference (m : ℕ) :
    (∫ t in Ici (0 : ℝ), |t| ^ m *
        firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t) =
      secondPeanoBetaCoeff m *
        ((∫ y, (max y 0) ^ (m + 2) ∂(gaussianReal 0 1)) -
          ∫ y, (max y 0) ^ (m + 2) ∂peanoKMeasure) := by
  have hGmom := integrable_maxPow_of_absPow (m + 2)
    (integrable_standardGaussian_absPow (m + 2))
  have hKmom := integrable_maxPow_of_absPow (m + 2)
    (integrable_absPow_peanoKMeasure (m + 2))
  have hG := integrableOn_Ici_absPow_mul_measure_firstStopLoss
    (gaussianReal 0 1) m hGmom
  have hK := integrableOn_Ici_absPow_mul_measure_firstStopLoss
    peanoKMeasure m hKmom
  calc
    _ = (∫ t in Ici (0 : ℝ), |t| ^ m *
          (∫ y, max (y - t) 0 ∂(gaussianReal 0 1))) -
        ∫ t in Ici (0 : ℝ), |t| ^ m *
          (∫ y, max (y - t) 0 ∂peanoKMeasure) := by
      rw [← integral_sub hG hK]
      apply integral_congr_ae
      filter_upwards [] with t
      unfold firstStopLossDifference
      ring
    _ = _ := by
      rw [integral_Ici_absPow_mul_measure_firstStopLoss
          (gaussianReal 0 1) m hGmom,
        integral_Ici_absPow_mul_measure_firstStopLoss peanoKMeasure m hKmom]
      ring

private theorem integral_max_evenPow_of_symmetric
    (μ : Measure ℝ) (hmap : μ.map (fun x : ℝ => -x) = μ)
    (ell : ℕ) (hell : 0 < ell)
    (habs : Integrable (fun x : ℝ => |x| ^ (2 * ell)) μ) :
    (∫ x, (max x 0) ^ (2 * ell) ∂μ) =
      (∫ x, |x| ^ (2 * ell) ∂μ) / 2 := by
  let f : ℝ → ℝ := fun x => (max x 0) ^ (2 * ell)
  have hf := integrable_maxPow_of_absPow (2 * ell) habs
  have hreflect : (∫ x, f (-x) ∂μ) = ∫ x, f x ∂μ := by
    have hfmap : AEStronglyMeasurable f (μ.map (fun x : ℝ => -x)) := by
      rw [hmap]
      exact hf.aestronglyMeasurable
    calc
      _ = ∫ x, f x ∂(μ.map (fun x : ℝ => -x)) := by
        exact (integral_map (μ := μ) (φ := fun x : ℝ => -x)
          (by fun_prop) hfmap).symm
      _ = _ := by rw [hmap]
  have hfneg : Integrable (fun x => f (-x)) μ := by
    have hfmap : Integrable f (μ.map (fun x : ℝ => -x)) := by
      rw [hmap]
      exact hf
    exact (integrable_map_measure hfmap.aestronglyMeasurable (by fun_prop)).mp hfmap
  have hsum : (∫ x, |x| ^ (2 * ell) ∂μ) =
      (∫ x, f x ∂μ) + ∫ x, f (-x) ∂μ := by
    rw [← integral_add hf hfneg]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp only [f]
    by_cases hx : 0 ≤ x
    · simp [hx, hell.ne', pow_mul, sq_abs]
    · have hx' : x ≤ 0 := le_of_not_ge hx
      simp [hx', hell.ne', pow_mul, sq_abs]
  rw [hreflect] at hsum
  dsimp only [f] at hsum ⊢
  linarith

theorem integrable_absPow_mul_firstStopLossDifference (m : ℕ) :
    Integrable (fun t : ℝ => |t| ^ m *
      firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t) := by
  let f : ℝ → ℝ := fun t => |t| ^ m *
    firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t
  have hpos : IntegrableOn f (Ici 0) := by
    simpa only [f] using integrableOn_Ici_absPow_mul_firstStopLossDifference m
  have hmap : (volume.restrict (Ici (0 : ℝ))).map (fun t : ℝ => -t) =
      volume.restrict (Iic 0) := by
    conv => rhs; rw [← Measure.map_neg_eq_self volume,
      measurableEmbedding_neg.restrict_map]
    simp
  have hneg : IntegrableOn f (Iic 0) := by
    rw [IntegrableOn, ← hmap, measurableEmbedding_neg.integrable_map_iff]
    refine hpos.congr (ae_restrict_mem measurableSet_Ici |>.mono fun t _ => ?_)
    dsimp only [Function.comp_apply, f]
    rw [abs_neg, firstStopLossDifference_standardGaussian_peanoKMeasure_neg]
  rw [← integrableOn_univ, ← Iic_union_Ici (a := (0 : ℝ)), integrableOn_union]
  exact ⟨hneg, hpos⟩

theorem integral_abs_evenPow_mul_firstStopLossDifference (ell : ℕ) :
    (∫ t : ℝ, |t| ^ (2 * ell) *
        firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t) =
      secondPeanoBetaCoeff (2 * ell) *
        ((∫ y, |y| ^ (2 * (ell + 1)) ∂(gaussianReal 0 1)) -
          ∫ y, |y| ^ (2 * (ell + 1)) ∂peanoKMeasure) := by
  let f : ℝ → ℝ := fun t => t ^ (2 * ell) *
    firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t
  calc
    (∫ t : ℝ, |t| ^ (2 * ell) *
        firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t) =
        ∫ t : ℝ, |t| ^ (2 * ell) *
          firstStopLossDifference (gaussianReal 0 1) peanoKMeasure |t| := by
      apply integral_congr_ae
      filter_upwards [] with t
      by_cases ht : 0 ≤ t
      · rw [abs_of_nonneg ht]
      · rw [abs_of_nonpos (le_of_not_ge ht),
          firstStopLossDifference_standardGaussian_peanoKMeasure_neg]
    _ = 2 * ∫ t in Ioi (0 : ℝ), t ^ (2 * ell) *
        firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t := by
      change (∫ t : ℝ, f |t|) = 2 * ∫ t in Ioi (0 : ℝ), f t
      exact integral_comp_abs
    _ = 2 * ∫ t in Ici (0 : ℝ), |t| ^ (2 * ell) *
        firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t := by
      rw [integral_Ici_eq_integral_Ioi]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change t ^ (2 * ell) *
          firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t =
        |t| ^ (2 * ell) *
          firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t
      rw [abs_of_pos ht]
    _ = 2 * secondPeanoBetaCoeff (2 * ell) *
        ((∫ y, (max y 0) ^ (2 * ell + 2) ∂(gaussianReal 0 1)) -
          ∫ y, (max y 0) ^ (2 * ell + 2) ∂peanoKMeasure) := by
      rw [integral_Ici_absPow_mul_firstStopLossDifference]
      ring
    _ = _ := by
      rw [show 2 * ell + 2 = 2 * (ell + 1) by omega,
        integral_max_evenPow_of_symmetric (gaussianReal 0 1)
          (by simpa using (gaussianReal_map_neg (μ := 0) (v := 1)))
          (ell + 1) (by omega) (integrable_standardGaussian_absPow _),
        integral_max_evenPow_of_symmetric peanoKMeasure peanoKMeasure_map_neg
          (ell + 1) (by omega) (integrable_absPow_peanoKMeasure _)]
      ring

private theorem integral_standardGaussian_abs_evenPow_succ (ell : ℕ) :
    (∫ y : ℝ, |y| ^ (2 * (ell + 1)) ∂(gaussianReal 0 1)) =
      (2 * ell + 1 : ℝ) *
        ∫ y : ℝ, |y| ^ (2 * ell) ∂(gaussianReal 0 1) := by
  rw [integral_standardGaussian_abs_evenPow,
    integral_standardGaussian_abs_evenPow]
  by_cases hell : ell = 0
  · subst ell
    norm_num
  · have hidx : 2 * (ell + 1) - 1 = (2 * ell - 1) + 2 := by omega
    rw [hidx, Nat.doubleFactorial_add_two]
    have hcast : (((2 * ell - 1) + 2 : ℕ) : ℝ) = 2 * (ell : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_sub (by omega)]
      push_cast
      ring
    simp only [Nat.cast_mul]
    rw [hcast]

theorem integral_abs_evenPow_mul_firstStopLossDifference_le (ell : ℕ) :
    (∫ t : ℝ, |t| ^ (2 * ell) *
        firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t) ≤
      (1 / (2 * ell + 2 : ℝ)) *
        ∫ y : ℝ, |y| ^ (2 * ell) ∂(gaussianReal 0 1) := by
  rw [integral_abs_evenPow_mul_firstStopLossDifference]
  have hcoeff : 0 ≤ secondPeanoBetaCoeff (2 * ell) := by
    unfold secondPeanoBetaCoeff
    positivity
  have hKnonneg : 0 ≤
      ∫ y : ℝ, |y| ^ (2 * (ell + 1)) ∂peanoKMeasure :=
    integral_nonneg_of_ae (ae_of_all _ fun y => pow_nonneg (abs_nonneg y) _)
  calc
    secondPeanoBetaCoeff (2 * ell) *
        ((∫ y, |y| ^ (2 * (ell + 1)) ∂(gaussianReal 0 1)) -
          ∫ y, |y| ^ (2 * (ell + 1)) ∂peanoKMeasure) ≤
        secondPeanoBetaCoeff (2 * ell) *
          ∫ y, |y| ^ (2 * (ell + 1)) ∂(gaussianReal 0 1) :=
      mul_le_mul_of_nonneg_left (sub_le_self _ hKnonneg) hcoeff
    _ = _ := by
      rw [integral_standardGaussian_abs_evenPow_succ]
      unfold secondPeanoBetaCoeff
      push_cast
      field_simp

theorem integral_abs_evenPow_mul_firstStopLossDifference_le_eleven_fifteenths
    (ell : ℕ) :
    (∫ t : ℝ, |t| ^ (2 * ell) *
        firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t) ≤
      (11 / 15 : ℝ) * centeredGaussianEvenMoment 1 ell := by
  have hbase := integral_abs_evenPow_mul_firstStopLossDifference_le ell
  have hmoment : 0 ≤
      ∫ y : ℝ, |y| ^ (2 * ell) ∂(gaussianReal 0 1) :=
    integral_nonneg_of_ae (ae_of_all _ fun y => pow_nonneg (abs_nonneg y) _)
  have hcoef : (1 / (2 * ell + 2 : ℝ)) ≤ 11 / 15 := by
    have hell : (0 : ℝ) ≤ ell := by positivity
    have hden : (0 : ℝ) < 2 * ell + 2 := by positivity
    rw [div_le_iff₀ hden]
    nlinarith
  unfold centeredGaussianEvenMoment
  exact hbase.trans (mul_le_mul_of_nonneg_right hcoef hmoment)

theorem stronglyMeasurable_firstStopLossDifference_standardGaussian_peanoKMeasure :
    StronglyMeasurable
      (firstStopLossDifference (gaussianReal 0 1) peanoKMeasure) := by
  have hjoint : StronglyMeasurable (Function.uncurry
      (fun t y : ℝ => max (y - t) 0)) := by fun_prop
  have hG : StronglyMeasurable (fun t : ℝ =>
      ∫ y, max (y - t) 0 ∂(gaussianReal 0 1)) :=
    hjoint.integral_prod_right'
  have hK : StronglyMeasurable (fun t : ℝ =>
      ∫ y, max (y - t) 0 ∂peanoKMeasure) :=
    hjoint.integral_prod_right'
  unfold firstStopLossDifference
  exact hG.sub hK

/-- The positive measure with density equal to the second Peano kernel. -/
noncomputable def peanoKStopLossMeasure : Measure ℝ :=
  positiveDensityMeasure
    (firstStopLossDifference (gaussianReal 0 1) peanoKMeasure)

private theorem integrable_firstStopLossDifference_standardGaussian_peanoKMeasure :
    Integrable (firstStopLossDifference (gaussianReal 0 1) peanoKMeasure) := by
  simpa only [abs_pow, pow_zero, one_mul] using
    integrable_absPow_mul_firstStopLossDifference 0

instance peanoKStopLossMeasure_isFiniteMeasure :
    IsFiniteMeasure peanoKStopLossMeasure := by
  unfold peanoKStopLossMeasure positiveDensityMeasure
  exact isFiniteMeasure_withDensity_ofReal
    integrable_firstStopLossDifference_standardGaussian_peanoKMeasure.hasFiniteIntegral

theorem peanoKStopLossMeasure_map_neg :
    peanoKStopLossMeasure.map (fun x : ℝ => -x) = peanoKStopLossMeasure := by
  ext s hs
  let e : ℝ ≃ᵐ ℝ := MeasurableEquiv.neg ℝ
  let h := firstStopLossDifference (gaussianReal 0 1) peanoKMeasure
  have hmap := e.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul'
    (g := h) hs (f' := fun _ => (-1 : ℝ))
    (fun x => hasDerivAt_neg x)
    (ae_of_all _ firstStopLossDifference_standardGaussian_peanoKMeasure_nonneg)
    integrable_firstStopLossDifference_standardGaussian_peanoKMeasure
  change peanoKStopLossMeasure.map (fun x : ℝ => -x) s = _
  rw [show peanoKStopLossMeasure.map (fun x : ℝ => -x) s =
      ENNReal.ofReal (∫ x in s, |(-1 : ℝ)| * h (-x)) by
    simpa [peanoKStopLossMeasure, positiveDensityMeasure, e] using hmap]
  unfold peanoKStopLossMeasure positiveDensityMeasure
  rw [withDensity_apply _ hs]
  rw [← ofReal_integral_eq_lintegral_ofReal
    integrable_firstStopLossDifference_standardGaussian_peanoKMeasure.integrableOn
    (ae_restrict_mem hs |>.mono fun x _ =>
      firstStopLossDifference_standardGaussian_peanoKMeasure_nonneg x)]
  congr 1
  apply setIntegral_congr_fun hs
  intro x _
  simp only [h, abs_neg, abs_one, one_mul]
  rw [firstStopLossDifference_standardGaussian_peanoKMeasure_neg]

theorem integrable_absPow_peanoKStopLossMeasure (n : ℕ) :
    Integrable (fun x : ℝ => |x| ^ n) peanoKStopLossMeasure := by
  unfold peanoKStopLossMeasure positiveDensityMeasure
  have hmeas :=
    stronglyMeasurable_firstStopLossDifference_standardGaussian_peanoKMeasure
      |>.measurable.ennreal_ofReal
  rw [integrable_withDensity_iff_integrable_smul' hmeas
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine (integrable_absPow_mul_firstStopLossDifference n).congr
    (ae_of_all _ fun x => ?_)
  simp only [ENNReal.toReal_ofReal
    (firstStopLossDifference_standardGaussian_peanoKMeasure_nonneg x), smul_eq_mul]
  ring

theorem integral_abs_evenPow_peanoKStopLossMeasure (ell : ℕ) :
    (∫ x : ℝ, |x| ^ (2 * ell) ∂peanoKStopLossMeasure) =
      ∫ x : ℝ, |x| ^ (2 * ell) *
        firstStopLossDifference (gaussianReal 0 1) peanoKMeasure x := by
  unfold peanoKStopLossMeasure
  rw [integral_positiveDensityMeasure _
    stronglyMeasurable_firstStopLossDifference_standardGaussian_peanoKMeasure.measurable
    firstStopLossDifference_standardGaussian_peanoKMeasure_nonneg]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul]
  ring

/-- The U6c moment package for the exact positive second Peano kernel. -/
theorem peanoK_positiveStopLossMomentDomination :
    PositiveStopLossMomentDomination
      (gaussianReal 0 1) peanoKMeasure (11 / 15) := by
  refine ⟨firstStopLossDifference_standardGaussian_peanoKMeasure_nonneg,
    stronglyMeasurable_firstStopLossDifference_standardGaussian_peanoKMeasure.measurable,
    ?_⟩
  change GaussianEvenMomentDomination peanoKStopLossMeasure (11 / 15) 1
  refine ⟨by norm_num, inferInstance, peanoKStopLossMeasure_map_neg,
    integrable_absPow_peanoKStopLossMeasure, ?_⟩
  intro ell
  rw [integral_abs_evenPow_peanoKStopLossMeasure]
  exact integral_abs_evenPow_mul_firstStopLossDifference_le_eleven_fifteenths ell

/-- U3b specialized to the exact Gaussian-to-K second Peano replacement. -/
theorem norm_partialSum_secondPeanoDifference_standardGaussian_peanoKMeasure_le
    {ρ : Measure ℝ} {varianceW : NNReal}
    (s : ℂ) (c : ℝ)
    (hlifted :
      (∫ w, ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
          ∂(gaussianReal 0 1) ∂ρ) -
          ∫ w, ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
            ∂peanoKMeasure ∂ρ =
        c ^ 2 • ∫ w, ∫ t,
          firstStopLossDifference (gaussianReal 0 1) peanoKMeasure t •
            iteratedDeriv 6 (complexQuadraticExp s) (w + c * t) ∂volume ∂ρ)
    (hW : GaussianEvenMomentDomination ρ 1 varianceW)
    (hvariance : varianceW + scaledVariance c 1 ≤ (2 : NNReal)⁻¹)
    (hs_nonneg : 0 ≤ s.re) (hs_lt_one : s.re < 1) :
    ‖(∫ w, ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
          ∂(gaussianReal 0 1) ∂ρ) -
        ∫ w, ∫ y, iteratedDeriv 4 (complexQuadraticExp s) (w + c * y)
          ∂peanoKMeasure ∂ρ‖ ≤
      (11 / 15 : ℝ) * c ^ 2 *
        quadraticExpDerivativeMajorant 6 ‖s‖ s.re := by
  exact norm_partialSum_secondPeanoDifference_le_of_positiveStopLossMomentDomination
    s c (11 / 15) hlifted hW peanoK_positiveStopLossMomentDomination
      hvariance hs_nonneg hs_lt_one

end CertifiedJL
