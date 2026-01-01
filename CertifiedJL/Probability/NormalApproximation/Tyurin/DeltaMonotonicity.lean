/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.NormalApproximation.Tyurin.EnvelopeBounds

/-!
# Monotonicity of Tyurin's second discrepancy

The moving cutoff in `tyurinDeltaTwo` obscures a simple fact.  After moving
the outside factor `L` into the integral, its density is a pointwise
nondecreasing function of `L`.  At the switch `L s³ = 125/27`, the two
pieces agree exactly: the exponent gap is precisely
`25/54 = -log tyurinRationalEll`.
-/

open MeasureTheory Set

namespace CertifiedJL
namespace Probability

/-- The one-piece density underlying `tyurinDeltaTwo`. -/
noncomputable def tyurinDeltaTwoDensity (L s : ℝ) : ℝ :=
  if L * s ^ 3 ≤ 125 / 27 then
    L * s ^ 2 / 2 *
      Real.exp (lyapunovVarianceCap L * s ^ 2 / 2)
  else
    L * s ^ 2 / (2 * tyurinRationalEll) *
      Real.exp (L * s ^ 3 / 5)

private theorem root_switch_iff
    {L s : ℝ} (hL : 0 < L) (hs : 0 ≤ s) :
    s * lyapunovThirdRoot L ≤ 5 / 3 ↔
      L * s ^ 3 ≤ 125 / 27 := by
  have hR0 : 0 ≤ lyapunovThirdRoot L :=
    lyapunovThirdRoot_nonneg hL.le
  have hleft0 : 0 ≤ s * lyapunovThirdRoot L :=
    mul_nonneg hs hR0
  have hright0 : 0 ≤ (5 / 3 : ℝ) := by norm_num
  rw [← pow_le_pow_iff_left₀ hleft0 hright0
    (by norm_num : (3 : ℕ) ≠ 0)]
  rw [mul_pow, lyapunovThirdRoot_cube hL.le]
  norm_num
  ring

private theorem varianceCap_mono
    {L₁ L₂ : ℝ} (hL₁ : 0 ≤ L₁) (hL : L₁ ≤ L₂) :
    lyapunovVarianceCap L₁ ≤ lyapunovVarianceCap L₂ := by
  unfold lyapunovVarianceCap
  exact Real.rpow_le_rpow hL₁ hL (by norm_num)

private theorem firstDensity_mono
    {L₁ L₂ s : ℝ} (hL₁ : 0 ≤ L₁) (hL : L₁ ≤ L₂)
    (_hs : 0 ≤ s) :
    L₁ * s ^ 2 / 2 *
        Real.exp (lyapunovVarianceCap L₁ * s ^ 2 / 2) ≤
      L₂ * s ^ 2 / 2 *
        Real.exp (lyapunovVarianceCap L₂ * s ^ 2 / 2) := by
  have hfront :
      L₁ * s ^ 2 / 2 ≤ L₂ * s ^ 2 / 2 := by
    gcongr
  have hfront0 : 0 ≤ L₁ * s ^ 2 / 2 := by positivity
  have hexp :
      Real.exp (lyapunovVarianceCap L₁ * s ^ 2 / 2) ≤
        Real.exp (lyapunovVarianceCap L₂ * s ^ 2 / 2) := by
    apply Real.exp_le_exp.mpr
    gcongr
    exact varianceCap_mono hL₁ hL
  exact mul_le_mul hfront hexp (Real.exp_nonneg _)
    (hfront0.trans hfront)

private theorem secondDensity_mono
    {L₁ L₂ s : ℝ} (hL₁ : 0 ≤ L₁) (hL : L₁ ≤ L₂)
    (hs : 0 ≤ s) :
    L₁ * s ^ 2 / (2 * tyurinRationalEll) *
        Real.exp (L₁ * s ^ 3 / 5) ≤
      L₂ * s ^ 2 / (2 * tyurinRationalEll) *
        Real.exp (L₂ * s ^ 3 / 5) := by
  have hEll : 0 < tyurinRationalEll := by
    unfold tyurinRationalEll
    positivity
  have hfront :
      L₁ * s ^ 2 / (2 * tyurinRationalEll) ≤
        L₂ * s ^ 2 / (2 * tyurinRationalEll) := by
    gcongr
  have hfront0 :
      0 ≤ L₁ * s ^ 2 / (2 * tyurinRationalEll) := by
    positivity
  have hexp :
      Real.exp (L₁ * s ^ 3 / 5) ≤
        Real.exp (L₂ * s ^ 3 / 5) := by
    apply Real.exp_le_exp.mpr
    have hs3 : 0 ≤ s ^ 3 := by positivity
    nlinarith
  exact mul_le_mul hfront hexp (Real.exp_nonneg _)
    (hfront0.trans hfront)

private theorem firstDensity_le_secondDensity_of_cross
    {L₁ L₂ s : ℝ} (hL₁ : 0 < L₁) (hL : L₁ ≤ L₂)
    (hs : 0 ≤ s)
    (hfirst : L₁ * s ^ 3 ≤ 125 / 27)
    (hsecond : 125 / 27 ≤ L₂ * s ^ 3) :
    L₁ * s ^ 2 / 2 *
        Real.exp (lyapunovVarianceCap L₁ * s ^ 2 / 2) ≤
      L₂ * s ^ 2 / (2 * tyurinRationalEll) *
        Real.exp (L₂ * s ^ 3 / 5) := by
  have hL₂ : 0 < L₂ := hL₁.trans_le hL
  have hR₁0 : 0 ≤ lyapunovThirdRoot L₁ :=
    lyapunovThirdRoot_nonneg hL₁.le
  have hswitch :
      s * lyapunovThirdRoot L₁ ≤ 5 / 3 :=
    (root_switch_iff hL₁ hs).2 hfirst
  have hsq :
      lyapunovVarianceCap L₁ * s ^ 2 ≤ 25 / 9 := by
    have hsquare :
        (s * lyapunovThirdRoot L₁) ^ 2 ≤ (5 / 3 : ℝ) ^ 2 :=
      (sq_le_sq₀ (mul_nonneg hs hR₁0) (by norm_num)).2 hswitch
    rw [mul_pow, lyapunovThirdRoot_sq hL₁.le] at hsquare
    nlinarith
  have hexponent :
      lyapunovVarianceCap L₁ * s ^ 2 / 2 ≤
        25 / 54 + L₂ * s ^ 3 / 5 := by
    nlinarith
  have hexp :
      Real.exp (lyapunovVarianceCap L₁ * s ^ 2 / 2) ≤
        Real.exp (25 / 54 + L₂ * s ^ 3 / 5) :=
    Real.exp_le_exp.mpr hexponent
  have hfront :
      L₁ * s ^ 2 / 2 ≤ L₂ * s ^ 2 / 2 := by
    gcongr
  have hfront0 : 0 ≤ L₁ * s ^ 2 / 2 := by positivity
  have hbase :=
    mul_le_mul hfront hexp (Real.exp_nonneg _)
      (hfront0.trans hfront)
  calc
    L₁ * s ^ 2 / 2 *
          Real.exp (lyapunovVarianceCap L₁ * s ^ 2 / 2) ≤
        L₂ * s ^ 2 / 2 *
          Real.exp (25 / 54 + L₂ * s ^ 3 / 5) := hbase
    _ = L₂ * s ^ 2 / (2 * tyurinRationalEll) *
          Real.exp (L₂ * s ^ 3 / 5) := by
      unfold tyurinRationalEll
      rw [Real.exp_add, Real.exp_neg]
      field_simp [Real.exp_ne_zero]

/-- The second-discrepancy density is pointwise nondecreasing in `L`. -/
theorem tyurinDeltaTwoDensity_mono
    {L₁ L₂ s : ℝ} (hL₁ : 0 < L₁) (hL : L₁ ≤ L₂)
    (hs : 0 ≤ s) :
    tyurinDeltaTwoDensity L₁ s ≤ tyurinDeltaTwoDensity L₂ s := by
  have hL₂ : 0 < L₂ := hL₁.trans_le hL
  unfold tyurinDeltaTwoDensity
  by_cases hfirst₁ : L₁ * s ^ 3 ≤ 125 / 27
  · rw [if_pos hfirst₁]
    by_cases hfirst₂ : L₂ * s ^ 3 ≤ 125 / 27
    · rw [if_pos hfirst₂]
      exact firstDensity_mono hL₁.le hL hs
    · rw [if_neg hfirst₂]
      exact firstDensity_le_secondDensity_of_cross
        hL₁ hL hs hfirst₁ (le_of_not_ge hfirst₂)
  · have hfirst₂ : ¬ L₂ * s ^ 3 ≤ 125 / 27 := by
      intro h
      apply hfirst₁
      have hs3 : 0 ≤ s ^ 3 := by positivity
      exact (mul_le_mul_of_nonneg_right hL hs3).trans h
    rw [if_neg hfirst₁, if_neg hfirst₂]
    exact secondDensity_mono hL₁.le hL hs

private theorem measurable_tyurinDeltaTwoDensity (L : ℝ) :
    Measurable (tyurinDeltaTwoDensity L) := by
  unfold tyurinDeltaTwoDensity
  apply Measurable.ite
  · exact measurableSet_le (measurable_const.mul
      (continuous_id.pow 3).measurable) measurable_const
  · fun_prop
  · fun_prop

private theorem tyurinDeltaTwoDensity_nonneg
    {L s : ℝ} (hL : 0 ≤ L) :
    0 ≤ tyurinDeltaTwoDensity L s := by
  unfold tyurinDeltaTwoDensity
  split_ifs
  · positivity
  · have hEll : 0 < tyurinRationalEll := by
      unfold tyurinRationalEll
      positivity
    positivity

/-- The unified Tyurin density is integrable on every finite positive interval. -/
theorem intervalIntegrable_tyurinDeltaTwoDensity
    {L T : ℝ} (hL : 0 < L) (hT : 0 ≤ T) :
    IntervalIntegrable (tyurinDeltaTwoDensity L) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
  let M : ℝ :=
    L * T ^ 2 / 2 *
        Real.exp (lyapunovVarianceCap L * T ^ 2 / 2) +
      L * T ^ 2 / (2 * tyurinRationalEll) *
        Real.exp (L * T ^ 3 / 5)
  refine Measure.integrableOn_of_bounded
    (M := M) measure_Icc_lt_top.ne
    (measurable_tyurinDeltaTwoDensity L).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have hs0 : 0 ≤ s := hs.1
  have hsT : s ≤ T := hs.2
  have hs2 : s ^ 2 ≤ T ^ 2 :=
    (sq_le_sq₀ hs0 hT).2 hsT
  have hs3 : s ^ 3 ≤ T ^ 3 := by
    nlinarith [mul_self_le_mul_self hs0 hsT]
  have hEll : 0 < tyurinRationalEll := by
    unfold tyurinRationalEll
    positivity
  have hfirst :
      L * s ^ 2 / 2 *
          Real.exp (lyapunovVarianceCap L * s ^ 2 / 2) ≤
        L * T ^ 2 / 2 *
          Real.exp (lyapunovVarianceCap L * T ^ 2 / 2) := by
    have hcap : 0 ≤ lyapunovVarianceCap L :=
      lyapunovVarianceCap_nonneg hL.le
    have he : Real.exp (lyapunovVarianceCap L * s ^ 2 / 2) ≤
        Real.exp (lyapunovVarianceCap L * T ^ 2 / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    exact mul_le_mul (by nlinarith)
      he (Real.exp_nonneg _) (by positivity)
  have hsecond :
      L * s ^ 2 / (2 * tyurinRationalEll) *
          Real.exp (L * s ^ 3 / 5) ≤
        L * T ^ 2 / (2 * tyurinRationalEll) *
          Real.exp (L * T ^ 3 / 5) := by
    have he : Real.exp (L * s ^ 3 / 5) ≤
        Real.exp (L * T ^ 3 / 5) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    exact mul_le_mul (by gcongr)
      he (Real.exp_nonneg _) (by positivity)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (tyurinDeltaTwoDensity_nonneg hL.le)]
  unfold tyurinDeltaTwoDensity
  split_ifs
  · exact hfirst.trans (le_add_of_nonneg_right (by positivity))
  · exact hsecond.trans (le_add_of_nonneg_left (by positivity))

/--
`tyurinDeltaTwo` is the Gaussian-weighted integral of the single moving
density above.  This is the normalization that exposes monotonicity.
-/
theorem tyurinDeltaTwo_eq_integral_density
    {L t : ℝ} (hL : 0 < L) :
    tyurinDeltaTwo L t =
      Real.exp (-(|t| ^ 2) / 2) *
        (∫ s : ℝ in 0..|t|, tyurinDeltaTwoDensity L s) := by
  let T : ℝ := |t|
  let R : ℝ := lyapunovThirdRoot L
  let A : ℝ := 5 / (3 * R)
  have hT : 0 ≤ T := abs_nonneg _
  have hR : 0 < R := by
    dsimp [R]
    unfold lyapunovThirdRoot
    positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  unfold tyurinDeltaTwo
  dsimp only
  by_cases hbranch : T * R ≤ 5 / 3
  · rw [if_pos hbranch]
    have hdensity :
        (∫ s : ℝ in 0..T, tyurinDeltaTwoDensity L s) =
          L * (∫ s : ℝ in 0..T,
            s ^ 2 / 2 *
              Real.exp (lyapunovVarianceCap L * s ^ 2 / 2)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Icc 0 T := by
        simpa [uIcc_of_le hT] using hs
      have hsSwitch : s * R ≤ 5 / 3 := by
        have hsR : s * R ≤ T * R :=
          mul_le_mul_of_nonneg_right hs'.2 hR.le
        exact hsR.trans hbranch
      have hs0 : 0 ≤ s := hs'.1
      have hpoly :
          L * s ^ 3 ≤ 125 / 27 :=
        (root_switch_iff hL hs0).1 (by simpa [R] using hsSwitch)
      simp only [tyurinDeltaTwoDensity, if_pos hpoly]
      ring
    rw [hdensity]
    ring
  · rw [if_neg hbranch]
    have hAT : A ≤ T := by
      have hstrict : 5 / 3 < T * R := lt_of_not_ge hbranch
      dsimp [A]
      rw [div_le_iff₀ (by positivity : 0 < 3 * R)]
      nlinarith
    have hglobal :=
      intervalIntegrable_tyurinDeltaTwoDensity hL hT
    have hleftInt :
        IntervalIntegrable (tyurinDeltaTwoDensity L) volume 0 A :=
      hglobal.mono_set (by
        rw [uIcc_of_le hT, uIcc_of_le hA]
        exact Icc_subset_Icc_right hAT)
    have hrightInt :
        IntervalIntegrable (tyurinDeltaTwoDensity L) volume A T :=
      hglobal.mono_set (by
        rw [uIcc_of_le hT, uIcc_of_le hAT]
        exact Icc_subset_Icc_left hA)
    have hsplit :
        (∫ s : ℝ in 0..T, tyurinDeltaTwoDensity L s) =
          (∫ s : ℝ in 0..A, tyurinDeltaTwoDensity L s) +
          ∫ s : ℝ in A..T, tyurinDeltaTwoDensity L s := by
      exact (intervalIntegral.integral_add_adjacent_intervals
        hleftInt hrightInt).symm
    have hleft :
        (∫ s : ℝ in 0..A, tyurinDeltaTwoDensity L s) =
          L * (∫ s : ℝ in 0..A,
            s ^ 2 / 2 *
              Real.exp (lyapunovVarianceCap L * s ^ 2 / 2)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Icc 0 A := by
        simpa [uIcc_of_le hA] using hs
      have hsSwitch : s * R ≤ 5 / 3 := by
        have hsR : s * R ≤ A * R :=
          mul_le_mul_of_nonneg_right hs'.2 hR.le
        have hAR : A * R = 5 / 3 := by
          dsimp [A]
          field_simp [hR.ne']
        rwa [hAR] at hsR
      have hpoly :
          L * s ^ 3 ≤ 125 / 27 :=
        (root_switch_iff hL hs'.1).1 (by simpa [R] using hsSwitch)
      simp only [tyurinDeltaTwoDensity, if_pos hpoly]
      ring
    have hright :
        (∫ s : ℝ in A..T, tyurinDeltaTwoDensity L s) =
          L * (∫ s : ℝ in A..T,
            s ^ 2 / (2 * tyurinRationalEll) *
              Real.exp (L * s ^ 3 / 5)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with s hs
      have hsAT : s ∈ Ioc A T := by
        simpa [uIoc_of_le hAT] using hs
      have hAStrict : A < s := hsAT.1
      have hs0 : 0 ≤ s := hA.trans hAStrict.le
      have hswitchStrict : 5 / 3 < s * R := by
        have hAR : A * R = 5 / 3 := by
          dsimp [A]
          field_simp [hR.ne']
        rw [← hAR]
        exact mul_lt_mul_of_pos_right hAStrict hR
      have hpoly :
          ¬ L * s ^ 3 ≤ 125 / 27 := by
        intro hp
        have := (root_switch_iff hL hs0).2 hp
        exact (not_le_of_gt hswitchStrict) (by simpa [R] using this)
      simp only [tyurinDeltaTwoDensity, if_neg hpoly]
      ring
    rw [hsplit, hleft, hright]
    ring

/-- The actual second discrepancy is nondecreasing in the Lyapunov ratio. -/
theorem tyurinDeltaTwo_mono
    {L₁ L₂ t : ℝ} (hL₁ : 0 < L₁) (hL : L₁ ≤ L₂) :
    tyurinDeltaTwo L₁ t ≤ tyurinDeltaTwo L₂ t := by
  have hL₂ : 0 < L₂ := hL₁.trans_le hL
  rw [tyurinDeltaTwo_eq_integral_density hL₁,
    tyurinDeltaTwo_eq_integral_density hL₂]
  apply mul_le_mul_of_nonneg_left
  · apply intervalIntegral.integral_mono_on
      (abs_nonneg t)
      (intervalIntegrable_tyurinDeltaTwoDensity hL₁ (abs_nonneg t))
      (intervalIntegrable_tyurinDeltaTwoDensity hL₂ (abs_nonneg t))
    intro s hs
    exact tyurinDeltaTwoDensity_mono hL₁ hL hs.1
  · exact Real.exp_nonneg _

/--
Endpoint version consumed by finite Lyapunov cells: move the actual
discrepancy to `L₂`, then apply the existing finite trapezoid there.
-/
theorem tyurinDeltaTwo_le_endpointTrapezoid
    {n : ℕ} {L₁ L₂ t : ℝ} (hn : 0 < n)
    (hL₁ : 0 < L₁) (hL : L₁ ≤ L₂) :
    tyurinDeltaTwo L₁ t ≤
      tyurinDeltaTwoTrapezoidUpper n L₂ t :=
  (tyurinDeltaTwo_mono hL₁ hL).trans
    (tyurinDeltaTwo_le_trapezoidUpper hn (hL₁.trans_le hL))

end Probability
end CertifiedJL
