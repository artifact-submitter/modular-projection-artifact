/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.NormalApproximation.Tyurin.GlobalEnvelope

/-!
# The complete Tyurin core envelope

This file closes the branch that was missing between the deleted-product
estimate and the `D*` bridge.  The first branch was already integrated in
`TyurinGlobalEnvelope`; here we integrate the second branch from
`A = 5 / (3 L^(1/3))`, join the two pieces, and specialize the resulting
`delta₂` bound to the standardized tilted-Rademacher law.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace CertifiedJL
namespace Probability

universe u_1

variable {ι : Type u_1} [Fintype ι]

theorem tyurinDeltaOne_neg (L u : ℝ) :
    tyurinDeltaOne L (-u) = tyurinDeltaOne L u := by
  simp [tyurinDeltaOne]

theorem tyurinDeltaTwo_neg (L u : ℝ) :
    tyurinDeltaTwo L (-u) = tyurinDeltaTwo L u := by
  simp [tyurinDeltaTwo]

theorem tyurinProductEnvelope_neg (L u : ℝ) :
    tyurinProductEnvelope L (-u) = tyurinProductEnvelope L u := by
  simp [tyurinProductEnvelope, tyurinB, Real.cos_neg]

/--
Integrated second branch of Tyurin's zero-bias comparison.  The first
segment `[0,A]` uses the endpoint first-branch estimate; `[A,t]` uses the
global deleted-product estimate at height `ell`.
-/
theorem norm_gaussianRenormalized_product_sub_one_le_tyurinSecondBranch
    (u a : ι → ℝ) {t L : ℝ}
    (hL : 0 < L)
    (hvar : ∑ i, biasedSignVarianceTerm (u i) (a i) = 1)
    (hthird : ∑ i, biasedSignThirdMomentTerm (u i) (a i) = L)
    (hbranch : ¬t * lyapunovThirdRoot L ≤ 5 / 3) :
    ‖Complex.exp (((t ^ 2 / 2 : ℝ) : ℂ)) *
          (∏ i, centeredBiasedSignChar (u i) (a i) t) - 1‖ ≤
      (∫ s : ℝ in 0..(5 / (3 * lyapunovThirdRoot L)),
          L * s ^ 2 / 2 *
            Real.exp (lyapunovVarianceCap L * s ^ 2 / 2)) +
        ∫ s : ℝ in (5 / (3 * lyapunovThirdRoot L))..t,
          L * s ^ 2 / (2 * tyurinRationalEll) *
            Real.exp (L * s ^ 3 / 5) := by
  classical
  let R : ℝ := lyapunovThirdRoot L
  let A : ℝ := 5 / (3 * R)
  let F : ℝ → ℂ := fun s =>
    Complex.exp (((s ^ 2 / 2 : ℝ) : ℂ)) *
      ∏ i, centeredBiasedSignChar (u i) (a i) s
  let D : ℝ → ℂ := fun s =>
    Complex.exp (((s ^ 2 / 2 : ℝ) : ℂ)) * (s : ℂ) *
      ((∏ i, centeredBiasedSignChar (u i) (a i) s) -
        centeredBiasedSignProductZeroBiasChar u a s)
  have hR : 0 < R := by
    dsimp only [R]
    unfold lyapunovThirdRoot
    positivity
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hAt : A < t := by
    have hstrict : 5 / 3 < t * R := lt_of_not_ge hbranch
    dsimp only [A]
    rw [div_lt_iff₀ (by positivity : 0 < 3 * R)]
    nlinarith
  have hAR : A * R = 5 / 3 := by
    dsimp only [A]
    field_simp [hR.ne']
  have hfirst :
      ‖F A - 1‖ ≤
        ∫ s : ℝ in 0..A,
          L * s ^ 2 / 2 *
            Real.exp (lyapunovVarianceCap L * s ^ 2 / 2) := by
    simpa only [F] using
      norm_gaussianRenormalized_product_sub_one_le_tyurinFirstBranch
        u a hA.le hL.le hvar hthird (by rw [hAR])
  have hderiv : ∀ s, HasDerivAt F (D s) s := by
    intro s
    exact
      hasDerivAt_gaussianRenormalized_centeredBiasedSignChar_product
        u a s
  have hcharCont (i : ι) :
      Continuous (centeredBiasedSignChar (u i) (a i)) := by
    rw [continuous_iff_continuousAt]
    intro s
    exact
      (hasDerivAt_centeredBiasedSignChar (u i) (a i) s).continuousAt
  have hzeroCont (i : ι) :
      Continuous (centeredBiasedSignZeroBiasChar (u i) (a i)) := by
    unfold centeredBiasedSignZeroBiasChar
    fun_prop
  have hprodCont :
      Continuous
        (fun s : ℝ =>
          ∏ i, centeredBiasedSignChar (u i) (a i) s) :=
    continuous_finsetProd Finset.univ fun i _ => hcharCont i
  have hzeroProductCont :
      Continuous (centeredBiasedSignProductZeroBiasChar u a) := by
    unfold centeredBiasedSignProductZeroBiasChar
    apply continuous_finsetSum Finset.univ
    intro i _
    exact ((continuous_const.mul (hzeroCont i)).mul
      (continuous_finsetProd (Finset.univ.erase i)
        fun j _ => hcharCont j))
  have hDcont : Continuous D := by
    dsimp [D]
    have hfront :
        Continuous (fun s : ℝ =>
          Complex.exp (((s ^ 2 / 2 : ℝ) : ℂ)) * (s : ℂ)) := by
      fun_prop
    exact hfront.mul (hprodCont.sub hzeroProductCont)
  have hFTC :
      (∫ s : ℝ in A..t, D s) = F t - F A := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hderiv s)
      (hDcont.intervalIntegrable A t)
  have hsecond :
      ‖F t - F A‖ ≤
        ∫ s : ℝ in A..t,
          L * s ^ 2 / (2 * tyurinRationalEll) *
            Real.exp (L * s ^ 3 / 5) := by
    rw [← hFTC]
    apply intervalIntegral.norm_integral_le_of_norm_le hAt.le
    · filter_upwards with s hs
      have hs0 : 0 ≤ s := hA.le.trans hs.1.le
      have hpoint :=
        norm_prod_sub_productZeroBiasChar_le_tyurinSecondBranch
          u a hs0 hvar hthird
      dsimp [D]
      rw [norm_mul, norm_mul, Complex.norm_exp,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
      have hexpReal :
          Real.exp ((↑((s ^ 2 / 2 : ℝ)) : ℂ).re) =
            Real.exp (s ^ 2 / 2) := by
        norm_cast
      rw [hexpReal]
      calc
        Real.exp (s ^ 2 / 2) * s *
            ‖(∏ i, centeredBiasedSignChar (u i) (a i) s) -
              centeredBiasedSignProductZeroBiasChar u a s‖
            ≤ Real.exp (s ^ 2 / 2) * s *
                (L * s / (2 * tyurinRationalEll) *
                  Real.exp (-(s ^ 2) / 2 + L * s ^ 3 / 5)) :=
          mul_le_mul_of_nonneg_left hpoint
            (mul_nonneg (Real.exp_nonneg _) hs0)
        _ = L * s ^ 2 / (2 * tyurinRationalEll) *
            Real.exp (L * s ^ 3 / 5) := by
          rw [show
              Real.exp (s ^ 2 / 2) * s *
                  (L * s / (2 * tyurinRationalEll) *
                    Real.exp (-(s ^ 2) / 2 + L * s ^ 3 / 5)) =
                L * s ^ 2 / (2 * tyurinRationalEll) *
                  (Real.exp (s ^ 2 / 2) *
                    Real.exp (-(s ^ 2) / 2 + L * s ^ 3 / 5)) by ring]
          rw [← Real.exp_add]
          congr 1
          ring_nf
    · have hscalar :
          Continuous (fun s : ℝ =>
            L * s ^ 2 / (2 * tyurinRationalEll) *
              Real.exp (L * s ^ 3 / 5)) := by
        fun_prop
      exact hscalar.intervalIntegrable _ _
  have htriangle :
      ‖F t - 1‖ ≤ ‖F t - F A‖ + ‖F A - 1‖ := by
    have hdecomp : F t - 1 = (F t - F A) + (F A - 1) := by ring
    rw [hdecomp]
    exact norm_add_le _ _
  dsimp only [F, A] at htriangle hfirst hsecond ⊢
  exact htriangle.trans (add_le_add hsecond hfirst) |>.trans_eq
    (add_comm _ _)

private theorem norm_product_sub_standardGaussian_eq_renormalized
    (u a : ι → ℝ) (t : ℝ) :
    ‖(∏ i, centeredBiasedSignChar (u i) (a i) t) -
        ((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ)‖ =
      Real.exp (-(t ^ 2) / 2) *
        ‖Complex.exp (((t ^ 2 / 2 : ℝ) : ℂ)) *
            (∏ i, centeredBiasedSignChar (u i) (a i) t) - 1‖ := by
  have hfactor :
      (∏ i, centeredBiasedSignChar (u i) (a i) t) -
          ((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ) =
        ((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ) *
          (Complex.exp (((t ^ 2 / 2 : ℝ) : ℂ)) *
            (∏ i, centeredBiasedSignChar (u i) (a i) t) - 1) := by
    have hcancel :
        ((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ) *
            Complex.exp (((t ^ 2 / 2 : ℝ) : ℂ)) = 1 := by
      rw [← Complex.ofReal_exp]
      push_cast
      rw [← Complex.exp_add]
      ring_nf
      simp
    symm
    calc
      ((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ) *
            (Complex.exp (((t ^ 2 / 2 : ℝ) : ℂ)) *
              (∏ i, centeredBiasedSignChar (u i) (a i) t) - 1)
          = (((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ) *
              Complex.exp (((t ^ 2 / 2 : ℝ) : ℂ))) *
                (∏ i, centeredBiasedSignChar (u i) (a i) t) -
              ((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ) := by ring
      _ = _ := by rw [hcancel, one_mul]
  rw [hfactor, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]

/-- Complete nonnegative-frequency `delta₂` characteristic discrepancy. -/
theorem norm_product_sub_standardGaussian_le_tyurinDeltaTwo
    (u a : ι → ℝ) {t L : ℝ}
    (ht : 0 ≤ t) (hL : 0 < L)
    (hvar : ∑ i, biasedSignVarianceTerm (u i) (a i) = 1)
    (hthird : ∑ i, biasedSignThirdMomentTerm (u i) (a i) = L) :
    ‖(∏ i, centeredBiasedSignChar (u i) (a i) t) -
        ((Real.exp (-(t ^ 2) / 2) : ℝ) : ℂ)‖ ≤
      tyurinDeltaTwo L t := by
  classical
  let R : ℝ := lyapunovThirdRoot L
  let A : ℝ := 5 / (3 * R)
  rw [norm_product_sub_standardGaussian_eq_renormalized]
  unfold tyurinDeltaTwo
  dsimp only
  rw [abs_of_nonneg ht]
  by_cases hbranch : t * R ≤ 5 / 3
  · rw [if_pos hbranch]
    have hrenorm :=
      norm_gaussianRenormalized_product_sub_one_le_tyurinFirstBranch
        u a ht hL.le hvar hthird hbranch
    apply (mul_le_mul_of_nonneg_left hrenorm
      (Real.exp_nonneg _)).trans_eq
    rw [show
        (∫ s : ℝ in 0..t,
            L * s ^ 2 / 2 *
              Real.exp (lyapunovVarianceCap L * s ^ 2 / 2)) =
          L * (∫ s : ℝ in 0..t,
            s ^ 2 / 2 *
              Real.exp (lyapunovVarianceCap L * s ^ 2 / 2)) by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      ring]
    ring
  · rw [if_neg hbranch]
    have hrenorm :=
      norm_gaussianRenormalized_product_sub_one_le_tyurinSecondBranch
        u a hL hvar hthird hbranch
    apply (mul_le_mul_of_nonneg_left hrenorm
      (Real.exp_nonneg _)).trans_eq
    have hfirst :
        (∫ s : ℝ in 0..A,
            L * s ^ 2 / 2 *
              Real.exp (lyapunovVarianceCap L * s ^ 2 / 2)) =
          L * (∫ s : ℝ in 0..A,
            s ^ 2 / 2 *
              Real.exp (lyapunovVarianceCap L * s ^ 2 / 2)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      ring
    have hsecond :
        (∫ s : ℝ in A..t,
            L * s ^ 2 / (2 * tyurinRationalEll) *
              Real.exp (L * s ^ 3 / 5)) =
          L * (∫ s : ℝ in A..t,
            s ^ 2 / (2 * tyurinRationalEll) *
              Real.exp (L * s ^ 3 / 5)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      ring
    dsimp only [A, R] at hfirst hsecond ⊢
    rw [hfirst, hsecond]
    ring

/-- `delta₂` specialized to the actual standardized tilted-Rademacher law. -/
theorem norm_rademacherTiltedCharFun_sub_standardGaussian_le_deltaTwo_of_nonneg
    (b : ι → ℝ) (x : ℝ) {t : ℝ}
    (hnorm : ∑ i, b i ^ 2 = 1) (ht : 0 ≤ t) :
    ‖charFun (rademacherTiltedStandardizedLaw b x) t -
        charFun (gaussianReal 0 1) t‖ ≤
      tyurinDeltaTwo (rademacherLyapunovRatio b x) t := by
  classical
  let u : ι → ℝ := fun i => x * b i
  let a : ι → ℝ := fun i =>
    b i / tiltedRademacherStdDev u b
  have hb : ∃ i, b i ≠ 0 := by
    by_contra h
    push Not at h
    have hbzero : b = 0 := funext h
    subst b
    simp at hnorm
  have hvar :
      ∑ i, biasedSignVarianceTerm (u i) (a i) = 1 := by
    simpa only [biasedSignVarianceTerm, u, a] using
      standardizedTiltedRademacherVariance_eq_one u b hb
  have hthird :
      ∑ i, biasedSignThirdMomentTerm (u i) (a i) =
        rademacherLyapunovRatio b x := by
    change tiltedRademacherThirdMomentSum u a =
      rademacherLyapunovRatio b x
    exact tiltedRademacherThirdMomentSum_standardized_specialize
      b x hnorm
  have hchar :
      charFun (rademacherTiltedStandardizedLaw b x) t =
        ∏ i, centeredBiasedSignChar (u i) (a i) t := by
    rw [charFun_rademacherTiltedStandardizedLaw_eq_prod]
    apply Finset.prod_congr rfl
    intro i _
    dsimp [u, a]
    rw [tiltedRademacherStdDev_specialize]
  rw [hchar, charFun_standardGaussian]
  exact norm_product_sub_standardGaussian_le_tyurinDeltaTwo
    u a ht (rademacherLyapunovRatio_pos b x hnorm) hvar hthird

private theorem norm_charFun_sub_standardGaussian_neg
    (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    ‖charFun μ (-t) - charFun (gaussianReal 0 1) (-t)‖ =
      ‖charFun μ t - charFun (gaussianReal 0 1) t‖ := by
  rw [charFun_neg, charFun_neg, ← map_sub, Complex.norm_conj]

theorem norm_rademacherTiltedCharFun_sub_standardGaussian_le_deltaOne_all
    (b : ι → ℝ) (x t : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1) :
    ‖charFun (rademacherTiltedStandardizedLaw b x) t -
        charFun (gaussianReal 0 1) t‖ ≤
      tyurinDeltaOne (rademacherLyapunovRatio b x) t := by
  by_cases ht : 0 ≤ t
  · simpa [charFun_standardGaussian, tyurinDeltaOne,
      abs_of_nonneg ht] using
      norm_rademacherTiltedCharFun_sub_standardGaussian_le_deltaOne
        b x hnorm ht
  · have htneg : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht)
    have hraw :=
      norm_rademacherTiltedCharFun_sub_standardGaussian_le_deltaOne
        b x hnorm htneg
    have h :
        ‖charFun (rademacherTiltedStandardizedLaw b x) (-t) -
            charFun (gaussianReal 0 1) (-t)‖ ≤
          tyurinDeltaOne (rademacherLyapunovRatio b x) (-t) := by
      rw [charFun_standardGaussian]
      simpa only [tyurinDeltaOne, abs_neg, neg_sq,
        abs_of_nonneg htneg] using hraw
    rw [norm_charFun_sub_standardGaussian_neg] at h
    simpa only [tyurinDeltaOne_neg] using h

theorem norm_rademacherTiltedCharFun_sub_standardGaussian_le_deltaTwo_all
    (b : ι → ℝ) (x t : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1) :
    ‖charFun (rademacherTiltedStandardizedLaw b x) t -
        charFun (gaussianReal 0 1) t‖ ≤
      tyurinDeltaTwo (rademacherLyapunovRatio b x) t := by
  classical
  by_cases ht : 0 ≤ t
  · exact
      norm_rademacherTiltedCharFun_sub_standardGaussian_le_deltaTwo_of_nonneg
        b x hnorm ht
  · have htneg : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht)
    have h :=
      norm_rademacherTiltedCharFun_sub_standardGaussian_le_deltaTwo_of_nonneg
        b x hnorm htneg
    rw [norm_charFun_sub_standardGaussian_neg] at h
    simpa only [tyurinDeltaTwo_neg] using h

/-- The complete core minimum used by Tyurin's `D*` functional. -/
theorem norm_rademacherTiltedCharFun_sub_standardGaussian_le_tyurinCore
    (b : ι → ℝ) (x t : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1) :
    ‖charFun (rademacherTiltedStandardizedLaw b x) t -
        charFun (gaussianReal 0 1) t‖ ≤
      min
        (tyurinDeltaOne (rademacherLyapunovRatio b x) t)
        (tyurinDeltaTwo (rademacherLyapunovRatio b x) t) := by
  classical
  rw [le_min_iff]
  exact
    ⟨norm_rademacherTiltedCharFun_sub_standardGaussian_le_deltaOne_all
        b x t hnorm,
      norm_rademacherTiltedCharFun_sub_standardGaussian_le_deltaTwo_all
        b x t hnorm⟩

/-- Actual-law specialization of the complete global product envelope. -/
theorem norm_rademacherTiltedCharFun_le_tyurinProductEnvelope
    (b : ι → ℝ) (x t : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1) :
    ‖charFun (rademacherTiltedStandardizedLaw b x) t‖ ≤
      tyurinProductEnvelope (rademacherLyapunovRatio b x) t := by
  classical
  let u : ι → ℝ := fun i => x * b i
  let a : ι → ℝ := fun i =>
    b i / tiltedRademacherStdDev u b
  have hb : ∃ i, b i ≠ 0 := by
    by_contra h
    push Not at h
    have hbzero : b = 0 := funext h
    subst b
    simp at hnorm
  have hvar :
      ∑ i, biasedSignVarianceTerm (u i) (a i) = 1 := by
    simpa only [biasedSignVarianceTerm, u, a] using
      standardizedTiltedRademacherVariance_eq_one u b hb
  have hthird :
      ∑ i, biasedSignThirdMomentTerm (u i) (a i) =
        rademacherLyapunovRatio b x := by
    change tiltedRademacherThirdMomentSum u a =
      rademacherLyapunovRatio b x
    exact tiltedRademacherThirdMomentSum_standardized_specialize
      b x hnorm
  have hchar :
      charFun (rademacherTiltedStandardizedLaw b x) t =
        ∏ i, centeredBiasedSignChar (u i) (a i) t := by
    rw [charFun_rademacherTiltedStandardizedLaw_eq_prod]
    apply Finset.prod_congr rfl
    intro i _
    dsimp [u, a]
    rw [tiltedRademacherStdDev_specialize]
  rw [hchar]
  exact norm_prod_centeredBiasedSignChar_le_tyurinProductEnvelope
    u a (rademacherLyapunovRatio_nonneg b x) hvar hthird

end Probability
end CertifiedJL
