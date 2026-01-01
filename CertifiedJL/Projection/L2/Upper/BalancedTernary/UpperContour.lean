/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Distributions.Entry
import CertifiedJL.Model.Distributions.BalancedTernary.MGF
import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperFourthOrder
import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperRealDeficit
import CertifiedJL.Analysis.SmoothBounds.NegativeLaplace
import CertifiedJL.Probability.Finite.IidQuadratic
import CertifiedJL.Analysis.Gaussian.ShiftedGaussianInversion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Sparse upper-tail contour assembly

This module connects the actual sparse-matrix experiment to the positive-real
shifted-Gaussian contour.  It owns the probability, smoothing, Fubini, and iid
row-product steps.  Pointwise row-MGF estimates and the numerical contour
certificate remain separate inputs downstream.
-/

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory

namespace CertifiedJL

private theorem sparseMatrix_integrable_of_finitePMF {m d : ℕ}
    (f : (Fin m → Fin d → ℤ) → ℝ) :
    Integrable f (sparseRademacherMatrix m d).toMeasure := by
  rw [sparseRademacherMatrix_eq_map_uniformSeed]
  rw [← PMF.toMeasure_map
    (p := PMF.uniformOfFintype (SparseSeed m d))
    (f := sparseMatrix) (measurable_of_finite sparseMatrix)]
  apply (integrable_map_measure
    (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_finite sparseMatrix).aemeasurable).2
  exact Integrable.of_finite

private theorem sparseRow_integrable_of_finitePMF {d : ℕ}
    (f : (Fin d → ℤ) → ℝ) :
    Integrable f (sparseRademacherRow d).toMeasure := by
  rw [sparseRademacherRow_eq_map_uniformRowSeed]
  rw [← PMF.toMeasure_map
    (p := PMF.uniformOfFintype (SparseRowSeed d))
    (f := sparseRow) (measurable_of_finite sparseRow)]
  apply (integrable_map_measure
    (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_finite sparseRow).aemeasurable).2
  exact Integrable.of_finite

/-- The normalized unmodulated projection squared norm of a sparse matrix. -/
noncomputable def realProjectionSqNorm {m d : ℕ}
    (a : Fin d → ℝ) (J : Fin m → Fin d → ℤ) : ℝ :=
  ∑ j, (realRowDot (J j) a) ^ 2

/-- The U4 row bound after extracting the common real Gaussian factor. -/
noncomputable def sparseUpperFourthOrderNormalizedMajorant
    (profile lambda frequency : ℝ) : ℝ :=
  let s : ℂ := lambda + frequency * Complex.I
  Real.sqrt (1 - lambda) *
    (‖(1 - s) ^ (-1 / 2 : ℂ) -
        ((profile / 8 : ℝ) : ℂ) * s ^ 2 *
          (1 - s) ^ (-5 / 2 : ℂ)‖ +
      profile ^ 2 / 9216 *
        quadraticExpDerivativeMajorant 8 ‖s‖ lambda +
      11 * (profile * Real.sqrt profile) / 5760 *
        quadraticExpDerivativeMajorant 6 ‖s‖ lambda)

/-- Minimum of the normalized U4 and U8 row bounds. -/
noncomputable def sparseUpperContourRowMajorant
    (profile lambda frequency : ℝ) : ℝ :=
  min (sparseUpperFourthOrderNormalizedMajorant profile lambda frequency)
    (realRowDeficitCap
      (Real.sqrt profile * lambda / (1 - lambda)))

/-- Normalize any proved literal U4 comparison by the real Gaussian factor. -/
theorem normalized_rowMGF_le_fourthOrderMajorant_of_error
    {M : ℂ} {profile lambda frequency : ℝ}
    (herror :
      ‖M - (1 - (lambda + frequency * Complex.I)) ^ (-1 / 2 : ℂ) +
          ((profile / 8 : ℝ) : ℂ) *
            (lambda + frequency * Complex.I) ^ 2 *
            (1 - (lambda + frequency * Complex.I)) ^ (-5 / 2 : ℂ)‖ ≤
        profile ^ 2 / 9216 *
            quadraticExpDerivativeMajorant 8
              ‖lambda + frequency * Complex.I‖ lambda +
          11 * (profile * Real.sqrt profile) / 5760 *
            quadraticExpDerivativeMajorant 6
              ‖lambda + frequency * Complex.I‖ lambda) :
    Real.sqrt (1 - lambda) * ‖M‖ ≤
      sparseUpperFourthOrderNormalizedMajorant profile lambda frequency := by
  let s : ℂ := lambda + frequency * Complex.I
  have hsqrt : 0 ≤ Real.sqrt (1 - lambda) := Real.sqrt_nonneg _
  apply mul_le_mul_of_nonneg_left _ hsqrt
  have hsplit :
      M =
        (M - (1 - s) ^ (-1 / 2 : ℂ) +
          ((profile / 8 : ℝ) : ℂ) * s ^ 2 *
            (1 - s) ^ (-5 / 2 : ℂ)) +
        ((1 - s) ^ (-1 / 2 : ℂ) -
          ((profile / 8 : ℝ) : ℂ) * s ^ 2 *
            (1 - s) ^ (-5 / 2 : ℂ)) := by ring
  calc
    ‖M‖ = ‖(M - (1 - s) ^ (-1 / 2 : ℂ) +
          ((profile / 8 : ℝ) : ℂ) * s ^ 2 *
            (1 - s) ^ (-5 / 2 : ℂ)) +
        ((1 - s) ^ (-1 / 2 : ℂ) -
          ((profile / 8 : ℝ) : ℂ) * s ^ 2 *
            (1 - s) ^ (-5 / 2 : ℂ))‖ := congrArg norm hsplit
    _ ≤ ‖M - (1 - s) ^ (-1 / 2 : ℂ) +
          ((profile / 8 : ℝ) : ℂ) * s ^ 2 *
            (1 - s) ^ (-5 / 2 : ℂ)‖ +
        ‖(1 - s) ^ (-1 / 2 : ℂ) -
          ((profile / 8 : ℝ) : ℂ) * s ^ 2 *
            (1 - s) ^ (-5 / 2 : ℂ)‖ := norm_add_le _ _
    _ ≤ (profile ^ 2 / 9216 *
            quadraticExpDerivativeMajorant 8 ‖s‖ lambda +
          11 * (profile * Real.sqrt profile) / 5760 *
            quadraticExpDerivativeMajorant 6 ‖s‖ lambda) +
        ‖(1 - s) ^ (-1 / 2 : ℂ) -
          ((profile / 8 : ℝ) : ℂ) * s ^ 2 *
            (1 - s) ^ (-5 / 2 : ℂ)‖ := by
      gcongr
    _ = ‖(1 - s) ^ (-1 / 2 : ℂ) -
          ((profile / 8 : ℝ) : ℂ) * s ^ 2 *
            (1 - s) ^ (-5 / 2 : ℂ)‖ +
        profile ^ 2 / 9216 *
            quadraticExpDerivativeMajorant 8 ‖s‖ lambda +
          11 * (profile * Real.sqrt profile) / 5760 *
            quadraticExpDerivativeMajorant 6 ‖s‖ lambda := by ring

/-- The actual U8 estimate after extracting the same Gaussian factor. -/
theorem normalized_rowMGF_le_realDeficit
    {d : ℕ} (a : Fin d → ℝ) {lambda frequency : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (hnorm : ∑ i, a i ^ 2 = 1) :
    Real.sqrt (1 - lambda) *
        ‖quadraticComplexMGF
          (fun row : Fin d → ℤ => realRowDot row a)
          (sparseRademacherRow d).toMeasure (lambda + frequency * Complex.I)‖ ≤
      realRowDeficitCap
        (Real.sqrt (sparseProfileFourthMoment a) *
          lambda / (1 - lambda)) := by
  have hsqrt : 0 < Real.sqrt (1 - lambda) := Real.sqrt_pos.2 (sub_pos.mpr hlambda1)
  have h := norm_sparseRow_quadraticComplexMGF_le_realDeficit
    a hlambda0 hlambda1 hnorm (u := frequency)
  calc
    Real.sqrt (1 - lambda) *
        ‖quadraticComplexMGF
          (fun row : Fin d → ℤ => realRowDot row a)
          (sparseRademacherRow d).toMeasure (lambda + frequency * Complex.I)‖ ≤
        Real.sqrt (1 - lambda) *
          ((1 / Real.sqrt (1 - lambda)) *
            realRowDeficitCap
              (Real.sqrt (sparseProfileFourthMoment a) *
                lambda / (1 - lambda))) :=
      mul_le_mul_of_nonneg_left h hsqrt.le
    _ = realRowDeficitCap
        (Real.sqrt (sparseProfileFourthMoment a) *
          lambda / (1 - lambda)) := by field_simp [hsqrt.ne']

/-- U4 and U8 combine pointwise by the exact minimum used by the certificate. -/
theorem normalized_rowMGF_le_contourRowMajorant
    {d : ℕ} (a : Fin d → ℝ) {lambda frequency : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (hnorm : ∑ i, a i ^ 2 = 1)
    (hfourth :
      Real.sqrt (1 - lambda) *
          ‖quadraticComplexMGF
            (fun row : Fin d → ℤ => realRowDot row a)
            (sparseRademacherRow d).toMeasure (lambda + frequency * Complex.I)‖ ≤
        sparseUpperFourthOrderNormalizedMajorant
          (sparseProfileFourthMoment a) lambda frequency) :
    Real.sqrt (1 - lambda) *
        ‖quadraticComplexMGF
          (fun row : Fin d → ℤ => realRowDot row a)
          (sparseRademacherRow d).toMeasure (lambda + frequency * Complex.I)‖ ≤
      sparseUpperContourRowMajorant
        (sparseProfileFourthMoment a) lambda frequency := by
  exact le_min hfourth (normalized_rowMGF_le_realDeficit
    a hlambda0 hlambda1 hnorm)

/-- The norm integrand in the iid sparse contour is absolutely integrable. -/
theorem integrable_sparseUpperContourNorm
    {d : ℕ} (a : Fin d → ℝ) (m : ℕ)
    {sigma theta threshold lambda : ℝ}
    (hlambda : 0 < lambda) (hsigma : 0 < sigma) :
    Integrable (fun u : ℝ =>
      ‖shiftedGaussianContourWeight sigma theta threshold lambda u‖ *
        ‖quadraticComplexMGF
          (fun row : Fin d → ℤ => realRowDot row a)
          (sparseRademacherRow d).toMeasure (lambda + u * Complex.I) ^ m‖) := by
  exact integrable_finiteIidQuadraticContourNorm
    (sparseRademacherRow d) (fun row => realRowDot row a) m
      (fun f => sparseRow_integrable_of_finitePMF f) hlambda hsigma

/-- The sparse contour norm reduces exactly to twice the positive-frequency half. -/
theorem integral_sparseUpperContourNorm_eq_two_mul_Ioi
    {d : ℕ} (a : Fin d → ℝ) (m : ℕ)
    {sigma theta threshold lambda : ℝ}
    (hlambda : 0 < lambda) (hsigma : 0 < sigma) :
    (∫ u : ℝ,
      ‖shiftedGaussianContourWeight sigma theta threshold lambda u‖ *
        ‖quadraticComplexMGF
          (fun row : Fin d → ℤ => realRowDot row a)
          (sparseRademacherRow d).toMeasure (lambda + u * Complex.I) ^ m‖) =
      2 * ∫ u in Set.Ioi (0 : ℝ),
        ‖shiftedGaussianContourWeight sigma theta threshold lambda u‖ *
          ‖quadraticComplexMGF
            (fun row : Fin d → ℤ => realRowDot row a)
            (sparseRademacherRow d).toMeasure (lambda + u * Complex.I) ^ m‖ := by
  exact integral_finiteIidQuadraticContourNorm_eq_two_mul_Ioi
    (sparseRademacherRow d) (fun row => realRowDot row a) m
      (fun f => sparseRow_integrable_of_finitePMF f) hlambda hsigma

/-- The exact iid factorization of the normalized sparse-matrix projection-squared-norm MGF. -/
theorem complexMGF_realProjectionSqNorm_eq_pow
    {m d : ℕ} (a : Fin d → ℝ) (s : ℂ) :
    complexMGF (realProjectionSqNorm a)
        (sparseRademacherMatrix m d).toMeasure s =
      quadraticComplexMGF
        (fun row : Fin d → ℤ => realRowDot row a)
        (sparseRademacherRow d).toMeasure s ^ m := by
  rw [sparseRademacherMatrix_toMeasure]
  change complexMGF
      (iidRowValueSqNorm
        (fun row : Fin d → ℤ => realRowDot row a))
      (Measure.pi (fun _ : Fin m => (sparseRademacherRow d).toMeasure)) s = _
  exact complexMGF_iidRowValueSqNorm_eq_pow (m := m)
    (sparseRademacherRow d)
    (fun row : Fin d → ℤ => realRowDot row a) s

/-- The exact positive Chernoff bound for normalized sparse projection squared norm. -/
theorem sparseRademacherMatrix_realProjectionSqNorm_toReal_le_chernoff
    {m d : ℕ} (a : Fin d → ℝ) {threshold lambda : ℝ}
    (hlambda : 0 ≤ lambda) :
    (eventProbability (sparseRademacherMatrix m d)
        (fun J => threshold < realProjectionSqNorm a J)).toReal ≤
      Real.exp (-lambda * threshold) *
        (∫ row, Real.exp (lambda * (realRowDot row a) ^ 2) ∂
          (sparseRademacherRow d).toMeasure) ^ m := by
  let X : (Fin m → Fin d → ℤ) → ℝ := realProjectionSqNorm a
  have hreal : Integrable (fun J => Real.exp (lambda * X J))
      (sparseRademacherMatrix m d).toMeasure :=
    sparseMatrix_integrable_of_finitePMF _
  rw [eventProbability_eq_toMeasure]
  calc
    (sparseRademacherMatrix m d).toMeasure.real (X ⁻¹' Set.Ioi threshold) ≤
        (sparseRademacherMatrix m d).toMeasure.real {J | threshold ≤ X J} := by
      apply measureReal_mono
      · intro J hJ
        exact (show threshold < X J from hJ).le
      · exact measure_ne_top _ _
    _ ≤ Real.exp (-lambda * threshold) *
        mgf X (sparseRademacherMatrix m d).toMeasure lambda :=
      measure_ge_le_exp_mul_mgf threshold hlambda hreal
    _ = Real.exp (-lambda * threshold) *
        (∫ row, Real.exp (lambda * (realRowDot row a) ^ 2) ∂
          (sparseRademacherRow d).toMeasure) ^ m := by
      congr 1
      rw [mgf]
      calc
        (∫ J, Real.exp (lambda * realProjectionSqNorm a J) ∂
            (sparseRademacherMatrix m d).toMeasure) =
            ∫ J, ∏ j, Real.exp
              (lambda * (realRowDot (J j) a) ^ 2) ∂
                (sparseRademacherMatrix m d).toMeasure := by
          apply integral_congr_ae
          filter_upwards [] with J
          rw [realProjectionSqNorm, Finset.mul_sum, Real.exp_sum]
        _ = ∏ _j : Fin m, ∫ row, Real.exp
              (lambda * (realRowDot row a) ^ 2) ∂
                (sparseRademacherRow d).toMeasure := by
          rw [sparseRademacherMatrix_toMeasure]
          exact MeasureTheory.integral_fintype_prod_eq_prod
            (μ := fun _ : Fin m => (sparseRademacherRow d).toMeasure)
            (fun _ row => Real.exp (lambda * (realRowDot row a) ^ 2))
        _ = (∫ row, Real.exp (lambda * (realRowDot row a) ^ 2) ∂
              (sparseRademacherRow d).toMeasure) ^ m := by simp

/-- The U8 real deficit supplies the complete coefficient-specific Chernoff bound. -/
theorem sparseRademacherMatrix_realProjectionSqNorm_toReal_le_realDeficit
    {m d : ℕ} (a : Fin d → ℝ) {threshold lambda : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (hnorm : ∑ i, a i ^ 2 = 1) :
    (eventProbability (sparseRademacherMatrix m d)
        (fun J => threshold < realProjectionSqNorm a J)).toReal ≤
      Real.exp (-lambda * threshold) *
        ((1 / Real.sqrt (1 - lambda)) *
          realRowDeficitCap
            (Real.sqrt (sparseProfileFourthMoment a) *
              lambda / (1 - lambda))) ^ m := by
  refine (sparseRademacherMatrix_realProjectionSqNorm_toReal_le_chernoff
    a hlambda0).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply pow_le_pow_left₀
  · exact integral_nonneg fun _ => (Real.exp_pos _).le
  · exact realSparseRowDeficit a hlambda0 hlambda1 hnorm

/-- On a high-profile range, antitonicity permits evaluation at its left endpoint. -/
theorem sparseRademacherMatrix_realProjectionSqNorm_toReal_le_realDeficit_at_profileLeft
    {m d : ℕ} (a : Fin d → ℝ) {threshold lambda profileLeft : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (hnorm : ∑ i, a i ^ 2 = 1)
    (hprofile : profileLeft ≤ sparseProfileFourthMoment a) :
    (eventProbability (sparseRademacherMatrix m d)
        (fun J => threshold < realProjectionSqNorm a J)).toReal ≤
      Real.exp (-lambda * threshold) *
        ((1 / Real.sqrt (1 - lambda)) *
          realRowDeficitCap
            (Real.sqrt profileLeft * lambda / (1 - lambda))) ^ m := by
  refine (sparseRademacherMatrix_realProjectionSqNorm_toReal_le_realDeficit
    a hlambda0 hlambda1 hnorm).trans ?_
  have hden : 0 < 1 - lambda := sub_pos.mpr hlambda1
  let v : ℝ := Real.sqrt (sparseProfileFourthMoment a) *
    lambda / (1 - lambda)
  let vLeft : ℝ := Real.sqrt profileLeft * lambda / (1 - lambda)
  have hvLeft : 0 ≤ vLeft := by dsimp only [vLeft]; positivity
  have hv : 0 ≤ v := by
    dsimp only [v]
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hlambda0) hden.le
  have hvle : vLeft ≤ v := by
    dsimp only [vLeft, v]
    gcongr
  have hcap : realRowDeficitCap v ≤ realRowDeficitCap vLeft :=
    antitoneOn_realRowDeficitCap hvLeft hv hvle
  have hcapNonneg : 0 ≤ realRowDeficitCap v := by
    unfold realRowDeficitCap
    have hvone : 0 < 1 + v := by linarith
    positivity
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply pow_le_pow_left₀
  · exact mul_nonneg (by positivity) hcapNonneg
  · exact mul_le_mul_of_nonneg_left hcap (by positivity)

/--
The actual sparse-matrix strict upper tail is bounded by the exact U10 contour
whose probability input is the `m`th power of the one-row quadratic MGF.
-/
theorem sparseRademacherMatrix_realProjectionSqNorm_toReal_le_contour
    {m d : ℕ} (a : Fin d → ℝ)
    {sigma theta t lambda : ℝ}
    (hsigma : 0 < sigma) (hlambda : 0 < lambda) :
    (eventProbability (sparseRademacherMatrix m d)
        (fun J => t < realProjectionSqNorm a J)).toReal ≤
      ∫ u : ℝ, ‖shiftedGaussianContourWeight sigma theta t lambda u‖ *
        ‖quadraticComplexMGF
          (fun row : Fin d → ℤ => realRowDot row a)
          (sparseRademacherRow d).toMeasure (lambda + u * Complex.I) ^ m‖ := by
  change (eventProbability (sparseRademacherMatrix m d)
      (fun J => t < iidRowValueSqNorm
        (fun row : Fin d → ℤ => realRowDot row a) J)).toReal ≤ _
  exact finiteIidRowValueSqNorm_toReal_le_contour
    (sparseRademacherRow d) (sparseRademacherMatrix m d)
    (sparseRademacherMatrix_toMeasure m d)
    (fun f => sparseMatrix_integrable_of_finitePMF f)
    (fun row : Fin d → ℤ => realRowDot row a) hsigma hlambda

/-- The actual sparse upper tail is bounded directly by twice the certified
positive-frequency contour integral. -/
theorem sparseRademacherMatrix_realProjectionSqNorm_toReal_le_positiveContour
    {m d : ℕ} (a : Fin d → ℝ)
    {sigma theta t lambda : ℝ}
    (hsigma : 0 < sigma) (hlambda : 0 < lambda) :
    (eventProbability (sparseRademacherMatrix m d)
        (fun J => t < realProjectionSqNorm a J)).toReal ≤
      2 * ∫ u in Set.Ioi (0 : ℝ),
        ‖shiftedGaussianContourWeight sigma theta t lambda u‖ *
          ‖quadraticComplexMGF
            (fun row : Fin d → ℤ => realRowDot row a)
            (sparseRademacherRow d).toMeasure (lambda + u * Complex.I) ^ m‖ := by
  change (eventProbability (sparseRademacherMatrix m d)
      (fun J => t < iidRowValueSqNorm
        (fun row : Fin d → ℤ => realRowDot row a) J)).toReal ≤ _
  exact finiteIidRowValueSqNorm_toReal_le_positiveContour
    (sparseRademacherRow d) (sparseRademacherMatrix m d)
    (sparseRademacherMatrix_toMeasure m d)
    (fun f => sparseRow_integrable_of_finitePMF f)
    (fun f => sparseMatrix_integrable_of_finitePMF f)
    (fun row : Fin d → ℤ => realRowDot row a) hsigma hlambda

end CertifiedJL
