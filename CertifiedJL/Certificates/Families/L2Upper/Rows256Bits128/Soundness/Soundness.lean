/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Transcendental.Cosh
import CertifiedJL.Arithmetic.Transcendental.Sinh
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.RowSoundness
import CertifiedJL.Certificates.Shared.UpperContourSoundness
import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperContourQuadrature
import CertifiedJL.Analysis.Fourier.CenteredUniformSmoothing

/-!
# Semantic soundness of the centered-hybrid sparse upper certificate

This layer is deliberately one-sided.  The executable cells store rational
upper surrogates, not intervals containing every transcendental value.
-/

namespace CertifiedJL
namespace SparseUpperHybrid

open UpperContourKernel
open MeasureTheory Set

set_option maxRecDepth 10000

private theorem upper_le_upperRat_of_contains
    {p : ℕ} {I : Interval p} {x : ℝ} (hI : I.Contains x) :
    x ≤ (I.upperRat : ℝ) := by
  simpa only [Interval.upperRat, Dyadic.cast_toRat] using hI.2

/-- A checked exponential enclosure can validate the compact evaluator's
rational `sinhUpper` scalar once per profile box. -/
theorem sinh_le_sinhUpper_of_check
    (box : ProfileBox)
    (hargument : 0 ≤ box.uniformHalfWidth * box.lam)
    (hargumentUpper : box.uniformHalfWidth * box.lam < (2 ^ 30 : ℕ))
    (hbase : 0 < (Interval.ofRat precision
      (1 - box.uniformHalfWidth * box.lam / (2 ^ 30 : ℕ))).lo)
    (hcheck : (Sinh.enclosure precision
      (box.uniformHalfWidth * box.lam) 30).upperRat ≤
        sinhUpper (box.uniformHalfWidth * box.lam)) :
    Real.sinh ((box.uniformHalfWidth * box.lam : ℚ) : ℝ) ≤
      (sinhUpper (box.uniformHalfWidth * box.lam) : ℝ) := by
  have henclosure := Sinh.enclosure_contains
    (p := precision) (k := 30) hargument hargumentUpper hbase
  calc
    Real.sinh ((box.uniformHalfWidth * box.lam : ℚ) : ℝ) ≤
        ((Sinh.enclosure precision
          (box.uniformHalfWidth * box.lam) 30).upperRat : ℝ) :=
      upper_le_upperRat_of_contains henclosure
    _ ≤ (sinhUpper (box.uniformHalfWidth * box.lam) : ℝ) := by
      exact_mod_cast hcheck

/-- One compact rational cell factor bounds the true centered-uniform
transform throughout the cell.  This is intentionally an upper-endpoint
statement rather than a false full-containment claim. -/
theorem compactNoiseUpper_bounds
    (box : ProfileBox) (frequencyLeft : ℚ) (frequency : ℝ)
    (hh : 0 < (box.uniformHalfWidth : ℝ))
    (hlambda : 0 < (box.lam : ℝ))
    (hfrequencyLeft : 0 ≤ (frequencyLeft : ℝ))
    (hfrequency : (frequencyLeft : ℝ) ≤ frequency)
    (hsinh : Real.sinh
      ((box.uniformHalfWidth * box.lam : ℚ) : ℝ) ≤
        (sinhUpper (box.uniformHalfWidth * box.lam) : ℝ))
    (hsqrtNumerator : 0 ≤
      ((frac precision (sinhUpper
        (box.uniformHalfWidth * box.lam))).square +
          frac precision
            (min 1 ((box.uniformHalfWidth * frequencyLeft) ^ 2))).lo)
    (hsqrtDenominator : 0 ≤
      (frac precision
        (box.lam ^ 2 + frequencyLeft ^ 2)).lo)
    (hdenominator : 0 <
      (frac precision box.uniformHalfWidth *
        (frac precision
          (box.lam ^ 2 + frequencyLeft ^ 2)).sqrt).lo) :
    ‖centeredUniformLaplace (box.uniformHalfWidth : ℝ)
        (box.lam : ℝ) frequency‖ ^ box.uniformCount ≤
      ((compactNoiseUpper box frequencyLeft).upperRat : ℝ) := by
  let S : ℝ := (sinhUpper
    (box.uniformHalfWidth * box.lam) : ℚ)
  let sineUpper : ℝ :=
    (min 1 ((box.uniformHalfWidth * frequencyLeft) ^ 2) : ℚ)
  let numeratorValue : ℝ := Real.sqrt (S ^ 2 + sineUpper)
  let denominatorValue : ℝ :=
    (box.uniformHalfWidth : ℝ) *
      Real.sqrt ((box.lam : ℝ) ^ 2 + (frequencyLeft : ℝ) ^ 2)
  let surrogate : ℝ := numeratorValue / denominatorValue
  have hsinh' : Real.sinh
      ((box.uniformHalfWidth : ℝ) * (box.lam : ℝ)) ≤ S := by
    simpa only [S, Rat.cast_mul] using hsinh
  have hfactor :
      ‖centeredUniformLaplace (box.uniformHalfWidth : ℝ)
          (box.lam : ℝ) frequency‖ ≤ surrogate := by
    have hraw := norm_centeredUniformLaplace_le_compactEnvelope hh hlambda
      hfrequencyLeft hfrequency hsinh'
    have heq :
        Real.sqrt
          ((S ^ 2 + min 1
              (((box.uniformHalfWidth : ℝ) * (frequencyLeft : ℝ)) ^ 2)) /
            ((box.uniformHalfWidth : ℝ) ^ 2 *
              ((box.lam : ℝ) ^ 2 + (frequencyLeft : ℝ) ^ 2))) =
          surrogate := by
      rw [Real.sqrt_div (by positivity)]
      rw [Real.sqrt_mul (sq_nonneg (box.uniformHalfWidth : ℝ)),
        Real.sqrt_sq_eq_abs, abs_of_pos hh]
      simp [surrogate, numeratorValue, denominatorValue, sineUpper]
    rw [heq] at hraw
    simpa [S] using hraw
  have hS : (frac precision (sinhUpper
      (box.uniformHalfWidth * box.lam))).Contains S := by
    simpa [S, frac] using Interval.contains_ofRat precision
      (sinhUpper (box.uniformHalfWidth * box.lam))
  have hSsq := Interval.contains_square hS
  have hsine : (frac precision
      (min 1 ((box.uniformHalfWidth * frequencyLeft) ^ 2))).Contains
        sineUpper := by
    have hraw := Interval.contains_ofRat precision
      (min 1 ((box.uniformHalfWidth * frequencyLeft) ^ 2))
    convert hraw using 1 <;> simp [sineUpper, frac]
  have hnumeratorBase := Interval.contains_add hSsq hsine
  have hnumerator :
      ((frac precision (sinhUpper
          (box.uniformHalfWidth * box.lam))).square +
        frac precision
          (min 1 ((box.uniformHalfWidth * frequencyLeft) ^ 2))).sqrt.Contains
        numeratorValue := by
    exact Interval.contains_sqrt hsqrtNumerator hnumeratorBase
  have hdenominatorBase :
      (frac precision
        (box.lam ^ 2 + frequencyLeft ^ 2)).Contains
      ((box.lam : ℝ) ^ 2 + (frequencyLeft : ℝ) ^ 2) := by
    have hraw := Interval.contains_ofRat precision
      (box.lam ^ 2 + frequencyLeft ^ 2)
    convert hraw using 1 <;> norm_num [frac]
  have hdenominatorSqrt :=
    Interval.contains_sqrt hsqrtDenominator hdenominatorBase
  have hhInterval : (frac precision box.uniformHalfWidth).Contains
      (box.uniformHalfWidth : ℝ) := by
    simpa [frac] using Interval.contains_ofRat precision box.uniformHalfWidth
  have hdenominatorValue :
      (frac precision box.uniformHalfWidth *
        (frac precision
          (box.lam ^ 2 + frequencyLeft ^ 2)).sqrt).Contains
        denominatorValue := by
    exact Interval.contains_mul hhInterval hdenominatorSqrt
  have hsurrogate :
      (divide
        ((frac precision (sinhUpper
          (box.uniformHalfWidth * box.lam))).square +
            frac precision
              (min 1 ((box.uniformHalfWidth * frequencyLeft) ^ 2))).sqrt
        (frac precision box.uniformHalfWidth *
          (frac precision
            (box.lam ^ 2 + frequencyLeft ^ 2)).sqrt)).Contains
        surrogate := by
    exact contains_divide_of_pos hdenominator hnumerator hdenominatorValue
  have hpower := contains_powNat hsurrogate box.uniformCount
  have hfactorNonneg := norm_nonneg
    (centeredUniformLaplace (box.uniformHalfWidth : ℝ)
      (box.lam : ℝ) frequency)
  have hpowLe :
      ‖centeredUniformLaplace (box.uniformHalfWidth : ℝ)
          (box.lam : ℝ) frequency‖ ^ box.uniformCount ≤
        surrogate ^ box.uniformCount :=
    pow_le_pow_left₀ hfactorNonneg hfactor box.uniformCount
  exact hpowLe.trans (upper_le_upperRat_of_contains hpower)

/-- The literal sparse-row upper endpoint selected by a hybrid cell. -/
noncomputable def hybridCellRowUpperValue
    (box : ProfileBox) (segment : Segment) (index : ℕ) : ℝ :=
  let frequencyLeft := segment.start + index * segment.mesh
  let frequencyRight := frequencyLeft + segment.mesh
  let expressionLeft := rowExpressionOnCell
    box.profileLeft frequencyLeft frequencyRight box.lam
  let expressionRight := rowExpressionOnCell
    box.profileRight frequencyLeft frequencyRight box.lam
  let cap := realCapUpper precision box.profileLeft box.lam
  Dyadic.toReal precision
    (min cap.hi (max expressionLeft.hi expressionRight.hi))

/-- The true positive-frequency integrand after factoring out the centered
hybrid prefactor. -/
noncomputable def actualHybridIntegrand
    (box : ProfileBox) (profile frequency : ℝ) : ℝ :=
  Real.exp (-((gaussianSigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
    sparseUpperContourRowMajorant
      profile (box.lam : ℝ) frequency ^ rows *
    ‖centeredUniformLaplace (box.uniformHalfWidth : ℝ)
      (box.lam : ℝ) frequency‖ ^ box.uniformCount *
    (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2))

/-- The deterministic hybrid integrand is absolutely integrable on the
line.  The centered-uniform factor is uniformly bounded, so the existing
Gaussian envelope remains an integrable dominator. -/
theorem integrable_actualHybridIntegrand
    (box : ProfileBox) (profile : ℝ) (hprofile : 0 ≤ profile)
    (hh : 0 < (box.uniformHalfWidth : ℝ))
    (hlam : 0 < (box.lam : ℝ)) (hlamOne : (box.lam : ℝ) < 1) :
    Integrable (actualHybridIntegrand box profile) := by
  let base : ℝ → ℝ :=
    gaussianSparseRowIntegrand box.lam gaussianSigma profile
  let constant : ℝ :=
    Real.exp ((box.lam : ℝ) * (box.uniformHalfWidth : ℝ)) ^
      box.uniformCount
  have hbase : Integrable base := by
    exact integrable_gaussianSparseRowIntegrand box.lam gaussianSigma
      profile hprofile hlam hlamOne (by norm_num [gaussianSigma])
  have hnoise : ∀ frequency : ℝ,
      ‖centeredUniformLaplace (box.uniformHalfWidth : ℝ)
        (box.lam : ℝ) frequency‖ ^ box.uniformCount ≤ constant := by
    intro frequency
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_centeredUniformLaplace_le hh hlam frequency) box.uniformCount
  have hcontinuousNoise : Continuous (fun frequency : ℝ =>
      ‖centeredUniformLaplace (box.uniformHalfWidth : ℝ)
        (box.lam : ℝ) frequency‖ ^ box.uniformCount) := by
    unfold centeredUniformLaplace
    apply Continuous.pow
    apply Continuous.norm
    apply Continuous.div₀
    · fun_prop
    · fun_prop
    · intro frequency
      apply mul_ne_zero (by exact_mod_cast hh.ne')
      intro hzero
      have hre := congrArg Complex.re hzero
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul,
        sub_zero, mul_zero, add_zero, Complex.zero_re] at hre
      exact hlam.ne' hre
  have hproductMeasurable :=
    hbase.aestronglyMeasurable.mul hcontinuousNoise.aestronglyMeasurable
  have hactualMeasurable :
      AEStronglyMeasurable (actualHybridIntegrand box profile) := by
    apply hproductMeasurable.congr
    filter_upwards [] with frequency
    change base frequency *
      ‖centeredUniformLaplace (box.uniformHalfWidth : ℝ)
        (box.lam : ℝ) frequency‖ ^ box.uniformCount =
      actualHybridIntegrand box profile frequency
    unfold actualHybridIntegrand base gaussianSparseRowIntegrand
    ring
  refine (hbase.const_mul constant).mono'
    hactualMeasurable ?_
  filter_upwards [] with frequency
  have hbaseNonneg : 0 ≤ base frequency := by
    unfold base gaussianSparseRowIntegrand
    positivity [sparseUpperContourRowMajorant_nonneg
      (frequency := frequency) hprofile hlam.le hlamOne]
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · unfold actualHybridIntegrand base
    calc
      _ = gaussianSparseRowIntegrand box.lam gaussianSigma profile frequency *
          ‖centeredUniformLaplace (box.uniformHalfWidth : ℝ)
            (box.lam : ℝ) frequency‖ ^ box.uniformCount := by
        unfold gaussianSparseRowIntegrand
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hnoise frequency) hbaseNonneg
      _ = constant * base frequency := mul_comm _ _
  · unfold actualHybridIntegrand
    positivity [sparseUpperContourRowMajorant_nonneg
      (frequency := frequency) hprofile hlam.le hlamOne]

/-- One semantic rectangle corresponding to a hybrid cell.  Its compact
factor is deliberately the checked upper endpoint rather than a claimed
interval enclosure of the transcendental value. -/
noncomputable def hybridCellRectangleValue
    (box : ProfileBox) (segment : Segment) (index : ℕ) : ℝ :=
  let frequencyLeft := segment.start + index * segment.mesh
  (segment.mesh : ℝ) *
    hybridCellRowUpperValue box segment index ^ rows *
    ((compactNoiseUpper box frequencyLeft).upperRat : ℝ) *
    Real.exp (-((gaussianSigma : ℝ) ^ 2 / 2) *
      (frequencyLeft : ℝ) ^ 2) *
    (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + (frequencyLeft : ℝ) ^ 2))

/-- Cellwise analytic domination by the literal rectangle encoded by the
hybrid evaluator. -/
theorem actualHybridIntegrand_le_rectangle
    (box : ProfileBox) (segment : Segment) (index : ℕ)
    (profile frequency : ℝ)
    (hprofile : 0 ≤ profile)
    (hlam : 0 < (box.lam : ℝ)) (hlamOne : (box.lam : ℝ) < 1)
    (hmesh : 0 ≤ (segment.mesh : ℝ))
    (hfrequencyLeft : 0 ≤
      ((segment.start + index * segment.mesh : ℚ) : ℝ))
    (hfrequency :
      ((segment.start + index * segment.mesh : ℚ) : ℝ) ≤ frequency)
    (hrow : sparseUpperContourRowMajorant
        profile (box.lam : ℝ) frequency ≤
      hybridCellRowUpperValue box segment index)
    (hcompact :
      ‖centeredUniformLaplace (box.uniformHalfWidth : ℝ)
          (box.lam : ℝ) frequency‖ ^ box.uniformCount ≤
        ((compactNoiseUpper box
          (segment.start + index * segment.mesh)).upperRat : ℝ)) :
    (segment.mesh : ℝ) * actualHybridIntegrand box profile frequency ≤
      hybridCellRectangleValue box segment index := by
  let left : ℝ :=
    ((segment.start + index * segment.mesh : ℚ) : ℝ)
  have hweight := gaussianQuadratureWeight_le_of_le
    (alpha := (gaussianSigma : ℝ) ^ 2 / 2)
    (lambda := (box.lam : ℝ)) (frequencyLeft := left)
    (frequency := frequency) (by positivity) hlam hfrequencyLeft hfrequency
  have hrowNonneg :=
    sparseUpperContourRowMajorant_nonneg
      (frequency := frequency) hprofile hlam.le hlamOne
  have hrowPower := pow_le_pow_left₀ hrowNonneg hrow rows
  have hcompactNonneg : 0 ≤
      ‖centeredUniformLaplace (box.uniformHalfWidth : ℝ)
        (box.lam : ℝ) frequency‖ ^ box.uniformCount := by positivity
  have hcompactUpperNonneg : 0 ≤
      ((compactNoiseUpper box
        (segment.start + index * segment.mesh)).upperRat : ℝ) :=
    hcompactNonneg.trans hcompact
  have hrowUpperPowerNonneg : 0 ≤
      hybridCellRowUpperValue box segment index ^ rows :=
    (pow_nonneg hrowNonneg rows).trans hrowPower
  have hweightRightNonneg : 0 ≤
      Real.exp (-((gaussianSigma : ℝ) ^ 2 / 2) *
        ((segment.start + index * segment.mesh : ℚ) : ℝ) ^ 2) *
      (1 / Real.sqrt ((box.lam : ℝ) ^ 2 +
        ((segment.start + index * segment.mesh : ℚ) : ℝ) ^ 2)) := by
    positivity
  have hrowCompact := mul_le_mul hrowPower hcompact hcompactNonneg
    hrowUpperPowerNonneg
  have hproduct := mul_le_mul hweight hrowCompact
    (mul_nonneg (pow_nonneg hrowNonneg rows) hcompactNonneg)
    hweightRightNonneg
  unfold actualHybridIntegrand hybridCellRectangleValue
  dsimp only [left]
  calc
    _ = (segment.mesh : ℝ) *
        ((Real.exp (-((gaussianSigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
          (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2))) *
        (sparseUpperContourRowMajorant
          profile (box.lam : ℝ) frequency ^ rows *
        ‖centeredUniformLaplace (box.uniformHalfWidth : ℝ)
          (box.lam : ℝ) frequency‖ ^ box.uniformCount)) := by ring
    _ ≤ (segment.mesh : ℝ) *
        ((Real.exp (-((gaussianSigma : ℝ) ^ 2 / 2) *
          ((segment.start + index * segment.mesh : ℚ) : ℝ) ^ 2) *
          (1 / Real.sqrt ((box.lam : ℝ) ^ 2 +
            ((segment.start + index * segment.mesh : ℚ) : ℝ) ^ 2))) *
        (hybridCellRowUpperValue box segment index ^ rows *
          ((compactNoiseUpper box
            (segment.start + index * segment.mesh)).upperRat : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hproduct hmesh
    _ = _ := by ring

/-- The outward-rounded hybrid cell upper endpoint dominates its literal
rectangle once the ordinary interval factors are valid. -/
theorem hybridCellRectangleValue_le_upperRat
    (box : ProfileBox) (segment : Segment) (index : ℕ)
    (hmeshNonneg : 0 ≤ (segment.mesh : ℝ))
    (hrowValueNonneg : 0 ≤ hybridCellRowUpperValue box segment index ^ rows)
    (hrowUpper : hybridCellRowUpperValue box segment index ^ rows ≤
      ((((Interval.mk 0
        (min (realCapUpper precision box.profileLeft box.lam).hi
          (max
            (rowExpressionOnCell box.profileLeft
              (segment.start + index * segment.mesh)
              (segment.start + index * segment.mesh + segment.mesh) box.lam).hi
            (rowExpressionOnCell box.profileRight
              (segment.start + index * segment.mesh)
              (segment.start + index * segment.mesh + segment.mesh) box.lam).hi)) :
          Interval precision).squareN 8).upperRat : ℚ) : ℝ))
    (hcompactNonneg : 0 ≤ ((compactNoiseUpper box
      (segment.start + index * segment.mesh)).upperRat : ℝ))
    (hinverse : 1 / Real.sqrt ((box.lam : ℝ) ^ 2 +
        (((segment.start + index * segment.mesh : ℚ) : ℝ)) ^ 2) ≤
      ((inverseSqrtAtLeft precision
        (segment.start + index * segment.mesh) box.lam).upperRat : ℝ)) :
    hybridCellRectangleValue box segment index ≤
      ((hybridCell box segment index).upperRat : ℝ) := by
  let left : ℚ := segment.start + index * segment.mesh
  let rowI : Interval precision := Interval.mk 0
    (min (realCapUpper precision box.profileLeft box.lam).hi
      (max
        (rowExpressionOnCell box.profileLeft left
          (left + segment.mesh) box.lam).hi
        (rowExpressionOnCell box.profileRight left
          (left + segment.mesh) box.lam).hi)) |>.squareN 8
  let compactI := compactNoiseUpper box left
  let gaussianI := Exp.negUpper precision
    (gaussianSigma ^ 2 * left ^ 2 / 2) 24
  let inverseI := inverseSqrtAtLeft precision left box.lam
  have hmeshI : (frac precision segment.mesh).Contains
      (segment.mesh : ℝ) := by
    simpa [frac] using Interval.contains_ofRat precision segment.mesh
  have hrowUpper' : hybridCellRowUpperValue box segment index ^ rows ≤
      (rowI.upperRat : ℝ) := by
    simpa only [rowI] using hrowUpper
  have hgaussian : Real.exp (-((gaussianSigma : ℝ) ^ 2 / 2) *
      (left : ℝ) ^ 2) ≤ (gaussianI.upperRat : ℝ) := by
    have h := Exp.negUpper_contains (p := precision) (k := 24)
      (x := gaussianSigma ^ 2 * left ^ 2 / 2) (by positivity)
    have h' := upper_le_upperRat_of_contains h
    convert h' using 1 <;>
      (try dsimp only [gaussianI]) <;> (try push_cast) <;> (try ring)
  have hinverse' : 1 / Real.sqrt ((box.lam : ℝ) ^ 2 + (left : ℝ) ^ 2) ≤
      (inverseI.upperRat : ℝ) := by
    simpa only [left, inverseI] using hinverse
  have hmeshUpper : (segment.mesh : ℝ) ≤
      ((frac precision segment.mesh).upperRat : ℝ) :=
    upper_le_upperRat_of_contains hmeshI
  have hgaussianNonneg : 0 ≤ Real.exp
      (-((gaussianSigma : ℝ) ^ 2 / 2) * (left : ℝ) ^ 2) := by positivity
  have hgaussianUpperNonneg : 0 ≤ (gaussianI.upperRat : ℝ) :=
    hgaussianNonneg.trans hgaussian
  have hinverseNonneg : 0 ≤
      1 / Real.sqrt ((box.lam : ℝ) ^ 2 + (left : ℝ) ^ 2) := by positivity
  have hinverseUpperNonneg : 0 ≤ (inverseI.upperRat : ℝ) :=
    hinverseNonneg.trans hinverse'
  have hliteral : hybridCellRectangleValue box segment index ≤
      ((frac precision segment.mesh).upperRat : ℝ) *
      (rowI.upperRat : ℝ) * (compactI.upperRat : ℝ) *
      (gaussianI.upperRat : ℝ) * (inverseI.upperRat : ℝ) := by
    unfold hybridCellRectangleValue
    dsimp only [left]
    have hfirst := mul_le_mul hmeshUpper hrowUpper' hrowValueNonneg
      (hmeshNonneg.trans hmeshUpper)
    have hsecond := mul_le_mul hfirst le_rfl hcompactNonneg
      (mul_nonneg (hmeshNonneg.trans hmeshUpper)
        (hrowValueNonneg.trans hrowUpper'))
    have hthird := mul_le_mul hsecond hgaussian hgaussianNonneg
      (mul_nonneg (mul_nonneg (hmeshNonneg.trans hmeshUpper)
        (hrowValueNonneg.trans hrowUpper')) hcompactNonneg)
    exact mul_le_mul hthird hinverse' hinverseNonneg
      (mul_nonneg (mul_nonneg
        (mul_nonneg (hmeshNonneg.trans hmeshUpper)
          (hrowValueNonneg.trans hrowUpper')) hcompactNonneg)
        hgaussianUpperNonneg)
  have h01 := Interval.upperRat_mul_upperRat_le
    (frac precision segment.mesh) rowI
  have h02 := Interval.upperRat_mul_upperRat_le
    (frac precision segment.mesh * rowI) compactI
  have h03 := Interval.upperRat_mul_upperRat_le
    (frac precision segment.mesh * rowI * compactI) gaussianI
  have h04 := Interval.upperRat_mul_upperRat_le
    (frac precision segment.mesh * rowI * compactI * gaussianI) inverseI
  apply hliteral.trans
  calc
    _ ≤ (((frac precision segment.mesh * rowI).upperRat : ℝ) *
        (compactI.upperRat : ℝ)) * (gaussianI.upperRat : ℝ) *
        (inverseI.upperRat : ℝ) := by
      have h01c := mul_le_mul_of_nonneg_right h01 hcompactNonneg
      have h01g := mul_le_mul_of_nonneg_right h01c hgaussianUpperNonneg
      have h01i := mul_le_mul_of_nonneg_right h01g hinverseUpperNonneg
      simpa only [mul_assoc] using h01i
    _ ≤ (((frac precision segment.mesh * rowI * compactI).upperRat : ℝ) *
        (gaussianI.upperRat : ℝ)) * (inverseI.upperRat : ℝ) := by
      have h02g := mul_le_mul_of_nonneg_right h02 hgaussianUpperNonneg
      have h02i := mul_le_mul_of_nonneg_right h02g hinverseUpperNonneg
      simpa only [mul_assoc] using h02i
    _ ≤ ((frac precision segment.mesh * rowI * compactI * gaussianI).upperRat : ℝ) *
        (inverseI.upperRat : ℝ) := by
      exact mul_le_mul_of_nonneg_right h03 hinverseUpperNonneg
    _ ≤ ((frac precision segment.mesh * rowI * compactI * gaussianI *
        inverseI).upperRat : ℝ) := h04
    _ = ((hybridCell box segment index).upperRat : ℝ) := by
      rfl

end SparseUpperHybrid
end CertifiedJL
