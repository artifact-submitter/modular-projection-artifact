/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Transcendental.Cosh
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.Soundness
import CertifiedJL.Analysis.Fourier.CenteredUniformSmoothing
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Polynomial-tail soundness for the centered-hybrid certificate

This file proves the analytic estimate represented by
`SparseUpperHybrid.tail`.  Beyond the finite cutoff, each centered-uniform
Laplace factor contributes one inverse power of frequency.  The remaining
shifted-Gaussian denominator contributes one further inverse power, whose
integral is elementary.
-/

open MeasureTheory

namespace CertifiedJL
namespace SparseUpperHybrid

open UpperContourKernel

private theorem upper_le_upperRat_of_contains
    {p : ℕ} {I : Interval p} {x : ℝ} (hI : I.Contains x) :
    x ≤ (I.upperRat : ℝ) := by
  simpa only [Interval.upperRat, Dyadic.cast_toRat] using hI.2

/-- On the positive frequency half-line, one centered-uniform transform is
bounded by `cosh (h * lambda) / (h * frequency)`. -/
theorem norm_centeredUniformLaplace_le_cosh_div
    {h lambda frequency : ℝ} (hh : 0 < h) (hlambda : 0 < lambda)
    (hfrequency : 0 < frequency) :
    ‖centeredUniformLaplace h lambda frequency‖ ≤
      Real.cosh (h * lambda) / (h * frequency) := by
  have hargument : 0 ≤ h * lambda := (mul_pos hh hlambda).le
  have hsinSq : Real.sin (h * frequency) ^ 2 ≤ 1 :=
    Real.sin_sq_le_one _
  have hcoshSq : Real.sinh (h * lambda) ^ 2 + 1 =
      Real.cosh (h * lambda) ^ 2 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq (h * lambda)]
  have hdenom : 0 < h ^ 2 * (lambda ^ 2 + frequency ^ 2) := by positivity
  have hfrequencyDenom : 0 < h * frequency := mul_pos hh hfrequency
  have hsq :
      ‖centeredUniformLaplace h lambda frequency‖ ^ 2 ≤
        (Real.cosh (h * lambda) / (h * frequency)) ^ 2 := by
    rw [norm_centeredUniformLaplace_sq]
    apply (div_le_iff₀ hdenom).2
    have hcoshNonneg : 0 ≤ Real.cosh (h * lambda) := (Real.cosh_pos _).le
    have hrightNonneg :
        0 ≤ (Real.cosh (h * lambda) / (h * frequency)) ^ 2 := sq_nonneg _
    calc
      Real.sinh (h * lambda) ^ 2 + Real.sin (h * frequency) ^ 2 ≤
          Real.cosh (h * lambda) ^ 2 := by nlinarith
      _ ≤ (Real.cosh (h * lambda) / (h * frequency)) ^ 2 *
          (h ^ 2 * (lambda ^ 2 + frequency ^ 2)) := by
        rw [div_pow]
        field_simp [hh.ne', hfrequency.ne']
        nlinarith [sq_nonneg lambda, sq_nonneg frequency,
          sq_nonneg (Real.cosh (h * lambda))]
  have hrightNonneg :
      0 ≤ Real.cosh (h * lambda) / (h * frequency) := by positivity
  nlinarith [norm_nonneg (centeredUniformLaplace h lambda frequency)]

/-- The positive-frequency compact-noise tail integrand, with the row factor
already replaced by a constant cap. -/
noncomputable def compactTailIntegrand
    (h lambda : ℝ) (uniformCount : ℕ) (rowCap : ℝ)
    (frequency : ℝ) : ℝ :=
  rowCap ^ rows *
    ‖centeredUniformLaplace h lambda frequency‖ ^ uniformCount *
      (1 / Real.sqrt (lambda ^ 2 + frequency ^ 2))

/-- Pointwise inverse-power envelope for the compact tail. -/
theorem compactTailIntegrand_le_inversePower
    {h lambda rowCap frequency : ℝ} {uniformCount : ℕ}
    (hh : 0 < h) (hlambda : 0 < lambda) (hrowCap : 0 ≤ rowCap)
    (hfrequency : 0 < frequency) :
    compactTailIntegrand h lambda uniformCount rowCap frequency ≤
      rowCap ^ rows * (Real.cosh (h * lambda) / h) ^ uniformCount /
        frequency ^ (uniformCount + 1) := by
  have hnoise := norm_centeredUniformLaplace_le_cosh_div
    hh hlambda hfrequency
  have hnoisePow := pow_le_pow_left₀
    (norm_nonneg (centeredUniformLaplace h lambda frequency))
    hnoise uniformCount
  have hsqrt : frequency ≤ Real.sqrt (lambda ^ 2 + frequency ^ 2) :=
    (Real.le_sqrt hfrequency.le (by positivity)).2 (by nlinarith [sq_nonneg lambda])
  have hinverse := one_div_le_one_div_of_le hfrequency hsqrt
  unfold compactTailIntegrand
  have hcapPow : 0 ≤ rowCap ^ rows := pow_nonneg hrowCap rows
  have hleftProduct :
      rowCap ^ rows *
          ‖centeredUniformLaplace h lambda frequency‖ ^ uniformCount ≤
        rowCap ^ rows *
          (Real.cosh (h * lambda) / (h * frequency)) ^ uniformCount :=
    mul_le_mul_of_nonneg_left hnoisePow hcapPow
  have hinverseNonneg :
      0 ≤ 1 / Real.sqrt (lambda ^ 2 + frequency ^ 2) := by
    exact one_div_nonneg.mpr (Real.sqrt_nonneg _)
  have hrightProductNonneg :
      0 ≤ rowCap ^ rows *
          (Real.cosh (h * lambda) / (h * frequency)) ^ uniformCount := by
    exact mul_nonneg hcapPow (pow_nonneg (by positivity) uniformCount)
  calc
    rowCap ^ rows *
          ‖centeredUniformLaplace h lambda frequency‖ ^ uniformCount *
          (1 / Real.sqrt (lambda ^ 2 + frequency ^ 2)) ≤
        rowCap ^ rows *
          (Real.cosh (h * lambda) / (h * frequency)) ^ uniformCount *
          (1 / frequency) := by
        exact mul_le_mul hleftProduct hinverse hinverseNonneg hrightProductNonneg
    _ = rowCap ^ rows * (Real.cosh (h * lambda) / h) ^ uniformCount /
          frequency ^ (uniformCount + 1) := by
      have hratio : Real.cosh (h * lambda) / (h * frequency) =
          (Real.cosh (h * lambda) / h) / frequency := by
        field_simp [hh.ne', hfrequency.ne']
      rw [hratio, div_pow, pow_succ]
      field_simp [hfrequency.ne']

/-- The compact inverse-power tail is integrable beyond every positive
cutoff. -/
theorem integrableOn_compactTailIntegrand
    {h lambda cutoff rowCap : ℝ} {uniformCount : ℕ}
    (hh : 0 < h) (hlambda : 0 < lambda) (hcutoff : 0 < cutoff)
    (hrowCap : 0 ≤ rowCap) (huniformCount : 0 < uniformCount) :
    IntegrableOn (compactTailIntegrand h lambda uniformCount rowCap)
      (Set.Ioi cutoff) := by
  let constant : ℝ :=
    rowCap ^ rows * (Real.cosh (h * lambda) / h) ^ uniformCount
  let upper : ℝ → ℝ := fun frequency =>
    constant * (1 / frequency ^ (uniformCount + 1))
  have hinverseIntegrable : IntegrableOn
      (fun frequency : ℝ => 1 / frequency ^ (uniformCount + 1))
      (Set.Ioi cutoff) := by
    have hexponent : -((uniformCount : ℝ) + 1) < -1 := by
      have hcountReal : (0 : ℝ) < uniformCount := by
        exact_mod_cast huniformCount
      linarith
    have hrpow := integrableOn_Ioi_rpow_of_lt hexponent hcutoff
    apply hrpow.congr_fun _ measurableSet_Ioi
    intro frequency hfrequency
    change frequency ^ (-((uniformCount : ℝ) + 1)) =
      1 / frequency ^ (uniformCount + 1)
    rw [Real.rpow_neg (le_of_lt (hcutoff.trans hfrequency))]
    rw [show (uniformCount : ℝ) + 1 =
      ((uniformCount + 1 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    simp only [one_div]
  have hupperIntegrable : IntegrableOn upper (Set.Ioi cutoff) :=
    hinverseIntegrable.const_mul constant
  have hactualMeasurable : AEStronglyMeasurable
      (compactTailIntegrand h lambda uniformCount rowCap) := by
    apply Measurable.aestronglyMeasurable
    unfold compactTailIntegrand centeredUniformLaplace
    fun_prop
  apply hupperIntegrable.mono' hactualMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with frequency hfrequency
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · simpa only [upper, constant, one_div, div_eq_mul_inv, one_mul] using
      (compactTailIntegrand_le_inversePower
        (uniformCount := uniformCount) hh hlambda hrowCap
        (hcutoff.trans hfrequency))
  · unfold compactTailIntegrand
    exact mul_nonneg
      (mul_nonneg (pow_nonneg hrowCap rows)
        (pow_nonneg (norm_nonneg _) uniformCount))
      (one_div_nonneg.mpr (Real.sqrt_nonneg _))

/-- Exact integral of the natural inverse power used by the tail checker. -/
theorem integral_Ioi_inversePower_nat
    {cutoff : ℝ} (hcutoff : 0 < cutoff) {k : ℕ} (hk : 0 < k) :
    (∫ frequency : ℝ in Set.Ioi cutoff,
        1 / frequency ^ (k + 1)) =
      1 / ((k : ℝ) * cutoff ^ k) := by
  have hexponent : -((k : ℝ) + 1) < -1 := by
    have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
    linarith
  have hbase := integral_Ioi_rpow_of_lt hexponent hcutoff
  calc
    (∫ frequency : ℝ in Set.Ioi cutoff,
        1 / frequency ^ (k + 1)) =
        ∫ frequency : ℝ in Set.Ioi cutoff,
          frequency ^ (-((k : ℝ) + 1)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro frequency hfrequency
      change 1 / frequency ^ (k + 1) =
        frequency ^ (-((k : ℝ) + 1))
      rw [Real.rpow_neg (le_of_lt (hcutoff.trans hfrequency))]
      rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      simp only [one_div]
    _ = -cutoff ^ (-((k : ℝ) + 1) + 1) /
          (-((k : ℝ) + 1) + 1) := hbase
    _ = 1 / ((k : ℝ) * cutoff ^ k) := by
      have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
      rw [show -((k : ℝ) + 1) + 1 = -(k : ℝ) by ring]
      rw [Real.rpow_neg hcutoff.le, Real.rpow_natCast]
      field_simp

/-- The complete positive-frequency tail integral is bounded by the scalar
encoded in `tail`, before outward rounding. -/
theorem integral_Ioi_compactTailIntegrand_le
    {h lambda cutoff rowCap : ℝ} {uniformCount : ℕ}
    (hh : 0 < h) (hlambda : 0 < lambda) (hcutoff : 0 < cutoff)
    (hrowCap : 0 ≤ rowCap) (huniformCount : 0 < uniformCount) :
    (∫ frequency : ℝ in Set.Ioi cutoff,
      compactTailIntegrand h lambda uniformCount rowCap frequency) ≤
      rowCap ^ rows * (Real.cosh (h * lambda) / h) ^ uniformCount /
        ((uniformCount : ℝ) * cutoff ^ uniformCount) := by
  let constant : ℝ :=
    rowCap ^ rows * (Real.cosh (h * lambda) / h) ^ uniformCount
  let upper : ℝ → ℝ := fun frequency =>
    constant * (1 / frequency ^ (uniformCount + 1))
  have hconstant : 0 ≤ constant := by
    dsimp only [constant]
    positivity
  have hinverseIntegrable : IntegrableOn
      (fun frequency : ℝ => 1 / frequency ^ (uniformCount + 1))
      (Set.Ioi cutoff) := by
    have hexponent : -((uniformCount : ℝ) + 1) < -1 := by
      have hcountReal : (0 : ℝ) < uniformCount := by
        exact_mod_cast huniformCount
      linarith
    have hrpow := integrableOn_Ioi_rpow_of_lt hexponent hcutoff
    apply hrpow.congr_fun _ measurableSet_Ioi
    intro frequency hfrequency
    change frequency ^ (-((uniformCount : ℝ) + 1)) =
      1 / frequency ^ (uniformCount + 1)
    rw [Real.rpow_neg (le_of_lt (hcutoff.trans hfrequency))]
    rw [show (uniformCount : ℝ) + 1 =
      ((uniformCount + 1 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    simp only [one_div]
  have hupperIntegrable : IntegrableOn upper (Set.Ioi cutoff) :=
    hinverseIntegrable.const_mul constant
  have hactualIntegrable : IntegrableOn
      (compactTailIntegrand h lambda uniformCount rowCap) (Set.Ioi cutoff) := by
    exact integrableOn_compactTailIntegrand hh hlambda hcutoff hrowCap
      huniformCount
  calc
    _ ≤ ∫ frequency : ℝ in Set.Ioi cutoff, upper frequency := by
      apply setIntegral_mono_on hactualIntegrable hupperIntegrable measurableSet_Ioi
      intro frequency hfrequency
      simpa only [upper, constant, one_div, div_eq_mul_inv, one_mul] using
        (compactTailIntegrand_le_inversePower
          (uniformCount := uniformCount) hh hlambda hrowCap
          (hcutoff.trans hfrequency))
    _ = constant * (1 / ((uniformCount : ℝ) * cutoff ^ uniformCount)) := by
      rw [MeasureTheory.integral_const_mul,
        integral_Ioi_inversePower_nat hcutoff huniformCount]
    _ = _ := by
      dsimp only [constant]
      ring

/-- The exact real scalar whose outward-rounded version is stored by
`SparseUpperHybrid.tail`. -/
noncomputable def analyticTailValue (box : ProfileBox) (rowCap : ℝ) : ℝ :=
  rowCap ^ rows *
    (Real.cosh ((box.uniformHalfWidth * box.lam : ℚ) : ℝ) /
      (box.uniformHalfWidth : ℝ)) ^ box.uniformCount /
    ((box.uniformCount : ℝ) * (cutoff : ℝ) ^ box.uniformCount)

/-- A checked exponential enclosure validates the rational `coshUpper`
constant used once per profile box by the polynomial tail evaluator. -/
theorem cosh_le_coshUpper_of_check
    (box : ProfileBox)
    (hargument : 0 ≤ box.uniformHalfWidth * box.lam)
    (hargumentUpper : box.uniformHalfWidth * box.lam < (2 ^ 30 : ℕ))
    (hbase : 0 < (Interval.ofRat precision
      (1 - box.uniformHalfWidth * box.lam / (2 ^ 30 : ℕ))).lo)
    (hcheck : (Cosh.upper precision
      (box.uniformHalfWidth * box.lam) 30).upperRat ≤
        coshUpper (box.uniformHalfWidth * box.lam)) :
    Real.cosh ((box.uniformHalfWidth * box.lam : ℚ) : ℝ) ≤
      (coshUpper (box.uniformHalfWidth * box.lam) : ℝ) := by
  have henclosure := Cosh.upper_contains
    (p := precision) (k := 30) hargument hargumentUpper hbase
  calc
    Real.cosh ((box.uniformHalfWidth * box.lam : ℚ) : ℝ) ≤
        ((Cosh.upper precision
          (box.uniformHalfWidth * box.lam) 30).upperRat : ℝ) :=
      upper_le_upperRat_of_contains henclosure
    _ ≤ (coshUpper (box.uniformHalfWidth * box.lam) : ℝ) := by
      exact_mod_cast hcheck

/-- The executable tail's upper endpoint bounds the exact analytic tail
scalar.  This is one-sided because `coshUpper` itself is an upper surrogate,
not the center of an interval containing the exact value. -/
theorem analyticTailValue_le_tail_upperRat
    (box : ProfileBox) (rowCap : ℝ)
    (hh : 0 < (box.uniformHalfWidth : ℝ))
    (hcount : 0 < box.uniformCount) (hrowCap : 0 ≤ rowCap)
    (hcap : (realCapUpper precision
      box.profileLeft box.lam).Contains rowCap)
    (hcosh : Real.cosh
      ((box.uniformHalfWidth * box.lam : ℚ) : ℝ) ≤
        (coshUpper (box.uniformHalfWidth * box.lam) : ℝ)) :
    analyticTailValue box rowCap ≤ ((tail box).upperRat : ℝ) := by
  let exactCosh : ℝ :=
    Real.cosh ((box.uniformHalfWidth * box.lam : ℚ) : ℝ)
  let rationalCosh : ℝ :=
    (coshUpper (box.uniformHalfWidth * box.lam) : ℝ)
  let rationalFactor : ℚ :=
    (coshUpper (box.uniformHalfWidth * box.lam) /
      box.uniformHalfWidth) ^ box.uniformCount /
      (box.uniformCount * cutoff ^ box.uniformCount)
  have hratio :
      exactCosh / (box.uniformHalfWidth : ℝ) ≤
        rationalCosh / (box.uniformHalfWidth : ℝ) := by
    exact div_le_div_of_nonneg_right (by simpa [exactCosh, rationalCosh] using hcosh)
      hh.le
  have hratioNonneg :
      0 ≤ exactCosh / (box.uniformHalfWidth : ℝ) := by
    dsimp only [exactCosh]
    positivity
  have hpower := pow_le_pow_left₀ hratioNonneg hratio box.uniformCount
  have hdenominator :
      0 < (box.uniformCount : ℝ) * (cutoff : ℝ) ^ box.uniformCount := by
    have hcountReal : (0 : ℝ) < box.uniformCount := by exact_mod_cast hcount
    have hcutoff : (0 : ℝ) < (cutoff : ℝ) := by
      norm_num [cutoff]
    positivity
  have hfactor :
      (exactCosh / (box.uniformHalfWidth : ℝ)) ^ box.uniformCount /
          ((box.uniformCount : ℝ) * (cutoff : ℝ) ^ box.uniformCount) ≤
        (rationalFactor : ℝ) := by
    have hdiv := div_le_div_of_nonneg_right hpower hdenominator.le
    simpa [rationalFactor, rationalCosh, Rat.cast_div, Rat.cast_pow,
      Rat.cast_natCast] using hdiv
  have hcapPower := Interval.contains_squareN hcap 8
  have hfactorContains :
      (frac precision rationalFactor).Contains (rationalFactor : ℝ) := by
    simpa [frac] using Interval.contains_ofRat precision rationalFactor
  have hproduct := Interval.contains_mul hcapPower hfactorContains
  have hproduct' : (tail box).Contains
      (rowCap ^ rows * (rationalFactor : ℝ)) := by
    simpa [tail, rationalFactor, frac, rows,
      Interval.iterSquare_eq_pow_two_pow] using hproduct
  have hvalueLe : analyticTailValue box rowCap ≤
      rowCap ^ rows * (rationalFactor : ℝ) := by
    unfold analyticTailValue
    calc
      rowCap ^ rows *
            (Real.cosh ((box.uniformHalfWidth * box.lam : ℚ) : ℝ) /
              (box.uniformHalfWidth : ℝ)) ^ box.uniformCount /
            ((box.uniformCount : ℝ) * (cutoff : ℝ) ^ box.uniformCount) =
          rowCap ^ rows *
            ((exactCosh / (box.uniformHalfWidth : ℝ)) ^ box.uniformCount /
              ((box.uniformCount : ℝ) * (cutoff : ℝ) ^ box.uniformCount)) := by
        simp only [exactCosh]
        ring
      _ ≤ rowCap ^ rows * (rationalFactor : ℝ) :=
        mul_le_mul_of_nonneg_left hfactor (pow_nonneg hrowCap rows)
  exact hvalueLe.trans (upper_le_upperRat_of_contains hproduct')

/-- End-to-end analytic connection: the true positive-frequency compact tail
integral lies below the executable endpoint in `SparseUpperHybrid.tail`. -/
theorem integral_Ioi_compactTailIntegrand_le_tail_upperRat
    (box : ProfileBox) (rowCap : ℝ)
    (hh : 0 < (box.uniformHalfWidth : ℝ))
    (hlambda : 0 < (box.lam : ℝ))
    (hcount : 0 < box.uniformCount) (hrowCap : 0 ≤ rowCap)
    (hcap : (realCapUpper precision
      box.profileLeft box.lam).Contains rowCap)
    (hcosh : Real.cosh
      ((box.uniformHalfWidth * box.lam : ℚ) : ℝ) ≤
        (coshUpper (box.uniformHalfWidth * box.lam) : ℝ)) :
    (∫ frequency : ℝ in Set.Ioi (cutoff : ℝ),
      compactTailIntegrand (box.uniformHalfWidth : ℝ) (box.lam : ℝ)
        box.uniformCount rowCap frequency) ≤
      ((tail box).upperRat : ℝ) := by
  calc
    _ ≤ analyticTailValue box rowCap := by
      simpa [analyticTailValue, Rat.cast_mul] using
        (integral_Ioi_compactTailIntegrand_le
          (h := (box.uniformHalfWidth : ℝ)) (lambda := (box.lam : ℝ))
          (cutoff := (cutoff : ℝ)) (rowCap := rowCap)
          (uniformCount := box.uniformCount) hh hlambda
          (by norm_num [cutoff]) hrowCap hcount)
    _ ≤ ((tail box).upperRat : ℝ) :=
      analyticTailValue_le_tail_upperRat box rowCap hh hcount hrowCap hcap hcosh

/-- After replacing the sparse row majorant by a fixed nonnegative cap, the
actual Gaussian-damped hybrid integrand is bounded by the compact tail
integrand.  The Gaussian factor is simply discarded using `exp (-x) ≤ 1`. -/
theorem actualHybridIntegrand_le_compactTailIntegrand
    (box : ProfileBox) (profile rowCap frequency : ℝ)
    (hprofile : 0 ≤ profile) (hlambda : 0 < (box.lam : ℝ))
    (hlambdaOne : (box.lam : ℝ) < 1)
    (hrow : sparseUpperContourRowMajorant
      profile (box.lam : ℝ) frequency ≤ rowCap) :
    actualHybridIntegrand box profile frequency ≤
      compactTailIntegrand (box.uniformHalfWidth : ℝ) (box.lam : ℝ)
        box.uniformCount rowCap frequency := by
  have hrowNonneg : 0 ≤ sparseUpperContourRowMajorant
      profile (box.lam : ℝ) frequency :=
    sparseUpperContourRowMajorant_nonneg
      hprofile hlambda.le hlambdaOne
  have hrowPower := pow_le_pow_left₀ hrowNonneg hrow rows
  have hgaussian :
      Real.exp (-((gaussianSigma : ℝ) ^ 2 / 2) * frequency ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (by positivity)) (sq_nonneg frequency)
  have hrowPowerNonneg : 0 ≤
      sparseUpperContourRowMajorant profile (box.lam : ℝ) frequency ^ rows :=
    pow_nonneg hrowNonneg rows
  have hfront :
      Real.exp (-((gaussianSigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
          sparseUpperContourRowMajorant
            profile (box.lam : ℝ) frequency ^ rows ≤
        rowCap ^ rows := by
    calc
      _ ≤ 1 * rowCap ^ rows :=
        mul_le_mul hgaussian hrowPower hrowPowerNonneg zero_le_one
      _ = _ := one_mul _
  have hrest : 0 ≤
      ‖centeredUniformLaplace (box.uniformHalfWidth : ℝ)
          (box.lam : ℝ) frequency‖ ^ box.uniformCount *
        (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2)) := by
    positivity
  unfold actualHybridIntegrand compactTailIntegrand
  calc
    _ = (Real.exp (-((gaussianSigma : ℝ) ^ 2 / 2) * frequency ^ 2) *
          sparseUpperContourRowMajorant
            profile (box.lam : ℝ) frequency ^ rows) *
        (‖centeredUniformLaplace (box.uniformHalfWidth : ℝ)
            (box.lam : ℝ) frequency‖ ^ box.uniformCount *
          (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2))) := by ring
    _ ≤ rowCap ^ rows *
        (‖centeredUniformLaplace (box.uniformHalfWidth : ℝ)
            (box.lam : ℝ) frequency‖ ^ box.uniformCount *
          (1 / Real.sqrt ((box.lam : ℝ) ^ 2 + frequency ^ 2))) :=
      mul_le_mul_of_nonneg_right hfront hrest
    _ = _ := by ring

/-- Set-integral form of the semantic tail bridge. -/
theorem integral_Ioi_actualHybridIntegrand_le_compactTailIntegrand
    (box : ProfileBox) (profile rowCap : ℝ)
    (hprofile : 0 ≤ profile) (hh : 0 < (box.uniformHalfWidth : ℝ))
    (hlambda : 0 < (box.lam : ℝ)) (hlambdaOne : (box.lam : ℝ) < 1)
    (hcount : 0 < box.uniformCount) (hrowCap : 0 ≤ rowCap)
    (hrow : ∀ frequency : ℝ, (cutoff : ℝ) < frequency →
      sparseUpperContourRowMajorant
        profile (box.lam : ℝ) frequency ≤ rowCap) :
    (∫ frequency : ℝ in Set.Ioi (cutoff : ℝ),
        actualHybridIntegrand box profile frequency) ≤
      ∫ frequency : ℝ in Set.Ioi (cutoff : ℝ),
        compactTailIntegrand (box.uniformHalfWidth : ℝ) (box.lam : ℝ)
          box.uniformCount rowCap frequency := by
  have hactualIntegrable : IntegrableOn
      (actualHybridIntegrand box profile) (Set.Ioi (cutoff : ℝ)) :=
    (integrable_actualHybridIntegrand box profile hprofile hh hlambda hlambdaOne).integrableOn
  have hcompactIntegrable : IntegrableOn
      (compactTailIntegrand (box.uniformHalfWidth : ℝ) (box.lam : ℝ)
        box.uniformCount rowCap) (Set.Ioi (cutoff : ℝ)) :=
    integrableOn_compactTailIntegrand hh hlambda (by norm_num [cutoff])
      hrowCap hcount
  exact setIntegral_mono_on hactualIntegrable hcompactIntegrable measurableSet_Ioi
    (fun frequency hfrequency =>
      actualHybridIntegrand_le_compactTailIntegrand box profile rowCap frequency
        hprofile hlambda hlambdaOne (hrow frequency hfrequency))

/-- Full semantic tail closure with the canonical U8 row cap.  The actual
hybrid tail integral is bounded directly by the executable endpoint in
`SparseUpperHybrid.tail`. -/
theorem integral_Ioi_actualHybridIntegrand_le_tail_upperRat
    (box : ProfileBox) (profile : ℝ)
    (hprofile : 0 ≤ profile) (hh : 0 < (box.uniformHalfWidth : ℝ))
    (hlambda : 0 < (box.lam : ℝ)) (hlambdaOne : (box.lam : ℝ) < 1)
    (hcount : 0 < box.uniformCount)
    (hcap : (realCapUpper precision
      box.profileLeft box.lam).Contains
        (realRowDeficitCap
          (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ)))))
    (hcosh : Real.cosh
      ((box.uniformHalfWidth * box.lam : ℚ) : ℝ) ≤
        (coshUpper (box.uniformHalfWidth * box.lam) : ℝ)) :
    (∫ frequency : ℝ in Set.Ioi (cutoff : ℝ),
      actualHybridIntegrand box profile frequency) ≤
        ((tail box).upperRat : ℝ) := by
  let rowCap : ℝ := realRowDeficitCap
    (Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ)))
  have hrowCap : 0 ≤ rowCap := by
    dsimp only [rowCap]
    unfold realRowDeficitCap
    have hv : 0 ≤
        Real.sqrt profile * (box.lam : ℝ) / (1 - (box.lam : ℝ)) := by
      positivity
    positivity
  have hrow : ∀ frequency : ℝ, (cutoff : ℝ) < frequency →
      sparseUpperContourRowMajorant
        profile (box.lam : ℝ) frequency ≤ rowCap := by
    intro frequency _
    unfold sparseUpperContourRowMajorant
    exact min_le_right _ _
  calc
    _ ≤ ∫ frequency : ℝ in Set.Ioi (cutoff : ℝ),
        compactTailIntegrand (box.uniformHalfWidth : ℝ) (box.lam : ℝ)
          box.uniformCount rowCap frequency :=
      integral_Ioi_actualHybridIntegrand_le_compactTailIntegrand
        box profile rowCap hprofile hh hlambda hlambdaOne hcount hrowCap hrow
    _ ≤ ((tail box).upperRat : ℝ) :=
      integral_Ioi_compactTailIntegrand_le_tail_upperRat
        box rowCap hh hlambda hcount hrowCap (by simpa [rowCap] using hcap) hcosh

end SparseUpperHybrid
end CertifiedJL
