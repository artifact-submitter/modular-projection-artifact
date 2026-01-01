/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author

The inverse-transform bridge is adapted from
`MathExtras/NumberTheory/Analysis/VaalerTheorem6JFT.lean` in
`gersh/ternary-goldbach-lean`, commit
`89416190c037331d7ebc04cd62ddb974cfb4dfcf` (Apache-2.0),
copyright (c) 2026 Gershon Bialer.
-/

import CertifiedJL.Analysis.Fourier.Beurling.JHatContinuity
import Mathlib.Analysis.Fourier.Inversion

/-!
# The spatial Vaaler kernel as an inverse Fourier transform

This file packages the continuous compactly supported multiplier
`beurlingJHat` as a complex function and defines its inverse Fourier
transform `beurlingJ`.  The remaining analytic input for the unconditional
transform identity is exactly `Integrable beurlingJ`; the next file proves
that fact by two integrations by parts on `[-1,0]` and `[0,1]`.
-/

open MeasureTheory Set Real
open FourierTransform
open scoped RealInnerProductSpace

namespace CertifiedJL
namespace Probability

/-- Complexification of the continuous compactly supported Vaaler multiplier. -/
noncomputable def beurlingJHatC (t : ℝ) : ℂ :=
  (beurlingJHat t : ℂ)

@[simp]
theorem beurlingJHatC_apply (t : ℝ) :
    beurlingJHatC t = (beurlingJHat t : ℂ) := rfl

theorem continuous_beurlingJHatC :
    Continuous beurlingJHatC :=
  Complex.continuous_ofReal.comp continuous_beurlingJHat

theorem beurlingJHatC_eq_zero_of_one_le_abs
    {t : ℝ} (ht : 1 ≤ |t|) :
    beurlingJHatC t = 0 := by
  simp [beurlingJHatC, beurlingJHat_eq_zero_of_one_le_abs ht]

theorem support_beurlingJHatC_subset :
    Function.support beurlingJHatC ⊆ Icc (-1 : ℝ) 1 := by
  intro t ht
  by_contra hmem
  rw [mem_Icc, not_and_or] at hmem
  apply ht
  apply beurlingJHatC_eq_zero_of_one_le_abs
  rcases hmem with hleft | hright
  · rw [le_abs]
    exact Or.inr (by linarith)
  · rw [le_abs]
    exact Or.inl (by linarith)

theorem hasCompactSupport_beurlingJHatC :
    HasCompactSupport beurlingJHatC :=
  HasCompactSupport.of_support_subset_isCompact
    isCompact_Icc support_beurlingJHatC_subset

theorem integrable_beurlingJHatC :
    Integrable beurlingJHatC :=
  continuous_beurlingJHatC.integrable_of_hasCompactSupport
    hasCompactSupport_beurlingJHatC

/--
The spatial Vaaler kernel.  This definition makes the Fourier normalization
unambiguous: `J` is the inverse transform of the continuous multiplier
`Ĵ`.
-/
noncomputable def beurlingJ (x : ℝ) : ℂ :=
  𝓕⁻ beurlingJHatC x

theorem beurlingJ_eq_fourierInv :
    beurlingJ = 𝓕⁻ beurlingJHatC := rfl

theorem beurlingJHatC_neg (t : ℝ) :
    beurlingJHatC (-t) = beurlingJHatC t := by
  simp [beurlingJHatC, beurlingJHat_neg]

theorem beurlingJ_neg (x : ℝ) :
    beurlingJ (-x) = beurlingJ x := by
  rw [beurlingJ_eq_fourierInv, fourierInv_eq', fourierInv_eq']
  rw [← integral_neg_eq_self
    (fun t : ℝ =>
      Complex.exp ((↑(2 * Real.pi * ⟪t, x⟫) : ℂ) * Complex.I) •
        beurlingJHatC t) volume]
  refine integral_congr_ae ?_
  filter_upwards with t
  rw [beurlingJHatC_neg]
  have hleft : (⟪t, -x⟫ : ℝ) = -(t * x) := by simp; ring
  have hright : (⟪-t, x⟫ : ℝ) = -(t * x) := by simp; ring
  rw [hleft, hright]

theorem fourier_beurlingJHatC_eq_beurlingJ :
    𝓕 beurlingJHatC = beurlingJ := by
  funext x
  calc
    𝓕 beurlingJHatC x =
        𝓕⁻ beurlingJHatC (-x) :=
      by simpa using
        (fourierInv_eq_fourier_neg beurlingJHatC (-x)).symm
    _ = beurlingJ (-x) := rfl
    _ = beurlingJ x := beurlingJ_neg x

theorem continuous_beurlingJ :
    Continuous beurlingJ := by
  rw [← fourier_beurlingJHatC_eq_beurlingJ]
  exact VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂
    integrable_beurlingJHatC

/--
Fourier inversion for the Vaaler kernel, reduced to its only genuine decay
input.  `integrable_beurlingJ` is discharged unconditionally by the
piecewise-`C²` two-integration-by-parts argument.
-/
theorem fourier_beurlingJ_eq_beurlingJHatC_of_integrable
    (hJ : Integrable beurlingJ) (t : ℝ) :
    𝓕 beurlingJ t = beurlingJHatC t := by
  have hinv :
      𝓕 (𝓕⁻ beurlingJHatC) = beurlingJHatC :=
    continuous_beurlingJHatC.fourier_fourierInv_eq
      integrable_beurlingJHatC
      (by simpa [fourier_beurlingJHatC_eq_beurlingJ] using hJ)
  exact congrFun hinv t

end Probability
end CertifiedJL
