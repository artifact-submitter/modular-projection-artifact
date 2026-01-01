/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Distributions.Entry
import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpGaussianHalfIntegral
import CertifiedJL.Statements.L2.Upper.Rows256Bits128
import Mathlib.Tactic

/-!
# Sparse upper-tail row normalization

This module owns the sparse-row normalization used by the upper-tail
proof.  The probability statement and its constants remain imported from the
headline contract; this file adds the exact finite-law moments and the
profile notation consumed by the analytic row comparison.

The fourth-moment profile is `r = ∑ a_i^4`.  A sparse entry has variance
`1/2`, so a normalized row has Gaussian reference MGF
`M₀(s) = (1 - s)^(-1/2)` on the real domain `s < 1`.  The latter is recorded
as notation here; its analytic integral identity is proved by the later row
comparison slice.
-/

open scoped BigOperators

open MeasureTheory

namespace CertifiedJL

/-! ## Frozen U0 normalization -/

/-- The variance of one normalized sparse-ternary entry. -/
def sparseNormalizedVariance : ℚ := 1 / 2

/-- The fourth-moment profile of a real coefficient vector. -/
def sparseProfileFourthMoment {d : ℕ} (a : Fin d → ℝ) : ℝ :=
  ∑ i, (a i) ^ 4

/-- The real Gaussian reference row MGF used on the domain `s < 1`. -/
noncomputable def gaussianRealRowMGF (s : ℝ) : ℝ :=
  Real.rpow (1 - s) (-1 / 2 : ℝ)

/-! ## First exact U1 consumer: the upper normalization notation agrees with
    the shared exact sparse-entry law. -/

theorem sparseEntry_secondMoment_normalized :
    ∫ z, (z : ℝ) ^ 2 ∂sparseEntryPMF.toMeasure =
      (sparseNormalizedVariance : ℝ) := by
  simpa [sparseNormalizedVariance] using sparseEntry_secondMoment

/-- The real upper-row reference is the restriction of the exact complex
quadratic MGF of the centered variance-one-half Gaussian. -/
theorem integral_gaussianHalf_complexQuadraticExp_real
    {s : ℝ} (hs : s < 1) :
    (∫ x : ℝ, complexQuadraticExp (s : ℂ) x
        ∂(ProbabilityTheory.gaussianReal 0 (2 : NNReal)⁻¹)) =
      (gaussianRealRowMGF s : ℂ) := by
  rw [integral_gaussianHalf_complexQuadraticExp (by simpa using hs)]
  unfold gaussianRealRowMGF
  have hpow := Complex.ofReal_cpow (sub_nonneg.mpr hs.le) (-1 / 2 : ℝ)
  simpa using hpow.symm

end CertifiedJL
