/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Lower.BalancedTernary.WrappedFourier
import CertifiedJL.Statements.Shared.Input

/-! # Retained wrapped-profile interfaces

These bounds stop before centered or affine transport. They can therefore
be shared by both lower-tail families without losing the shift-uniform
Fourier comparison. The support is chosen from the input before the row.
-/

namespace CertifiedJL

/-- A near-dominant input admits a retained wrapped row bound at modulus
margin three. The interface is valid at the closed `49/50` endpoint; the
assembly's preceding weak singleton test assigns that endpoint to the
singleton branch. Its strict lower cutoff assigns `3/4` to diffuse. -/
def SparseThresholdNearWrappedRowBound : Prop :=
  ∀ (q d : ℕ) (w : Fin d → ℤ) (b : ℕ),
    Odd q → 0 < b → InputThresholdAtMostNorm b w → 3 * b ≤ q →
    (∀ i, 50 * (w i).natAbs ≤ 49 * b) →
    (∃ i, 3 * b < 4 * (w i).natAbs) →
    ∃ support : Finset (Fin d),
      ∫ row, wrappedGaussianKernel q ((23 / 10 : ℝ) / (b : ℝ) ^ 2)
          (∑ i, row i * (if i ∈ support then w i else 0))
          ∂(sparseRademacherRow d).toMeasure ≤ 681 / 1250

/-- A diffuse input admits a retained wrapped row bound at modulus margin three. -/
def SparseThresholdDiffuseWrappedRowBoundAt (t K : ℝ) : Prop :=
  ∀ (q d : ℕ) (w : Fin d → ℤ) (b : ℕ),
    Odd q → 0 < b → InputThresholdAtMostNorm b w → 3 * b ≤ q →
    (∀ i, 4 * (w i).natAbs ≤ 3 * b) →
    ∃ support : Finset (Fin d),
      ∫ row, wrappedGaussianKernel q (t / (b : ℝ) ^ 2)
          (∑ i, row i * (if i ∈ support then w i else 0))
          ∂(sparseRademacherRow d).toMeasure ≤ K

end CertifiedJL
