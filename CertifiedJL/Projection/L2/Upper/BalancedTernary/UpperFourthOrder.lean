/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperNormalization
import CertifiedJL.Analysis.SmoothBounds.QuadraticExponential.QuadraticExpGaussianHalfIntegral

/-!
# Exact algebraic assembly of the fourth-order sparse-row bound

This module isolates the final substitution from the paper's hybrid estimate
to U4.  Its premise is deliberately the still-open hybrid estimate U7.  The
conclusion substitutes the exact Gaussian fourth derivative and the exact
duplicated fourth/sixth coefficient sums, so later work cannot silently alter
the constants `9216` or `5760`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CertifiedJL

/-- The paper's U7 hybrid estimate implies the literal U4 row comparison.

The complex number `M` is the actual sparse-row quadratic MGF.  This theorem
does not assume or manufacture U7; it discharges only the exact Gaussian and
coefficient algebra once that analytic premise is available. -/
theorem sparseUpper_fourthOrder_of_hybrid
    {d : ℕ} (a : Fin d → ℝ)
    (M : ℂ) {s : ℂ} (hs : s.re < 1)
    (hhybrid :
      ‖(1 - s) ^ (-1 / 2 : ℂ) - M -
          ((∑ p : Fin d × Fin 2,
              sparseUpperDuplicatedCoefficient a p ^ 4) / 12 : ℂ) *
            (∫ x : ℝ, iteratedDeriv 4 (complexQuadraticExp s) x
              ∂(gaussianReal 0 (2 : NNReal)⁻¹))‖ ≤
        (∑ p : Fin d × Fin 2,
            sparseUpperDuplicatedCoefficient a p ^ 4) ^ 2 / 144 *
              quadraticExpDerivativeMajorant 8 ‖s‖ s.re +
        11 * (∑ p : Fin d × Fin 2,
            sparseUpperDuplicatedCoefficient a p ^ 6) / 180 *
              quadraticExpDerivativeMajorant 6 ‖s‖ s.re) :
    ‖M - (1 - s) ^ (-1 / 2 : ℂ) +
        ((sparseProfileFourthMoment a / 8 : ℝ) : ℂ) * s ^ 2 *
          (1 - s) ^ (-5 / 2 : ℂ)‖ ≤
      sparseProfileFourthMoment a ^ 2 / 9216 *
          quadraticExpDerivativeMajorant 8 ‖s‖ s.re +
      11 * (sparseProfileFourthMoment a *
          Real.sqrt (sparseProfileFourthMoment a)) / 5760 *
            quadraticExpDerivativeMajorant 6 ‖s‖ s.re := by
  rw [sum_fourth_sparseUpperDuplicatedCoefficient,
    integral_gaussianHalf_iteratedDeriv_four_complexQuadraticExp hs] at hhybrid
  have hD6 : 0 ≤ quadraticExpDerivativeMajorant 6 ‖s‖ s.re :=
    quadraticExpDerivativeMajorant_nonneg (norm_nonneg _) hs
  have hsix := sum_sixth_sparseUpperDuplicatedCoefficient_le a
  have hcoeff :
      11 * (∑ p : Fin d × Fin 2,
          sparseUpperDuplicatedCoefficient a p ^ 6) / 180 ≤
        11 * (sparseProfileFourthMoment a *
            Real.sqrt (sparseProfileFourthMoment a)) / 5760 := by
    nlinarith [hsix]
  have hbound :
      sparseProfileFourthMoment a ^ 2 / 9216 *
            quadraticExpDerivativeMajorant 8 ‖s‖ s.re +
          11 * (∑ p : Fin d × Fin 2,
              sparseUpperDuplicatedCoefficient a p ^ 6) / 180 *
            quadraticExpDerivativeMajorant 6 ‖s‖ s.re ≤
        sparseProfileFourthMoment a ^ 2 / 9216 *
            quadraticExpDerivativeMajorant 8 ‖s‖ s.re +
          11 * (sparseProfileFourthMoment a *
              Real.sqrt (sparseProfileFourthMoment a)) / 5760 *
            quadraticExpDerivativeMajorant 6 ‖s‖ s.re := by
    exact add_le_add (le_refl _)
      (mul_le_mul_of_nonneg_right hcoeff hD6)
  have hnorm :
      ‖M - (1 - s) ^ (-1 / 2 : ℂ) +
          ((sparseProfileFourthMoment a / 8 : ℝ) : ℂ) * s ^ 2 *
            (1 - s) ^ (-5 / 2 : ℂ)‖ =
        ‖(1 - s) ^ (-1 / 2 : ℂ) - M -
          ((sparseProfileFourthMoment a / 8 : ℝ) : ℂ) / 12 *
            (12 * s ^ 2 * (1 - s) ^ (-5 / 2 : ℂ))‖ := by
    rw [← norm_neg]
    congr 1
    push_cast
    ring
  rw [hnorm]
  have hhybrid' :
      ‖(1 - s) ^ (-1 / 2 : ℂ) - M -
          ((sparseProfileFourthMoment a / 8 : ℝ) : ℂ) / 12 *
            (12 * s ^ 2 * (1 - s) ^ (-5 / 2 : ℂ))‖ ≤
        sparseProfileFourthMoment a ^ 2 / 9216 *
            quadraticExpDerivativeMajorant 8 ‖s‖ s.re +
          11 * (∑ p : Fin d × Fin 2,
              sparseUpperDuplicatedCoefficient a p ^ 6) / 180 *
            quadraticExpDerivativeMajorant 6 ‖s‖ s.re := by
    convert hhybrid using 1
    ring
  exact hhybrid'.trans hbound

end CertifiedJL
