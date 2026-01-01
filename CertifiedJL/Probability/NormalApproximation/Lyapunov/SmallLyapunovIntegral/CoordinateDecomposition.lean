/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.NormalApproximation.Lyapunov.SmallLyapunovIntegral.Core

/-!
# Coordinate decomposition of the small-Lyapunov finite-band integral

This file decomposes the sharp finite-band majorant into its coordinate
contributions while retaining all deleted-coordinate damping.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace CertifiedJL
namespace Probability

universe u_1

variable {ι : Type u_1} [Fintype ι]

theorem integrableOn_scaledPrawitzKernel_mul_tiltedCoordinateMajorant
    (b : ι → ℝ) (x : ℝ) (i : ι) {U₀ U : ℝ}
    (hU₀ : 0 ≤ U₀) (hband : U₀ < U) :
    IntegrableOn
      (fun t =>
        ‖scaledPrawitzKernel U t‖ *
          tiltedRademacherGaussianCFCoordinateMajorant b x i t)
      (Icc (-U₀) U₀) volume := by
  classical
  have hglobal :=
    integrableOn_scaledPrawitzKernel_mul_tiltedMajorant
      b x hU₀ hband
  apply Integrable.mono' hglobal
  · exact
      ((measurable_scaledPrawitzKernel U).norm.mul
        (measurable_tiltedRademacherGaussianCFCoordinateMajorant
          b x i)).aestronglyMeasurable.restrict
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (norm_nonneg _)
        (tiltedRademacherGaussianCFCoordinateMajorant_nonneg
          b x i t))]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [tiltedRademacherGaussianCFMajorant_eq_sum_coordinate]
    exact Finset.single_le_sum
      (fun j _ =>
        tiltedRademacherGaussianCFCoordinateMajorant_nonneg b x j t)
      (Finset.mem_univ i)

/--
Coordinate-wise decomposition of the sharp finite-band integral.  No
deleted-coordinate damping is discarded.
-/
theorem integral_scaledPrawitzKernel_mul_tiltedMajorant_eq_sum
    (b : ι → ℝ) (x : ℝ) {U₀ U : ℝ}
    (hU₀ : 0 ≤ U₀) (hband : U₀ < U) :
    (∫ t in Icc (-U₀) U₀,
        ‖scaledPrawitzKernel U t‖ *
          tiltedRademacherGaussianCFMajorant b x t) =
      ∑ i, ∫ t in Icc (-U₀) U₀,
        ‖scaledPrawitzKernel U t‖ *
          tiltedRademacherGaussianCFCoordinateMajorant b x i t := by
  classical
  rw [show
      (fun t =>
        ‖scaledPrawitzKernel U t‖ *
          tiltedRademacherGaussianCFMajorant b x t) =
        fun t =>
          ∑ i, ‖scaledPrawitzKernel U t‖ *
            tiltedRademacherGaussianCFCoordinateMajorant b x i t by
    funext t
    rw [tiltedRademacherGaussianCFMajorant_eq_sum_coordinate,
      Finset.mul_sum]]
  exact integral_finsetSum Finset.univ fun i _ =>
    integrableOn_scaledPrawitzKernel_mul_tiltedCoordinateMajorant
      b x i hU₀ hband

end Probability
end CertifiedJL
