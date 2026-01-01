/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.NormalApproximation.Rademacher.TiltedRademacherBridge

/-!
# Moments of the standardized tilted Rademacher coordinates

This file exposes the exact variance and third-absolute-moment normalization
used by the quantitative normal-approximation theorem.
-/

open scoped BigOperators

namespace CertifiedJL
namespace Probability

/-- Sum of the third absolute moments of centered weighted biased signs. -/
noncomputable def tiltedRademacherThirdMomentSum
    {ι : Type*} [Fintype ι] (u a : ι → ℝ) : ℝ :=
  ∑ i, |a i| ^ 3 * (1 - Real.tanh (u i) ^ 4)

theorem tiltedRademacherThirdMomentSum_nonneg
    {ι : Type*} [Fintype ι] (u a : ι → ℝ) :
    0 ≤ tiltedRademacherThirdMomentSum u a := by
  unfold tiltedRademacherThirdMomentSum
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (by positivity)
  have ht := Real.tanh_sq_lt_one (u i)
  nlinarith [sq_nonneg (Real.tanh (u i) ^ 2)]

/--
After standardization, the coordinate variances sum to one.
-/
theorem standardizedTiltedRademacherVariance_eq_one
    {ι : Type*} [Fintype ι] (u a : ι → ℝ)
    (ha : ∃ i, a i ≠ 0) :
    ∑ i,
        (a i / tiltedRademacherStdDev u a) ^ 2 *
          (1 - Real.tanh (u i) ^ 2) = 1 := by
  simpa [tiltedRademacherVariance] using
    tiltedRademacherVariance_standardized_eq_one u a ha

/--
At the Esscher tilt `uᵢ=x bᵢ`, the standardized third-moment sum is exactly
the Lyapunov ratio used by the profile bound.
-/
theorem tiltedRademacherThirdMomentSum_standardized_specialize
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (x : ℝ)
    (hnorm : ∑ i, b i ^ 2 = 1) :
    tiltedRademacherThirdMomentSum (fun i => x * b i)
        (fun i => b i /
          tiltedRademacherStdDev (fun j => x * b j) b) =
      rademacherLyapunovRatio b x := by
  have hs :
      0 < rademacherTiltedStdDev b x :=
    sqrt_rademacherTiltedVariance_pos b x hnorm
  unfold tiltedRademacherThirdMomentSum rademacherLyapunovRatio
    rademacherLyapunovNumerator
  rw [show tiltedRademacherStdDev (fun j => x * b j) b =
      rademacherTiltedStdDev b x by
    exact tiltedRademacherStdDev_specialize b x]
  simp_rw [abs_div, abs_of_pos hs, div_pow]
  rw [show
      (∑ i, |b i| ^ 3 / rademacherTiltedStdDev b x ^ 3 *
          (1 - Real.tanh (x * b i) ^ 4)) =
        (∑ i, |b i| ^ 3 *
          (1 - Real.tanh (x * b i) ^ 4)) /
            rademacherTiltedStdDev b x ^ 3 by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring]
  rfl

end Probability
end CertifiedJL
