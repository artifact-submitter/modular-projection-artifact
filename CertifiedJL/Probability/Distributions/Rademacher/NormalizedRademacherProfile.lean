/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.Distributions.Rademacher.RademacherLyapunovProfile

/-!
# Elementary bounds for normalized Rademacher profiles

This module records the coefficientwise estimate used when an ordinary
Rademacher sum is close to Gaussian. It is independent of any quantitative
normal-approximation constant or certificate.
-/

open scoped BigOperators

namespace CertifiedJL
namespace Probability

/--
For a variance-one coefficient profile, a uniform coefficient bound also
bounds the sum of absolute cubes.
-/
theorem sum_abs_cube_le_of_sum_sq_eq_one_of_abs_le
    {ι : Type*} [Fintype ι] (b : ι → ℝ) {B : ℝ}
    (hnorm : ∑ i, b i ^ 2 = 1)
    (hbound : ∀ i, |b i| ≤ B) :
    ∑ i, |b i| ^ 3 ≤ B := by
  calc
    ∑ i, |b i| ^ 3 = ∑ i, |b i| * b i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ, sq_abs]
      ring
    _ ≤ ∑ i, B * b i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hbound i) (sq_nonneg (b i))
    _ = B * ∑ i, b i ^ 2 := by rw [Finset.mul_sum]
    _ = B := by rw [hnorm, mul_one]

end Probability
end CertifiedJL
