/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Probability.NormalApproximation.Shared.ClosedIntervalTransfer

/-!
# Canaries for closed-interval Kolmogorov transfer

The source law below is concentrated exactly at both endpoints of the
singleton interval. Thus the source probability is one, while the atomless
Gaussian comparator assigns the same closed interval probability zero.
-/

open MeasureTheory ProbabilityTheory Set

namespace CertifiedJL.Tests.ClosedIntervalTransfer

open CertifiedJL.Probability

/-- A point mass belongs to the closed singleton interval. -/
example : (Measure.dirac (0 : ℝ)).real (Icc 0 0) = 1 := by
  simp [measureReal_def]

/-- The standard Gaussian gives the closed singleton interval zero mass. -/
example : (gaussianReal 0 1).real (Icc 0 0) = 0 := by
  let : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  simp [measureReal_def]

/-- The transfer theorem preserves the closed endpoints for an atomic source. -/
example :
    (Measure.dirac (0 : ℝ)).real (Icc 0 0) ≤
      (gaussianReal 0 1).real (Icc 0 0) + 2 := by
  have h := probability_Icc_le_standardGaussian_add_two_mul
    (μ := Measure.dirac (0 : ℝ)) (δ := 1) (a := 0) (b := 0)
    (by norm_num) (kolmogorovDistance_le_one _ _)
  norm_num at h ⊢
  exact h

#print axioms CertifiedJL.Probability.probability_Icc_eq_cdf_sub_leftLim
#print axioms
  CertifiedJL.Probability.probability_Icc_le_add_two_mul_of_kolmogorovDistance
#print axioms
  CertifiedJL.Probability.probability_Icc_le_standardGaussian_add_two_mul

end CertifiedJL.Tests.ClosedIntervalTransfer
