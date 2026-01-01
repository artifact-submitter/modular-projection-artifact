/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperContourQuadrature

namespace CertifiedJL.Tests

/-- An asymmetric producer-direct canary for every quadrature factor. -/
example (frequency : ℝ) :
    ‖shiftedGaussianContourWeight (3 / 5) (1 / 3) 338 (2 / 3) frequency‖ =
      (1 / (2 * Real.pi * standardGaussianCDF (1 / 3))) *
        Real.exp (-((2 / 3) * (338 - (1 / 3) * (3 / 5)) -
          (3 / 5) ^ 2 * (2 / 3) ^ 2 / 2)) *
        Real.exp (-((3 / 5) ^ 2 / 2) * frequency ^ 2) *
        (1 / Real.sqrt ((2 / 3) ^ 2 + frequency ^ 2)) := by
  exact norm_shiftedGaussianContourWeight_eq_quadrature
    (3 / 5) (1 / 3) 338 (2 / 3) frequency

/-- A non-unit, asymmetric producer canary for right-endpoint monotonicity. -/
example :
    Real.exp (-(7 / 10 : ℝ) * 2 ^ 2) *
        (1 / Real.sqrt ((3 / 5 : ℝ) ^ 2 + 2 ^ 2)) ≤
      Real.exp (-(7 / 10 : ℝ) * 1 ^ 2) *
        (1 / Real.sqrt ((3 / 5 : ℝ) ^ 2 + 1 ^ 2)) := by
  exact gaussianQuadratureWeight_le_of_le
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- A non-unit producer canary for the exact tail denominator. -/
example :
    (∫ frequency : ℝ in Set.Ioi (3 : ℝ),
        7 * Real.exp (-(2 : ℝ) * frequency ^ 2) *
          (1 / Real.sqrt ((4 : ℝ) ^ 2 + frequency ^ 2))) ≤
      7 * Real.exp (-(2 : ℝ) * 3 ^ 2) / (2 * 2 * 3 ^ 2) := by
  exact integral_Ioi_gaussianQuadratureWeight_le
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- A non-unit cell-length canary for the rectangle integral. -/
example :
    (∫ _x : ℝ in Set.Ioc (2 : ℝ) 5, (7 : ℝ)) ≤ (5 - 2) * 7 := by
  exact integral_Ioc_le_length_mul (by norm_num)
    (MeasureTheory.integrableOn_const (by simp)) (by intro; norm_num)

end CertifiedJL.Tests
