/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Fourier.CosineProductComparison

/-! Direct canaries for the finite cosine--Gaussian telescope. -/

namespace CertifiedJL

/-- A two-coordinate canary with unequal, nonzero coefficients.  It pins both
the matching variance `1² + 2² = 5` and fourth-power cost `1⁴ + 2⁴ = 17`, so
it rejects a copied-coordinate or squared-moment replacement cost. -/
example (t : ℝ) :
    |Real.cos t * Real.cos (2 * t) - Real.exp (-(5 * t ^ 2) / 2)| ≤
      17 * t ^ 4 / 12 := by
  have h := abs_prod_cos_sub_exp_neg_sum_sq_half_le
    (c := ![(1 : ℝ), 2]) t
  norm_num [Fin.prod_univ_two] at h ⊢
  simpa using h

#print axioms abs_prod_cos_sub_exp_neg_sum_sq_half_le

end CertifiedJL
