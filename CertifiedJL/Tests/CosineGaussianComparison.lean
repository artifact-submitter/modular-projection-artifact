/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Analysis.Fourier.CosineGaussianComparison

/-! Direct canaries for the global cosine--Gaussian comparison (S2). -/

namespace CertifiedJL

/-- Small-domain canary: exercises the nontrivial Taylor branch. -/
example : |Real.cos (1 / 2) - Real.exp (-((1 / 2 : ℝ) ^ 2) / 2)| ≤
    (1 / 2 : ℝ) ^ 4 / 12 :=
  abs_cos_sub_exp_neg_half_sq_le (1 / 2)

/-- Large-domain canary: exercises the global, nonlocal branch. -/
example : |Real.cos 5 - Real.exp (-(5 : ℝ) ^ 2 / 2)| ≤
    (5 : ℝ) ^ 4 / 12 :=
  abs_cos_sub_exp_neg_half_sq_le 5

#print axioms abs_cos_sub_exp_neg_half_sq_le

end CertifiedJL
