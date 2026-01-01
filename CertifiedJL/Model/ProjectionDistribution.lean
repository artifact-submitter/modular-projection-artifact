/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Model.Distributions.BalancedTernary

/-!
# Projection distributions

This module gives the public vocabulary for the matrix distributions used by
CertifiedJL. A descriptor determines the exact PMF of one row and of a matrix.
The balanced-ternary case samples each entry independently, with masses `1/4`,
`1/2`, and `1/4` at `-1`, `0`, and `1`.
-/

namespace CertifiedJL

/-- A supported distribution for sampling projection rows and matrices. -/
inductive ProjectionDistribution
  | balancedTernary
deriving DecidableEq, Repr

namespace ProjectionDistribution

/-- The exact finite PMF of one projection row in dimension `d`. In the
balanced-ternary case, its `d` entries are mutually independent. -/
noncomputable def rowPMF (distribution : ProjectionDistribution) (d : ℕ) : PMF (Fin d → ℤ) :=
  match distribution with
  | .balancedTernary => sparseRademacherRow d

/-- The exact finite PMF of a `rows`-by-`d` projection matrix. In the
balanced-ternary case, all entries are mutually independent. -/
noncomputable def matrixPMF (distribution : ProjectionDistribution) (rows d : ℕ) :
    PMF (Fin rows → Fin d → ℤ) :=
  match distribution with
  | .balancedTernary => sparseRademacherMatrix rows d

@[simp]
theorem rowPMF_balancedTernary (d : ℕ) :
    rowPMF .balancedTernary d = sparseRademacherRow d :=
  rfl

@[simp]
theorem matrixPMF_balancedTernary (rows d : ℕ) :
    matrixPMF .balancedTernary rows d =
      sparseRademacherMatrix rows d :=
  rfl

end ProjectionDistribution
end CertifiedJL
