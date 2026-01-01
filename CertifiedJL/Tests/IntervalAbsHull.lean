/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Interval.Interval

/-! # Exact canaries for the interval absolute-value hull -/

namespace CertifiedJL.Interval

/- A wholly negative cell must use the negated lower endpoint for its upper
absolute bound. -/
example : (⟨-5, -2⟩ : Interval 0).absHull = ⟨0, 5⟩ := by rfl

/- A zero-crossing cell keeps the larger endpoint magnitude. -/
example : (⟨-3, 7⟩ : Interval 0).absHull = ⟨0, 7⟩ := by rfl

/- A positive cell remains sound with the uniform zero lower endpoint. -/
example : (⟨2, 5⟩ : Interval 0).absHull = ⟨0, 5⟩ := by rfl

/- Direct semantic canary for the negative branch. -/
example : (⟨-5, -2⟩ : Interval 0).absHull.Contains |(-4 : ℝ)| := by
  apply contains_absHull
  norm_num [Contains, Dyadic.toReal, Dyadic.scale]

#print axioms contains_absHull

set_option linter.style.longLine false in
open Lean in
run_cmd
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms ``contains_absHull
  unless axioms.size == allowed.size &&
      axioms.all allowed.contains && allowed.all axioms.contains do
    throwError "unexpected exact axiom set for contains_absHull: {axioms}"

end CertifiedJL.Interval
