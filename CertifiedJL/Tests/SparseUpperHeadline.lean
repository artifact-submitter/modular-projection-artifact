/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Results.L2.Upper.Rows256Bits128
import Lean.Util.CollectAxioms

/-! Mutation and trust canaries for the unconditional sparse upper tail. -/

open Lean

namespace CertifiedJL.Tests

example : SparseUpper128Statement := sparseUpper128_assembly

/-- The public upper theorem includes the zero vector at modulus zero. -/
example :
    eventProbability (sparseRademacherMatrix 256 0)
        (SparseUpperFailure 0 (fun i : Fin 0 => Fin.elim0 i)) <
      failureTarget 128 := by
  simpa [rowCount, securityBits] using
    sparseUpper128_assembly 0 0 (fun i : Fin 0 => Fin.elim0 i)

/-- Expand the checked certificate theorem to its literal mathematical proposition. -/
example :
    ∀ (q d : ℕ) (w : Fin d → ℤ),
      eventProbability (sparseRademacherMatrix 256 d)
          (fun J => modularProjectionSqNorm q J w > 338 * sqNorm w) <
        (2 : ENNReal)⁻¹ ^ 128 := by
  intro q d w
  have h := sparseUpper128_assembly q d w
  change eventProbability (sparseRademacherMatrix 256 d)
      (fun J => modularProjectionSqNorm q J w > 338 * sqNorm w) <
    (2 : ENNReal)⁻¹ ^ 128 at h
  exact h

set_option linter.style.longLine false in
run_cmd
  let allowed : Array Lean.Name :=
    #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Lean.Name :=
    #[``CertifiedJL.sparseUpper_hybrid,
      ``CertifiedJL.sparseUpper_fourthOrder,
      ``CertifiedJL.Results.L2.Upper.Rows256Bits128.ternaryL2Upper338]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    unless axioms.size == allowed.size &&
        axioms.all allowed.contains && allowed.all axioms.contains do
      throwError "unexpected axioms for {target}: {axioms}"

end CertifiedJL.Tests
