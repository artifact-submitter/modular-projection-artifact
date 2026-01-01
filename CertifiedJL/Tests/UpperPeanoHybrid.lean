/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperPeanoHybrid
import Lean.Util.CollectAxioms

/-! Mutation canaries for the exact finite U7 assembler. -/

open Lean
open scoped BigOperators

namespace CertifiedJL.Tests.UpperPeanoHybrid

/-- A negative, nonunit coefficient pins the sign and both exact constants in
the one-coordinate specialization. -/
example (G0 R0 G4 K4 Gcoord4 : ℂ) (D6 D8 : ℝ)
    (hfirst : G0 - R0 = (((-3 / 5 : ℝ) ^ 4) / 12 : ℝ) • K4)
    (hGK : ‖Gcoord4 - K4‖ ≤
      (11 / 15 : ℝ) * (-3 / 5 : ℝ) ^ 2 * D6)
    (hGG : ‖Gcoord4 - G4‖ ≤
      (((-3 / 5 : ℝ) ^ 4) / 12 : ℝ) * D8) :
    ‖G0 - R0 - (((-3 / 5 : ℝ) ^ 4) / 12 : ℝ) • G4‖ ≤
      ((-3 / 5 : ℝ) ^ 4) ^ 2 / 144 * D8 +
        11 * (-3 / 5 : ℝ) ^ 6 / 180 * D6 := by
  simpa using
    (norm_fourthPeanoHybridRemainder_le
      (ι := Fin 1) (fun _ => (-3 / 5 : ℝ))
      G0 R0 G4 (fun _ => K4) (fun _ => Gcoord4) D6 D8
      (by simpa using hfirst) (fun _ => by simpa using hGK)
      (fun _ => by simpa using hGG))

set_option linter.style.longLine false in
run_cmd
  let allowed : Array Lean.Name :=
    #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Lean.Name :=
    #[``CertifiedJL.norm_fourthPeanoHybridRemainder_le]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    unless axioms.size == allowed.size &&
        axioms.all allowed.contains && allowed.all axioms.contains do
      throwError "unexpected axioms for {target}: {axioms}"

end CertifiedJL.Tests.UpperPeanoHybrid
