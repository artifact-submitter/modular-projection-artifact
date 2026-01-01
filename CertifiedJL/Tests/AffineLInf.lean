/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Results.Affine.LInf.Lower.Direct
import Lean.Util.CollectAxioms

/-! # Affine lower-tail public import, event-boundary and trust canaries -/

namespace CertifiedJL.Tests.AffineLInf

-- The public import must expose both closed endpoints and the concrete two-tilt formula.
#check Results.Affine.LInf.Lower.Direct.ternaryAffineLInfThresholdLower256Cap67Over200Bits130
#check Results.Affine.LInf.Lower.Direct.ternaryAffineLInfThresholdLower256Cap6Over25Bits197
#check Results.Affine.LInf.Lower.Direct.ternaryAffineLInfThresholdLower_probability_le

private def quarterParameters : LInfThresholdLowerParameters :=
  { distribution := .balancedTernary, rows := 1,
    coordinateCap := { numerator := 1, denominator := 4, denominator_pos := by decide },
    modulusMargin := NonnegativeRatio.ofNat 3 }

-- A shift exactly at the cap passes: replacing the closed event by a strict event fails here.
example : AffineLInfThresholdSmallProjection quarterParameters 4 13
    (fun _ => 1) (fun _ : Fin 1 => 1) (fun _ _ => 0) := by
  unfold AffineLInfThresholdSmallProjection quarterParameters
  decide

-- A larger nonzero shift fails: dropping the shift from the event fails here.
example : ¬ AffineLInfThresholdSmallProjection quarterParameters 4 13
    (fun _ => 2) (fun _ : Fin 1 => 1) (fun _ _ => 0) := by
  unfold AffineLInfThresholdSmallProjection quarterParameters
  decide

run_cmd
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Lean.Name := #[
    ``Results.Affine.LInf.Lower.Direct.ternaryAffineLInfThresholdLower256Cap67Over200Bits130,
    ``Results.Affine.LInf.Lower.Direct.ternaryAffineLInfThresholdLower256Cap6Over25Bits197,
    ``Results.Affine.LInf.Lower.Direct.ternaryAffineLInfThresholdLower_probability_le]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    unless axioms.all allowed.contains do
      throwError "unexpected axioms for {target}: {axioms}"

end CertifiedJL.Tests.AffineLInf
