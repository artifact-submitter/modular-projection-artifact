/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperPeanoFinal
import Lean.Util.CollectAxioms

/-! Direct positive-strip and trust canaries for the unconditional sparse U7/U4 producer. -/

open Lean MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace CertifiedJL.Tests.UpperPeanoFinal

private noncomputable def asymmetricWeights : Fin 2 → ℝ :=
  ![(3 / 5 : ℝ), -4 / 5]

private theorem asymmetricWeights_sq :
    ∑ i, asymmetricWeights i ^ 2 = 1 := by
  simp [asymmetricWeights, Fin.sum_univ_two]
  norm_num

/-- A genuinely asymmetric sparse row and nonreal positive-strip parameter
consume the unconditional U7 producer directly. -/
example := sparseUpper_hybrid asymmetricWeights asymmetricWeights_sq
  (s := (4 / 5 : ℝ) + 2 * Complex.I) (by norm_num) (by norm_num)

/-- The same profile consumes the literal U4 theorem, with no hybrid premise. -/
example := sparseUpper_fourthOrder asymmetricWeights asymmetricWeights_sq
  (s := (4 / 5 : ℝ) + 2 * Complex.I) (by norm_num) (by norm_num)

set_option linter.style.longLine false in
run_cmd
  let allowed : Array Lean.Name :=
    #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Lean.Name :=
    #[``CertifiedJL.norm_upperPeanoHybridDerivFourValue_sub_zero_le_unconditional,
      ``CertifiedJL.norm_upperPeanoHybridRemainder_le,
      ``CertifiedJL.norm_upperPeanoHybridRemainder_le_all,
      ``CertifiedJL.sparseUpper_hybrid,
      ``CertifiedJL.sparseUpper_fourthOrder]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    unless axioms.size == allowed.size &&
        axioms.all allowed.contains && allowed.all axioms.contains do
      throwError "unexpected axioms for {target}: {axioms}"

end CertifiedJL.Tests.UpperPeanoFinal
