/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperPeanoProductLaws
import Lean.Util.CollectAxioms

/-! Direct endpoint and trust canaries for the U7 product-law bridges. -/

open Lean MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CertifiedJL.Tests.UpperPeanoProductLaws

private noncomputable def asymmetricWeights : Fin 2 → ℝ :=
  ![(1 / 2 : ℝ), -1 / 2]

/-- Pins the sign convention of both Rademacher coordinates and the asymmetric
weighted-sum map. -/
example :
    Measure.map (rademacherSum asymmetricWeights)
        (rademacherPMF (Fin 2)).toMeasure =
      Measure.map (fun x : Fin 2 → ℝ =>
        ∑ i, asymmetricWeights i * x i)
        (Measure.pi (fun _ : Fin 2 => standardRademacherMeasure)) := by
  exact rademacherSum_map_eq_map_pi_standardRademacher asymmetricWeights

/-- The opposite-sign two-coordinate profile has squared mass exactly `1/2`,
so its Gaussian product endpoint is the U7 Gaussian-half law. -/
example :
    Measure.map (fun x : Fin 2 → ℝ =>
        ∑ i, asymmetricWeights i * x i)
        (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) =
      gaussianReal 0 (2 : NNReal)⁻¹ := by
  apply map_weightedSum_pi_gaussianReal_eq_gaussianHalf asymmetricWeights
  simp [asymmetricWeights, Fin.sum_univ_two]
  norm_num

set_option linter.style.longLine false in
run_cmd
  let allowed : Array Lean.Name :=
    #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Lean.Name :=
    #[``CertifiedJL.rademacherSigns_toMeasure,
      ``CertifiedJL.rademacherSum_map_eq_map_pi_standardRademacher,
      ``CertifiedJL.map_weightedSum_pi_gaussianReal,
      ``CertifiedJL.map_weightedSum_pi_gaussianReal_eq_gaussianHalf]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    unless axioms.size == allowed.size &&
        axioms.all allowed.contains && allowed.all axioms.contains do
      throwError "unexpected axioms for {target}: {axioms}"

end CertifiedJL.Tests.UpperPeanoProductLaws
