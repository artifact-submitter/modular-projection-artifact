/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperHybrid
import Lean.Util.CollectAxioms

open MeasureTheory ProbabilityTheory Lean

namespace CertifiedJL.Tests.PeanoKHybrid

example (a : Fin 3 → ℝ) :
    (sparseRademacherRow 3).map (fun row => realRowDot row a) =
      (rademacherPMF (Fin 3 × Fin 2)).map
        (rademacherSum (sparseUpperDuplicatedCoefficient a)) :=
  sparseRademacherRow_map_realRowDot_eq_rademacherSum a

example (a : Fin 2 → ℝ) :
    quadraticComplexMGF (fun row : Fin 2 → ℤ => realRowDot row a)
        (sparseRademacherRow 2).toMeasure ((1 / 3 : ℝ) + 2 * Complex.I) =
      ∫ bits, complexQuadraticExp ((1 / 3 : ℝ) + 2 * Complex.I)
          (rademacherSum (sparseUpperDuplicatedCoefficient a) bits)
        ∂(rademacherPMF (Fin 2 × Fin 2)).toMeasure :=
  quadraticComplexMGF_sparseRow_eq_rademacherSum a _

run_cmd
  let allowed : Array Lean.Name :=
    #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Lean.Name :=
    #[``CertifiedJL.realRowDot_sparseRow_eq_rademacherSum,
      ``CertifiedJL.sparseRademacherRow_map_realRowDot_eq_rademacherSum,
      ``CertifiedJL.quadraticComplexMGF_sparseRow_eq_rademacherSum]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    unless axioms.size == allowed.size &&
        axioms.all allowed.contains && allowed.all axioms.contains do
      throwError "unexpected axioms for {target}: {axioms}"

end CertifiedJL.Tests.PeanoKHybrid
