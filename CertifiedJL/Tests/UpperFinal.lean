/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.L2.Upper.BalancedTernary.UpperFinal
import Lean.Util.CollectAxioms

/-! Producer-direct canaries for the final sparse upper normalization. -/

namespace CertifiedJL.Tests.UpperFinal

/-- The final real-to-ENNReal adapter preserves the strict endpoint. -/
example {α : Type*} [MeasurableSpace α] (p : PMF α) (event : α → Prop)
    (hreal : (eventProbability p event).toReal < (2 : ℝ)⁻¹ ^ 7) :
    eventProbability p event < failureTarget 7 :=
  eventProbability_lt_failureTarget_of_toReal_lt p event 7 hreal

private def asymmetricWeights : Fin 2 → ℤ := ![3, 4]

/-- The canonical integer normalization uses the Euclidean square root. -/
example :
    sparseUpperNormalizedCoefficient asymmetricWeights = ![3 / 5, 4 / 5] := by
  funext i
  fin_cases i <;>
    norm_num [sparseUpperNormalizedCoefficient, asymmetricWeights,
      sqNorm, Fin.sum_univ_succ]

/-- The normalized-energy identity directly consumes the public producer. -/
example {m d : ℕ} (J : Matrix (Fin m) (Fin d) ℤ) (w : Fin d → ℤ)
    (hw : w ≠ 0) :
    realProjectionSqNorm (sparseUpperNormalizedCoefficient w) J =
      (projectionSqNorm J w : ℝ) / (sqNorm w : ℝ) :=
  realProjectionSqNorm_eq_projectionSqNorm_div J w hw

/-- The exact strict modular event maps to the strict normalized threshold. -/
example {q m d : ℕ} (J : Matrix (Fin m) (Fin d) ℤ) (w : Fin d → ℤ)
    (hw : w ≠ 0) (hfailure : SparseUpperFailure q w J) :
    (sparseUpperThreshold : ℝ) <
      realProjectionSqNorm (sparseUpperNormalizedCoefficient w) J :=
  sparseUpperFailure_imp_realProjectionSqNorm J w hw hfailure

/-- The final wrapper consumes exactly one coefficient-uniform normalized theorem. -/
example
    (hnormalized : ∀ (d : ℕ) (a : Fin d → ℝ),
      ∑ i, a i ^ 2 = 1 →
      eventProbability (sparseRademacherMatrix rowCount d)
          (fun J => (sparseUpperThreshold : ℝ) <
            realProjectionSqNorm a J) <
        failureTarget securityBits) :
    SparseUpper128Statement :=
  sparseUpper128_of_realProjectionSqNorm hnormalized

run_cmd
  let allowed : Array Lean.Name :=
    #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Lean.Name :=
    #[``CertifiedJL.sum_sq_sparseUpperNormalizedCoefficient,
      ``CertifiedJL.realProjectionSqNorm_eq_projectionSqNorm_div,
      ``CertifiedJL.sparseUpperFailure_imp_realProjectionSqNorm,
      ``CertifiedJL.sparseUpperFailure_probability_le_normalized,
      ``CertifiedJL.eventProbability_lt_failureTarget_of_toReal_lt,
      ``CertifiedJL.sparseUpper128_of_realProjectionSqNorm,
      ``CertifiedJL.sparseProfileFourthMoment_le_one,
      ``CertifiedJL.sparseUpper128_of_profileSplit]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    unless axioms.size == allowed.size &&
        axioms.all allowed.contains && allowed.all axioms.contains do
      throwError "unexpected axioms for {target}: {axioms}"

end CertifiedJL.Tests.UpperFinal
