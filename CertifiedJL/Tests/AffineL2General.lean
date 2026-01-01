/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.Affine.Assembly.AffineL2General
import Lean.Util.CollectAxioms

/-! # Strict-event, profile-boundary and trust canaries for general affine L2 -/

namespace CertifiedJL.Tests.AffineL2General

-- The singleton cutoff is inclusive, including a negative coefficient.
example : ∃ i : Fin 1, 49 * 50 ≤ 50 * ((fun _ : Fin 1 => (-49 : ℤ)) i).natAbs := by
  decide

-- At exactly 3/4, an input with enough total energy belongs to the diffuse
-- branch, while neither the singleton nor strict near test is satisfied.
example :
    InputThresholdAtMostNorm 4 (fun _ : Fin 2 => (3 : ℤ)) ∧
    (¬ ∃ i : Fin 2, 49 * 4 ≤ 50 * ((fun _ : Fin 2 => (3 : ℤ)) i).natAbs) ∧
    (¬ ∃ i : Fin 2, 3 * 4 < 4 * ((fun _ : Fin 2 => (3 : ℤ)) i).natAbs) ∧
    (∀ i : Fin 2, 4 * ((fun _ : Fin 2 => (3 : ℤ)) i).natAbs ≤ 3 * 4) := by
  norm_num [InputThresholdAtMostNorm, sqNorm]

private def quarter : NonnegativeRatio :=
  { numerator := 1, denominator := 4, denominator_pos := by decide }

-- E=1 and (1/4)*b²=1: equality is excluded on both sides of the bridge.
example : ¬ AffineL2ThresholdLowerFailure quarter 2 7
    (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 2) (fun _ _ => 0) := by
  norm_num [AffineL2ThresholdLowerFailure, quarter, shiftedModularProjectionSqNorm,
    centeredMod, rowDot]
  all_goals decide

example : ¬ AffineL2RealThresholdLowerFailure quarter.toReal 2 7
    (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 2) (fun _ _ => 0) := by
  rw [affineL2RealThresholdLowerFailure_toReal_iff]
  norm_num [AffineL2ThresholdLowerFailure, quarter, shiftedModularProjectionSqNorm,
    centeredMod, rowDot]
  all_goals decide

-- A zero floor has an empty strict failure event, even with arbitrary shifts.
example {q b rows d : ℕ} (shift : Fin rows → ℤ) (w : Fin d → ℤ)
    (J : Fin rows → Fin d → ℤ) :
    ¬ AffineL2RealThresholdLowerFailure 0 b q shift w J := by
  unfold AffineL2RealThresholdLowerFailure
  simp only [zero_mul, not_lt]
  exact Nat.cast_nonneg _

run_cmd
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Lean.Name := #[
    ``thresholdProfile_singleton_near_diffuse,
    ``affineL2RealThresholdLowerFailure_toReal_iff,
    ``ternaryAffineThresholdLowerTail_from_rowKernelIntegral_real_at,
    ``affineL2SingletonTiltValues_nonempty,
    ``affineL2SingletonTiltValues_bddBelow,
    ``ternaryAffineL2LowerTail_toReal_le_finiteTilt,
    ``ternaryAffineL2LowerTail_toReal_le_general,
    ``ternaryAffineL2LowerTail_toReal_le_general_of_ratio,
    ``ternaryAffineL2ThresholdLowerTailAt_of_generalBound_lt_failureTarget,
    ``ternaryAffineL2ThresholdLowerTailAt_of_finiteTilt_lt_failureTarget,
    ``CertificateAssembly.affineL2General_profiles]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    unless axioms.all allowed.contains do
      throwError "unexpected axioms for {target}: {axioms}"

end CertifiedJL.Tests.AffineL2General
