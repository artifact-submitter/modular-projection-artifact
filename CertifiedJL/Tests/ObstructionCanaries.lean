/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Tests.ObstructionCanariesFast
import CertifiedJL.Obstructions

/-!
# Obstruction regression tests

These canaries extend `ObstructionCanariesFast` with the generated
threshold-76 certificate replay and its public obstruction theorem types.
-/

namespace CertifiedJL
namespace Tests
namespace ObstructionCanaries

open MeasureTheory Probability

example :
    eventProbability (sparseRademacherMatrix 512 81)
        (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 76) 9 27
          thresholdLower512Bits192Floor76Witness) >
      failureTarget 192 :=
  thresholdLower512Bits192Floor76Counterexample

example : thresholdLower512Bits192Floor76Witness =
    fun _ : Fin 81 => (1 : ℤ) := rfl

example (matrix : Fin 512 → Fin 81 → ℤ) :
    L2ThresholdLowerFailure (NonnegativeRatio.ofNat 76) 9 27
        thresholdLower512Bits192Floor76Witness matrix ↔
      modularProjectionSqNorm 27 matrix (fun _ : Fin 81 => (1 : ℤ)) < 6156 := by
  rw [show thresholdLower512Bits192Floor76Witness =
    (fun _ : Fin 81 => (1 : ℤ)) by rfl]
  norm_num [L2ThresholdLowerFailure, NonnegativeRatio.ofNat]

example : Odd 27 := by norm_num

example : CenteredInput 27 thresholdLower512Bits192Floor76Witness := by
  simpa [thresholdLower512Bits192Floor76Witness] using
    Counterexamples.ThresholdLower76.Internal.witness_centered

example :
    InputThresholdAtMostNorm 9 thresholdLower512Bits192Floor76Witness := by
  simp [InputThresholdAtMostNorm, thresholdLower512Bits192Floor76Witness,
    Counterexamples.ThresholdLower76.Internal.witness_sqNorm]

example :
    InputThresholdWithinModulus (NonnegativeRatio.ofNat 3) 27 9 := by
  norm_num [InputThresholdWithinModulus, NonnegativeRatio.ofNat]

example :
    ¬ L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        squaredNormFloor := NonnegativeRatio.ofNat 76
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 192) :=
  Obstructions.ternaryL2ThresholdRows512Bits192Floor76False

example (squaredNormFloor : ℕ) (hfloor : 76 ≤ squaredNormFloor) :
    ¬ L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        squaredNormFloor := NonnegativeRatio.ofNat squaredNormFloor
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 192) :=
  Obstructions.ternaryL2ThresholdRows512Bits192AtLeast76False squaredNormFloor hfloor

#print axioms thresholdLower512Bits192Floor76Counterexample
#print axioms Obstructions.ternaryL2ThresholdRows512Bits192Floor76False
#print axioms Obstructions.ternaryL2ThresholdRows512Bits192AtLeast76False

end ObstructionCanaries
end Tests
end CertifiedJL
