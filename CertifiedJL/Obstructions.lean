/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.Counterexamples.L2Lower.LNPLowerTail
import CertifiedJL.Projection.Counterexamples.L2Lower.OrthusPrintedParameters
import CertifiedJL.Obstructions.Lightweight
import CertifiedJL.Projection.Counterexamples.L2Lower.ThresholdLower76

/-!
# Exact certificate-backed obstructions

This umbrella extends the lightweight exact obstructions with the
certificate-backed threshold-76 counterexample.
-/

namespace CertifiedJL.Obstructions

/-- The 512-row balanced-ternary law cannot satisfy the strict 192-bit
threshold-relative lower tail at squared-norm floor `76`.  The witness is the
81-dimensional all-ones vector with modulus `27` and public threshold `9`. -/
theorem ternaryL2ThresholdRows512Bits192Floor76False :
    ¬ L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        squaredNormFloor := NonnegativeRatio.ofNat 76
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 192) := by
  intro h
  have hbad := h 27 81
    thresholdLower512Bits192Floor76Witness 9
    (by norm_num)
    (by simpa [thresholdLower512Bits192Floor76Witness] using
      Counterexamples.ThresholdLower76.Internal.witness_centered)
    (by norm_num)
    (by simp [InputThresholdAtMostNorm,
      thresholdLower512Bits192Floor76Witness,
      Counterexamples.ThresholdLower76.Internal.witness_sqNorm])
    (by norm_num [InputThresholdWithinModulus, NonnegativeRatio.ofNat])
  simp only [ProjectionDistribution.matrixPMF_balancedTernary] at hbad
  exact (not_lt_of_ge thresholdLower512Bits192Floor76Counterexample.le) hbad

/-- Every integer threshold-relative squared-norm floor at least `76` is impossible
for the 512-row balanced-ternary law at 192 bits. -/
theorem ternaryL2ThresholdRows512Bits192AtLeast76False
    (squaredNormFloor : ℕ) (hfloor : 76 ≤ squaredNormFloor) :
    ¬ L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        squaredNormFloor := NonnegativeRatio.ofNat squaredNormFloor
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 192) := by
  intro h
  have hbad := h 27 81
    thresholdLower512Bits192Floor76Witness 9
    (by norm_num)
    (by simpa [thresholdLower512Bits192Floor76Witness] using
      Counterexamples.ThresholdLower76.Internal.witness_centered)
    (by norm_num)
    (by simp [InputThresholdAtMostNorm,
      thresholdLower512Bits192Floor76Witness,
      Counterexamples.ThresholdLower76.Internal.witness_sqNorm])
    (by norm_num [InputThresholdWithinModulus, NonnegativeRatio.ofNat])
  simp only [ProjectionDistribution.matrixPMF_balancedTernary] at hbad
  let _ : MeasurableSpace (Fin 512 → Fin 81 → ℤ) := ⊤
  have hmono :
      eventProbability (sparseRademacherMatrix 512 81)
          (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 76) 9 27
            thresholdLower512Bits192Floor76Witness) ≤
        eventProbability (sparseRademacherMatrix 512 81)
          (L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor) 9 27
            thresholdLower512Bits192Floor76Witness) := by
    apply eventProbability_mono
    intro matrix hfailure
    simp only [L2ThresholdLowerFailure, NonnegativeRatio.ofNat,
      Nat.reducePow, one_mul] at hfailure ⊢
    exact hfailure.trans_le (Nat.mul_le_mul_right 81 hfloor)
  exact (not_lt_of_ge
    (thresholdLower512Bits192Floor76Counterexample.le.trans hmono)) hbad

end CertifiedJL.Obstructions
