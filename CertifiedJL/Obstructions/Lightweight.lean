/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Projection.Counterexamples.L2Upper
import CertifiedJL.Projection.Counterexamples.L2Upper.SecurityCeiling
import CertifiedJL.Projection.Counterexamples.L2Upper.Rows192Upper287Bits130
import CertifiedJL.Projection.Counterexamples.L2Upper.Rows256Upper404Bits192
import CertifiedJL.Projection.Counterexamples.L2Upper.Rows384Upper507Bits192
import CertifiedJL.Projection.Counterexamples.L2Upper.Rows512Upper605Bits192
import CertifiedJL.Projection.Counterexamples.L2Upper.Rows512Upper678Bits256
import CertifiedJL.Projection.Counterexamples.LInf.SparseLInfTwoCoordinate
import CertifiedJL.Projection.Counterexamples.LInf.TernaryLInfThresholdMarginOne
import CertifiedJL.Projection.Counterexamples.LInf.TernaryLInfRows192Cap34
import CertifiedJL.Projection.Counterexamples.LInf.TernaryLInfRows256CapHalf
import CertifiedJL.Projection.Counterexamples.LInf.TernaryLInfUpperRows192
import CertifiedJL.Projection.Counterexamples.L2Lower.DenseSignThreshold
import CertifiedJL.Projection.Counterexamples.L2Lower.TernaryL2Rows256Floor30
import CertifiedJL.Projection.Counterexamples.L2Lower.TernaryL2Rows256Floor31
import CertifiedJL.Projection.Counterexamples.L2Lower.TernaryL2Rows256MarginTwo
import CertifiedJL.Projection.Counterexamples.L2Lower.ThresholdSecurityCeiling
import CertifiedJL.Projection.Counterexamples.L2Lower.ThresholdLowerRows192Floor12

/-!
# Lightweight exact obstructions

This module contains the exact obstruction theorems that do not depend on a
large generated certificate replay.  It is safe to import from fast CI roots.
-/

namespace CertifiedJL.Obstructions

/-- Squared threshold `30` is false for 256 balanced-ternary rows at a
128-bit failure budget under modulus margin `3`.  The fixed witness already
has strict failure probability greater than `2^-127`. -/
theorem ternaryL2ThresholdRows256Floor30Bits128False :
    ¬ L2ThresholdLowerTailAt
      Counterexamples.TernaryL2Rows256Floor30.parametersMarginThree
      (failureTarget 128) :=
  Counterexamples.TernaryL2Rows256Floor30.bits128_marginThree_false

/-- The same strict floor-30 witness also rules out the stronger historical
modulus margin `125` at a 128-bit failure budget. -/
theorem ternaryL2ThresholdRows256Floor30Margin125Bits128False :
    ¬ L2ThresholdLowerTailAt
      Counterexamples.TernaryL2Rows256Floor30.parametersMargin125
      (failureTarget 128) :=
  Counterexamples.TernaryL2Rows256Floor30.bits128_margin125_false

/-- Squared floor `29` is false for 256 balanced-ternary rows at a 128-bit
budget for every exact rational modulus margin at most `9/4`. -/
theorem ternaryL2ThresholdRows256Floor29MarginAtMostNineFourthsBits128False
    (margin : NonnegativeRatio)
    (hmargin : margin.LE Counterexamples.TernaryL2Rows256MarginTwo.nineFourths) :
    ¬ L2ThresholdLowerTailAt
      (Counterexamples.TernaryL2Rows256MarginTwo.parameters margin)
      (failureTarget 128) :=
  Counterexamples.TernaryL2Rows256MarginTwo.bits128_false_of_le_nineFourths
    margin hmargin

/-- Exact integer-margin-two specialization of the floor-29 obstruction. -/
theorem ternaryL2ThresholdRows256Floor29MarginTwoBits128False :
    ¬ L2ThresholdLowerTailAt
      Counterexamples.TernaryL2Rows256MarginTwo.parametersTwo
      (failureTarget 128) :=
  Counterexamples.TernaryL2Rows256MarginTwo.bits128_marginTwo_false

/-- Squared threshold `31` is false for 256 balanced-ternary rows at a
128-bit failure budget. -/
theorem ternaryL2ThresholdRows256Floor31Bits128False :
    ¬ L2ThresholdLowerTailAt
      Counterexamples.TernaryL2Rows256Floor31.parameters
      (failureTarget 128) :=
  Counterexamples.TernaryL2Rows256Floor31.bits128_false

/-- Generic singleton/binomial obstruction at arbitrary rows, integral strict
floor, and security budget, discharged by one exact cross-multiplied check. -/
theorem ternaryL2SingletonThresholdFalseOfScaled
    (rows squaredNormFloor securityBits : ℕ)
    (hscaled : 2 ^ rows < 2 ^ securityBits *
      Counterexamples.TernaryL2Rows256Floor31.binomialTailNumerator
        rows squaredNormFloor) :
    ¬ L2ThresholdLowerTailAt
      (Counterexamples.TernaryL2Rows256Floor31.familyParameters
        rows squaredNormFloor)
      (failureTarget securityBits) :=
  Counterexamples.TernaryL2Rows256Floor31.lowerTail_false_of_scaled
    rows squaredNormFloor securityBits hscaled

theorem ternaryL2ThresholdRows192Floor14Bits128False :
    ¬ L2ThresholdLowerTailAt
      (Counterexamples.TernaryL2Rows256Floor31.familyParameters 192 14)
      (failureTarget 128) :=
  Counterexamples.TernaryL2Rows256Floor31.rows192_floor14_bits128_false

theorem ternaryL2ThresholdRows256Floor13Bits192False :
    ¬ L2ThresholdLowerTailAt
      (Counterexamples.TernaryL2Rows256Floor31.familyParameters 256 13)
      (failureTarget 192) :=
  Counterexamples.TernaryL2Rows256Floor31.rows256_floor13_bits192_false

theorem ternaryL2ThresholdRows384Floor45Bits192False :
    ¬ L2ThresholdLowerTailAt
      (Counterexamples.TernaryL2Rows256Floor31.familyParameters 384 45)
      (failureTarget 192) :=
  Counterexamples.TernaryL2Rows256Floor31.rows384_floor45_bits192_false

theorem ternaryL2ThresholdRows512Floor59Bits256False :
    ¬ L2ThresholdLowerTailAt
      (Counterexamples.TernaryL2Rows256Floor31.familyParameters 512 59)
      (failureTarget 256) :=
  Counterexamples.TernaryL2Rows256Floor31.rows512_floor59_bits256_false

theorem ternaryL2ThresholdRows256Floor29Bits132False :
    ¬ L2ThresholdLowerTailAt
      (Counterexamples.TernaryL2Rows256Floor31.familyParameters 256 29)
      (failureTarget 132) :=
  Counterexamples.TernaryL2Rows256Floor31.rows256_floor29_bits132_false

theorem ternaryL2ThresholdRows256Floor9Bits208False :
    ¬ L2ThresholdLowerTailAt
      (Counterexamples.TernaryL2Rows256Floor31.familyParameters 256 9)
      (failureTarget 208) :=
  Counterexamples.TernaryL2Rows256Floor31.rows256_floor9_bits208_false

theorem ternaryL2ThresholdRows384Floor43Bits197False :
    ¬ L2ThresholdLowerTailAt
      (Counterexamples.TernaryL2Rows256Floor31.familyParameters 384 43)
      (failureTarget 197) :=
  Counterexamples.TernaryL2Rows256Floor31.rows384_floor43_bits197_false

theorem ternaryL2ThresholdRows512Floor57Bits261False :
    ¬ L2ThresholdLowerTailAt
      (Counterexamples.TernaryL2Rows256Floor31.familyParameters 512 57)
      (failureTarget 261) :=
  Counterexamples.TernaryL2Rows256Floor31.rows512_floor57_bits261_false

/-- Coordinate cap `1/2` is false for 256 balanced-ternary rows at a 128-bit
failure budget, for every exact modulus margin. -/
theorem ternaryLInfThresholdRows256CapHalfBits128False
    (margin : NonnegativeRatio) :
    ¬ LInfThresholdLowerTailAt
      (Counterexamples.TernaryLInfRows256CapHalf.parameters margin)
      (failureTarget 128) :=
  Counterexamples.TernaryLInfRows256CapHalf.bits128_false margin

/-- The explicit two-coordinate small-projection event for 256
balanced-ternary rows at coordinate cap `1`. -/
def TernaryLInfRows256CoordinateCap1Pass
    (J : Fin 256 → Fin 2 → ℤ) : Prop :=
  ∀ j, |J j 0 + J j 1| ≤ 1

/-- The 256-row balanced-ternary infinity-norm event at coordinate cap `1`
has probability strictly greater than `2⁻¹²⁸` for the explicit
two-coordinate input. -/
theorem ternaryLInfRows256CoordinateCap1Bits128 :
    eventProbability (sparseRademacherMatrix 256 2)
        TernaryLInfRows256CoordinateCap1Pass >
      failureTarget 128 := by
  rw [eventProbability_congr (sparseRademacherMatrix 256 2)
    (event' := SparseLInfTwoCoordinatePass) (by intro J; rfl)]
  simpa [rowCount, securityBits] using
    Counterexamples.SparseLInfTwoCoordinate.Internal.sparseLInfTwoCoordinateProbability_gt

/-- Integer modulus margin one is impossible for the public-threshold
`21/50` infinity theorem: the explicit modulus-three input passes for every
balanced-ternary matrix. -/
theorem ternaryLInfThresholdMarginOneBits130False :
    ¬ LInfThresholdLowerTailAt
      Counterexamples.TernaryLInfThresholdMarginOne.parameters
      (failureTarget 130) :=
  Counterexamples.TernaryLInfThresholdMarginOne.bits130_false

/-- Integer modulus margin one is impossible at every row count and every
exact rational coordinate cap at least `1/3`, for every target budget at most
one. -/
theorem ternaryLInfThresholdMarginOneFamilyFalse
    (rows : ℕ) (coordinateCap : NonnegativeRatio) (budget : ENNReal)
    (hcap : Counterexamples.TernaryLInfThresholdMarginOne.oneThird.LE
      coordinateCap)
    (hbudget : budget ≤ 1) :
    ¬ LInfThresholdLowerTailAt
      (Counterexamples.TernaryLInfThresholdMarginOne.familyParameters
        rows coordinateCap) budget :=
  Counterexamples.TernaryLInfThresholdMarginOne.lowerTail_false_of_oneThird_le
    hcap hbudget

/-- At 192 rows and coordinate cap `17/50`, the explicit admissible input
`(q,d,b,w) = (7,6,3,(1,1,1,1,1,2))` passes all rows with probability
`(529/1024)^192 > 2^-183`.  Consequently the uniform 183-bit lower-tail
statement is false. -/
theorem ternaryLInfThresholdRows192Cap34Bits183False :
    ¬ LInfThresholdLowerTailAt
      Counterexamples.TernaryLInfRows192Cap34.parameters
      (failureTarget 183) :=
  Counterexamples.TernaryLInfRows192Cap34.bits183_false

/-- At 192 rows and threshold-relative energy floor `12`, the admissible
input `(q,d,b,w) = (301,2,100,(100,1))` fails with probability greater than
`2^-132`. Consequently the uniform 132-bit theorem is false. -/
theorem ternaryL2ThresholdRows192Floor12Bits132False :
    ¬ L2ThresholdLowerTailAt
      Counterexamples.ThresholdLowerRows192Floor12.parameters
      (failureTarget 132) :=
  Counterexamples.ThresholdLowerRows192Floor12.bits132_false

/-- The maintained 192-row threshold `287` cannot satisfy a uniform 130-bit
balanced-ternary L2 upper-tail bound.  The witness is finite and explicit:
`d = 10¹⁶`, `q = 2d+1`, and every coefficient is one. -/
theorem ternaryL2UpperRows192Threshold287Bits130False :
    ¬ L2UpperTailAt
      { distribution := .balancedTernary
        rows := 192
        threshold := NonnegativeRatio.ofNat 287 }
      (failureTarget 130) := by
  have hwitness :=
    ternaryL2UpperRows192Threshold287Bits130Counterexample
  dsimp only [Rows192L2Upper287Bits130CounterexampleStatement] at hwitness
  exact Counterexamples.SparseUpper.FlatWitness.not_l2UpperTailAt_of_probability_gt
    rows192L2UpperCounterexampleModulus
    rows192L2UpperCounterexampleVector hwitness.2.2

/-- The explicit `d = 10^16`, `q = 2d+1` all-ones witness rules out a
uniform 192-bit upper-tail bound at 256 rows and threshold `404`. -/
theorem ternaryL2UpperRows256Threshold404Bits192False :
    ¬ L2UpperTailAt
      { distribution := .balancedTernary
        rows := 256
        threshold := NonnegativeRatio.ofNat 404 }
      (failureTarget 192) := by
  have hwitness := ternaryL2UpperRows256Threshold404Bits192Counterexample
  dsimp only [Rows256L2Upper404Bits192CounterexampleStatement] at hwitness
  exact Counterexamples.SparseUpper.FlatWitness.not_l2UpperTailAt_of_probability_gt
    highSecurityL2UpperCounterexampleModulus
    highSecurityL2UpperCounterexampleVector hwitness.2.2

/-- The explicit flat witness rules out a uniform 192-bit upper-tail bound at
384 rows and threshold `507`. -/
theorem ternaryL2UpperRows384Threshold507Bits192False :
    ¬ L2UpperTailAt
      { distribution := .balancedTernary
        rows := 384
        threshold := NonnegativeRatio.ofNat 507 }
      (failureTarget 192) := by
  have hwitness := ternaryL2UpperRows384Threshold507Bits192Counterexample
  dsimp only [Rows384L2Upper507Bits192CounterexampleStatement] at hwitness
  exact Counterexamples.SparseUpper.FlatWitness.not_l2UpperTailAt_of_probability_gt
    highSecurityL2UpperCounterexampleModulus
    highSecurityL2UpperCounterexampleVector hwitness.2.2

/-- The shared 512-row flat witness rules out threshold `605` at 192 bits. -/
theorem ternaryL2UpperRows512Threshold605Bits192False :
    ¬ L2UpperTailAt
      { distribution := .balancedTernary
        rows := 512
        threshold := NonnegativeRatio.ofNat 605 }
      (failureTarget 192) := by
  have hwitness := ternaryL2UpperRows512Threshold605Bits192Counterexample
  dsimp only [Rows512L2Upper605Bits192CounterexampleStatement] at hwitness
  exact Counterexamples.SparseUpper.FlatWitness.not_l2UpperTailAt_of_probability_gt
    highSecurityL2UpperCounterexampleModulus
    highSecurityL2UpperCounterexampleVector hwitness.2.2

/-- The same 512-row flat witness rules out threshold `678` at 256 bits. -/
theorem ternaryL2UpperRows512Threshold678Bits256False :
    ¬ L2UpperTailAt
      { distribution := .balancedTernary
        rows := 512
        threshold := NonnegativeRatio.ofNat 678 }
      (failureTarget 256) := by
  have hwitness := ternaryL2UpperRows512Threshold678Bits256Counterexample
  dsimp only [Rows512L2Upper678Bits256CounterexampleStatement] at hwitness
  exact Counterexamples.SparseUpper.FlatWitness.not_l2UpperTailAt_of_probability_gt
    highSecurityL2UpperCounterexampleModulus
    highSecurityL2UpperCounterexampleVector hwitness.2.2

/-- The maintained 192-row threshold `487/50` cannot satisfy a uniform
134-bit balanced-ternary infinity-upper bound.  The witness is finite and
explicit: `d = 500²`, `q = 2d+1`, and every coefficient is one. -/
theorem ternaryLInfUpperRows192Threshold487Over50Bits134False :
    ¬ LInfUpperTailAt
      { distribution := .balancedTernary
        rows := 192
        coordinateThreshold :=
          { numerator := 487, denominator := 50, denominator_pos := by decide } }
      (failureTarget 134) := by
  simpa [Counterexamples.TernaryLInfUpperRows192.parameters] using
    Counterexamples.TernaryLInfUpperRows192.ternaryUpper487Over50Rows192Bits134_false

/-- The dense-sign matrix law fails the public-threshold lower event at the
admissible threshold `667` for every seed, not merely with nonzero
probability. The squared norm appears only in the threshold-admissibility
hypothesis. -/
theorem denseSignThreshold29FailsForEverySeed (seed : SignSeed 256 2) :
    CenteredInput 2001 Counterexamples.DenseSignThreshold.witness ∧
      0 < 667 ∧
      InputThresholdAtMostNorm 667
        Counterexamples.DenseSignThreshold.witness ∧
      InputThresholdWithinModulus (NonnegativeRatio.ofNat 3) 2001 667 ∧
      L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29) 667 2001
        Counterexamples.DenseSignThreshold.witness (signMatrix seed) := by
  refine ⟨?_, by norm_num, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      norm_num [Counterexamples.DenseSignThreshold.witness, centeredInterval]
  · norm_num [InputThresholdAtMostNorm,
      Counterexamples.DenseSignThreshold.witness_sqNorm]
  · norm_num [InputThresholdWithinModulus, NonnegativeRatio.ofNat]
  · simp only [L2ThresholdLowerFailure, NonnegativeRatio.ofNat, one_mul]
    exact (Counterexamples.DenseSignThreshold.modularProjectionSqNorm_witness_le_rows
      256 seed).trans_lt (by norm_num)

end CertifiedJL.Obstructions
