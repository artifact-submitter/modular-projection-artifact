/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Obstructions.Lightweight
import CertifiedJL.Projection.Counterexamples.L2Upper.FlatWitnessGeometry

/-!
# Lightweight obstruction regression tests

These canaries pin the public obstruction theorem types and concrete witness
parameters that do not require generated certificate replay.  The separate
`ObstructionCanaries` module extends this root with the threshold-76 checks.
-/

namespace CertifiedJL
namespace Tests
namespace ObstructionCanariesFast

open scoped BigOperators ENNReal

open MeasureTheory Probability

example : counterexampleModulus = 2 ^ 32 - 99 := rfl
example : counterexampleSide = 46_340 := rfl
example : counterexampleDimension = 46_340 ^ 2 := rfl

example :
    Fintype.card
        {f : Fin 3 → Bool // (boolSupport f).card = 1} = 3 := by
  simpa using card_bool_true_count (Fin 3) 1

example {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    -(u + u ^ 2 / 2 + u ^ 3 / (1 - u)) ≤
      Real.log (1 - u) :=
  neg_add_sq_add_log_one_sub_le hu0 hu1

example (d : ℕ) :
    centeredBinomialMassAt d 0 = centralBinomialMass d :=
  centeredBinomialMassAt_zero d

example {d k : ℕ} (hk : k < d) :
    centeredBinomialMassAt d (k + 1) =
      centeredBinomialMassAt d k *
        ((d - k : ℕ) : ℝ) / (d + k + 1) :=
  centeredBinomialMassAt_succ hk

example : gammaSurvivalNat 1 0 = 1 := by
  simp [gammaSurvivalNat]

example :
    gammaSurvivalNat 128 336 >
      (3 / 2 : ℝ) * (2 : ℝ)⁻¹ ^ 128 :=
  gammaSurvivalNat_128_336_gt

example :
    gammaSurvivalNat 128 338 >
      (17 / 10 : ℝ) * (2 : ℝ)⁻¹ ^ 130 :=
  gammaSurvivalNat_128_338_gt

example {a : ℝ} (ha : 0 ≤ a) :
    (∫ x : Fin 256 → ℝ in
        {x | a < ∑ i, (x i) ^ 2}, halfGaussianProductDensity x) =
      gammaSurvivalNat 128 a :=
  integral_halfGaussianProductDensity_tail ha

example : SparseUpper336CounterexampleStatement :=
  ternaryUpper336Counterexample

example : SparseUpper338Bits130CounterexampleStatement :=
  ternaryUpper338Bits130Counterexample

example : highSecurityL2UpperCounterexampleDimension = 10 ^ 16 := by
  norm_num [highSecurityL2UpperCounterexampleDimension,
    highSecurityL2UpperCounterexampleSide]

example : highSecurityL2UpperCounterexampleModulus = 2 * 10 ^ 16 + 1 := by
  norm_num [highSecurityL2UpperCounterexampleModulus,
    highSecurityL2UpperCounterexampleDimension,
    highSecurityL2UpperCounterexampleSide]

/-- The generic flat-witness geometry includes the smallest nonempty case:
dimension one with centered modulus three. -/
example (seed : SparseSeed 1 1) (j : Fin 1) :
    centeredMod 3
        (Probability.SparseAllOnes.sparseAllOnesRowSum (seed j)) =
      Probability.SparseAllOnes.sparseAllOnesRowSum (seed j) := by
  simpa using
    (Counterexamples.SparseUpper.FlatWitness.centeredMod_rowSum seed j)

/-- Equality at the threshold is excluded: the upper event remains strict. -/
example (threshold : ℕ) (seed : SparseSeed 1 1)
    (heq :
      Counterexamples.SparseUpper.FlatWitness.rowSqNorm
          (fun j => Probability.SparseAllOnes.sparseAllOnesRowSum (seed j)) =
        threshold) :
    ¬ modularProjectionSqNorm 3 (sparseMatrix seed)
          (Counterexamples.SparseUpper.FlatWitness.vector 1) >
        threshold * sqNorm
          (Counterexamples.SparseUpper.FlatWitness.vector 1) := by
  have hgeom :=
    Counterexamples.SparseUpper.FlatWitness.modularProjectionSqNorm_sparseMatrix_vector
      seed
  norm_num at hgeom
  rw [hgeom, Counterexamples.SparseUpper.FlatWitness.sqNorm_vector, heq]
  omega

/- The generic radial law must carry the row count and Gamma shape together
at each concrete even dimension used by the obstruction family. -/
example {a : ℝ} (ha : 0 ≤ a) :
    (∫ x : Fin 192 → ℝ in {x | a < ∑ i, (x i) ^ 2},
        HalfGaussianEven.halfGaussianProductDensity x) =
      gammaSurvivalNat 96 a :=
  HalfGaussianEven.integral_halfGaussianProductDensity_tail
    (rows := 192) (shape := 96) (by norm_num) (by norm_num) ha

example {a : ℝ} (ha : 0 ≤ a) :
    (∫ x : Fin 256 → ℝ in {x | a < ∑ i, (x i) ^ 2},
        HalfGaussianEven.halfGaussianProductDensity x) =
      gammaSurvivalNat 128 a :=
  HalfGaussianEven.integral_halfGaussianProductDensity_tail
    (rows := 256) (shape := 128) (by norm_num) (by norm_num) ha

example {a : ℝ} (ha : 0 ≤ a) :
    (∫ x : Fin 384 → ℝ in {x | a < ∑ i, (x i) ^ 2},
        HalfGaussianEven.halfGaussianProductDensity x) =
      gammaSurvivalNat 192 a :=
  HalfGaussianEven.integral_halfGaussianProductDensity_tail
    (rows := 384) (shape := 192) (by norm_num) (by norm_num) ha

example {a : ℝ} (ha : 0 ≤ a) :
    (∫ x : Fin 512 → ℝ in {x | a < ∑ i, (x i) ^ 2},
        HalfGaussianEven.halfGaussianProductDensity x) =
      gammaSurvivalNat 256 a :=
  HalfGaussianEven.integral_halfGaussianProductDensity_tail
    (rows := 512) (shape := 256) (by norm_num) (by norm_num) ha

example : GammaRows256Threshold404Bits192Certificate :=
  gammaRows256Threshold404Bits192_verified

example : GammaRows384Threshold507Bits192Certificate :=
  gammaRows384Threshold507Bits192_verified

example : GammaRows512Threshold605Bits192Certificate :=
  gammaRows512Threshold605Bits192_verified

example : GammaRows512Threshold678Bits256Certificate :=
  gammaRows512Threshold678Bits256_verified

example : Rows192L2Upper287Bits130CounterexampleStatement :=
  ternaryL2UpperRows192Threshold287Bits130Counterexample

example : Rows256L2Upper404Bits192CounterexampleStatement :=
  ternaryL2UpperRows256Threshold404Bits192Counterexample

example : Rows384L2Upper507Bits192CounterexampleStatement :=
  ternaryL2UpperRows384Threshold507Bits192Counterexample

example : Rows512L2Upper605Bits192CounterexampleStatement :=
  ternaryL2UpperRows512Threshold605Bits192Counterexample

example : Rows512L2Upper678Bits256CounterexampleStatement :=
  ternaryL2UpperRows512Threshold678Bits256Counterexample

example :
    ¬ L2UpperTailAt
      { distribution := .balancedTernary, rows := 192,
        threshold := NonnegativeRatio.ofNat 287 }
      (failureTarget 130) :=
  Obstructions.ternaryL2UpperRows192Threshold287Bits130False

example :
    ¬ L2UpperTailAt
      { distribution := .balancedTernary, rows := 256,
        threshold := NonnegativeRatio.ofNat 404 }
      (failureTarget 192) :=
  Obstructions.ternaryL2UpperRows256Threshold404Bits192False

example :
    ¬ L2UpperTailAt
      { distribution := .balancedTernary, rows := 384,
        threshold := NonnegativeRatio.ofNat 507 }
      (failureTarget 192) :=
  Obstructions.ternaryL2UpperRows384Threshold507Bits192False

example :
    ¬ L2UpperTailAt
      { distribution := .balancedTernary, rows := 512,
        threshold := NonnegativeRatio.ofNat 605 }
      (failureTarget 192) :=
  Obstructions.ternaryL2UpperRows512Threshold605Bits192False

example :
    ¬ L2UpperTailAt
      { distribution := .balancedTernary, rows := 512,
        threshold := NonnegativeRatio.ofNat 678 }
      (failureTarget 256) :=
  Obstructions.ternaryL2UpperRows512Threshold678Bits256False

/-- The concrete upper obstruction records that its witness modulus is odd. -/
example : Odd counterexampleModulus :=
  ternaryUpper336Counterexample.1

/-- The concrete upper obstruction records that its witness vector is nonzero. -/
example : sparseUpperCounterexampleVector ≠ 0 :=
  ternaryUpper336Counterexample.2.1

example (m : ℕ) (seed : SignSeed m 2) :
    modularProjectionSqNorm 2001 (signMatrix seed)
        Counterexamples.DenseSignThreshold.witness ≤ m :=
  Counterexamples.DenseSignThreshold.modularProjectionSqNorm_witness_le_rows m seed

-- This canary covers the concrete q=2001, b=667 witness. The paper's
-- general construction separately chooses min(a, floor((2*a+1)/M)) to
-- preserve the input norm condition even for small positive margins.
example (seed : SignSeed 256 2) :
    L2ThresholdLowerFailure (NonnegativeRatio.ofNat 29) 667 2001
      Counterexamples.DenseSignThreshold.witness (signMatrix seed) :=
  (Obstructions.denseSignThreshold29FailsForEverySeed seed).2.2.2.2

example :
    ¬ L2ThresholdLowerTailAt
      Counterexamples.TernaryL2Rows256Floor30.parametersMarginThree
      (failureTarget 128) :=
  Obstructions.ternaryL2ThresholdRows256Floor30Bits128False

example :
    ¬ L2ThresholdLowerTailAt
      Counterexamples.TernaryL2Rows256Floor30.parametersMargin125
      (failureTarget 128) :=
  Obstructions.ternaryL2ThresholdRows256Floor30Margin125Bits128False

example :
    ¬ L2ThresholdLowerTailAt
      Counterexamples.TernaryL2Rows256MarginTwo.parametersTwo
      (failureTarget 128) :=
  Obstructions.ternaryL2ThresholdRows256Floor29MarginTwoBits128False

example (margin : NonnegativeRatio)
    (hmargin : margin.LE Counterexamples.TernaryL2Rows256MarginTwo.nineFourths) :
    ¬ L2ThresholdLowerTailAt
      (Counterexamples.TernaryL2Rows256MarginTwo.parameters margin)
      (failureTarget 128) :=
  Obstructions.ternaryL2ThresholdRows256Floor29MarginAtMostNineFourthsBits128False
    margin hmargin

example :
    Odd Counterexamples.TernaryL2Rows256Floor30.modulus ∧
      CenteredInput Counterexamples.TernaryL2Rows256Floor30.modulus
        Counterexamples.TernaryL2Rows256Floor30.witness ∧
      0 < Counterexamples.TernaryL2Rows256Floor30.inputThreshold ∧
      InputThresholdAtMostNorm
        Counterexamples.TernaryL2Rows256Floor30.inputThreshold
        Counterexamples.TernaryL2Rows256Floor30.witness ∧
      InputThresholdWithinModulus (NonnegativeRatio.ofNat 3)
        Counterexamples.TernaryL2Rows256Floor30.modulus
        Counterexamples.TernaryL2Rows256Floor30.inputThreshold ∧
      InputThresholdWithinModulus (NonnegativeRatio.ofNat 125)
        Counterexamples.TernaryL2Rows256Floor30.modulus
        Counterexamples.TernaryL2Rows256Floor30.inputThreshold ∧
      eventProbability (sparseRademacherMatrix 256 2)
          (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 30)
            Counterexamples.TernaryL2Rows256Floor30.inputThreshold
            Counterexamples.TernaryL2Rows256Floor30.modulus
            Counterexamples.TernaryL2Rows256Floor30.witness) > failureTarget 127 :=
  Counterexamples.TernaryL2Rows256Floor30.admissible_witness

example :
    ¬ L2ThresholdLowerTailAt
      Counterexamples.TernaryL2Rows256Floor31.parameters
      (failureTarget 128) :=
  Obstructions.ternaryL2ThresholdRows256Floor31Bits128False

example :
    ¬ L2ThresholdLowerTailAt
      (Counterexamples.TernaryL2Rows256Floor31.familyParameters 192 14)
      (failureTarget 128) :=
  Obstructions.ternaryL2ThresholdRows192Floor14Bits128False

example :
    ¬ L2ThresholdLowerTailAt
      (Counterexamples.TernaryL2Rows256Floor31.familyParameters 256 13)
      (failureTarget 192) :=
  Obstructions.ternaryL2ThresholdRows256Floor13Bits192False

example :
    ¬ L2ThresholdLowerTailAt
      (Counterexamples.TernaryL2Rows256Floor31.familyParameters 384 45)
      (failureTarget 192) :=
  Obstructions.ternaryL2ThresholdRows384Floor45Bits192False

example :
    ¬ L2ThresholdLowerTailAt
      (Counterexamples.TernaryL2Rows256Floor31.familyParameters 512 59)
      (failureTarget 256) :=
  Obstructions.ternaryL2ThresholdRows512Floor59Bits256False

example :
    ¬ L2ThresholdLowerTailAt
      (Counterexamples.TernaryL2Rows256Floor31.familyParameters 256 29)
      (failureTarget 132) :=
  Obstructions.ternaryL2ThresholdRows256Floor29Bits132False

example :
    ¬ L2ThresholdLowerTailAt
      (Counterexamples.TernaryL2Rows256Floor31.familyParameters 256 9)
      (failureTarget 208) :=
  Obstructions.ternaryL2ThresholdRows256Floor9Bits208False

example :
    ¬ L2ThresholdLowerTailAt
      (Counterexamples.TernaryL2Rows256Floor31.familyParameters 384 43)
      (failureTarget 197) :=
  Obstructions.ternaryL2ThresholdRows384Floor43Bits197False

example :
    ¬ L2ThresholdLowerTailAt
      (Counterexamples.TernaryL2Rows256Floor31.familyParameters 512 57)
      (failureTarget 261) :=
  Obstructions.ternaryL2ThresholdRows512Floor57Bits261False

example : Counterexamples.TernaryL2Rows256Floor31.parameters.rows = 256 := rfl

example :
    Counterexamples.TernaryL2Rows256Floor31.parameters.squaredNormFloor =
      NonnegativeRatio.ofNat 31 := rfl

example :
    Counterexamples.TernaryL2Rows256Floor31.parameters.modulusMargin =
      NonnegativeRatio.ofNat 3 := rfl

example {b q : ℕ} (hb : 0 < b) (hq : Odd q) (hmargin : 3 * b ≤ q) :
    CenteredInput q (Counterexamples.TernaryL2Rows256Floor31.witness b) ∧
      InputThresholdAtMostNorm b
        (Counterexamples.TernaryL2Rows256Floor31.witness b) ∧
      InputThresholdWithinModulus (NonnegativeRatio.ofNat 3) q b ∧
      eventProbability (sparseRademacherMatrix 256 1)
          (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 31) b q
            (Counterexamples.TernaryL2Rows256Floor31.witness b)) =
        ((∑ k ∈ Finset.range 31, (256 : ℕ).choose k : ℕ) : ℝ≥0∞) *
          ((2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ ∧
      eventProbability (sparseRademacherMatrix 256 1)
          (L2ThresholdLowerFailure (NonnegativeRatio.ofNat 31) b q
            (Counterexamples.TernaryL2Rows256Floor31.witness b)) >
        failureTarget 128 :=
  Counterexamples.TernaryL2Rows256Floor31.admissible_family hb hq hmargin

example (margin : NonnegativeRatio) :
    ¬ LInfThresholdLowerTailAt
      (Counterexamples.TernaryLInfRows256CapHalf.parameters margin)
      (failureTarget 128) :=
  Obstructions.ternaryLInfThresholdRows256CapHalfBits128False margin

example (margin : NonnegativeRatio) :
    (Counterexamples.TernaryLInfRows256CapHalf.parameters margin).rows = 256 := rfl

example (margin : NonnegativeRatio) :
    (Counterexamples.TernaryLInfRows256CapHalf.parameters margin).coordinateCap =
      { numerator := 1, denominator := 2, denominator_pos := by decide } := rfl

example (margin : NonnegativeRatio) :
    (Counterexamples.TernaryLInfRows256CapHalf.parameters margin).modulusMargin =
      margin := rfl

example (M : ℝ) (hM : 0 < M) :
    ∃ q : ℕ,
      Odd q ∧
      8 * 1 < q ∧
      M * (2 : ℝ) ≤ q ∧
      CenteredInput q (Counterexamples.TernaryLInfRows256CapHalf.witness 1) ∧
      InputThresholdAtMostNorm 2
        (Counterexamples.TernaryLInfRows256CapHalf.witness 1) ∧
      eventProbability (sparseRademacherMatrix 256 4)
          (LInfThresholdSmallProjection
            (Counterexamples.TernaryLInfRows256CapHalf.parameters
              (NonnegativeRatio.ofNat 1))
            2 q (Counterexamples.TernaryLInfRows256CapHalf.witness 1)) =
        ((182 : ℝ≥0∞) * (256 : ℝ≥0∞)⁻¹) ^ 256 ∧
      eventProbability (sparseRademacherMatrix 256 4)
          (LInfThresholdSmallProjection
            (Counterexamples.TernaryLInfRows256CapHalf.parameters
              (NonnegativeRatio.ofNat 1))
            2 q (Counterexamples.TernaryLInfRows256CapHalf.witness 1)) >
        failureTarget 128 :=
  Counterexamples.TernaryLInfRows256CapHalf.realMargin_admissible_family M hM

example (m : ℕ) (M c : ℝ) (hM : 0 < M) (hc : 0 < c) :
    ∃ a b : ℕ,
      0 < a ∧
      0 < b ∧
      Odd (2 * a + 1) ∧
      CenteredInput (2 * a + 1)
        (Counterexamples.DenseSignThreshold.scaledWitness a) ∧
      InputThresholdAtMostNorm b
        (Counterexamples.DenseSignThreshold.scaledWitness a) ∧
      M * (b : ℝ) ≤ (2 * a + 1 : ℕ) ∧
      (m : ℝ) < c * (b : ℝ) ^ 2 ∧
      ∀ seed : SignSeed m 2,
        modularProjectionSqNorm (2 * a + 1) (signMatrix seed)
            (Counterexamples.DenseSignThreshold.scaledWitness a) ≤ m ∧
          (modularProjectionSqNorm (2 * a + 1) (signMatrix seed)
              (Counterexamples.DenseSignThreshold.scaledWitness a) : ℝ) <
            c * (b : ℝ) ^ 2 :=
  Counterexamples.DenseSignThreshold.universal_real_threshold_failure m M c hM hc

/-- At the fixed cap 21/50, the integer-margin-one obstruction is deterministic:
its failure event has probability exactly one. This does not quantify over
other positive caps or real modulus margins. -/
example :
    eventProbability
        (Counterexamples.TernaryLInfThresholdMarginOne.parameters.distribution.matrixPMF
          Counterexamples.TernaryLInfThresholdMarginOne.parameters.rows 9)
        (LInfThresholdSmallProjection
          Counterexamples.TernaryLInfThresholdMarginOne.parameters 3 3
          Counterexamples.TernaryLInfThresholdMarginOne.witness) = 1 :=
  Counterexamples.TernaryLInfThresholdMarginOne.probability_eq_one

/-- The generalized public obstruction quantifies over row counts, rational
caps, and budgets while preserving the closed-event endpoint. -/
example (rows : ℕ) (coordinateCap : NonnegativeRatio) (budget : ENNReal)
    (hcap : Counterexamples.TernaryLInfThresholdMarginOne.oneThird.LE
      coordinateCap)
    (hbudget : budget ≤ 1) :
    ¬ LInfThresholdLowerTailAt
      (Counterexamples.TernaryLInfThresholdMarginOne.familyParameters
        rows coordinateCap) budget :=
  Obstructions.ternaryLInfThresholdMarginOneFamilyFalse
    rows coordinateCap budget hcap hbudget

#print axioms ternaryUpper336Counterexample
#print axioms ternaryUpper338Bits130Counterexample
#print axioms ternaryL2UpperRows192Threshold287Bits130Counterexample
#print axioms ternaryL2UpperRows256Threshold404Bits192Counterexample
#print axioms ternaryL2UpperRows384Threshold507Bits192Counterexample
#print axioms ternaryL2UpperRows512Threshold605Bits192Counterexample
#print axioms ternaryL2UpperRows512Threshold678Bits256Counterexample
#print axioms Obstructions.ternaryL2UpperRows192Threshold287Bits130False
#print axioms Obstructions.ternaryL2UpperRows256Threshold404Bits192False
#print axioms Obstructions.ternaryL2UpperRows384Threshold507Bits192False
#print axioms Obstructions.ternaryL2UpperRows512Threshold605Bits192False
#print axioms Obstructions.ternaryL2UpperRows512Threshold678Bits256False
#print axioms Counterexamples.DenseSignThreshold.modularProjectionSqNorm_witness_le_rows
#print axioms Obstructions.denseSignThreshold29FailsForEverySeed
#print axioms Obstructions.ternaryL2ThresholdRows256Floor30Bits128False
#print axioms Obstructions.ternaryL2ThresholdRows256Floor30Margin125Bits128False
#print axioms Obstructions.ternaryL2ThresholdRows256Floor29MarginAtMostNineFourthsBits128False
#print axioms Obstructions.ternaryL2ThresholdRows256Floor29MarginTwoBits128False
#print axioms Counterexamples.TernaryL2Rows256MarginTwo.admissible_family
#print axioms Counterexamples.TernaryL2Rows256Floor30.admissible_witness
#print axioms Obstructions.ternaryL2ThresholdRows256Floor31Bits128False
#print axioms Obstructions.ternaryL2SingletonThresholdFalseOfScaled
#print axioms Obstructions.ternaryL2ThresholdRows192Floor14Bits128False
#print axioms Obstructions.ternaryL2ThresholdRows256Floor13Bits192False
#print axioms Obstructions.ternaryL2ThresholdRows384Floor45Bits192False
#print axioms Obstructions.ternaryL2ThresholdRows512Floor59Bits256False
#print axioms Obstructions.ternaryL2ThresholdRows256Floor29Bits132False
#print axioms Obstructions.ternaryL2ThresholdRows256Floor9Bits208False
#print axioms Obstructions.ternaryL2ThresholdRows384Floor43Bits197False
#print axioms Obstructions.ternaryL2ThresholdRows512Floor57Bits261False
#print axioms Obstructions.ternaryLInfThresholdRows256CapHalfBits128False
#print axioms Counterexamples.TernaryLInfRows256CapHalf.realMargin_admissible_family
#print axioms Counterexamples.DenseSignThreshold.universal_real_threshold_failure
#print axioms Counterexamples.TernaryLInfThresholdMarginOne.probability_eq_one
#print axioms Obstructions.ternaryLInfThresholdMarginOneBits130False
#print axioms Obstructions.ternaryLInfThresholdMarginOneFamilyFalse
#print axioms Probability.HalfGaussianEven.integral_halfGaussianProductDensity_tail
#print axioms Counterexamples.SparseUpper.EvenGaussian.Internal.tensorComparison
#print axioms Counterexamples.SparseUpper.FlatWitness.eventProbability_eq
#print axioms
  Counterexamples.SparseUpper.EvenRadialEndpoint.integral_gaussianCore_eq_gamma_sub_truncation
#print axioms Counterexamples.SparseUpper.EvenEndpoint.tensorLowerBound_gt

end ObstructionCanariesFast
end Tests
end CertifiedJL
