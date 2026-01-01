/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL

/-!
# Public theorem API regression checks

These declarations pin the production umbrella's canonical result names and
their exact law/row/threshold/cap/budget specializations.
-/

namespace CertifiedJL.Tests.PublicAPI

-- Foundational names needed to read the public statement schemas.
#check ProjectionDistribution.rowPMF
#check ProjectionDistribution.matrixPMF
#check eventProbability
#check failureTarget
#check sparseRademacherRow
#check sparseRademacherMatrix
#check centeredMod
#check sqNorm
#check rowDot
#check projectionSqNorm
#check modularProjectionSqNorm
#check shiftedModularProjectionSqNorm
#check L2ThresholdLowerFailure
#check L2UpperFailure

#check CertifiedJL.Results.Affine.L2.Lower.General.ternaryAffineL2LowerTail_toReal_le_finiteTilt
#check CertifiedJL.Results.Affine.L2.Lower.General.ternaryAffineL2LowerTail_toReal_le_general
#check CertifiedJL.Results.Affine.L2.Lower.General.ternaryAffineL2LowerTail_toReal_le_general_of_ratio
#check CertifiedJL.Results.Affine.L2.Lower.General.ternaryAffineL2ThresholdLowerTailAt_of_generalBound_lt_failureTarget
#check CertifiedJL.Results.Affine.L2.Lower.General.ternaryAffineL2ThresholdLowerTailAt_of_finiteTilt_lt_failureTarget

#check Results.Affine.LInf.Lower.Direct.ternaryAffineLInfThresholdLower256Cap67Over200Bits130
#check Results.Affine.LInf.Lower.Direct.ternaryAffineLInfThresholdLower256Cap6Over25Bits197
#check Results.Affine.LInf.Lower.Direct.ternaryAffineLInfThresholdLower_probability_le

#check Results.L2.Lower.Rows256Bits128.ternaryL2ThresholdLower29
#check Results.L2.Upper.Rows256Bits128.ternaryL2Upper338
#check L2UpperTailAt.mono_parameters
#check Results.L2.Upper.Rows256Frontier.certifiedEndpoint
#check Results.L2.Upper.Rows256Frontier.ofCertifiedEndpoint
#check Results.L2.Upper.Rows256Frontier.ofCertifiedEndpointAtBits
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper5623Over16Bits140
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper5641Over16Bits141
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper5659Over16Bits142
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper5677Over16Bits143
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper2847Over8Bits144
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper357Bits145
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper2865Over8Bits146
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper1437Over4Bits147
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper5765Over16Bits148
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper5783Over16Bits149
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper5801Over16Bits150
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper2909Over8Bits151
#check Results.L2.Upper.Rows256Frontier.ternaryL2Upper1459Over4Bits152
#check Results.L2.Lower.Rows192Bits128.ternaryL2ThresholdLower12
#check Results.L2.Upper.Rows192Bits128.ternaryL2Upper287
#check Results.LInf.Lower.Rows192Bits128.ternaryLInfThresholdLower17Over50
#check Results.LInf.Upper.Rows192Bits128.ternaryLInfUpper487Over50
#check Results.Composites.Rows192Bits128.allBounds
#check Results.LInf.Lower.TwoDecimal.rowPass21Over50_lt_13939Over20000
#check Results.LInf.Lower.TwoDecimal.lower6Over25Rows256Bits197
#check Results.LInf.Lower.TwoDecimal.lower21Over50Rows256Bits133
#check Results.LInf.Lower.TwoDecimal.lower21Over50Rows384Bits200
#check Results.LInf.Lower.TwoDecimal.lower21Over50Rows512Bits266
#check Results.LInf.Lower.TwoDecimal.lower47Over100Rows512Bits206
#check AffineRatioEndpointNumeric.endpointCheck
#check CertificateAssembly.affineL2RatioEndpoint
#check Results.L2.Lower.Rows256Bits152.frontier
#check Results.L2.Lower.Rows256Bits152.frontier_all_checked
#check Results.L2.Lower.Rows256Bits152.ternaryL2ThresholdLower79Over4Bits152
#check Results.L2.Lower.Rows256Bits152.ternaryL2ThresholdLower20Bits151
#check Results.L2.Lower.Rows256Bits152.ternaryL2ThresholdLower41Over2Bits150
#check Results.L2.Lower.Rows256Bits152.ternaryL2ThresholdLower83Over4Bits149
#check Results.L2.Lower.Rows256Bits152.ternaryL2ThresholdLower21Bits148
#check Results.L2.Lower.Rows256Bits152.ternaryL2ThresholdLower85Over4Bits147
#check Results.L2.Lower.Rows256Bits152.ternaryL2ThresholdLower43Over2Bits146
#check Results.L2.Lower.Rows256Bits152.ternaryL2ThresholdLower87Over4Bits145
#check Results.L2.Lower.Rows256Bits152.ternaryL2ThresholdLower22Bits144
#check Results.L2.Lower.Rows256Bits192.ternaryL2ThresholdLower9
#check Results.L2.Lower.Rows384Bits192.ternaryL2ThresholdLower43
#check Results.L2.Upper.Rows512Bits192.ternaryL2Upper607
#check Results.L2.Upper.Rows256Bits192.ternaryL2Upper406
#check Results.L2.Upper.Rows384Bits192.ternaryL2Upper509
#check Results.L2.Upper.Rows512Bits256.ternaryL2Upper681
#check Results.L2.Lower.Rows512Bits192.ternaryL2ThresholdLower71
#check Results.L2.Lower.Rows512Bits193.ternaryL2ThresholdLower73
#check Results.L2.Lower.Rows512Bits192.ternaryL2ThresholdLower73
#check Results.L2.Lower.Rows512Bits256.ternaryL2ThresholdLower57
#check thresholdLower512Bits192Floor76Witness
#check thresholdLower512Bits192Floor76Counterexample
#check Results.L2.Lower.HighSecurity.allLowerBounds
#check Results.L2.Lower.HighSecurity.allLowerBoundsIncluding256
#check Results.L2.Lower.HighSecurity.allLowerBoundsIncludingFloor73
#check Results.Composites.L2Rows256Bits128.allL2Bounds
#check Results.LInf.Upper.Rows256.ternaryLInfUpper39Over4Bits133
#check Results.LInf.Upper.Rows256.ternaryLInfUpper39Over4
#check Results.LInf.Upper.Rows256Bits192.ternaryLInfUpper1181Over100
#check Results.LInf.Upper.Rows384Bits192.ternaryLInfUpper1183Over100
#check Results.LInf.Upper.Rows512Bits192.ternaryLInfUpper1184Over100
#check Results.LInf.Upper.Rows512Bits256.ternaryLInfUpper1358Over100
#check Results.LInf.Lower.HighSecurity.allThresholdLowerBounds
#check Results.LInf.Upper.HighSecurity.allUpperBounds
#check Obstructions.ternaryLInfRows256CoordinateCap1Bits128
#check Obstructions.ternaryLInfThresholdMarginOneBits130False
#check Obstructions.ternaryLInfThresholdMarginOneFamilyFalse
#check Obstructions.ternaryLInfThresholdRows192Cap34Bits183False
#check Obstructions.ternaryL2ThresholdRows256Floor30Bits128False
#check Obstructions.ternaryL2ThresholdRows256Floor30Margin125Bits128False
#check Obstructions.ternaryL2ThresholdRows256Floor29MarginAtMostNineFourthsBits128False
#check Obstructions.ternaryL2ThresholdRows256Floor29MarginTwoBits128False
#check Counterexamples.TernaryL2Rows256MarginTwo.admissible_family
#check Counterexamples.TernaryL2Rows256Floor30.admissible_witness
#check Obstructions.ternaryL2ThresholdRows256Floor31Bits128False
#check Counterexamples.TernaryL2Rows256Floor31.admissible_family
#check Obstructions.ternaryL2SingletonThresholdFalseOfScaled
#check Obstructions.ternaryL2ThresholdRows192Floor14Bits128False
#check Obstructions.ternaryL2ThresholdRows256Floor13Bits192False
#check Obstructions.ternaryL2ThresholdRows384Floor45Bits192False
#check Obstructions.ternaryL2ThresholdRows512Floor59Bits256False
#check Obstructions.ternaryL2ThresholdRows256Floor29Bits132False
#check Obstructions.ternaryL2ThresholdRows256Floor9Bits208False
#check Obstructions.ternaryL2ThresholdRows384Floor43Bits197False
#check Obstructions.ternaryL2ThresholdRows512Floor57Bits261False
#check Obstructions.ternaryLInfThresholdRows256CapHalfBits128False
#check Counterexamples.TernaryLInfRows256CapHalf.realMargin_admissible_family
#check Counterexamples.DenseSignThreshold.universal_real_threshold_failure
#check Obstructions.ternaryL2ThresholdRows192Floor12Bits132False
#check ternaryL2UpperRows192Threshold287Bits130Counterexample
#check Obstructions.ternaryL2UpperRows192Threshold287Bits130False
#check ternaryLInfUpperRows192Threshold487Over50Bits134Counterexample
#check Obstructions.ternaryLInfUpperRows192Threshold487Over50Bits134False
#check Obstructions.ternaryL2ThresholdRows512Bits192Floor76False
#check Obstructions.ternaryL2ThresholdRows512Bits192AtLeast76False
#check sparseLInfTwoCoordinateRowPass
#check SparseLInfTwoCoordinatePass
#check AffineL2ThresholdLowerTailAt
#check AffineLInfThresholdLowerTailAt
#check affineLInfThresholdSmallProjection_implies_l2Failure
#check affineLInfThresholdLowerTailAt_of_affineL2
#check rows256_cap67div200_fits_squaredNormFloor29

example :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 256
        squaredNormFloor := ⟨79, 4, by decide⟩
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 152) :=
  Results.L2.Lower.Rows256Bits152.ternaryL2ThresholdLower79Over4Bits152

example :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 256
        squaredNormFloor := NonnegativeRatio.ofNat 21
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 148) :=
  Results.L2.Lower.Rows256Bits152.ternaryL2ThresholdLower21Bits148

example :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 256
        squaredNormFloor := NonnegativeRatio.ofNat 9
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 192) :=
  Results.L2.Lower.Rows256Bits192.ternaryL2ThresholdLower9

example :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 256
        squaredNormFloor := NonnegativeRatio.ofNat 29
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 128) :=
  Results.L2.Lower.Rows256Bits128.ternaryL2ThresholdLower29

example :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 384
        squaredNormFloor := NonnegativeRatio.ofNat 43
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 192) :=
  Results.L2.Lower.Rows384Bits192.ternaryL2ThresholdLower43

example :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 192
        squaredNormFloor := NonnegativeRatio.ofNat 12
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 128) :=
  Results.L2.Lower.Rows192Bits128.ternaryL2ThresholdLower12

example :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 256
        threshold := NonnegativeRatio.ofNat 338 }
      (failureTarget 128) :=
  Results.L2.Upper.Rows256Bits128.ternaryL2Upper338

example :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 192
        threshold := NonnegativeRatio.ofNat 287 }
      (failureTarget 128) :=
  Results.L2.Upper.Rows192Bits128.ternaryL2Upper287

example :
    LInfThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 192
        coordinateCap :=
          { numerator := 17, denominator := 50, denominator_pos := by decide }
        modulusMargin := NonnegativeRatio.ofNat 2 }
      (failureTarget 129) :=
  Results.LInf.Lower.Rows192Bits128.ternaryLInfThresholdLower17Over50

example :
    LInfUpperTailAt
      { distribution := .balancedTernary
        rows := 192
        coordinateThreshold :=
          { numerator := 487, denominator := 50, denominator_pos := by decide } }
      (failureTarget 128) :=
  Results.LInf.Upper.Rows192Bits128.ternaryLInfUpper487Over50

example :
    ¬ LInfUpperTailAt
      { distribution := .balancedTernary
        rows := 192
        coordinateThreshold :=
          { numerator := 487, denominator := 50, denominator_pos := by decide } }
      (failureTarget 134) :=
  Obstructions.ternaryLInfUpperRows192Threshold487Over50Bits134False

example :
    LInfThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 256
        coordinateCap :=
          { numerator := 6, denominator := 25, denominator_pos := by decide }
        modulusMargin := NonnegativeRatio.ofNat 2 }
      (failureTarget 197) :=
  Results.LInf.Lower.TwoDecimal.lower6Over25Rows256Bits197

example :
    LInfThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 256
        coordinateCap :=
          { numerator := 21, denominator := 50, denominator_pos := by decide }
        modulusMargin := NonnegativeRatio.ofNat 2 }
      (failureTarget 133) :=
  Results.LInf.Lower.TwoDecimal.lower21Over50Rows256Bits133

example :
    LInfThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 384
        coordinateCap :=
          { numerator := 21, denominator := 50, denominator_pos := by decide }
        modulusMargin := NonnegativeRatio.ofNat 2 }
      (failureTarget 200) :=
  Results.LInf.Lower.TwoDecimal.lower21Over50Rows384Bits200

example :
    LInfThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        coordinateCap :=
          { numerator := 21, denominator := 50, denominator_pos := by decide }
        modulusMargin := NonnegativeRatio.ofNat 2 }
      (failureTarget 266) :=
  Results.LInf.Lower.TwoDecimal.lower21Over50Rows512Bits266

example :
    LInfThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        coordinateCap :=
          { numerator := 47, denominator := 100, denominator_pos := by decide }
        modulusMargin := NonnegativeRatio.ofNat 2 }
      (failureTarget 206) :=
  Results.LInf.Lower.TwoDecimal.lower47Over100Rows512Bits206

example :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 512
        threshold := NonnegativeRatio.ofNat 607 }
      (failureTarget 192) :=
  Results.L2.Upper.Rows512Bits192.ternaryL2Upper607

example :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 256
        threshold := NonnegativeRatio.ofNat 406 }
      (failureTarget 192) :=
  Results.L2.Upper.Rows256Bits192.ternaryL2Upper406

example :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 384
        threshold := NonnegativeRatio.ofNat 509 }
      (failureTarget 192) :=
  Results.L2.Upper.Rows384Bits192.ternaryL2Upper509

example :
    L2UpperTailAt
      { distribution := .balancedTernary
        rows := 512
        threshold := NonnegativeRatio.ofNat 681 }
      (failureTarget 256) :=
  Results.L2.Upper.Rows512Bits256.ternaryL2Upper681

example :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        squaredNormFloor := NonnegativeRatio.ofNat 71
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 192) :=
  Results.L2.Lower.Rows512Bits192.ternaryL2ThresholdLower71

example :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        squaredNormFloor := NonnegativeRatio.ofNat 73
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 193) :=
  Results.L2.Lower.Rows512Bits193.ternaryL2ThresholdLower73

example :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        squaredNormFloor := NonnegativeRatio.ofNat 73
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 192) :=
  Results.L2.Lower.Rows512Bits192.ternaryL2ThresholdLower73

example : ∀ (q d : ℕ) (w : Fin d → ℤ) (inputThreshold : ℕ),
    Odd q → CenteredInput q w → 0 < inputThreshold →
    inputThreshold ^ 2 ≤ sqNorm w → 3 * inputThreshold ≤ q →
    eventProbability (sparseRademacherMatrix 512 d)
      (fun J => modularProjectionSqNorm q J w < 73 * inputThreshold ^ 2) <
        failureTarget 193 := by
  intro q d w inputThreshold hq hcentered hpositive hnorm hmodulus
  rw [eventProbability_congr (sparseRademacherMatrix 512 d)
    (event' := L2ThresholdLowerFailure
      (NonnegativeRatio.ofNat 73) inputThreshold q w) (by
        intro J
        simp [L2ThresholdLowerFailure, NonnegativeRatio.ofNat])]
  exact Results.L2.Lower.Rows512Bits193.ternaryL2ThresholdLower73
    q d w inputThreshold hq hcentered hpositive hnorm
      (by simpa [InputThresholdWithinModulus,
        NonnegativeRatio.ofNat] using hmodulus)

example :
    L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        squaredNormFloor := NonnegativeRatio.ofNat 57
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 256) :=
  Results.L2.Lower.Rows512Bits256.ternaryL2ThresholdLower57

/- The legacy aggregate remains a three-conjunct API in its original order. -/
example :
    L2ThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 384
          squaredNormFloor := NonnegativeRatio.ofNat 43
          modulusMargin := NonnegativeRatio.ofNat 3 }
        (failureTarget 192) ∧
      L2ThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 512
          squaredNormFloor := NonnegativeRatio.ofNat 71
          modulusMargin := NonnegativeRatio.ofNat 3 }
        (failureTarget 192) ∧
      L2ThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 512
          squaredNormFloor := NonnegativeRatio.ofNat 57
          modulusMargin := NonnegativeRatio.ofNat 3 }
        (failureTarget 256) :=
  Results.L2.Lower.HighSecurity.allLowerBounds

/- The current aggregate pins the five strongest public specializations and
their order. -/
example :
    L2ThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 256
          squaredNormFloor := NonnegativeRatio.ofNat 9
          modulusMargin := NonnegativeRatio.ofNat 3 }
        (failureTarget 192) ∧
      L2ThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 384
          squaredNormFloor := NonnegativeRatio.ofNat 43
          modulusMargin := NonnegativeRatio.ofNat 3 }
        (failureTarget 192) ∧
      L2ThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 512
          squaredNormFloor := NonnegativeRatio.ofNat 73
          modulusMargin := NonnegativeRatio.ofNat 3 }
        (failureTarget 192) ∧
      L2ThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 512
          squaredNormFloor := NonnegativeRatio.ofNat 73
          modulusMargin := NonnegativeRatio.ofNat 3 }
        (failureTarget 193) ∧
      L2ThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 512
          squaredNormFloor := NonnegativeRatio.ofNat 57
          modulusMargin := NonnegativeRatio.ofNat 3 }
        (failureTarget 256) :=
  Results.L2.Lower.HighSecurity.allLowerBoundsIncludingFloor73

/- The infinity aggregates pin every surviving row/security specialization. -/
example :
    LInfThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 256
          coordinateCap :=
            { numerator := 6, denominator := 25, denominator_pos := by decide }
          modulusMargin := NonnegativeRatio.ofNat 2 }
        (failureTarget 197) ∧
      LInfThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 256
          coordinateCap :=
            { numerator := 21, denominator := 50, denominator_pos := by decide }
          modulusMargin := NonnegativeRatio.ofNat 2 }
        (failureTarget 133) ∧
      LInfThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 384
          coordinateCap :=
            { numerator := 21, denominator := 50, denominator_pos := by decide }
          modulusMargin := NonnegativeRatio.ofNat 2 }
        (failureTarget 200) ∧
      LInfThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 512
          coordinateCap :=
            { numerator := 47, denominator := 100, denominator_pos := by decide }
          modulusMargin := NonnegativeRatio.ofNat 2 }
        (failureTarget 206) ∧
      LInfThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 512
          coordinateCap :=
            { numerator := 21, denominator := 50, denominator_pos := by decide }
          modulusMargin := NonnegativeRatio.ofNat 2 }
        (failureTarget 266) :=
  Results.LInf.Lower.HighSecurity.allThresholdLowerBounds

example :
    LInfUpperTailAt
        { distribution := .balancedTernary
          rows := 256
          coordinateThreshold :=
            { numerator := 39, denominator := 4, denominator_pos := by decide } }
        (failureTarget 133) ∧
      LInfUpperTailAt
        { distribution := .balancedTernary
          rows := 256
          coordinateThreshold :=
            { numerator := 1181, denominator := 100,
              denominator_pos := by decide } }
        (failureTarget 192) ∧
      LInfUpperTailAt
        { distribution := .balancedTernary
          rows := 384
          coordinateThreshold :=
            { numerator := 1183, denominator := 100,
              denominator_pos := by decide } }
        (failureTarget 192) ∧
      LInfUpperTailAt
        { distribution := .balancedTernary
          rows := 512
          coordinateThreshold :=
            { numerator := 1184, denominator := 100,
              denominator_pos := by decide } }
        (failureTarget 192) ∧
      LInfUpperTailAt
        { distribution := .balancedTernary
          rows := 512
          coordinateThreshold :=
            { numerator := 1358, denominator := 100,
              denominator_pos := by decide } }
        (failureTarget 256) :=
  Results.LInf.Upper.HighSecurity.allUpperBounds

example :
    ¬ LInfThresholdLowerTailAt
      Counterexamples.TernaryLInfThresholdMarginOne.parameters
      (failureTarget 130) :=
  Obstructions.ternaryLInfThresholdMarginOneBits130False

example :
    ¬ LInfThresholdLowerTailAt
      Counterexamples.TernaryLInfRows192Cap34.parameters
      (failureTarget 183) :=
  Obstructions.ternaryLInfThresholdRows192Cap34Bits183False

example :
    ¬ L2ThresholdLowerTailAt
      Counterexamples.ThresholdLowerRows192Floor12.parameters
      (failureTarget 132) :=
  Obstructions.ternaryL2ThresholdRows192Floor12Bits132False

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

example :
    ¬ L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        squaredNormFloor := NonnegativeRatio.ofNat 76
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 192) :=
  Obstructions.ternaryL2ThresholdRows512Bits192Floor76False

example : ∀ squaredNormFloor : ℕ, 76 ≤ squaredNormFloor →
    ¬ L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        squaredNormFloor := NonnegativeRatio.ofNat squaredNormFloor
        modulusMargin := NonnegativeRatio.ofNat 3 }
      (failureTarget 192) :=
  Obstructions.ternaryL2ThresholdRows512Bits192AtLeast76False

/-! ## Literal semantic canaries -/

/- The typed assignments above pin each threshold endpoint's rows, floor,
margin, and budget.  These shared canaries pin the exact expanded semantics. -/
example (parameters : L2ThresholdLowerParameters) (budget : ENNReal) :
    L2ThresholdLowerTailAt parameters budget ↔
      ∀ (q d : ℕ) (w : Fin d → ℤ) (inputThreshold : ℕ),
        Odd q →
        CenteredInput q w →
        0 < inputThreshold →
        InputThresholdAtMostNorm inputThreshold w →
        InputThresholdWithinModulus parameters.modulusMargin q inputThreshold →
        eventProbability (parameters.distribution.matrixPMF parameters.rows d)
          (L2ThresholdLowerFailure parameters.squaredNormFloor inputThreshold q w) < budget :=
  Iff.rfl

example : ∀ {rows d : ℕ} (squaredNormFloor q inputThreshold : ℕ)
    (w : Fin d → ℤ) (J : Fin rows → Fin d → ℤ),
    L2ThresholdLowerFailure (NonnegativeRatio.ofNat squaredNormFloor)
        inputThreshold q w J ↔
      modularProjectionSqNorm q J w < squaredNormFloor * inputThreshold ^ 2 := by
  intros
  simp [L2ThresholdLowerFailure, NonnegativeRatio.ofNat]

example : ∀ {d : ℕ} (inputThreshold : ℕ) (w : Fin d → ℤ),
    InputThresholdAtMostNorm inputThreshold w ↔
      inputThreshold ^ 2 ≤ sqNorm w := by
  intros
  rfl

example : ∀ (q inputThreshold : ℕ),
    InputThresholdWithinModulus (NonnegativeRatio.ofNat 3) q inputThreshold ↔
      3 * inputThreshold ≤ q := by
  intros
  simp [InputThresholdWithinModulus, NonnegativeRatio.ofNat]

example : ∀ (q d : ℕ) (w : Fin d → ℤ),
    eventProbability (sparseRademacherMatrix 256 d)
      (fun J ↦ 338 * sqNorm w < modularProjectionSqNorm q J w) < failureTarget 128 := by
  intro q d w
  rw [eventProbability_congr (sparseRademacherMatrix 256 d)
    (event' := L2UpperFailure (NonnegativeRatio.ofNat 338) q w)
    (by intro J; simp [L2UpperFailure, NonnegativeRatio.ofNat])]
  exact Results.L2.Upper.Rows256Bits128.ternaryL2Upper338 q d w

example : ∀ (q d : ℕ) (w : Fin d → ℤ),
    eventProbability (sparseRademacherMatrix 512 d)
      (fun J ↦ 607 * sqNorm w < modularProjectionSqNorm q J w) < failureTarget 192 := by
  intro q d w
  rw [eventProbability_congr (sparseRademacherMatrix 512 d)
    (event' := L2UpperFailure (NonnegativeRatio.ofNat 607) q w)
    (by intro J; simp [L2UpperFailure, NonnegativeRatio.ofNat])]
  exact Results.L2.Upper.Rows512Bits192.ternaryL2Upper607 q d w

example : ∀ (q d : ℕ) (w : Fin d → ℤ),
    eventProbability (sparseRademacherMatrix 256 d)
      (fun J ↦ 406 * sqNorm w < modularProjectionSqNorm q J w) < failureTarget 192 := by
  intro q d w
  rw [eventProbability_congr (sparseRademacherMatrix 256 d)
    (event' := L2UpperFailure (NonnegativeRatio.ofNat 406) q w)
    (by intro J; simp [L2UpperFailure, NonnegativeRatio.ofNat])]
  exact Results.L2.Upper.Rows256Bits192.ternaryL2Upper406 q d w

example : ∀ (q d : ℕ) (w : Fin d → ℤ),
    eventProbability (sparseRademacherMatrix 384 d)
      (fun J ↦ 509 * sqNorm w < modularProjectionSqNorm q J w) < failureTarget 192 := by
  intro q d w
  rw [eventProbability_congr (sparseRademacherMatrix 384 d)
    (event' := L2UpperFailure (NonnegativeRatio.ofNat 509) q w)
    (by intro J; simp [L2UpperFailure, NonnegativeRatio.ofNat])]
  exact Results.L2.Upper.Rows384Bits192.ternaryL2Upper509 q d w

example : ∀ (q d : ℕ) (w : Fin d → ℤ),
    eventProbability (sparseRademacherMatrix 512 d)
      (fun J ↦ 681 * sqNorm w < modularProjectionSqNorm q J w) < failureTarget 256 := by
  intro q d w
  rw [eventProbability_congr (sparseRademacherMatrix 512 d)
    (event' := L2UpperFailure (NonnegativeRatio.ofNat 681) q w)
    (by intro J; simp [L2UpperFailure, NonnegativeRatio.ofNat])]
  exact Results.L2.Upper.Rows512Bits256.ternaryL2Upper681 q d w

example : ∀ (q d : ℕ) (w : Fin d → ℤ) (inputThreshold : ℕ),
    Odd q → CenteredInput q w → 0 < inputThreshold →
    inputThreshold ^ 2 ≤ sqNorm w → 2 * inputThreshold ≤ q →
    eventProbability (sparseRademacherMatrix 256 d)
      (fun J ↦ ∀ j,
        2500 * (centeredMod q (rowDot J w j)).natAbs ^ 2 ≤
          441 * inputThreshold ^ 2) <
      failureTarget 133 := by
  intro q d w inputThreshold hq hcentered hpositive hnorm hmargin
  exact Results.LInf.Lower.TwoDecimal.lower21Over50Rows256Bits133
    q d w inputThreshold hq hcentered hpositive
      (by simpa [InputThresholdAtMostNorm] using hnorm)
      (by simpa [InputThresholdWithinModulus, NonnegativeRatio.ofNat] using hmargin)

end CertifiedJL.Tests.PublicAPI
