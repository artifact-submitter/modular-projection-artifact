/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJLFast

/-! # Fast umbrella public theorem API regression checks -/

namespace CertifiedJLFast.Tests.PublicAPI

#check CertifiedJLFast.Results.Affine.L2.Lower.General.ternaryAffineL2LowerTail_toReal_le_finiteTilt
#check CertifiedJLFast.Results.Affine.L2.Lower.General.ternaryAffineL2LowerTail_toReal_le_general
#check CertifiedJLFast.Results.Affine.L2.Lower.General.ternaryAffineL2LowerTail_toReal_le_general_of_ratio
#check CertifiedJLFast.Results.Affine.L2.Lower.General.ternaryAffineL2ThresholdLowerTailAt_of_generalBound_lt_failureTarget
#check CertifiedJLFast.Results.Affine.L2.Lower.General.ternaryAffineL2ThresholdLowerTailAt_of_finiteTilt_lt_failureTarget

#check Results.Affine.LInf.Lower.Direct.ternaryAffineLInfThresholdLower256Cap67Over200Bits130
#check Results.Affine.LInf.Lower.Direct.ternaryAffineLInfThresholdLower256Cap6Over25Bits197

#check Results.L2.Lower.Rows192Bits128.ternaryL2ThresholdLower12
#check Results.L2.Upper.Rows192Bits128.ternaryL2Upper287
#check Results.LInf.Lower.Rows192Bits128.ternaryLInfThresholdLower17Over50
#check Results.LInf.Upper.Rows192Bits128.ternaryLInfUpper487Over50
#check Results.Composites.Rows192Bits128.allBounds
#check Results.LInf.Lower.TwoDecimal.lower17Over50Rows192Bits129
#check Results.L2.Lower.Rows256Bits128.ternaryL2ThresholdLower29
#check CertifiedJL.Obstructions.ternaryL2ThresholdRows256Floor30Bits128False
#check CertifiedJL.Obstructions.ternaryL2ThresholdRows256Floor30Margin125Bits128False
#check CertifiedJL.Counterexamples.TernaryL2Rows256Floor30.admissible_witness
#check Results.L2.Upper.Rows256Bits128.ternaryL2Upper338
#check Results.LInf.Upper.Rows256Bits128.ternaryLInfUpper39Over4Bits133
#check Results.LInf.Upper.Rows256Bits128.ternaryLInfUpper39Over4
#check Results.LInf.Lower.TwoDecimal.lower6Over25Rows256Bits197
#check Results.LInf.Lower.TwoDecimal.lower21Over50Rows256Bits133
#check Results.LInf.Lower.TwoDecimal.lower21Over50Rows384Bits200
#check Results.LInf.Lower.TwoDecimal.lower21Over50Rows512Bits266
#check Results.LInf.Lower.TwoDecimal.lower47Over100Rows512Bits206
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

example :
    CertifiedJL.L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 192
        squaredNormFloor := CertifiedJL.NonnegativeRatio.ofNat 12
        modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 3 }
      (CertifiedJL.failureTarget 128) :=
  Results.L2.Lower.Rows192Bits128.ternaryL2ThresholdLower12

example :
    CertifiedJL.L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 256
        squaredNormFloor := CertifiedJL.NonnegativeRatio.ofNat 9
        modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 3 }
      (CertifiedJL.failureTarget 192) :=
  Results.L2.Lower.Rows256Bits192.ternaryL2ThresholdLower9

example :
    CertifiedJL.L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 256
        squaredNormFloor := CertifiedJL.NonnegativeRatio.ofNat 29
        modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 3 }
      (CertifiedJL.failureTarget 128) :=
  Results.L2.Lower.Rows256Bits128.ternaryL2ThresholdLower29

example :
    CertifiedJL.L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 384
        squaredNormFloor := CertifiedJL.NonnegativeRatio.ofNat 43
        modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 3 }
      (CertifiedJL.failureTarget 192) :=
  Results.L2.Lower.Rows384Bits192.ternaryL2ThresholdLower43

example :
    CertifiedJL.L2UpperTailAt
      { distribution := .balancedTernary
        rows := 256
        threshold := CertifiedJL.NonnegativeRatio.ofNat 338 }
      (CertifiedJL.failureTarget 128) :=
  Results.L2.Upper.Rows256Bits128.ternaryL2Upper338

example :
    CertifiedJL.L2UpperTailAt
      { distribution := .balancedTernary
        rows := 192
        threshold := CertifiedJL.NonnegativeRatio.ofNat 287 }
      (CertifiedJL.failureTarget 128) :=
  Results.L2.Upper.Rows192Bits128.ternaryL2Upper287

example :
    CertifiedJL.LInfThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 192
        coordinateCap :=
          { numerator := 17, denominator := 50, denominator_pos := by decide }
        modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 2 }
      (CertifiedJL.failureTarget 129) :=
  Results.LInf.Lower.Rows192Bits128.ternaryLInfThresholdLower17Over50

example :
    CertifiedJL.LInfUpperTailAt
      { distribution := .balancedTernary
        rows := 192
        coordinateThreshold :=
          { numerator := 487, denominator := 50, denominator_pos := by decide } }
      (CertifiedJL.failureTarget 128) :=
  Results.LInf.Upper.Rows192Bits128.ternaryLInfUpper487Over50

example :
    CertifiedJL.L2ThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 192
          squaredNormFloor := CertifiedJL.NonnegativeRatio.ofNat 12
          modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 3 }
        (CertifiedJL.failureTarget 128) ∧
      CertifiedJL.L2UpperTailAt
        { distribution := .balancedTernary
          rows := 192
          threshold := CertifiedJL.NonnegativeRatio.ofNat 287 }
        (CertifiedJL.failureTarget 128) ∧
      CertifiedJL.LInfThresholdLowerTailAt
        { distribution := .balancedTernary
          rows := 192
          coordinateCap :=
            { numerator := 17, denominator := 50, denominator_pos := by decide }
          modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 2 }
        (CertifiedJL.failureTarget 129) ∧
      CertifiedJL.LInfUpperTailAt
        { distribution := .balancedTernary
          rows := 192
          coordinateThreshold :=
            { numerator := 487, denominator := 50, denominator_pos := by decide } }
        (CertifiedJL.failureTarget 128) :=
  Results.Composites.Rows192Bits128.allBounds

example :
    CertifiedJL.LInfUpperTailAt
      { distribution := .balancedTernary
        rows := 256
        coordinateThreshold :=
          { numerator := 39, denominator := 4, denominator_pos := by decide } }
      (CertifiedJL.failureTarget 133) :=
  Results.LInf.Upper.Rows256Bits128.ternaryLInfUpper39Over4Bits133

example :
    CertifiedJL.LInfThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 256
        coordinateCap :=
          { numerator := 6, denominator := 25, denominator_pos := by decide }
        modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 2 }
      (CertifiedJL.failureTarget 197) :=
  Results.LInf.Lower.TwoDecimal.lower6Over25Rows256Bits197

example :
    CertifiedJL.LInfThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 256
        coordinateCap :=
          { numerator := 21, denominator := 50, denominator_pos := by decide }
        modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 2 }
      (CertifiedJL.failureTarget 133) :=
  Results.LInf.Lower.TwoDecimal.lower21Over50Rows256Bits133

example :
    CertifiedJL.LInfThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 384
        coordinateCap :=
          { numerator := 21, denominator := 50, denominator_pos := by decide }
        modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 2 }
      (CertifiedJL.failureTarget 200) :=
  Results.LInf.Lower.TwoDecimal.lower21Over50Rows384Bits200

example :
    CertifiedJL.LInfThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        coordinateCap :=
          { numerator := 21, denominator := 50, denominator_pos := by decide }
        modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 2 }
      (CertifiedJL.failureTarget 266) :=
  Results.LInf.Lower.TwoDecimal.lower21Over50Rows512Bits266

example :
    CertifiedJL.LInfThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        coordinateCap :=
          { numerator := 47, denominator := 100, denominator_pos := by decide }
        modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 2 }
      (CertifiedJL.failureTarget 206) :=
  Results.LInf.Lower.TwoDecimal.lower47Over100Rows512Bits206

example :
    CertifiedJL.L2UpperTailAt
      { distribution := .balancedTernary
        rows := 512
        threshold := CertifiedJL.NonnegativeRatio.ofNat 607 }
      (CertifiedJL.failureTarget 192) :=
  Results.L2.Upper.Rows512Bits192.ternaryL2Upper607

example : CertifiedJL.L2UpperTailAt
    { distribution := .balancedTernary, rows := 256,
      threshold := CertifiedJL.NonnegativeRatio.ofNat 406 }
    (CertifiedJL.failureTarget 192) :=
  Results.L2.Upper.Rows256Bits192.ternaryL2Upper406

example : CertifiedJL.L2UpperTailAt
    { distribution := .balancedTernary, rows := 384,
      threshold := CertifiedJL.NonnegativeRatio.ofNat 509 }
    (CertifiedJL.failureTarget 192) :=
  Results.L2.Upper.Rows384Bits192.ternaryL2Upper509

example : CertifiedJL.L2UpperTailAt
    { distribution := .balancedTernary, rows := 512,
      threshold := CertifiedJL.NonnegativeRatio.ofNat 681 }
    (CertifiedJL.failureTarget 256) :=
  Results.L2.Upper.Rows512Bits256.ternaryL2Upper681

example :
    CertifiedJL.L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        squaredNormFloor := CertifiedJL.NonnegativeRatio.ofNat 71
        modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 3 }
      (CertifiedJL.failureTarget 192) :=
  Results.L2.Lower.Rows512Bits192.ternaryL2ThresholdLower71

example :
    CertifiedJL.L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        squaredNormFloor := CertifiedJL.NonnegativeRatio.ofNat 73
        modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 3 }
      (CertifiedJL.failureTarget 193) :=
  Results.L2.Lower.Rows512Bits193.ternaryL2ThresholdLower73

example :
    CertifiedJL.L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        squaredNormFloor := CertifiedJL.NonnegativeRatio.ofNat 73
        modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 3 }
      (CertifiedJL.failureTarget 192) :=
  Results.L2.Lower.Rows512Bits192.ternaryL2ThresholdLower73

example : ∀ (q d : ℕ) (w : Fin d → ℤ) (inputThreshold : ℕ),
    Odd q → CertifiedJL.CenteredInput q w → 0 < inputThreshold →
    inputThreshold ^ 2 ≤ CertifiedJL.sqNorm w → 3 * inputThreshold ≤ q →
    CertifiedJL.eventProbability (CertifiedJL.sparseRademacherMatrix 512 d)
      (fun J => CertifiedJL.modularProjectionSqNorm q J w < 73 * inputThreshold ^ 2) <
        CertifiedJL.failureTarget 193 := by
  intro q d w inputThreshold hq hcentered hpositive hnorm hmodulus
  rw [CertifiedJL.eventProbability_congr
    (CertifiedJL.sparseRademacherMatrix 512 d)
    (event' := CertifiedJL.L2ThresholdLowerFailure
      (CertifiedJL.NonnegativeRatio.ofNat 73) inputThreshold q w) (by
        intro J
        simp [CertifiedJL.L2ThresholdLowerFailure,
          CertifiedJL.NonnegativeRatio.ofNat])]
  exact Results.L2.Lower.Rows512Bits193.ternaryL2ThresholdLower73
    q d w inputThreshold hq hcentered hpositive hnorm
      (by simpa [CertifiedJL.InputThresholdWithinModulus,
        CertifiedJL.NonnegativeRatio.ofNat] using hmodulus)

example :
    CertifiedJL.L2ThresholdLowerTailAt
      { distribution := .balancedTernary
        rows := 512
        squaredNormFloor := CertifiedJL.NonnegativeRatio.ofNat 57
        modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 3 }
      (CertifiedJL.failureTarget 256) :=
  Results.L2.Lower.Rows512Bits256.ternaryL2ThresholdLower57

/-! ## Literal semantic canaries -/

/- The assignments above pin every threshold theorem's concrete parameters and
budget.  These compositional canaries pin the fully expanded event and input
conditions without repeatedly normalizing the same large umbrella theorem. -/
example (parameters : CertifiedJL.L2ThresholdLowerParameters)
    (budget : ENNReal) :
    CertifiedJL.L2ThresholdLowerTailAt parameters budget ↔
      ∀ (q d : ℕ) (w : Fin d → ℤ) (inputThreshold : ℕ),
        Odd q →
        CertifiedJL.CenteredInput q w →
        0 < inputThreshold →
        CertifiedJL.InputThresholdAtMostNorm inputThreshold w →
        CertifiedJL.InputThresholdWithinModulus
          parameters.modulusMargin q inputThreshold →
        CertifiedJL.eventProbability
          (parameters.distribution.matrixPMF parameters.rows d)
          (CertifiedJL.L2ThresholdLowerFailure parameters.squaredNormFloor
            inputThreshold q w) < budget :=
  Iff.rfl

example : ∀ {rows d : ℕ} (squaredNormFloor q inputThreshold : ℕ)
    (w : Fin d → ℤ) (J : Fin rows → Fin d → ℤ),
    CertifiedJL.L2ThresholdLowerFailure
        (CertifiedJL.NonnegativeRatio.ofNat squaredNormFloor)
        inputThreshold q w J ↔
      CertifiedJL.modularProjectionSqNorm q J w < squaredNormFloor * inputThreshold ^ 2 := by
  intros
  simp [CertifiedJL.L2ThresholdLowerFailure,
    CertifiedJL.NonnegativeRatio.ofNat]

example : ∀ {d : ℕ} (inputThreshold : ℕ) (w : Fin d → ℤ),
    CertifiedJL.InputThresholdAtMostNorm inputThreshold w ↔
      inputThreshold ^ 2 ≤ CertifiedJL.sqNorm w := by
  intros
  rfl

example : ∀ (q inputThreshold : ℕ),
    CertifiedJL.InputThresholdWithinModulus
        (CertifiedJL.NonnegativeRatio.ofNat 3) q inputThreshold ↔
      3 * inputThreshold ≤ q := by
  intros
  simp [CertifiedJL.InputThresholdWithinModulus,
    CertifiedJL.NonnegativeRatio.ofNat]

example : ∀ (q d : ℕ) (w : Fin d → ℤ),
    CertifiedJL.eventProbability (CertifiedJL.sparseRademacherMatrix 256 d)
      (fun J ↦ 338 * CertifiedJL.sqNorm w <
        CertifiedJL.modularProjectionSqNorm q J w) < CertifiedJL.failureTarget 128 := by
  intro q d w
  rw [CertifiedJL.eventProbability_congr
    (CertifiedJL.sparseRademacherMatrix 256 d)
    (event' := CertifiedJL.L2UpperFailure
      (CertifiedJL.NonnegativeRatio.ofNat 338) q w) (by
        intro J
        simp [CertifiedJL.L2UpperFailure, CertifiedJL.NonnegativeRatio.ofNat])]
  exact Results.L2.Upper.Rows256Bits128.ternaryL2Upper338 q d w

example : ∀ (q d : ℕ) (w : Fin d → ℤ),
    CertifiedJL.eventProbability (CertifiedJL.sparseRademacherMatrix 512 d)
      (fun J ↦ 607 * CertifiedJL.sqNorm w <
        CertifiedJL.modularProjectionSqNorm q J w) < CertifiedJL.failureTarget 192 := by
  intro q d w
  rw [CertifiedJL.eventProbability_congr
    (CertifiedJL.sparseRademacherMatrix 512 d)
    (event' := CertifiedJL.L2UpperFailure
      (CertifiedJL.NonnegativeRatio.ofNat 607) q w) (by
        intro J
        simp [CertifiedJL.L2UpperFailure, CertifiedJL.NonnegativeRatio.ofNat])]
  exact Results.L2.Upper.Rows512Bits192.ternaryL2Upper607 q d w

example : ∀ (q d : ℕ) (w : Fin d → ℤ),
    CertifiedJL.eventProbability (CertifiedJL.sparseRademacherMatrix 256 d)
      (fun J ↦ 406 * CertifiedJL.sqNorm w <
        CertifiedJL.modularProjectionSqNorm q J w) < CertifiedJL.failureTarget 192 := by
  intro q d w
  rw [CertifiedJL.eventProbability_congr
    (CertifiedJL.sparseRademacherMatrix 256 d)
    (event' := CertifiedJL.L2UpperFailure
      (CertifiedJL.NonnegativeRatio.ofNat 406) q w) (by
        intro J
        simp [CertifiedJL.L2UpperFailure, CertifiedJL.NonnegativeRatio.ofNat])]
  exact Results.L2.Upper.Rows256Bits192.ternaryL2Upper406 q d w

example : ∀ (q d : ℕ) (w : Fin d → ℤ),
    CertifiedJL.eventProbability (CertifiedJL.sparseRademacherMatrix 384 d)
      (fun J ↦ 509 * CertifiedJL.sqNorm w <
        CertifiedJL.modularProjectionSqNorm q J w) < CertifiedJL.failureTarget 192 := by
  intro q d w
  rw [CertifiedJL.eventProbability_congr
    (CertifiedJL.sparseRademacherMatrix 384 d)
    (event' := CertifiedJL.L2UpperFailure
      (CertifiedJL.NonnegativeRatio.ofNat 509) q w) (by
        intro J
        simp [CertifiedJL.L2UpperFailure, CertifiedJL.NonnegativeRatio.ofNat])]
  exact Results.L2.Upper.Rows384Bits192.ternaryL2Upper509 q d w

example : ∀ (q d : ℕ) (w : Fin d → ℤ),
    CertifiedJL.eventProbability (CertifiedJL.sparseRademacherMatrix 512 d)
      (fun J ↦ 681 * CertifiedJL.sqNorm w <
        CertifiedJL.modularProjectionSqNorm q J w) < CertifiedJL.failureTarget 256 := by
  intro q d w
  rw [CertifiedJL.eventProbability_congr
    (CertifiedJL.sparseRademacherMatrix 512 d)
    (event' := CertifiedJL.L2UpperFailure
      (CertifiedJL.NonnegativeRatio.ofNat 681) q w) (by
        intro J
        simp [CertifiedJL.L2UpperFailure, CertifiedJL.NonnegativeRatio.ofNat])]
  exact Results.L2.Upper.Rows512Bits256.ternaryL2Upper681 q d w

example : ∀ (q d : ℕ) (w : Fin d → ℤ) (b : ℕ),
    Odd q → CertifiedJL.CenteredInput q w → 0 < b →
    b ^ 2 ≤ CertifiedJL.sqNorm w → 2 * b ≤ q →
    CertifiedJL.eventProbability (CertifiedJL.sparseRademacherMatrix 256 d)
      (fun J ↦ ∀ j,
        2500 * (CertifiedJL.centeredMod q
          (CertifiedJL.rowDot J w j)).natAbs ^ 2 ≤
            441 * b ^ 2) < CertifiedJL.failureTarget 133 := by
  intro q d w b hq hcentered hpositive hnorm hmargin
  exact Results.LInf.Lower.TwoDecimal.lower21Over50Rows256Bits133
    q d w b hq hcentered hpositive
      (by simpa [CertifiedJL.InputThresholdAtMostNorm] using hnorm)
      (by simpa [CertifiedJL.InputThresholdWithinModulus,
        CertifiedJL.TernaryLInfThresholdLower21Over50TwoDecimal.parametersAt,
        CertifiedJL.NonnegativeRatio.ofNat] using hmargin)

-- The paper's generic assembly must retain the selectable diffuse boundary.
#check CertifiedJL.sparseThresholdLowerTail_marginThree_of_analyticBoundsWithDiffuse

-- The floor-73/193-bit target uses the tighter dominant budget split.
example : CertifiedJL.Threshold512Floor73Bits193.config.lowBudget =
    (1 : ENNReal) / 100000 * CertifiedJL.failureTarget 193 := rfl

example : CertifiedJL.Threshold512Floor73Bits193.config.highBudget =
    (99999 : ENNReal) / 100000 * CertifiedJL.failureTarget 193 := rfl

-- Closed affine cap, a fixed shift in each row, and modulus margin three.
example : CertifiedJL.AffineLInfThresholdLowerTailAt
    { distribution := .balancedTernary, rows := 256,
      coordinateCap := { numerator := 67, denominator := 200, denominator_pos := by decide },
      modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 3 }
    (CertifiedJL.failureTarget 130) :=
  Results.Affine.LInf.Lower.Direct.ternaryAffineLInfThresholdLower256Cap67Over200Bits130

-- Closed affine cap, a fixed shift in each row, and modulus margin three.
example : CertifiedJL.AffineLInfThresholdLowerTailAt
    { distribution := .balancedTernary, rows := 256,
      coordinateCap := { numerator := 6, denominator := 25, denominator_pos := by decide },
      modulusMargin := CertifiedJL.NonnegativeRatio.ofNat 3 }
    (CertifiedJL.failureTarget 197) :=
  Results.Affine.LInf.Lower.Direct.ternaryAffineLInfThresholdLower256Cap6Over25Bits197

end CertifiedJLFast.Tests.PublicAPI
