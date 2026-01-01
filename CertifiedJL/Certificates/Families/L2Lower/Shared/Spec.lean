/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Soundness.CappedFourierNumeric128
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.CappedFourierCover128
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Soundness.ConstantNumeric
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Soundness.SingletonFourierNumeric128
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Replay.SingletonFourierCover128
import CertifiedJL.Projection.L2.Lower.BalancedTernary.Shared.CosineLaplace
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Soundness.ThresholdNearChordCurvatureSoundness128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Replay.ThresholdNearChordEndpoints128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Soundness.ThresholdNearChordSoundness128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Soundness.ThresholdNearCoarseSoundness128

/-!
# Narrow semantic certificate contracts for the threshold-relative lower tail

Only finite cover and reflected-numeric conclusions appear here. Analytic
transport, support selection, regime routing, and probability assembly remain
ordinary kernel-checked Lean in both production and fast modes.
-/

namespace CertifiedJL.CertificateContracts

def SparseL2ThresholdDominantDirectCover128 : Prop :=
  ∀ (u r B : ℝ),
    0 ≤ u → u ≤ 1 / 2 → 0 ≤ r → r ≤ 2500 / 2401 → r ≤ 1 + u →
    2 ≤ B → 9 * r ≤ B ^ 2 →
    ∃ entry : SparseThresholdDominant.ConstantNumeric.Entry,
      entry.cell.Valid ∧
      (entry.cell.lower : ℝ) ≤ u ∧
      u ≤ (entry.cell.upper : ℝ) ∧
      r ≤ (entry.cell.thresholdUpper : ℝ) ∧
      (entry.cell.modulusLower : ℝ) ≤ B ∧
      thresholdDominantCellMajorant entry.cell.decode <
        (((187 / (200 * 2 ^ 128) : ℚ) : ℝ))

def SparseL2ThresholdDominantCappedFourierCover128 : Prop :=
  ∀ {B r : ℝ},
    2 ≤ B → B ≤ 3 → 9 * r ≤ B ^ 2 →
    ∃ cell : SparseThresholdDominant.CappedFourierNumeric128.Cell,
      cell ∈ SparseThresholdDominant.CappedFourierCover128.cells ∧
      (cell.lower : ℝ) ≤ B ∧ B ≤ cell.upper ∧
      r ≤ cell.thresholdUpper ∧
      SparseThresholdDominant.CappedFourierNumeric128.certifiedCheck cell = true

def SparseL2ThresholdDominantSingletonFourierCover128 : Prop :=
  ∀ {B r : ℝ},
    2 ≤ B → B ≤ 5 / 2 → 9 * r ≤ B ^ 2 →
    ∃ cell : SparseThresholdDominant.SingletonFourierNumeric128.Cell,
      cell ∈ SparseThresholdDominant.SingletonFourierCover128.cells ∧
      (cell.lower : ℝ) ≤ B ∧ B ≤ cell.upper ∧
      r ≤ cell.thresholdUpper ∧
      SparseThresholdDominant.SingletonFourierNumeric128.certifiedCheck cell = true

structure SparseL2ThresholdDominantRetainedCoarse128 : Prop where
  central : ∀ {x : ℝ},
    3 / 2 ≤ x → x ≤ 11 / 5 →
    ThresholdNearCoarse128.semanticCoarseCentral x 1 < 12 / 25
  conditionedTail : ∀ {x : ℝ},
    3 / 2 ≤ x → x ≤ 11 / 5 →
    (ThresholdNearCoarse128.semanticInactiveTail x 1 +
      ThresholdNearCoarse128.semanticActiveTail x 1) / 2 < 1 / 20

def SparseL2ThresholdDominantRetainedChord128 : Prop :=
  ∀ {x y : ℝ},
    3 / 2 ≤ x → x ≤ 11 / 5 → 4 / 5 ≤ y → y ≤ 1 →
    ThresholdNearChord128.semanticChordCentral x 1 y < 12 / 25

def SparseL2ThresholdDominantFinalRatio128 : Prop :=
  Real.exp ((23 / 10 : ℝ) * 29 * (2500 / 2401)) *
      (53 / 100 : ℝ) ^ 256 <
    (187 / 200 : ℝ) * (2 : ℝ)⁻¹ ^ 128

/-- Target-dependent direct-cover boundary shared by fixed- and
target-selected-tilt replay structures. -/
def SparseL2ThresholdDominantDirectCoverAt
    (rows squaredNormFloor : ℕ) (highBudget : ℝ) : Prop :=
  ∀ (u r B : ℝ),
    0 ≤ u → u ≤ 1 / 2 → 0 ≤ r → r ≤ 2500 / 2401 → r ≤ 1 + u →
    2 ≤ B → 9 * r ≤ B ^ 2 →
    ∃ entry : SparseThresholdDominant.ConstantNumeric.Entry,
      entry.cell.Valid ∧
      (entry.cell.lower : ℝ) ≤ u ∧
      u ≤ (entry.cell.upper : ℝ) ∧
      r ≤ (entry.cell.thresholdUpper : ℝ) ∧
      (entry.cell.modulusLower : ℝ) ≤ B ∧
      thresholdDominantCellMajorantAt rows squaredNormFloor
        (entry.cell.decodeAt rows) < highBudget

/-- Target-dependent capped-Fourier cover boundary. -/
def SparseL2ThresholdDominantCappedFourierCoverAt
    (rows squaredNormFloor : ℕ) (highBudget : ℝ) : Prop :=
  ∀ {B r : ℝ},
    2 ≤ B → B ≤ 3 → 9 * r ≤ B ^ 2 →
    ∃ cell : SparseThresholdDominant.CappedFourierNumeric128.Cell,
      cell ∈ SparseThresholdDominant.CappedFourierCover128.cells ∧
      (cell.lower : ℝ) ≤ B ∧ B ≤ cell.upper ∧
      r ≤ cell.thresholdUpper ∧
      (2 : ℝ) ≤ cell.lower ∧ (cell.upper : ℝ) ≤ 3 ∧
      Real.exp (squaredNormFloor * (9 / 4 : ℝ) * (cell.thresholdUpper : ℝ)) *
        thresholdDominantCappedFourierCellRow
          (cell.lower : ℝ) (cell.upper : ℝ) (9 / 4) ^ rows < highBudget

/-- Target-dependent singleton-Fourier cover boundary. -/
def SparseL2ThresholdDominantSingletonFourierCoverAt
    (rows squaredNormFloor : ℕ) (highBudget : ℝ) : Prop :=
  ∀ {B r : ℝ},
    2 ≤ B → B ≤ 5 / 2 → 9 * r ≤ B ^ 2 →
    ∃ cell : SparseThresholdDominant.SingletonFourierNumeric128.Cell,
      cell ∈ SparseThresholdDominant.SingletonFourierCover128.cells ∧
      (cell.lower : ℝ) ≤ B ∧ B ≤ cell.upper ∧
      r ≤ cell.thresholdUpper ∧
      (0 : ℝ) < cell.lower ∧
      Real.exp (squaredNormFloor * (9 / 4 : ℝ) * (cell.thresholdUpper : ℝ)) *
        thresholdDominantSingletonLowFourierCellRow
          (cell.lower : ℝ) (cell.upper : ℝ) (9 / 4) ^ rows < highBudget

/-! Target-dependent 384/43/192 certificate boundaries. The retained, near,
and diffuse one-row geometry above remains target-neutral and is reused. -/

def SparseL2ThresholdDominantDirectCover384Bits192 : Prop :=
  ∀ (u r B : ℝ),
    0 ≤ u → u ≤ 1 / 2 → 0 ≤ r → r ≤ 2500 / 2401 → r ≤ 1 + u →
    2 ≤ B → 9 * r ≤ B ^ 2 →
    ∃ entry : SparseThresholdDominant.ConstantNumeric.Entry,
      entry.cell.Valid ∧
      (entry.cell.lower : ℝ) ≤ u ∧
      u ≤ (entry.cell.upper : ℝ) ∧
      r ≤ (entry.cell.thresholdUpper : ℝ) ∧
      (entry.cell.modulusLower : ℝ) ≤ B ∧
      thresholdDominantCellMajorantAt 384 43
        (entry.cell.decodeAt 384) <
          (((19 / (20 * 2 ^ 192) : ℚ) : ℝ))

def SparseL2ThresholdDominantCappedFourierCover384Bits192 : Prop :=
  ∀ {B r : ℝ},
    2 ≤ B → B ≤ 3 → 9 * r ≤ B ^ 2 →
    ∃ cell : SparseThresholdDominant.CappedFourierNumeric128.Cell,
      cell ∈ SparseThresholdDominant.CappedFourierCover128.cells ∧
      (cell.lower : ℝ) ≤ B ∧ B ≤ cell.upper ∧
      r ≤ cell.thresholdUpper ∧
      (2 : ℝ) ≤ cell.lower ∧ (cell.upper : ℝ) ≤ 3 ∧
      Real.exp (43 * (9 / 4 : ℝ) * (cell.thresholdUpper : ℝ)) *
        thresholdDominantCappedFourierCellRow
          (cell.lower : ℝ) (cell.upper : ℝ) (9 / 4) ^ 384 <
            (((19 / (20 * 2 ^ 192) : ℚ) : ℝ))

def SparseL2ThresholdDominantSingletonFourierCover384Bits192 : Prop :=
  ∀ {B r : ℝ},
    2 ≤ B → B ≤ 5 / 2 → 9 * r ≤ B ^ 2 →
    ∃ cell : SparseThresholdDominant.SingletonFourierNumeric128.Cell,
      cell ∈ SparseThresholdDominant.SingletonFourierCover128.cells ∧
      (cell.lower : ℝ) ≤ B ∧ B ≤ cell.upper ∧
      r ≤ cell.thresholdUpper ∧
      (0 : ℝ) < cell.lower ∧
      Real.exp (43 * (9 / 4 : ℝ) * (cell.thresholdUpper : ℝ)) *
        thresholdDominantSingletonLowFourierCellRow
          (cell.lower : ℝ) (cell.upper : ℝ) (9 / 4) ^ 384 <
            (((19 / (20 * 2 ^ 192) : ℚ) : ℝ))

def SparseL2ThresholdDominantFinalRatio384Bits192 : Prop :=
  Real.exp ((23 / 10 : ℝ) * 43 * (2500 / 2401)) *
      (53 / 100 : ℝ) ^ 384 <
    (((19 / (20 * 2 ^ 192) : ℚ) : ℝ))

def SparseL2ThresholdNearFinalRatio384Bits192 : Prop :=
  Real.exp ((23 / 10 : ℝ) * 43) * (681 / 1250 : ℝ) ^ 384 <
    (2 : ℝ)⁻¹ ^ 192

def SparseL2ThresholdDiffuseFinalRatio384Bits192 : Prop :=
  Real.exp ((33 / 10 : ℝ) * 43) * (97 / 200 : ℝ) ^ 384 <
    (2 : ℝ)⁻¹ ^ 192


/-! Target-dependent 512/71/192 certificate boundaries. -/

def SparseL2ThresholdDominantDirectCover512Bits192 : Prop :=
  ∀ (u r B : ℝ),
    0 ≤ u → u ≤ 1 / 2 → 0 ≤ r → r ≤ 2500 / 2401 → r ≤ 1 + u →
    2 ≤ B → 9 * r ≤ B ^ 2 →
    ∃ entry : SparseThresholdDominant.ConstantNumeric.Entry,
      entry.cell.Valid ∧
      (entry.cell.lower : ℝ) ≤ u ∧
      u ≤ (entry.cell.upper : ℝ) ∧
      r ≤ (entry.cell.thresholdUpper : ℝ) ∧
      (entry.cell.modulusLower : ℝ) ≤ B ∧
      thresholdDominantCellMajorantAt 512 71
        (entry.cell.decodeAt 512) <
          (((99 / (100 * 2 ^ 192)) : ℚ) : ℝ)

def SparseL2ThresholdDominantCappedFourierCover512Bits192 : Prop :=
  ∀ {B r : ℝ},
    2 ≤ B → B ≤ 3 → 9 * r ≤ B ^ 2 →
    ∃ cell : SparseThresholdDominant.CappedFourierNumeric128.Cell,
      cell ∈ SparseThresholdDominant.CappedFourierCover128.cells ∧
      (cell.lower : ℝ) ≤ B ∧ B ≤ cell.upper ∧
      r ≤ cell.thresholdUpper ∧
      (2 : ℝ) ≤ cell.lower ∧ (cell.upper : ℝ) ≤ 3 ∧
      Real.exp (71 * (9 / 4 : ℝ) * (cell.thresholdUpper : ℝ)) *
        thresholdDominantCappedFourierCellRow
          (cell.lower : ℝ) (cell.upper : ℝ) (9 / 4) ^ 512 <
            (((99 / (100 * 2 ^ 192)) : ℚ) : ℝ)

def SparseL2ThresholdDominantSingletonFourierCover512Bits192 : Prop :=
  ∀ {B r : ℝ},
    2 ≤ B → B ≤ 5 / 2 → 9 * r ≤ B ^ 2 →
    ∃ cell : SparseThresholdDominant.SingletonFourierNumeric128.Cell,
      cell ∈ SparseThresholdDominant.SingletonFourierCover128.cells ∧
      (cell.lower : ℝ) ≤ B ∧ B ≤ cell.upper ∧
      r ≤ cell.thresholdUpper ∧
      (0 : ℝ) < cell.lower ∧
      Real.exp (71 * (9 / 4 : ℝ) * (cell.thresholdUpper : ℝ)) *
        thresholdDominantSingletonLowFourierCellRow
          (cell.lower : ℝ) (cell.upper : ℝ) (9 / 4) ^ 512 <
            (((99 / (100 * 2 ^ 192)) : ℚ) : ℝ)

def SparseL2ThresholdDominantFinalRatio512Bits192 : Prop :=
  Real.exp ((23 / 10 : ℝ) * 71 * (2500 / 2401)) *
      (53 / 100 : ℝ) ^ 512 <
    (((99 / (100 * 2 ^ 192)) : ℚ) : ℝ)

def SparseL2ThresholdNearFinalRatio512Bits192 : Prop :=
  Real.exp ((23 / 10 : ℝ) * 71) * (681 / 1250 : ℝ) ^ 512 <
    (2 : ℝ)⁻¹ ^ 192

def SparseL2ThresholdDiffuseFinalRatio512Bits192 : Prop :=
  Real.exp ((33 / 10 : ℝ) * 71) * (97 / 200 : ℝ) ^ 512 <
    (2 : ℝ)⁻¹ ^ 192

/-! Target-dependent 512/73/193 certificate boundaries. -/

def SparseL2ThresholdDominantDirectCover512Floor73Bits193 : Prop :=
  SparseL2ThresholdDominantDirectCoverAt 512 73
    (((99999 / (100000 * 2 ^ 193) : ℚ) : ℝ))

def SparseL2ThresholdDominantCappedFourierCover512Floor73Bits193 : Prop :=
  SparseL2ThresholdDominantCappedFourierCoverAt 512 73
    (((99999 / (100000 * 2 ^ 193) : ℚ) : ℝ))

def SparseL2ThresholdDominantSingletonFourierCover512Floor73Bits193 : Prop :=
  SparseL2ThresholdDominantSingletonFourierCoverAt 512 73
    (((99999 / (100000 * 2 ^ 193) : ℚ) : ℝ))

def SparseL2ThresholdDominantFinalRatio512Floor73Bits193 : Prop :=
  Real.exp ((23 / 10 : ℝ) * 73 * (2500 / 2401)) *
      (53 / 100 : ℝ) ^ 512 <
    (((99999 / (100000 * 2 ^ 193) : ℚ) : ℝ))

def SparseL2ThresholdNearFinalRatio512Floor73Bits193 : Prop :=
  Real.exp ((23 / 10 : ℝ) * 73) * (681 / 1250 : ℝ) ^ 512 <
    (2 : ℝ)⁻¹ ^ 193

def SparseL2ThresholdDiffuseFinalRatio512Floor73Bits193 : Prop :=
  Real.exp ((5 / 2 : ℝ) * 73) * (539 / 1000 : ℝ) ^ 512 <
    (2 : ℝ)⁻¹ ^ 193

/-! Target-dependent 512/57/256 certificate boundaries. -/

def SparseL2ThresholdDominantDirectCover512Bits256 : Prop :=
  ∀ (u r B : ℝ),
    0 ≤ u → u ≤ 1 / 2 → 0 ≤ r → r ≤ 2500 / 2401 → r ≤ 1 + u →
    2 ≤ B → 9 * r ≤ B ^ 2 →
    ∃ entry : SparseThresholdDominant.ConstantNumeric.Entry,
      entry.cell.Valid ∧
      (entry.cell.lower : ℝ) ≤ u ∧
      u ≤ (entry.cell.upper : ℝ) ∧
      r ≤ (entry.cell.thresholdUpper : ℝ) ∧
      (entry.cell.modulusLower : ℝ) ≤ B ∧
      thresholdDominantCellMajorantAt 512 57
        (entry.cell.decodeAt 512) <
          (((24 / (25 * 2 ^ 256)) : ℚ) : ℝ)

def SparseL2ThresholdDominantCappedFourierCover512Bits256 : Prop :=
  ∀ {B r : ℝ},
    2 ≤ B → B ≤ 3 → 9 * r ≤ B ^ 2 →
    ∃ cell : SparseThresholdDominant.CappedFourierNumeric128.Cell,
      cell ∈ SparseThresholdDominant.CappedFourierCover128.cells ∧
      (cell.lower : ℝ) ≤ B ∧ B ≤ cell.upper ∧
      r ≤ cell.thresholdUpper ∧
      (2 : ℝ) ≤ cell.lower ∧ (cell.upper : ℝ) ≤ 3 ∧
      Real.exp (57 * (9 / 4 : ℝ) * (cell.thresholdUpper : ℝ)) *
        thresholdDominantCappedFourierCellRow
          (cell.lower : ℝ) (cell.upper : ℝ) (9 / 4) ^ 512 <
            (((24 / (25 * 2 ^ 256)) : ℚ) : ℝ)

def SparseL2ThresholdDominantSingletonFourierCover512Bits256 : Prop :=
  ∀ {B r : ℝ},
    2 ≤ B → B ≤ 5 / 2 → 9 * r ≤ B ^ 2 →
    ∃ cell : SparseThresholdDominant.SingletonFourierNumeric128.Cell,
      cell ∈ SparseThresholdDominant.SingletonFourierCover128.cells ∧
      (cell.lower : ℝ) ≤ B ∧ B ≤ cell.upper ∧
      r ≤ cell.thresholdUpper ∧
      (0 : ℝ) < cell.lower ∧
      Real.exp (57 * (9 / 4 : ℝ) * (cell.thresholdUpper : ℝ)) *
        thresholdDominantSingletonLowFourierCellRow
          (cell.lower : ℝ) (cell.upper : ℝ) (9 / 4) ^ 512 <
            (((24 / (25 * 2 ^ 256)) : ℚ) : ℝ)

def SparseL2ThresholdDominantFinalRatio512Bits256 : Prop :=
  Real.exp ((23 / 10 : ℝ) * 57 * (2500 / 2401)) *
      (53 / 100 : ℝ) ^ 512 <
    (((24 / (25 * 2 ^ 256)) : ℚ) : ℝ)

def SparseL2ThresholdNearFinalRatio512Bits256 : Prop :=
  Real.exp ((23 / 10 : ℝ) * 57) * (681 / 1250 : ℝ) ^ 512 <
    (2 : ℝ)⁻¹ ^ 256

def SparseL2ThresholdDiffuseFinalRatio512Bits256 : Prop :=
  Real.exp ((33 / 10 : ℝ) * 57) * (97 / 200 : ℝ) ^ 512 <
    (2 : ℝ)⁻¹ ^ 256

/-! Target-dependent 192/12/128 certificate boundaries.  This endpoint uses
the compact target-selected Fourier tilts and one retuned direct cell. -/

def SparseL2ThresholdDominantDirectCover192Bits128 : Prop :=
  SparseL2ThresholdDominantDirectCoverAt 192 12
    (((19 / (20 * 2 ^ 128)) : ℚ) : ℝ)

def SparseL2ThresholdDominantCappedFourierCover192Bits128 : Prop :=
  ∀ {B r : ℝ},
    2 ≤ B → B ≤ 3 → 9 * r ≤ B ^ 2 →
    ∃ L U thresholdUpper : ℝ,
      L ≤ B ∧ B ≤ U ∧ r ≤ thresholdUpper ∧
      2 ≤ L ∧ U ≤ 3 ∧
      Real.exp (12 * (13 / 4 : ℝ) * thresholdUpper) *
        thresholdDominantCappedFourierCellRow L U (13 / 4) ^ 192 <
          (((19 / (20 * 2 ^ 128)) : ℚ) : ℝ)

def SparseL2ThresholdDominantSingletonFourierCover192Bits128 : Prop :=
  ∀ {B r : ℝ},
    2 ≤ B → B ≤ 5 / 2 → 9 * r ≤ B ^ 2 →
    ∃ L U thresholdUpper : ℝ,
      L ≤ B ∧ B ≤ U ∧ r ≤ thresholdUpper ∧
      2 ≤ L ∧ U ≤ 3 ∧
      Real.exp (12 * (7 / 2 : ℝ) * thresholdUpper) *
        thresholdDominantSingletonPhaseFourierCellRow L U (7 / 2) ^ 192 <
          (((19 / (20 * 2 ^ 128)) : ℚ) : ℝ)

def SparseL2ThresholdDominantFinalRatio192Bits128 : Prop :=
  Real.exp ((23 / 10 : ℝ) * 12 * (2500 / 2401)) *
      (53 / 100 : ℝ) ^ 192 <
    (((19 / (20 * 2 ^ 128)) : ℚ) : ℝ)

def SparseL2ThresholdNearFinalRatio192Bits128 : Prop :=
  Real.exp ((23 / 10 : ℝ) * 12) * (681 / 1250 : ℝ) ^ 192 <
    (2 : ℝ)⁻¹ ^ 128

def SparseL2ThresholdDiffuseFinalRatio192Bits128 : Prop :=
  Real.exp ((33 / 10 : ℝ) * 12) * (97 / 200 : ℝ) ^ 192 <
    (2 : ℝ)⁻¹ ^ 128

/-! Target-dependent 256/9/192 certificate boundaries.  This endpoint uses
target-selected Fourier tilts and the phase-retaining singleton envelope. -/

def SparseL2ThresholdDominantDirectCover256Bits192 : Prop :=
  SparseL2ThresholdDominantDirectCoverAt 256 9
    (((99 / (100 * 2 ^ 192)) : ℚ) : ℝ)

def SparseL2ThresholdDominantCappedFourierCover256Bits192 : Prop :=
  ∀ {B r : ℝ},
    2 ≤ B → B ≤ 3 → 9 * r ≤ B ^ 2 →
    ∃ L U thresholdUpper : ℝ,
      L ≤ B ∧ B ≤ U ∧ r ≤ thresholdUpper ∧
      2 ≤ L ∧ U ≤ 3 ∧
      Real.exp (9 * (13 / 4 : ℝ) * thresholdUpper) *
        thresholdDominantCappedFourierCellRow L U (13 / 4) ^ 256 <
          (((99 / (100 * 2 ^ 192)) : ℚ) : ℝ)

def SparseL2ThresholdDominantSingletonFourierCover256Bits192 : Prop :=
  ∀ {B r : ℝ},
    2 ≤ B → B ≤ 5 / 2 → 9 * r ≤ B ^ 2 →
    ∃ L U thresholdUpper : ℝ,
      L ≤ B ∧ B ≤ U ∧ r ≤ thresholdUpper ∧
      2 ≤ L ∧ U ≤ 3 ∧
      Real.exp (9 * (7 / 2 : ℝ) * thresholdUpper) *
        thresholdDominantSingletonPhaseFourierCellRow L U (7 / 2) ^ 256 <
          (((99 / (100 * 2 ^ 192)) : ℚ) : ℝ)

def SparseL2ThresholdDominantFinalRatio256Bits192 : Prop :=
  Real.exp ((23 / 10 : ℝ) * 9 * (2500 / 2401)) *
      (53 / 100 : ℝ) ^ 256 <
    (((99 / (100 * 2 ^ 192)) : ℚ) : ℝ)

def SparseL2ThresholdNearFinalRatio256Bits192 : Prop :=
  Real.exp ((23 / 10 : ℝ) * 9) * (681 / 1250 : ℝ) ^ 256 <
    (2 : ℝ)⁻¹ ^ 192

def SparseL2ThresholdDiffuseFinalRatio256Bits192 : Prop :=
  Real.exp ((33 / 10 : ℝ) * 9) * (97 / 200 : ℝ) ^ 256 <
    (2 : ℝ)⁻¹ ^ 192

def SparseL2ThresholdNearCoarseCover128 : Prop :=
  ∀ {x a : ℝ},
    1 ≤ x → x ≤ 4901 / 2500 → 9 / 16 ≤ a → a ≤ 2401 / 2500 →
    ThresholdNearCoarse128.semanticEnvelope x a < 543 / 1000

structure SparseL2ThresholdNearEndpoints128 : Prop where
  fourFifths : ∀ {x a : ℝ},
    (1 : ℝ) ≤ x ∧ x ≤ 4901 / 2500 →
    (9 / 16 : ℝ) ≤ a ∧ a ≤ 2401 / 2500 →
    ThresholdNearChord128.semanticEnvelope x a (4 / 5) <
      (ThresholdNearChord128.endpointCap128 : ℚ)
  seventeenTwentieths : ∀ {x a : ℝ},
    (1 : ℝ) ≤ x ∧ x ≤ 4901 / 2500 →
    (9 / 16 : ℝ) ≤ a ∧ a ≤ 2401 / 2500 →
    ThresholdNearChord128.semanticEnvelope x a (17 / 20) <
      (ThresholdNearChord128.endpointCap128 : ℚ)
  nineTenths : ∀ {x a : ℝ},
    (1 : ℝ) ≤ x ∧ x ≤ 4901 / 2500 →
    (9 / 16 : ℝ) ≤ a ∧ a ≤ 2401 / 2500 →
    ThresholdNearChord128.semanticEnvelope x a (9 / 10) <
      (ThresholdNearChord128.endpointCap128 : ℚ)
  nineteenTwentieths : ∀ {x a : ℝ},
    (1 : ℝ) ≤ x ∧ x ≤ 4901 / 2500 →
    (9 / 16 : ℝ) ≤ a ∧ a ≤ 2401 / 2500 →
    ThresholdNearChord128.semanticEnvelope x a (19 / 20) <
      (ThresholdNearChord128.endpointCap128 : ℚ)
  one : ∀ {x a : ℝ},
    (1 : ℝ) ≤ x ∧ x ≤ 4901 / 2500 →
    (9 / 16 : ℝ) ≤ a ∧ a ≤ 2401 / 2500 →
    ThresholdNearChord128.semanticEnvelope x a 1 <
      (ThresholdNearChord128.endpointCap128 : ℚ)

def SparseL2ThresholdNearCurvature128 : Prop :=
  ∀ {x a y : ℝ},
    (1 : ℝ) ≤ x ∧ x ≤ 4901 / 2500 →
    (9 / 16 : ℝ) ≤ a ∧ a ≤ 2401 / 2500 →
    (4 / 5 : ℝ) ≤ y ∧ y ≤ 1 →
    -(81 / 20 : ℝ) < ThresholdNearChord128.semanticChordCentralSecond x a y

structure SparseL2ThresholdDiffuseLowScalar128 : Prop where
  lowBand : ∀ {x p : ℝ},
    1 ≤ x → x ≤ 26 / 25 → (32 / 9) * x ≤ p →
    sparseScalarF ((33 / 10) * x) p < (603 / 1250 : ℝ)
  highBand : ∀ {x p : ℝ},
    (26 / 25 : ℝ) ≤ x → x ≤ 11 / 10 → (32 / 9) * x ≤ p →
    sparseScalarF ((33 / 10) * x) p < (12 / 25 : ℝ)

structure SparseL2ThresholdDiffuseLowModularTail128 : Prop where
  lowBand : ∀ {c : ℝ}, (7425 / 1108 : ℝ) ≤ c →
    2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) < (13 / 5000 : ℝ)
  fullBand : ∀ {c : ℝ}, (2970 / 463 : ℝ) ≤ c →
    2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) < (1 / 200 : ℝ)

structure SparseL2ThresholdDiffuseHighEndpoints128 : Prop where
  firstLobe :
    1 / Real.sqrt (1 + (363 / 100 : ℝ)) *
        (1 + 2 * Real.exp
            (-((320 / 297 : ℝ) * (363 / 100) * Real.pi ^ 2 /
              (2 * (1 + (363 / 100))))) /
          (1 - (Real.exp
            (-((320 / 297 : ℝ) * (363 / 100) * Real.pi ^ 2 /
              (2 * (1 + (363 / 100)))))) ^ 3)) <
      (2399 / 5000 : ℝ)
  firstTail : ∀ {c : ℝ}, (1485 / 248 : ℝ) ≤ c →
    2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) < (1 / 198 : ℝ)
  secondLobe :
    1 / Real.sqrt (1 + (99 / 25 : ℝ)) *
        (1 + 2 * Real.exp
            (-((320 / 297 : ℝ) * (99 / 25) * Real.pi ^ 2 /
              (2 * (1 + (99 / 25))))) /
          (1 - (Real.exp
            (-((320 / 297 : ℝ) * (99 / 25) * Real.pi ^ 2 /
              (2 * (1 + (99 / 25)))))) ^ 3)) <
      (58 / 125 : ℝ)
  secondTail : ∀ {c : ℝ}, (4752 / 985 : ℝ) ≤ c →
    2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) < (1 / 59 : ℝ)

/-- Reflected endpoint facts for the floor-73 diffuse profile at tilt `5/2`.
The three low bands expose the semantic scalar envelope; the high bands use
the general lobe theorem and need only their endpoint inequalities. -/
structure SparseL2ThresholdDiffuseFloor73Endpoints : Prop where
  lowScalarFirst : ∀ {x p : ℝ},
    1 ≤ x → x ≤ 101 / 100 → (32 / 9) * x ≤ p →
    sparseScalarF ((5 / 2) * x) p < (107 / 200 : ℝ)
  lowScalarSecond : ∀ {x p : ℝ},
    (101 / 100 : ℝ) ≤ x → x ≤ 26 / 25 → (32 / 9) * x ≤ p →
    sparseScalarF ((5 / 2) * x) p < (107 / 200 : ℝ)
  lowScalarThird : ∀ {x p : ℝ},
    (26 / 25 : ℝ) ≤ x → x ≤ 11 / 10 → (32 / 9) * x ≤ p →
    sparseScalarF ((5 / 2) * x) p < (267 / 500 : ℝ)
  lowTailFirst : ∀ {c : ℝ}, (300 / 47 : ℝ) ≤ c →
    2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) < (7 / 2000 : ℝ)
  lowTailSecond : ∀ {c : ℝ}, (25 / 4 : ℝ) ≤ c →
    2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) < (1 / 250 : ℝ)
  lowTailThird : ∀ {c : ℝ}, (6 : ℝ) ≤ c →
    2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) < (1 / 200 : ℝ)
  highFirstLobe :
    1 / Real.sqrt (1 + (11 / 4 : ℝ)) *
        (1 + 2 * Real.exp
            (-((64 / 45 : ℝ) * (11 / 4) * Real.pi ^ 2 /
              (2 * (1 + (11 / 4))))) /
          (1 - (Real.exp
            (-((64 / 45 : ℝ) * (11 / 4) * Real.pi ^ 2 /
              (2 * (1 + (11 / 4)))))) ^ 3)) <
      (523 / 1000 : ℝ)
  highFirstTail : ∀ {c : ℝ}, (45 / 8 : ℝ) ≤ c →
    2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) < (3 / 400 : ℝ)
  highSecondLobe :
    1 / Real.sqrt (1 + (3 : ℝ)) *
        (1 + 2 * Real.exp
            (-((64 / 45 : ℝ) * 3 * Real.pi ^ 2 / (2 * (1 + 3)))) /
          (1 - (Real.exp
            (-((64 / 45 : ℝ) * 3 * Real.pi ^ 2 / (2 * (1 + 3))))) ^ 3)) <
      (253 / 500 : ℝ)
  highSecondTail : ∀ {c : ℝ}, (720 / 157 : ℝ) ≤ c →
    2 * Real.exp (-c) / (1 - (Real.exp (-c)) ^ 3) < (21 / 1000 : ℝ)

/-- Target-neutral retained-profile facts used by every dominant endpoint. -/
structure SparseL2ThresholdDominantRetainedGeometry : Prop where
  coarseCentral : ∀ {x : ℝ},
    3 / 2 ≤ x → x ≤ 11 / 5 →
    ThresholdNearCoarse128.semanticCoarseCentral x 1 < 12 / 25
  conditionedTail : ∀ {x : ℝ},
    3 / 2 ≤ x → x ≤ 11 / 5 →
    (ThresholdNearCoarse128.semanticInactiveTail x 1 +
      ThresholdNearCoarse128.semanticActiveTail x 1) / 2 < 1 / 20
  chordCentral : ∀ {x y : ℝ},
    3 / 2 ≤ x → x ≤ 11 / 5 → 4 / 5 ≤ y → y ≤ 1 →
    ThresholdNearChord128.semanticChordCentral x 1 y < 12 / 25

/-- Target-dependent finite-certificate outputs used by the dominant regime.
The cover geometry is reusable; only the row count, squared-norm floor, and final
real budget vary between endpoints. -/
structure SparseL2ThresholdDominantReplayAt
    (rows squaredNormFloor : ℕ) (highBudget : ℝ) : Prop where
  directCover : SparseL2ThresholdDominantDirectCoverAt
    rows squaredNormFloor highBudget
  cappedFourierCover : ∀ {B r : ℝ},
    2 ≤ B → B ≤ 3 → 9 * r ≤ B ^ 2 →
    ∃ cell : SparseThresholdDominant.CappedFourierNumeric128.Cell,
      cell ∈ SparseThresholdDominant.CappedFourierCover128.cells ∧
      (cell.lower : ℝ) ≤ B ∧ B ≤ cell.upper ∧
      r ≤ cell.thresholdUpper ∧
      (2 : ℝ) ≤ cell.lower ∧ (cell.upper : ℝ) ≤ 3 ∧
      Real.exp (squaredNormFloor * (9 / 4 : ℝ) *
          (cell.thresholdUpper : ℝ)) *
        thresholdDominantCappedFourierCellRow
          (cell.lower : ℝ) (cell.upper : ℝ) (9 / 4) ^ rows < highBudget
  singletonFourierCover : ∀ {B r : ℝ},
    2 ≤ B → B ≤ 5 / 2 → 9 * r ≤ B ^ 2 →
    ∃ cell : SparseThresholdDominant.SingletonFourierNumeric128.Cell,
      cell ∈ SparseThresholdDominant.SingletonFourierCover128.cells ∧
      (cell.lower : ℝ) ≤ B ∧ B ≤ cell.upper ∧
      r ≤ cell.thresholdUpper ∧
      (0 : ℝ) < cell.lower ∧
      Real.exp (squaredNormFloor * (9 / 4 : ℝ) *
          (cell.thresholdUpper : ℝ)) *
        thresholdDominantSingletonLowFourierCellRow
          (cell.lower : ℝ) (cell.upper : ℝ) (9 / 4) ^ rows < highBudget
  retainedGeometry : SparseL2ThresholdDominantRetainedGeometry
  retainedFinalRatio :
    Real.exp ((23 / 10 : ℝ) * squaredNormFloor * (2500 / 2401)) *
        (53 / 100 : ℝ) ^ rows < highBudget

/-- Target-dependent replay with independently chosen Fourier tilts.  Unlike
`SparseL2ThresholdDominantReplayAt`, its Fourier fields expose only their
semantic endpoint cells, so the certificate data type remains private to the
target replay. -/
structure SparseL2ThresholdDominantTiltedReplayAt
    (rows squaredNormFloor : ℕ) (singletonTilt cappedTilt highBudget : ℝ) : Prop where
  singletonTiltPositive : 0 < singletonTilt
  cappedTiltPositive : 0 < cappedTilt
  directCover : SparseL2ThresholdDominantDirectCoverAt
    rows squaredNormFloor highBudget
  cappedFourierCover : ∀ {B r : ℝ},
    2 ≤ B → B ≤ 3 → 9 * r ≤ B ^ 2 →
    ∃ L U thresholdUpper : ℝ,
      L ≤ B ∧ B ≤ U ∧ r ≤ thresholdUpper ∧
      2 ≤ L ∧ U ≤ 3 ∧
      Real.exp (squaredNormFloor * cappedTilt * thresholdUpper) *
        thresholdDominantCappedFourierCellRow L U cappedTilt ^ rows < highBudget
  singletonFourierCover : ∀ {B r : ℝ},
    2 ≤ B → B ≤ 5 / 2 → 9 * r ≤ B ^ 2 →
    ∃ L U thresholdUpper : ℝ,
      L ≤ B ∧ B ≤ U ∧ r ≤ thresholdUpper ∧
      2 ≤ L ∧ U ≤ 3 ∧
      Real.exp (squaredNormFloor * singletonTilt * thresholdUpper) *
        thresholdDominantSingletonPhaseFourierCellRow
          L U singletonTilt ^ rows < highBudget
  retainedGeometry : SparseL2ThresholdDominantRetainedGeometry
  retainedFinalRatio :
    Real.exp ((23 / 10 : ℝ) * squaredNormFloor * (2500 / 2401)) *
        (53 / 100 : ℝ) ^ rows < highBudget

/-- Finite-certificate outputs used by the dominant regime. -/
structure SparseL2ThresholdDominantReplay128 : Prop where
  directCover : ∀ (u r B : ℝ),
    0 ≤ u → u ≤ 1 / 2 → 0 ≤ r → r ≤ 2500 / 2401 → r ≤ 1 + u →
    2 ≤ B → 9 * r ≤ B ^ 2 →
    ∃ entry : SparseThresholdDominant.ConstantNumeric.Entry,
      entry.cell.Valid ∧
      (entry.cell.lower : ℝ) ≤ u ∧
      u ≤ (entry.cell.upper : ℝ) ∧
      r ≤ (entry.cell.thresholdUpper : ℝ) ∧
      (entry.cell.modulusLower : ℝ) ≤ B ∧
      thresholdDominantCellMajorant entry.cell.decode <
        (((187 / (200 * 2 ^ 128) : ℚ) : ℝ))
  cappedFourierCover : ∀ {B r : ℝ},
    2 ≤ B → B ≤ 3 → 9 * r ≤ B ^ 2 →
    ∃ cell : SparseThresholdDominant.CappedFourierNumeric128.Cell,
      cell ∈ SparseThresholdDominant.CappedFourierCover128.cells ∧
      (cell.lower : ℝ) ≤ B ∧ B ≤ cell.upper ∧
      r ≤ cell.thresholdUpper ∧
      SparseThresholdDominant.CappedFourierNumeric128.certifiedCheck cell = true
  singletonFourierCover : ∀ {B r : ℝ},
    2 ≤ B → B ≤ 5 / 2 → 9 * r ≤ B ^ 2 →
    ∃ cell : SparseThresholdDominant.SingletonFourierNumeric128.Cell,
      cell ∈ SparseThresholdDominant.SingletonFourierCover128.cells ∧
      (cell.lower : ℝ) ≤ B ∧ B ≤ cell.upper ∧
      r ≤ cell.thresholdUpper ∧
      SparseThresholdDominant.SingletonFourierNumeric128.certifiedCheck cell = true
  retainedCoarseCentral : ∀ {x : ℝ},
    3 / 2 ≤ x → x ≤ 11 / 5 →
    ThresholdNearCoarse128.semanticCoarseCentral x 1 < 12 / 25
  retainedConditionedTail : ∀ {x : ℝ},
    3 / 2 ≤ x → x ≤ 11 / 5 →
    (ThresholdNearCoarse128.semanticInactiveTail x 1 +
      ThresholdNearCoarse128.semanticActiveTail x 1) / 2 < 1 / 20
  retainedChordCentral : ∀ {x y : ℝ},
    3 / 2 ≤ x → x ≤ 11 / 5 → 4 / 5 ≤ y → y ≤ 1 →
    ThresholdNearChord128.semanticChordCentral x 1 y < 12 / 25
  retainedFinalRatio :
    Real.exp ((23 / 10 : ℝ) * 29 * (2500 / 2401)) *
        (53 / 100 : ℝ) ^ 256 <
      (187 / 200 : ℝ) * (2 : ℝ)⁻¹ ^ 128

theorem SparseL2ThresholdDominantReplay128.retainedGeometry
    (replay : SparseL2ThresholdDominantReplay128) :
    SparseL2ThresholdDominantRetainedGeometry where
  coarseCentral := replay.retainedCoarseCentral
  conditionedTail := replay.retainedConditionedTail
  chordCentral := replay.retainedChordCentral

/-- Finite-certificate outputs used by the near-dominant regime. -/
structure SparseL2ThresholdNearReplay128 : Prop where
  coarseEnvelope : ∀ {x a : ℝ},
    1 ≤ x → x ≤ 4901 / 2500 → 9 / 16 ≤ a → a ≤ 2401 / 2500 →
    ThresholdNearCoarse128.semanticEnvelope x a < 543 / 1000
  endpointFourFifths : ∀ {x a : ℝ},
    (1 : ℝ) ≤ x ∧ x ≤ 4901 / 2500 →
    (9 / 16 : ℝ) ≤ a ∧ a ≤ 2401 / 2500 →
    ThresholdNearChord128.semanticEnvelope x a (4 / 5) <
      (ThresholdNearChord128.endpointCap128 : ℚ)
  endpointSeventeenTwentieths : ∀ {x a : ℝ},
    (1 : ℝ) ≤ x ∧ x ≤ 4901 / 2500 →
    (9 / 16 : ℝ) ≤ a ∧ a ≤ 2401 / 2500 →
    ThresholdNearChord128.semanticEnvelope x a (17 / 20) <
      (ThresholdNearChord128.endpointCap128 : ℚ)
  endpointNineTenths : ∀ {x a : ℝ},
    (1 : ℝ) ≤ x ∧ x ≤ 4901 / 2500 →
    (9 / 16 : ℝ) ≤ a ∧ a ≤ 2401 / 2500 →
    ThresholdNearChord128.semanticEnvelope x a (9 / 10) <
      (ThresholdNearChord128.endpointCap128 : ℚ)
  endpointNineteenTwentieths : ∀ {x a : ℝ},
    (1 : ℝ) ≤ x ∧ x ≤ 4901 / 2500 →
    (9 / 16 : ℝ) ≤ a ∧ a ≤ 2401 / 2500 →
    ThresholdNearChord128.semanticEnvelope x a (19 / 20) <
      (ThresholdNearChord128.endpointCap128 : ℚ)
  endpointOne : ∀ {x a : ℝ},
    (1 : ℝ) ≤ x ∧ x ≤ 4901 / 2500 →
    (9 / 16 : ℝ) ≤ a ∧ a ≤ 2401 / 2500 →
    ThresholdNearChord128.semanticEnvelope x a 1 <
      (ThresholdNearChord128.endpointCap128 : ℚ)
  curvature : ∀ {x a y : ℝ},
    (1 : ℝ) ≤ x ∧ x ≤ 4901 / 2500 →
    (9 / 16 : ℝ) ≤ a ∧ a ≤ 2401 / 2500 →
    (4 / 5 : ℝ) ≤ y ∧ y ≤ 1 →
    -(81 / 20 : ℝ) < ThresholdNearChord128.semanticChordCentralSecond x a y

end CertifiedJL.CertificateContracts
