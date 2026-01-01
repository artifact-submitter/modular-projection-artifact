/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Data.ThresholdNearCoarseNumeric128

/-!
# Executable power-chord near-band envelope at 128 bits

For a residual Holder weight `y ∈ [1/2,1]`, the power chord reduces the
coupled moment to exact cosine powers two and four.  This file encloses that
closed expression together with the same exact conditioned modular tails as
the coarse branch.
-/

namespace CertifiedJL
namespace ThresholdNearChord128

open ThresholdNearCoarse128

abbrev DInterval := ThresholdNearCoarse128.DInterval

def rat := ThresholdNearCoarse128.rat

instance : One DInterval := ⟨rat 1⟩

def div := ThresholdNearCoarse128.div
def powNat := ThresholdNearCoarse128.powNat
def expUpper := ThresholdNearCoarse128.expUpper

/-- A rational box in normalized total mass `x`, retained mass `a`, and one
normalized residual Holder weight `y`. -/
structure Cell where
  xLower : ℚ
  xUpper : ℚ
  aLower : ℚ
  aUpper : ℚ
  yLower : ℚ
  yUpper : ℚ
deriving DecidableEq, Repr

def xInterval (cell : Cell) : DInterval :=
  Interval.enclose ThresholdNearCoarse128.precision cell.xLower cell.xUpper

def aInterval (cell : Cell) : DInterval :=
  Interval.enclose ThresholdNearCoarse128.precision cell.aLower cell.aUpper

def yInterval (cell : Cell) : DInterval :=
  Interval.enclose ThresholdNearCoarse128.precision cell.yLower cell.yUpper

def aFreqSq (cell : Cell) : DInterval :=
  rat (23 / 20) * aInterval cell

def bFreqSq (cell : Cell) : DInterval :=
  rat (23 / 20) * (xInterval cell - aInterval cell) * yInterval cell

def aFreq (cell : Cell) : DInterval := (aFreqSq cell).sqrt
def bFreq (cell : Cell) : DInterval := (bFreqSq cell).sqrt

def expNeg (I : DInterval) : DInterval := expUpper (-I)

/-- Exact `E[cos²(AG)cos²(BG)]`. -/
def momentTwo (cell : Cell) : DInterval :=
  rat (1 / 4) *
    (rat 1 + expNeg (rat 2 * powNat (aFreq cell) 2) +
      expNeg (rat 2 * powNat (bFreq cell) 2) +
      rat (1 / 2) *
        (expNeg (rat 2 * powNat (aFreq cell + bFreq cell) 2) +
          expNeg (rat 2 * powNat (aFreq cell - bFreq cell) 2)))

def mixedMoment (cell : Cell) (frequencyMultiplier : ℚ) : DInterval :=
  let C := rat frequencyMultiplier * bFreq cell
  rat (1 / 2) * expNeg (rat (1 / 2) * powNat C 2) +
    rat (1 / 4) *
      (expNeg (rat (1 / 2) * powNat (C + rat 2 * aFreq cell) 2) +
        expNeg (rat (1 / 2) * powNat (C - rat 2 * aFreq cell) 2))

/-- Exact `E[cos²(AG)cos⁴(BG)]`. -/
def momentFour (cell : Cell) : DInterval :=
  rat (3 / 8) *
      (rat (1 / 2) * (rat 1 +
        expNeg (rat 2 * powNat (aFreq cell) 2))) +
    rat (1 / 2) * mixedMoment cell 2 +
    rat (1 / 8) * mixedMoment cell 4

def inverseY (cell : Cell) : DInterval := div (rat 1) (yInterval cell)

/-- Power-chord central moment. -/
def chordCentral (cell : Cell) : DInterval :=
  (rat 2 - inverseY cell) * momentTwo cell +
    (inverseY cell - rat 1) * momentFour cell

/-- Forget the Holder weight when evaluating the common conditioned tails. -/
def coarseCell (cell : Cell) : ThresholdNearCoarse128.Cell where
  xLower := cell.xLower
  xUpper := cell.xUpper
  aLower := cell.aLower
  aUpper := cell.aUpper

def inactiveTail (cell : Cell) : DInterval :=
  ThresholdNearCoarse128.inactiveTail (coarseCell cell)

def activeTail (cell : Cell) : DInterval :=
  ThresholdNearCoarse128.activeTail (coarseCell cell)

def envelope (cell : Cell) : DInterval :=
  chordCentral cell + rat (1 / 2) * (inactiveTail cell + activeTail cell)

def chordSafeCheck (cell : Cell) : Bool :=
  decide (
    0 ≤ (aInterval cell).lo ∧
    0 ≤ (aFreqSq cell).lo ∧
    0 ≤ (bFreqSq cell).lo ∧
    0 < (yInterval cell).lo ∧
    (∀ I ∈ [
      rat 2 * powNat (aFreq cell) 2,
      rat 2 * powNat (bFreq cell) 2,
      rat 2 * powNat (aFreq cell + bFreq cell) 2,
      rat 2 * powNat (aFreq cell - bFreq cell) 2,
      rat (1 / 2) * powNat (rat 2 * bFreq cell) 2,
      rat (1 / 2) * powNat (rat 2 * bFreq cell + rat 2 * aFreq cell) 2,
      rat (1 / 2) * powNat (rat 2 * bFreq cell - rat 2 * aFreq cell) 2,
      rat (1 / 2) * powNat (rat 4 * bFreq cell) 2,
      rat (1 / 2) * powNat (rat 4 * bFreq cell + rat 2 * aFreq cell) 2,
      rat (1 / 2) * powNat (rat 4 * bFreq cell - rat 2 * aFreq cell) 2],
      (-I).upperRat ≤ 1))

def safeCheck (cell : Cell) : Bool :=
  chordSafeCheck cell && ThresholdNearCoarse128.safeCheck (coarseCell cell)

end ThresholdNearChord128
end CertifiedJL
