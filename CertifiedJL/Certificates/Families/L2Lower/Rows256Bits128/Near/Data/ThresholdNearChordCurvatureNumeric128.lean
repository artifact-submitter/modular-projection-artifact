/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Data.ThresholdNearChordNumeric128

/-! # Interval evaluator for the Holder-weight curvature -/

namespace CertifiedJL
namespace ThresholdNearChordCurvature128

open ThresholdNearChord128

abbrev DInterval := ThresholdNearChord128.DInterval
abbrev Cell := ThresholdNearChord128.Cell

def mode (cell : Cell) (m : ℚ) (offset : DInterval) : DInterval :=
  expNeg (rat (1 / 2) * powNat (rat m * bFreq cell + offset) 2)

def modePrime (cell : Cell) (m : ℚ) (offset : DInterval) : DInterval :=
  rat (-(1 / 2)) * mode cell m offset *
    div (rat m * bFreq cell * (rat m * bFreq cell + offset))
      (yInterval cell)

def modeSecond (cell : Cell) (m : ℚ) (offset : DInterval) : DInterval :=
  rat (1 / 4) * mode cell m offset *
    div (div
      (powNat (rat m * bFreq cell * (rat m * bFreq cell + offset)) 2 +
        rat m * bFreq cell * offset) (yInterval cell)) (yInterval cell)

/-- The exact second moment, written in the same mode basis as its derivatives. -/
def momentTwoValue (cell : Cell) : DInterval :=
  rat (1 / 4) *
    (rat 1 + expNeg (rat 2 * powNat (aFreq cell) 2) +
      mode cell 2 (rat 0) + rat (1 / 2) *
        (mode cell 2 (rat 2 * aFreq cell) +
          mode cell 2 (-(rat 2 * aFreq cell))))

def momentTwoPrime (cell : Cell) : DInterval :=
  rat (1 / 4) *
    (modePrime cell 2 (rat 0) + rat (1 / 2) *
      (modePrime cell 2 (rat 2 * aFreq cell) +
        modePrime cell 2 (-(rat 2 * aFreq cell))))

def momentTwoSecond (cell : Cell) : DInterval :=
  rat (1 / 4) *
    (modeSecond cell 2 (rat 0) + rat (1 / 2) *
      (modeSecond cell 2 (rat 2 * aFreq cell) +
        modeSecond cell 2 (-(rat 2 * aFreq cell))))

def mixedMomentPrime (cell : Cell) (m : ℚ) : DInterval :=
  rat (1 / 2) * modePrime cell m (rat 0) + rat (1 / 4) *
    (modePrime cell m (rat 2 * aFreq cell) +
      modePrime cell m (-(rat 2 * aFreq cell)))

def mixedMomentSecond (cell : Cell) (m : ℚ) : DInterval :=
  rat (1 / 2) * modeSecond cell m (rat 0) + rat (1 / 4) *
      (modeSecond cell m (rat 2 * aFreq cell) +
        modeSecond cell m (-(rat 2 * aFreq cell)))

/-- A mixed moment, written in the mode basis shared with its derivatives. -/
def mixedMomentValue (cell : Cell) (m : ℚ) : DInterval :=
  rat (1 / 2) * mode cell m (rat 0) + rat (1 / 4) *
    (mode cell m (rat 2 * aFreq cell) +
      mode cell m (-(rat 2 * aFreq cell)))

/-- The exact fourth moment, written in the mode basis shared with its derivatives. -/
def momentFourValue (cell : Cell) : DInterval :=
  rat (3 / 8) *
      (rat (1 / 2) * (rat 1 + expNeg (rat 2 * powNat (aFreq cell) 2))) +
    rat (1 / 2) * mixedMomentValue cell 2 +
    rat (1 / 8) * mixedMomentValue cell 4

def momentFourPrime (cell : Cell) : DInterval :=
  rat (1 / 2) * mixedMomentPrime cell 2 +
    rat (1 / 8) * mixedMomentPrime cell 4

def momentFourSecond (cell : Cell) : DInterval :=
  rat (1 / 2) * mixedMomentSecond cell 2 +
    rat (1 / 8) * mixedMomentSecond cell 4

def chordCentralSecond (cell : Cell) : DInterval :=
  (rat 2 - inverseY cell) * momentTwoSecond cell +
    (inverseY cell - rat 1) * momentFourSecond cell +
    rat 2 * inverseY cell * inverseY cell *
      (momentTwoPrime cell - momentFourPrime cell) -
    rat 2 * inverseY cell * inverseY cell * inverseY cell *
      (momentTwoValue cell - momentFourValue cell)

def curvatureExponentIntervals (cell : Cell) : List DInterval := [
  rat (1 / 2) * powNat (rat 2 * bFreq cell + rat 0) 2,
  rat (1 / 2) * powNat (rat 2 * bFreq cell + rat 2 * aFreq cell) 2,
  rat (1 / 2) * powNat (rat 2 * bFreq cell + -(rat 2 * aFreq cell)) 2,
  rat (1 / 2) * powNat (rat 4 * bFreq cell + rat 0) 2,
  rat (1 / 2) * powNat (rat 4 * bFreq cell + rat 2 * aFreq cell) 2,
  rat (1 / 2) * powNat (rat 4 * bFreq cell + -(rat 2 * aFreq cell)) 2]

def curvatureExponentSafeCheck (cell : Cell) : Bool :=
  decide (∀ I ∈ curvatureExponentIntervals cell, (-I).upperRat ≤ 1)

def curvatureCheck (cell : Cell) : Bool :=
  chordSafeCheck cell && curvatureExponentSafeCheck cell &&
    decide ((-(81 / 20) : ℚ) < (chordCentralSecond cell).lowerRat)

end ThresholdNearChordCurvature128
end CertifiedJL
