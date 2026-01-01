/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Transcendental.Exponential.DyadicExpData
import CertifiedJL.Arithmetic.Interval.ReflectionData
import CertifiedJL.Arithmetic.Transcendental.SquareRoot.SqrtData

/-!
# Executable coarse near-band envelope at 128 bits

This file contains only the exact interval evaluator for the low residual
Holder-weight branch of the public-threshold near band.  Its semantic
soundness and exhaustive domain cover are proved separately.
-/

namespace CertifiedJL
namespace ThresholdNearCoarse128

/-- Fractional precision of the reflected envelope. -/
def precision : ℕ := 192

/-- Repeated-squaring depth for every exponential enclosure. -/
def expSquarings : ℕ := 16

abbrev DInterval := Interval precision

def rat (x : ℚ) : DInterval := Interval.ofRat precision x

instance : One DInterval := ⟨rat 1⟩

def div (I J : DInterval) : DInterval := I * J.reciprocal

def powNat (I : DInterval) (n : ℕ) : DInterval := npowBinRec n I

def expUpper (I : DInterval) : DInterval :=
  DyadicExp.ofIntervalUpper precision I expSquarings

/-- Six-decimal theorem-backed enclosure of `π`. -/
def piInterval : DInterval :=
  Interval.enclose precision (3141592 / 1000000) (3141593 / 1000000)

/-- One rational rectangle in `(x,a)`, where `x=‖w‖²/b²` and
`a=wᵢ²/b²`. -/
structure Cell where
  xLower : ℚ
  xUpper : ℚ
  aLower : ℚ
  aUpper : ℚ
deriving DecidableEq, Repr

def xInterval (cell : Cell) : DInterval :=
  Interval.enclose precision cell.xLower cell.xUpper

def aInterval (cell : Cell) : DInterval :=
  Interval.enclose precision cell.aLower cell.aUpper

def dInterval (cell : Cell) : DInterval :=
  rat 1 + rat (23 / 10) * (xInterval cell - aInterval cell)

def tInterval (cell : Cell) : DInterval :=
  div (rat (23 / 10) * aInterval cell) (dInterval cell)

def thetaInterval (cell : Cell) : DInterval :=
  expUpper (-(div (rat (5 / 4) * powNat piInterval 2) (dInterval cell)))

def coarseCentral (cell : Cell) : DInterval :=
  rat (2⁻¹ : ℚ) * (rat 1 + expUpper (-(tInterval cell))) *
      div (rat 1) (dInterval cell).sqrt *
    (rat 1 + div (rat 2 * thetaInterval cell)
      (rat 1 - powNat (thetaInterval cell) 3))

def rhoInterval (cell : Cell) : DInterval :=
  expUpper (-(div (rat (207 / 10)) (dInterval cell)))

def inactiveTail (cell : Cell) : DInterval :=
  div (rat 2 * rhoInterval cell)
    (rat 1 - powNat (rhoInterval cell) 3)

def mInterval (cell : Cell) : DInterval :=
  div (rat 3) (aInterval cell).sqrt

def activeMinusExponent (cell : Cell) : DInterval :=
  -(tInterval cell * powNat (mInterval cell - rat 1) 2)

def activeMinusRatioExponent (cell : Cell) : DInterval :=
  -(tInterval cell *
    (rat 3 * powNat (mInterval cell) 2 - rat 2 * mInterval cell))

def activePlusExponent (cell : Cell) : DInterval :=
  -(tInterval cell * powNat (mInterval cell + rat 1) 2)

def activePlusRatioExponent (cell : Cell) : DInterval :=
  -(tInterval cell *
    (rat 3 * powNat (mInterval cell) 2 + rat 2 * mInterval cell))

def activeTail (cell : Cell) : DInterval :=
  div (expUpper (activeMinusExponent cell))
      (rat 1 - expUpper (activeMinusRatioExponent cell)) +
    div (expUpper (activePlusExponent cell))
      (rat 1 - expUpper (activePlusRatioExponent cell))

def conditionedTail (cell : Cell) : DInterval :=
  rat (2⁻¹ : ℚ) * (inactiveTail cell + activeTail cell)

/-- Complete coarse-lobe plus conditioned-image envelope on one cell. -/
def envelope (cell : Cell) : DInterval :=
  coarseCentral cell + conditionedTail cell

/-- All raw sign and exponential-range obligations used by soundness. -/
def safeCheck (cell : Cell) : Bool :=
  decide (
    0 ≤ (aInterval cell).lo ∧
    0 < (aInterval cell).sqrt.lo ∧
    0 < (dInterval cell).lo ∧
    0 < (dInterval cell).sqrt.lo ∧
    (-(tInterval cell)).upperRat ≤ 1 ∧
    (-(div (rat (5 / 4) * powNat piInterval 2)
      (dInterval cell))).upperRat ≤ 1 ∧
    0 < (rat 1 - powNat (thetaInterval cell) 3).lo ∧
    (-(div (rat (207 / 10)) (dInterval cell))).upperRat ≤ 1 ∧
    0 < (rat 1 - powNat (rhoInterval cell) 3).lo ∧
    (activeMinusExponent cell).upperRat ≤ 1 ∧
    (activeMinusRatioExponent cell).upperRat ≤ 1 ∧
    (activePlusExponent cell).upperRat ≤ 1 ∧
    (activePlusRatioExponent cell).upperRat ≤ 1 ∧
    0 < (rat 1 - expUpper (activeMinusRatioExponent cell)).lo ∧
    0 < (rat 1 - expUpper (activePlusRatioExponent cell)).lo)

def certifiedCheck (cell : Cell) : Bool :=
  safeCheck cell && Interval.upperLTCheck (envelope cell) (543 / 1000)

end ThresholdNearCoarse128
end CertifiedJL
