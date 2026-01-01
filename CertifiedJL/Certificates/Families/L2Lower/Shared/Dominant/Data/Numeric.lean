/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import Mathlib.Data.Nat.Choose.Basic
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ScalarNumeric
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.Cell

/-!
# Executable public-threshold dominant-cell arithmetic

This evaluator keeps the residual endpoint, public threshold endpoint, and
modulus endpoint independent. Its interval primitives live in
`DominantNumeric` because they are shared by the threshold certificate
families.
-/

namespace CertifiedJL
namespace SparseThresholdDominant
namespace Numeric

abbrev DecodedCell := ThresholdDominantCellRowBounds
abbrev DInterval := DominantNumeric.DInterval

open DominantNumeric

/-- Exact algebraic match between the independent modulus endpoint and the
row evaluator's square-root endpoint. -/
def ModulusMatched (cell : DecodedCell) : Prop :=
  3 ≤ cell.modulusLower ∧
    cell.modulusLower ^ 2 = 9 * (1 + cell.lower)

def bInterval (cell : DecodedCell) : DInterval :=
  rat cell.modulusLower

def alphaInterval (cell : DecodedCell) (z : ℚ) : DInterval :=
  rat (z / (1 + z * cell.upper))

def inactiveWrap (cell : DecodedCell) (z : ℚ) : DInterval :=
  let B := bInterval cell
  let alpha := alphaInterval cell z
  let exponent := -(alpha * powNat B 2)
  rat 2 * div (expUpper exponent)
    (rat 1 - expUpper (rat 3 * exponent))

def activeWrap (cell : DecodedCell) (z : ℚ) : DInterval :=
  let B := bInterval cell
  let alpha := alphaInterval cell z
  let minusExponent := -(alpha * powNat (B - rat 1) 2)
  let minusRatioExponent :=
    -(alpha * (rat 3 * powNat B 2 - rat 2 * B))
  let plusExponent := -(alpha * powNat (B + rat 1) 2)
  let plusRatioExponent :=
    -(alpha * (rat 3 * powNat B 2 + rat 2 * B))
  div (expUpper minusExponent)
      (rat 1 - expUpper minusRatioExponent) +
    div (expUpper plusExponent)
      (rat 1 - expUpper plusRatioExponent)

def inactiveRow (cell : DecodedCell) (z : ℚ) : DInterval :=
  let sLower := rat (z * cell.lower)
  let sUpper := rat (z * cell.upper)
  let thetaExponent := -(powNat piInterval 2 *
    div (rat 1) (rat 1 + sUpper))
  let theta := expUpper thetaExponent
  div (rat 1) (rat 1 + sLower).sqrt *
      (rat 1 + div (rat 2 * theta) (rat 1 - powNat theta 3)) +
    inactiveWrap cell z

def activeRow (cell : DecodedCell) (z : ℚ) : DInterval :=
  let sUpper := rat (z * cell.upper)
  expUpper (-(div (rat z) (rat 1 + sUpper))) *
      rat (DominantNumeric.rhoRat cell.lower cell.upper z) +
    activeWrap cell z

def growthUpper (cell : DecodedCell) (z : ℚ) (k : ℕ) : DInterval :=
  powNat
    (expUpper (rat (29 * z * cell.thresholdUpper /
      (k * DominantNumeric.growthScale))))
    DominantNumeric.growthScale

def inactiveRowSafeCheck (cell : DecodedCell) (z : ℚ) : Bool :=
  decide (0 < (rat 1 + rat (z * cell.upper)).lo ∧
    (-(powNat piInterval 2 *
      div (rat 1) (rat 1 + rat (z * cell.upper)))).upperRat ≤ 1 ∧
    0 ≤ (rat 1 + rat (z * cell.lower)).lo ∧
    0 < (rat 1 + rat (z * cell.lower)).sqrt.lo ∧
    0 < (rat 1 - powNat
      (expUpper (-(powNat piInterval 2 *
        div (rat 1) (rat 1 + rat (z * cell.upper))))) 3).lo ∧
    (-(alphaInterval cell z * powNat (bInterval cell) 2)).upperRat ≤ 1 ∧
    (rat 3 *
      (-(alphaInterval cell z * powNat (bInterval cell) 2))).upperRat ≤ 1 ∧
    0 < (rat 1 - expUpper
      (rat 3 * (-(alphaInterval cell z * powNat (bInterval cell) 2)))).lo)

def activeRowSafeCheck (cell : DecodedCell) (z : ℚ) : Bool :=
  decide (0 < (rat 1 + rat (z * cell.upper)).lo ∧
    (-(div (rat z) (rat 1 + rat (z * cell.upper)))).upperRat ≤ 1 ∧
    (-(alphaInterval cell z *
      powNat (bInterval cell - rat 1) 2)).upperRat ≤ 1 ∧
    (-(alphaInterval cell z *
      (rat 3 * powNat (bInterval cell) 2 -
        rat 2 * bInterval cell))).upperRat ≤ 1 ∧
    (-(alphaInterval cell z *
      powNat (bInterval cell + rat 1) 2)).upperRat ≤ 1 ∧
    (-(alphaInterval cell z *
      (rat 3 * powNat (bInterval cell) 2 +
        rat 2 * bInterval cell))).upperRat ≤ 1 ∧
    0 < (rat 1 - expUpper (-(alphaInterval cell z *
      (rat 3 * powNat (bInterval cell) 2 -
        rat 2 * bInterval cell)))).lo ∧
    0 < (rat 1 - expUpper (-(alphaInterval cell z *
      (rat 3 * powNat (bInterval cell) 2 +
        rat 2 * bInterval cell)))).lo)

def conditionalSafeCheck (cell : DecodedCell) (k : Fin 257) : Bool :=
  let z := cell.z k
  if (k : ℕ) < 29 ∨ z = 0 then true
  else
    decide ((rat (29 * z * cell.thresholdUpper /
      ((k : ℕ) * DominantNumeric.growthScale))).upperRat ≤ 1) &&
      (inactiveRowSafeCheck cell z && activeRowSafeCheck cell z)

def cellNumericSafeCheck (cell : DecodedCell) : Bool :=
  (List.ofFn fun k : Fin 257 => conditionalSafeCheck cell k).all id

def conditionalMajorant
    (cell : DecodedCell) (k : Fin 257) : DInterval :=
  let z := cell.z k
  if (k : ℕ) < 29 then rat 0
  else if z = 0 then rat 1
  else
    minInterval (rat 1)
      (powNat (growthUpper cell z (k : ℕ) * activeRow cell z) (k : ℕ) *
        powNat (inactiveRow cell z) (256 - (k : ℕ)))

def majorantUpper (cell : DecodedCell) : DInterval :=
  (List.ofFn fun k : Fin 257 =>
      rat (((256 : ℕ).choose (k : ℕ) : ℚ) / 2 ^ 256) *
        conditionalMajorant cell k).foldl (· + ·) (rat 0)

def localNumericCheckAt (cell : DecodedCell) (budget : ℚ) : Bool :=
  Interval.upperLTCheck (majorantUpper cell) budget

def localCertifiedCheckAt (cell : DecodedCell) (budget : ℚ) : Bool :=
  cellNumericSafeCheck cell && localNumericCheckAt cell budget

end Numeric
end SparseThresholdDominant
end CertifiedJL
