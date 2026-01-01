/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ScalarNumeric
import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.TargetNumericData

/-! Executable Fourier-cell arithmetic, independent of probability soundness. -/
namespace CertifiedJL.SparseThresholdDominant.SingletonFourierNumeric128
open DominantNumeric

abbrev DInterval := DominantNumeric.DInterval

structure Cell where
  lower : ℚ
  upper : ℚ
  thresholdUpper : ℚ
  rowUpper : ℚ

def z : ℚ := 9 / 4

def cUpper (cell : Cell) : DInterval :=
  powNat piInterval 2 *
    div (rat 1) (rat z * powNat (rat cell.upper) 2)

def piDivUpper (cell : Cell) : DInterval :=
  div piInterval (rat cell.upper)

def firstMode (cell : Cell) : DInterval :=
  expUpper (-(powNat (piDivUpper cell) 2 * rat (3 / 2)))

def prefactor (cell : Cell) : DInterval :=
  div (rat 1)
    (div (rat z * powNat (rat cell.lower) 2) piInterval).sqrt

def rowInterval (cell : Cell) : DInterval :=
  let c := cUpper cell
  let modeOne := expUpper (-c) * firstMode cell
  let modeTwo := expUpper (-(rat 4 * c))
  let tail := div (expUpper (-(rat 9 * c)))
    (rat 1 - expUpper (-(rat 7 * c)))
  prefactor cell * (rat 1 + rat 2 * (modeOne + modeTwo) + rat 2 * tail)

def growthInterval (cell : Cell) : DInterval :=
  powNat (expUpper (rat (29 * z * cell.thresholdUpper / 256))) 256

def finalUpperRat (cell : Cell) : ℚ :=
  (growthInterval cell).upperRat * cell.rowUpper ^ 256

def safeCheck (cell : Cell) : Bool :=
  decide (
    2 ≤ cell.lower ∧ cell.lower ≤ cell.upper ∧ cell.upper ≤ 5 / 2 ∧
    0 ≤ cell.thresholdUpper ∧ 0 ≤ cell.rowUpper ∧
    0 < (rat cell.lower).lo ∧ 0 < (rat cell.upper).lo ∧
    0 < piInterval.lo ∧
    0 < (rat z * powNat (rat cell.upper) 2).lo ∧
    0 ≤ (div (rat z * powNat (rat cell.lower) 2) piInterval).lo ∧
    0 < (div (rat z * powNat (rat cell.lower) 2) piInterval).sqrt.lo ∧
    (-cUpper cell).upperRat ≤ 1 ∧
    (-(rat 4 * cUpper cell)).upperRat ≤ 1 ∧
    (-(rat 7 * cUpper cell)).upperRat ≤ 1 ∧
    (-(rat 9 * cUpper cell)).upperRat ≤ 1 ∧
    (-(powNat (piDivUpper cell) 2 * rat (3 / 2))).upperRat ≤ 1 ∧
    0 < (rat 1 - expUpper (-(rat 7 * cUpper cell))).lo ∧
    (rat (29 * z * cell.thresholdUpper / 256)).upperRat ≤ 1 ∧
    (rowInterval cell).upperRat ≤ cell.rowUpper)

def certifiedCheck (cell : Cell) : Bool :=
  safeCheck cell &&
    decide (finalUpperRat cell < 187 / (200 * 2 ^ 128))

theorem safeCheck_of_certifiedCheck {cell : Cell}
    (hcheck : certifiedCheck cell = true) : safeCheck cell = true := by
  have h : safeCheck cell = true ∧
      decide (finalUpperRat cell < 187 / (200 * 2 ^ 128)) = true := by
    simpa only [certifiedCheck, Bool.and_eq_true] using hcheck
  exact h.1

/-- Every certified cell lies in the low-singleton analytic modulus domain. -/
def certifiedCheckAt (rows squaredNormFloor : ℕ) (budget : ℚ)
    (cell : Cell) : Bool :=
  safeCheck cell && TargetNumeric.certifiedCheckAt rows squaredNormFloor z
    cell.thresholdUpper cell.rowUpper budget

end CertifiedJL.SparseThresholdDominant.SingletonFourierNumeric128
