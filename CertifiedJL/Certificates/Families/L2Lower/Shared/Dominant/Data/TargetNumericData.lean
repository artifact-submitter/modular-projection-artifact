/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Shared.Dominant.Data.ScalarNumeric

/-! Executable target arithmetic, independent of probability soundness. -/
namespace CertifiedJL.SparseThresholdDominant.TargetNumeric
open DominantNumeric

abbrev DInterval := DominantNumeric.DInterval

/-- Combine separately replayed target-independent and target-dependent list
checks without evaluating either side again. -/
theorem all_and_eq_true_of_all {α : Type*} (items : List α)
    (shared target : α → Bool)
    (hshared : items.all shared = true) (htarget : items.all target = true) :
    items.all (fun item => shared item && target item) = true := by
  rw [List.all_eq_true] at hshared htarget ⊢
  intro item hmem
  simp only [hshared item hmem, htarget item hmem, Bool.true_and]

def growthIntervalAt (rows squaredNormFloor : ℕ) (z thresholdUpper : ℚ) : DInterval :=
  powNat (expUpper (rat (squaredNormFloor * z * thresholdUpper / rows))) rows

def finalUpperRatAt (rows squaredNormFloor : ℕ)
    (z thresholdUpper rowUpper : ℚ) : ℚ :=
  (growthIntervalAt rows squaredNormFloor z thresholdUpper).upperRat * rowUpper ^ rows

def certifiedCheckAt (rows squaredNormFloor : ℕ) (z thresholdUpper rowUpper budget : ℚ) :
    Bool :=
  decide (
    0 < rows ∧
    (rat (squaredNormFloor * z * thresholdUpper / rows)).upperRat ≤ 1 ∧
    finalUpperRatAt rows squaredNormFloor z thresholdUpper rowUpper < budget)

/-- Exact target arithmetic for a rational squared-norm floor. -/
def growthIntervalAtRatio (rows : ℕ) (squaredNormFloor z thresholdUpper : ℚ) :
    DInterval :=
  powNat (expUpper (rat (squaredNormFloor * z * thresholdUpper / rows))) rows

def finalUpperRatAtRatio (rows : ℕ) (squaredNormFloor z thresholdUpper rowUpper : ℚ) :
    ℚ :=
  (growthIntervalAtRatio rows squaredNormFloor z thresholdUpper).upperRat *
    rowUpper ^ rows

/-- Executable target check supporting any nonnegative rational floor. -/
def certifiedCheckAtRatio (rows : ℕ)
    (squaredNormFloor z thresholdUpper rowUpper budget : ℚ) : Bool :=
  decide (
    0 < rows ∧ 0 ≤ squaredNormFloor ∧
    (rat (squaredNormFloor * z * thresholdUpper / rows)).upperRat ≤ 1 ∧
    finalUpperRatAtRatio rows squaredNormFloor z thresholdUpper rowUpper < budget)

end CertifiedJL.SparseThresholdDominant.TargetNumeric
