/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Soundness.ThresholdNearChordSoundness128

/-!
# Lightweight retained-profile numerics for the dominant 128-bit branch

This file certifies the two real quantities that must be composed separately:
the coupled central moment and the conditioned modular-image tail.  Keeping the
certificates separate prevents the tail from being tensorized across 256 rows.

The normalized box is the one produced by retaining the dominant coordinate
and a compact residual subprofile:

* total mass `x ∈ [3/2, 11/5]`;
* dominant mass `a = 1`;
* residual Holder weight `y ∈ (0,1]`.

The coarse formula handles `y ≤ 4/5`; the power chord handles `y ≥ 4/5`.
Both central formulas are below `12/25`, while the conditioned image tail is
below `1/20`.
-/

namespace CertifiedJL
namespace ThresholdDominantRetained128

namespace Coarse

open ThresholdNearCoarse128

inductive Plan where
  | leaf
  | splitX (left right : Plan)
deriving DecidableEq, Repr

def xMid (cell : Cell) : ℚ := (cell.xLower + cell.xUpper) / 2
def leftX (cell : Cell) : Cell := { cell with xUpper := xMid cell }
def rightX (cell : Cell) : Cell := { cell with xLower := xMid cell }

def localCheck (cell : Cell) : Bool :=
  safeCheck cell && Interval.upperLTCheck (coarseCentral cell) (12 / 25)

def planCheck : Cell → Plan → Bool
  | cell, .leaf => localCheck cell
  | cell, .splitX left right =>
      planCheck (leftX cell) left && planCheck (rightX cell) right

def adaptiveRefine : ℕ → Cell → Plan
  | 0, _ => .leaf
  | depth + 1, cell =>
      if localCheck cell then .leaf
      else .splitX (adaptiveRefine depth (leftX cell))
        (adaptiveRefine depth (rightX cell))

def rootCell : Cell where
  xLower := 3 / 2
  xUpper := 11 / 5
  aLower := 1
  aUpper := 1

def verifiedPlan : Plan := adaptiveRefine 3 rootCell

private theorem verifiedPlan_check : planCheck rootCell verifiedPlan = true := by
  decide +kernel

private theorem and_check {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by simpa only [Bool.and_eq_true] using h

private theorem semanticCentral_lt_of_localCheck (cell : Cell) {x a : ℝ}
    (hcell : (cell.xLower : ℝ) ≤ x ∧ x ≤ cell.xUpper ∧
      (cell.aLower : ℝ) ≤ a ∧ a ≤ cell.aUpper)
    (hcheck : localCheck cell = true) :
    semanticCoarseCentral x a < 12 / 25 := by
  have hc : safeCheck cell = true ∧
      Interval.upperLTCheck (coarseCentral cell) (12 / 25) = true := by
    simpa only [localCheck, Bool.and_eq_true] using hcheck
  have hcontains := coarseCentral_contains_semantic cell hcell
    (safeCheck_sound hc.1)
  simpa using Interval.lt_of_contains_of_upperLTCheck hcontains hc.2

private theorem semanticCentral_lt_of_planCheck
    (cell : Cell) (plan : Plan) {x a : ℝ}
    (hcell : (cell.xLower : ℝ) ≤ x ∧ x ≤ cell.xUpper ∧
      (cell.aLower : ℝ) ≤ a ∧ a ≤ cell.aUpper)
    (hcheck : planCheck cell plan = true) :
    semanticCoarseCentral x a < 12 / 25 := by
  induction plan generalizing cell with
  | leaf => exact semanticCentral_lt_of_localCheck cell hcell hcheck
  | splitX left right ihLeft ihRight =>
      have hc : planCheck (leftX cell) left = true ∧
          planCheck (rightX cell) right = true := by
        simpa only [planCheck, Bool.and_eq_true] using hcheck
      by_cases hx : x ≤ (xMid cell : ℝ)
      · apply ihLeft (cell := leftX cell)
        · exact ⟨hcell.1, hx, hcell.2.2.1, hcell.2.2.2⟩
        · exact hc.1
      · apply ihRight (cell := rightX cell)
        · exact ⟨le_of_not_ge hx, hcell.2.1, hcell.2.2.1, hcell.2.2.2⟩
        · exact hc.2

/-- Uniform coarse central-moment cap on the retained box. -/
theorem semanticCoarseCentral_lt
    {x : ℝ} (hxLower : 3 / 2 ≤ x) (hxUpper : x ≤ 11 / 5) :
    semanticCoarseCentral x 1 < 12 / 25 := by
  apply semanticCentral_lt_of_planCheck rootCell verifiedPlan
  · simpa [rootCell] using And.intro hxLower
      (And.intro hxUpper (And.intro (le_refl (1 : ℝ)) (le_refl (1 : ℝ))))
  · exact verifiedPlan_check

private theorem tailCell_check :
    safeCheck rootCell = true ∧
      Interval.upperLTCheck (conditionedTail rootCell) (1 / 20) = true := by
  decide +kernel

/-- Uniform conditioned modular-image tail cap on the retained box. -/
theorem semanticConditionedTail_lt
    {x : ℝ} (hxLower : 3 / 2 ≤ x) (hxUpper : x ≤ 11 / 5) :
    (semanticInactiveTail x 1 + semanticActiveTail x 1) / 2 < 1 / 20 := by
  have hcell : (rootCell.xLower : ℝ) ≤ x ∧ x ≤ rootCell.xUpper ∧
      (rootCell.aLower : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ rootCell.aUpper := by
    simpa [rootCell] using And.intro hxLower
      (And.intro hxUpper (And.intro (le_refl (1 : ℝ)) (le_refl (1 : ℝ))))
  have hcontains := conditionedTail_contains_semantic rootCell
    (x := x) (a := 1) hcell
    (safeCheck_sound tailCell_check.1)
  simpa using Interval.lt_of_contains_of_upperLTCheck hcontains tailCell_check.2

end Coarse

namespace Chord

open ThresholdNearChord128

inductive Plan where
  | leaf
  | splitX (left right : Plan)
  | splitY (left right : Plan)
deriving DecidableEq, Repr

def xMid (cell : Cell) : ℚ := (cell.xLower + cell.xUpper) / 2
def yMid (cell : Cell) : ℚ := (cell.yLower + cell.yUpper) / 2
def leftX (cell : Cell) : Cell := { cell with xUpper := xMid cell }
def rightX (cell : Cell) : Cell := { cell with xLower := xMid cell }
def leftY (cell : Cell) : Cell := { cell with yUpper := yMid cell }
def rightY (cell : Cell) : Cell := { cell with yLower := yMid cell }

def localCheck (cell : Cell) : Bool :=
  chordSafeCheck cell && Interval.upperLTCheck (chordCentral cell) (12 / 25)

def planCheck : Cell → Plan → Bool
  | cell, .leaf => localCheck cell
  | cell, .splitX left right =>
      planCheck (leftX cell) left && planCheck (rightX cell) right
  | cell, .splitY left right =>
      planCheck (leftY cell) left && planCheck (rightY cell) right

/-- Alternate exact `x` and `y` bisections until every leaf passes. -/
def adaptiveRefine : ℕ → Bool → Cell → Plan
  | 0, _, _ => .leaf
  | depth + 1, splitXNext, cell =>
      if localCheck cell then .leaf
      else if splitXNext then
        .splitX (adaptiveRefine depth false (leftX cell))
          (adaptiveRefine depth false (rightX cell))
      else
        .splitY (adaptiveRefine depth true (leftY cell))
          (adaptiveRefine depth true (rightY cell))

def rootCell : Cell where
  xLower := 3 / 2
  xUpper := 11 / 5
  aLower := 1
  aUpper := 1
  yLower := 4 / 5
  yUpper := 1

def verifiedPlan : Plan := adaptiveRefine 7 true rootCell

private theorem verifiedPlan_check : planCheck rootCell verifiedPlan = true := by
  decide +kernel

private theorem and_check {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by simpa only [Bool.and_eq_true] using h

private theorem semanticCentral_lt_of_localCheck (cell : Cell) {x a y : ℝ}
    (hcell : (cell.xLower : ℝ) ≤ x ∧ x ≤ cell.xUpper ∧
      (cell.aLower : ℝ) ≤ a ∧ a ≤ cell.aUpper ∧
      (cell.yLower : ℝ) ≤ y ∧ y ≤ cell.yUpper)
    (hcheck : localCheck cell = true) :
    semanticChordCentral x a y < 12 / 25 := by
  have hc : chordSafeCheck cell = true ∧
      Interval.upperLTCheck (chordCentral cell) (12 / 25) = true := by
    simpa only [localCheck, Bool.and_eq_true] using hcheck
  have hcontains := chordCentral_contains_semantic cell hcell
    (chordSafeCheck_sound hc.1)
  simpa using Interval.lt_of_contains_of_upperLTCheck hcontains hc.2

private theorem semanticCentral_lt_of_planCheck
    (cell : Cell) (plan : Plan) {x a y : ℝ}
    (hcell : (cell.xLower : ℝ) ≤ x ∧ x ≤ cell.xUpper ∧
      (cell.aLower : ℝ) ≤ a ∧ a ≤ cell.aUpper ∧
      (cell.yLower : ℝ) ≤ y ∧ y ≤ cell.yUpper)
    (hcheck : planCheck cell plan = true) :
    semanticChordCentral x a y < 12 / 25 := by
  induction plan generalizing cell with
  | leaf => exact semanticCentral_lt_of_localCheck cell hcell hcheck
  | splitX left right ihLeft ihRight =>
      have hc : planCheck (leftX cell) left = true ∧
          planCheck (rightX cell) right = true := by
        simpa only [planCheck, Bool.and_eq_true] using hcheck
      by_cases hx : x ≤ (xMid cell : ℝ)
      · apply ihLeft (cell := leftX cell)
        · exact ⟨hcell.1, hx, hcell.2.2.1, hcell.2.2.2.1,
            hcell.2.2.2.2.1, hcell.2.2.2.2.2⟩
        · exact hc.1
      · apply ihRight (cell := rightX cell)
        · exact ⟨le_of_not_ge hx, hcell.2.1, hcell.2.2.1,
            hcell.2.2.2.1, hcell.2.2.2.2.1, hcell.2.2.2.2.2⟩
        · exact hc.2
  | splitY left right ihLeft ihRight =>
      have hc : planCheck (leftY cell) left = true ∧
          planCheck (rightY cell) right = true := by
        simpa only [planCheck, Bool.and_eq_true] using hcheck
      by_cases hy : y ≤ (yMid cell : ℝ)
      · apply ihLeft (cell := leftY cell)
        · exact ⟨hcell.1, hcell.2.1, hcell.2.2.1,
            hcell.2.2.2.1, hcell.2.2.2.2.1, hy⟩
        · exact hc.1
      · apply ihRight (cell := rightY cell)
        · exact ⟨hcell.1, hcell.2.1, hcell.2.2.1,
            hcell.2.2.2.1, le_of_not_ge hy, hcell.2.2.2.2.2⟩
        · exact hc.2

/-- Uniform power-chord central-moment cap on the retained box. -/
theorem semanticChordCentral_lt
    {x y : ℝ} (hxLower : 3 / 2 ≤ x) (hxUpper : x ≤ 11 / 5)
    (hyLower : 4 / 5 ≤ y) (hyUpper : y ≤ 1) :
    semanticChordCentral x 1 y < 12 / 25 := by
  apply semanticCentral_lt_of_planCheck rootCell verifiedPlan
  · simpa [rootCell] using And.intro hxLower
      (And.intro hxUpper (And.intro (le_refl (1 : ℝ))
        (And.intro (le_refl (1 : ℝ)) (And.intro hyLower hyUpper))))
  · exact verifiedPlan_check

end Chord
end ThresholdDominantRetained128
end CertifiedJL
