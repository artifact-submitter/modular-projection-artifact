/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Soundness.ThresholdNearChordCover128

/-! # Fixed endpoint certificates for semiconvex interpolation -/

namespace CertifiedJL
namespace ThresholdNearChord128

/-- The endpoint budget leaves exactly the semiconvex defect `81/64000`
below the locked row cap `681/1250`. -/
def endpointCap128 : ℚ := 173931 / 320000

def endpointCheck128 (cell : Cell) : Bool :=
  safeCheck cell && Interval.upperLTCheck (envelope cell) endpointCap128

def endpointPlanCheck128 : Cell → Plan → Bool
  | cell, .leaf => endpointCheck128 cell
  | cell, .splitX left right =>
      endpointPlanCheck128 (leftX cell) left && endpointPlanCheck128 (rightX cell) right
  | cell, .splitA left right =>
      endpointPlanCheck128 (leftA cell) left && endpointPlanCheck128 (rightA cell) right
  | cell, .splitY left right =>
      endpointPlanCheck128 (leftY cell) left && endpointPlanCheck128 (rightY cell) right

def endpointRefine128 : ℕ → Bool → Cell → Plan
  | 0, _, _ => .leaf
  | depth + 1, splitXNext, cell =>
      if endpointCheck128 cell then .leaf
      else if splitXNext then
        .splitX (endpointRefine128 depth false (leftX cell))
          (endpointRefine128 depth false (rightX cell))
      else
        .splitA (endpointRefine128 depth true (leftA cell))
          (endpointRefine128 depth true (rightA cell))

theorem semanticEnvelope_lt_endpointCap128_of_endpointCheck128
    (cell : Cell) {x a y : ℝ}
    (hcell : (cell.xLower : ℝ) ≤ x ∧ x ≤ cell.xUpper ∧
      (cell.aLower : ℝ) ≤ a ∧ a ≤ cell.aUpper ∧
      (cell.yLower : ℝ) ≤ y ∧ y ≤ cell.yUpper)
    (hcheck : endpointCheck128 cell = true) :
    semanticEnvelope x a y < (endpointCap128 : ℚ) := by
  have hc : safeCheck cell = true ∧
      Interval.upperLTCheck (envelope cell) endpointCap128 = true := by
    simpa only [endpointCheck128, Bool.and_eq_true] using hcheck
  have hsafety : chordSafeCheck cell = true ∧
      ThresholdNearCoarse128.safeCheck (coarseCell cell) = true := by
    simpa only [safeCheck, Bool.and_eq_true] using hc.1
  have hcontains := envelope_contains_semantic cell hcell
    (chordSafeCheck_sound hsafety.1)
    (ThresholdNearCoarse128.safeCheck_sound hsafety.2)
  exact Interval.lt_of_contains_of_upperLTCheck hcontains hc.2

private theorem and_check {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by simpa only [Bool.and_eq_true] using h

theorem semanticEnvelope_lt_endpointCap128_of_planCheck
    (cell : Cell) (plan : Plan) {x a y : ℝ}
    (hcell : (cell.xLower : ℝ) ≤ x ∧ x ≤ cell.xUpper ∧
      (cell.aLower : ℝ) ≤ a ∧ a ≤ cell.aUpper ∧
      (cell.yLower : ℝ) ≤ y ∧ y ≤ cell.yUpper)
    (hcheck : endpointPlanCheck128 cell plan = true) :
    semanticEnvelope x a y < (endpointCap128 : ℚ) := by
  induction plan generalizing cell with
  | leaf =>
      exact semanticEnvelope_lt_endpointCap128_of_endpointCheck128 cell hcell hcheck
  | splitX left right ihLeft ihRight =>
      have hc := and_check hcheck
      by_cases hx : x ≤ (xMid cell : ℝ)
      · exact ihLeft (cell := leftX cell)
          ⟨hcell.1, hx, hcell.2.2.1, hcell.2.2.2.1,
            hcell.2.2.2.2.1, hcell.2.2.2.2.2⟩ hc.1
      · exact ihRight (cell := rightX cell)
          ⟨le_of_not_ge hx, hcell.2.1, hcell.2.2.1,
            hcell.2.2.2.1, hcell.2.2.2.2.1, hcell.2.2.2.2.2⟩ hc.2
  | splitA left right ihLeft ihRight =>
      have hc := and_check hcheck
      by_cases ha : a ≤ (aMid cell : ℝ)
      · exact ihLeft (cell := leftA cell)
          ⟨hcell.1, hcell.2.1, hcell.2.2.1, ha,
            hcell.2.2.2.2.1, hcell.2.2.2.2.2⟩ hc.1
      · exact ihRight (cell := rightA cell)
          ⟨hcell.1, hcell.2.1, le_of_not_ge ha,
            hcell.2.2.2.1, hcell.2.2.2.2.1, hcell.2.2.2.2.2⟩ hc.2
  | splitY left right ihLeft ihRight =>
      have hc := and_check hcheck
      by_cases hy : y ≤ (yMid cell : ℝ)
      · exact ihLeft (cell := leftY cell)
          ⟨hcell.1, hcell.2.1, hcell.2.2.1,
            hcell.2.2.2.1, hcell.2.2.2.2.1, hy⟩ hc.1
      · exact ihRight (cell := rightY cell)
          ⟨hcell.1, hcell.2.1, hcell.2.2.1,
            hcell.2.2.2.1, le_of_not_ge hy, hcell.2.2.2.2.2⟩ hc.2

def endpointCell128 (y : ℚ) : Cell where
  xLower := 1
  xUpper := 4901 / 2500
  aLower := 9 / 16
  aUpper := 2401 / 2500
  yLower := y
  yUpper := y

def endpointUnitPass128 (unit : Cell × Plan) : Bool :=
  endpointPlanCheck128 unit.1 unit.2

end ThresholdNearChord128
end CertifiedJL
