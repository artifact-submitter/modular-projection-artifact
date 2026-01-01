/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Soundness.ThresholdNearChordCover128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Soundness.ThresholdNearChordCurvatureSoundness128

/-! # Gap-free curvature cover for the high Holder-weight band -/

namespace CertifiedJL
namespace ThresholdNearChordCurvature128

open ThresholdNearChord128

def curvaturePlanCheck : Cell → Plan → Bool
  | cell, .leaf => curvatureCheck cell
  | cell, .splitX left right =>
      curvaturePlanCheck (leftX cell) left && curvaturePlanCheck (rightX cell) right
  | cell, .splitA left right =>
      curvaturePlanCheck (leftA cell) left && curvaturePlanCheck (rightA cell) right
  | cell, .splitY left right =>
      curvaturePlanCheck (leftY cell) left && curvaturePlanCheck (rightY cell) right

private theorem and_check {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by simpa only [Bool.and_eq_true] using h

theorem semanticChordCentralSecond_gt_neg_81_div_20_of_planCheck
    (cell : Cell) (plan : Plan) {x a y : ℝ}
    (hcell : (cell.xLower : ℝ) ≤ x ∧ x ≤ cell.xUpper ∧
      (cell.aLower : ℝ) ≤ a ∧ a ≤ cell.aUpper ∧
      (cell.yLower : ℝ) ≤ y ∧ y ≤ cell.yUpper)
    (hcheck : curvaturePlanCheck cell plan = true) :
    -(81 / 20 : ℝ) < semanticChordCentralSecond x a y := by
  induction plan generalizing cell with
  | leaf =>
      exact semanticChordCentralSecond_gt_neg_81_div_20_of_curvatureCheck
        cell hcell hcheck
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

def fullCurvatureCell : Cell where
  xLower := 1
  xUpper := 4901 / 2500
  aLower := 9 / 16
  aUpper := 2401 / 2500
  yLower := 4 / 5
  yUpper := 1

/-- The complete three-dimensional cover has only nine leaves. -/
def fullCurvaturePlan : Plan :=
  .splitX
    (.splitA
      (.splitY (.splitX .leaf .leaf) .leaf)
      (.splitY (.splitX .leaf .leaf) (.splitX .leaf .leaf)))
    (.splitA .leaf .leaf)

theorem fullCurvaturePlan_check :
    curvaturePlanCheck fullCurvatureCell fullCurvaturePlan = true := by
  decide +kernel

theorem semanticChordCentralSecond_gt_neg_81_div_20
    {x a y : ℝ}
    (hx : (1 : ℝ) ≤ x ∧ x ≤ 4901 / 2500)
    (ha : (9 / 16 : ℝ) ≤ a ∧ a ≤ 2401 / 2500)
    (hy : (4 / 5 : ℝ) ≤ y ∧ y ≤ 1) :
    -(81 / 20 : ℝ) < semanticChordCentralSecond x a y := by
  exact semanticChordCentralSecond_gt_neg_81_div_20_of_planCheck
    fullCurvatureCell fullCurvaturePlan
    (by simpa [fullCurvatureCell] using
      And.intro hx.1 (And.intro hx.2 (And.intro ha.1
        (And.intro ha.2 (And.intro hy.1 hy.2)))))
    fullCurvaturePlan_check

end ThresholdNearChordCurvature128
end CertifiedJL
