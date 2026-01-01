/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Soundness.ThresholdNearCoarseSoundness128
import CertifiedJL.Certificates.Families.L2Lower.Rows256Bits128.Near.Data.ThresholdNearCoarsePlan128

/-! # Gap-free adaptive cover for the coarse near-band envelope -/

namespace CertifiedJL
namespace ThresholdNearCoarse128


private theorem and_check {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  simpa only [Bool.and_eq_true] using h

/-- A passing adaptive plan certifies every point of its root rectangle.
There is no sampling assumption: recursion chooses a child using the exact
real comparison with the rational midpoint, and both children include the
seam. -/
theorem semanticEnvelope_lt_of_planCheck
    (cell : Cell) (plan : Plan) {x a : ℝ}
    (hcell : (cell.xLower : ℝ) ≤ x ∧ x ≤ cell.xUpper ∧
      (cell.aLower : ℝ) ≤ a ∧ a ≤ cell.aUpper)
    (hcheck : planCheck cell plan = true) :
    semanticEnvelope x a < 543 / 1000 := by
  induction plan generalizing cell with
  | leaf =>
      exact semanticEnvelope_lt_of_certifiedCheck cell hcell hcheck
  | splitX left right ihLeft ihRight =>
      have hc := and_check hcheck
      by_cases hx : x ≤ (xMid cell : ℝ)
      · apply ihLeft (cell := leftX cell)
        · exact ⟨hcell.1, hx, hcell.2.2.1, hcell.2.2.2⟩
        · exact hc.1
      · apply ihRight (cell := rightX cell)
        · exact ⟨le_of_not_ge hx, hcell.2.1, hcell.2.2.1, hcell.2.2.2⟩
        · exact hc.2
  | splitA left right ihLeft ihRight =>
      have hc := and_check hcheck
      by_cases ha : a ≤ (aMid cell : ℝ)
      · apply ihLeft (cell := leftA cell)
        · exact ⟨hcell.1, hcell.2.1, hcell.2.2.1, ha⟩
        · exact hc.1
      · apply ihRight (cell := rightA cell)
        · exact ⟨hcell.1, hcell.2.1, le_of_not_ge ha, hcell.2.2.2⟩
        · exact hc.2

end ThresholdNearCoarse128
end CertifiedJL
