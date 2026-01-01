/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Quadrature.EndpointRiemann

/-!
# Left-endpoint Riemann-sum canaries

These examples exercise both affine and zero-based forms of the certified
left-endpoint upper sum for antitone functions.
-/

open MeasureTheory Set
open scoped BigOperators

namespace CertifiedJL.Tests.EndpointRiemann

open CertifiedJL

/-- A concrete decreasing affine function is bounded by its four-cell sum. -/
example :
    (∫ x : ℝ in 0..1, 1 - x) ≤
      ((1 : ℝ) / 4) *
        ∑ i ∈ Finset.range 4, (1 - ((1 : ℝ) / 4) * (i : ℕ)) := by
  apply intervalIntegral_le_leftRiemannSum (n := 4)
  · norm_num
  · norm_num
  · intro x _ y _ hxy
    linarith

/-- The affine API handles intervals whose left endpoint is not zero. -/
example :
    (∫ x : ℝ in (-2)..3, -x) ≤
      (((3 : ℝ) - (-2)) / 5) *
        ∑ i ∈ Finset.range 5,
          -((-2 : ℝ) + ((3 - (-2)) / 5) * (i : ℕ)) := by
  apply intervalIntegral_le_leftRiemannSum_of_le (n := 5)
  · norm_num
  · norm_num
  · intro x _ y _ hxy
    linarith

/-- Degenerate compact intervals reduce to equality. -/
example (f : ℝ → ℝ) :
    (∫ x : ℝ in 7..7, f x) ≤
      (((7 : ℝ) - 7) / 1) *
        ∑ i ∈ Finset.range 1,
          f (7 + ((7 - 7) / 1) * (i : ℕ)) := by
  have hanti : AntitoneOn f (Icc (7 : ℝ) 7) := by
    intro x hx y hy _
    have hx7 : x = 7 := le_antisymm hx.2 hx.1
    have hy7 : y = 7 := le_antisymm hy.2 hy.1
    simp [hx7, hy7]
  simpa only [Nat.cast_one] using
    intervalIntegral_le_leftRiemannSum_of_le
      (f := f) (A := (7 : ℝ)) (B := 7) 1 (by norm_num) (by norm_num) hanti

#print axioms intervalIntegral_le_leftRiemannSum_of_le
#print axioms intervalIntegral_le_leftRiemannSum

end CertifiedJL.Tests.EndpointRiemann
