/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Transcendental.Exponential.Exp

/-!
# Certified hyperbolic-cosine upper enclosures

The numeric certificates evaluate `cosh x` as
`(exp x + exp (-x)) / 2`.  This module packages the corresponding interval
algorithm and its real soundness theorem.
-/

namespace CertifiedJL
namespace Cosh

/-- Outward-rounded upper enclosure of `cosh x`. -/
def upper (p : ℕ) (x : ℚ) (k : ℕ) : Interval p :=
  (Exp.posUpper p x k + Exp.negUpper p x k) *
    Interval.ofRat p (1 / 2)

/-- Soundness of the hyperbolic-cosine upper enclosure. -/
theorem upper_contains {p k : ℕ} {x : ℚ}
    (hx : 0 ≤ x) (hupper : x < (2 ^ k : ℕ))
    (hbase : 0 < (Interval.ofRat p (1 - x / (2 ^ k : ℕ))).lo) :
    (upper p x k).Contains (Real.cosh x) := by
  have hpos := Exp.posUpper_contains (p := p) hx hupper hbase
  have hneg := Exp.negUpper_contains (p := p) (k := k) hx
  have hadd := Interval.contains_add hpos hneg
  have hhalf :
      (Interval.ofRat p (1 / 2)).Contains ((1 / 2 : ℚ) : ℝ) :=
    Interval.contains_ofRat p (1 / 2)
  have hmul := Interval.contains_mul hadd hhalf
  rw [Real.cosh_eq]
  simpa [upper, div_eq_mul_inv] using hmul

end Cosh
end CertifiedJL
