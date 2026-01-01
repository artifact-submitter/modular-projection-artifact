/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Transcendental.Exponential.Exp

/-!
# Certified hyperbolic-sine enclosures

This module derives a sound interval for `sinh x` from the already verified
positive- and negative-exponential enclosures.  Sparse hybrid certificates use
it once per profile box to validate their compact rational surrogate.
-/

namespace CertifiedJL
namespace Sinh

/-- Outward-rounded enclosure of `sinh x`. -/
def enclosure (p : ℕ) (x : ℚ) (k : ℕ) : Interval p :=
  (Exp.posUpper p x k - Exp.negUpper p x k) *
    Interval.ofRat p (1 / 2)

/-- Soundness of the hyperbolic-sine enclosure. -/
theorem enclosure_contains {p k : ℕ} {x : ℚ}
    (hx : 0 ≤ x) (hupper : x < (2 ^ k : ℕ))
    (hbase : 0 < (Interval.ofRat p (1 - x / (2 ^ k : ℕ))).lo) :
    (enclosure p x k).Contains (Real.sinh x) := by
  have hpos := Exp.posUpper_contains (p := p) hx hupper hbase
  have hneg := Exp.negUpper_contains (p := p) (k := k) hx
  have hsub := Interval.contains_sub hpos hneg
  have hhalf :
      (Interval.ofRat p (1 / 2)).Contains ((1 / 2 : ℚ) : ℝ) :=
    Interval.contains_ofRat p (1 / 2)
  have hmul := Interval.contains_mul hsub hhalf
  rw [Real.sinh_eq]
  simpa [enclosure, div_eq_mul_inv] using hmul

end Sinh
end CertifiedJL
