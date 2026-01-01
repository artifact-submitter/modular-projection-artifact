/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Transcendental.Exponential.ExpData

/-! Integer-only exponential evaluator, separated from its soundness proof. -/
namespace CertifiedJL.DyadicExp

/--
The dyadic enclosure of `1 - x / 2^k` when `x` is represented by the signed
numerator `upper` over the precision-`p` scale.
-/
def base (p : ℕ) (upper : ℤ) (k : ℕ) : Interval p :=
  let n : ℤ := (2 : ℤ) ^ k
  let scale : ℤ := Dyadic.scale p
  ⟨scale + Dyadic.floorDivBy (-upper) n,
    scale + Dyadic.ceilDivBy (-upper) n⟩

/--
Integer-only evaluator extensionally equal to
`Exp.ofIntervalUpper p I k`.
-/
def ofIntervalUpper (p : ℕ) (I : Interval p) (k : ℕ) : Interval p :=
  Exp.upperHull ((base p I.hi k).reciprocal.squareN k)

end CertifiedJL.DyadicExp
