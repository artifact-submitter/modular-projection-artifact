import CertifiedJL.Arithmetic.Transcendental.Exponential.ExpData

/-! Experimental fourth-degree Taylor exponential enclosures. -/

namespace CertifiedJL.TaylorExp

def polynomial4 (p : ℕ) (t : Interval p) : Interval p :=
  let q := Interval.ofRat p
  q 1 + t * (q 1 + t * (q (1 / 2) + t * (q (1 / 6) + t * q (1 / 24))))

def polynomial5Upper (p : ℕ) (t : Interval p) : Interval p :=
  let q := Interval.ofRat p
  q 1 + t * (q 1 + t * (q (1 / 2) + t *
    (q (1 / 6) + t * (q (1 / 24) + t * q (1 / 100)))))

/-- The Taylor polynomial is at least one for a nonnegative argument. -/
def positiveBase (p : ℕ) (x : ℚ) (k : ℕ) : Interval p :=
  let P := polynomial4 p (Interval.ofRat p (x / (2 ^ k : ℕ)))
  ⟨max (Dyadic.scale p : ℤ) P.lo, P.hi⟩

def negUpper (p : ℕ) (x : ℚ) (k : ℕ) : Interval p :=
  Exp.upperHull ((positiveBase p x k).reciprocal.squareN k)

def posUpper (p : ℕ) (x : ℚ) (k : ℕ) : Interval p :=
  Exp.upperHull ((polynomial5Upper p
    (Interval.ofRat p (x / (2 ^ k : ℕ)))).squareN k)

end CertifiedJL.TaylorExp
