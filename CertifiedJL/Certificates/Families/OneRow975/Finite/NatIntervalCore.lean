import CertifiedJL.Certificates.Families.OneRow975.Finite.Core

namespace CertifiedJL
namespace SparseOneRowCertificate

/-!
Nonnegative dyadic interval evaluator for the sparse one-row certificate.

The production `Interval` type stores signed `Int` numerators and multiplies
by taking four signed corners.  Every quantity in the sparse one-row scalar
certificate is nonnegative, so this representation stores `Nat` numerators and
uses one product plus floor/ceiling division.
-/

structure NatInterval (p : ℕ) where
  lo : ℕ
  hi : ℕ
deriving DecidableEq, Repr

namespace NatInterval

variable {p : ℕ}

def scale (p : ℕ) : ℕ := 2 ^ p

def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

def lowerRat (I : NatInterval p) : ℚ := (I.lo : ℚ) / scale p

def upperRat (I : NatInterval p) : ℚ := (I.hi : ℚ) / scale p

def ofRat (p : ℕ) (x : ℚ) : NatInterval p :=
  ⟨Int.toNat (Dyadic.roundDown p x), Int.toNat (Dyadic.roundUp p x)⟩

def add (I J : NatInterval p) : NatInterval p :=
  ⟨I.lo + J.lo, I.hi + J.hi⟩

instance natIntervalAdd : Add (NatInterval p) := ⟨add⟩

def mul (I J : NatInterval p) : NatInterval p :=
  let s := scale p
  ⟨I.lo * J.lo / s, ceilDiv (I.hi * J.hi) s⟩

instance natIntervalMul : Mul (NatInterval p) := ⟨mul⟩

def square (I : NatInterval p) : NatInterval p := I * I

def squareN (I : NatInterval p) : ℕ → NatInterval p
  | 0 => I
  | n + 1 => (squareN I n).square

def reciprocal (I : NatInterval p) : NatInterval p :=
  let s := scale p
  let ss := s * s
  ⟨ss / I.hi, ceilDiv ss I.lo⟩

def upperHull (I : NatInterval p) : NatInterval p := ⟨0, I.hi⟩

def expNegUpper (p : ℕ) (x : ℚ) (k : ℕ) : NatInterval p :=
  upperHull ((ofRat p 1 + ofRat p (x / (2 ^ k : ℕ))).reciprocal.squareN k)

def expPosUpper (p : ℕ) (x : ℚ) (k : ℕ) : NatInterval p :=
  upperHull ((ofRat p (1 - x / (2 ^ k : ℕ))).reciprocal.squareN k)

def coshUpper (p : ℕ) (x : ℚ) (k : ℕ) : NatInterval p :=
  (expPosUpper p x k + expNegUpper p x k) * ofRat p (1 / 2)

def upperLTCheck (I : NatInterval p) (bound : ℚ) : Bool :=
  decide ((I.hi : ℚ) / (scale p : ℚ) < bound)

end NatInterval

open NatInterval

def natCellUpper (index : ℕ) : NatInterval precision :=
  let left := cellLeftRat index
  let right := cellRightRat index
  let leftSquare := left * left
  let rightSquare := right * right
  let exponential := expNegUpper precision
    (exponentRate * (1 + leftSquare)) squarings
  let coshLinear := NatInterval.coshUpper precision (xUpper * right) squarings
  let coshQuadratic := NatInterval.coshUpper precision (xUpper * rightSquare) squarings
  let bracket :=
    ofRat precision gaussianCoefficientUpper * coshQuadratic +
      ofRat precision berryEsseenFactor * ofRat precision rightSquare *
        (coshQuadratic * coshQuadratic * coshQuadratic)
  exponential * coshLinear * bracket

def natCellCheck (index : ℕ) : Bool :=
  upperLTCheck (natCellUpper index) target


end SparseOneRowCertificate
end CertifiedJL
