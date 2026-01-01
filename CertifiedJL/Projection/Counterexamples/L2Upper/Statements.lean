/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Statements.L2.Upper.Rows256Bits128

/-!
# Explicit squared-norm upper-tail obstruction statements

These definitions state the concrete finite counterexamples used to delimit
the maintained upper-tail endpoints. Defining a proposition does not prove it.
-/

namespace CertifiedJL

/-! ## Sparse counterexample constants and exact propositions -/

/-- The modulus in the paper's sparse upper-336 counterexample. -/
def counterexampleModulus : ℕ := 2 ^ 32 - 99

/-- The square-root dimension of the sparse upper-336 counterexample. -/
def counterexampleSide : ℕ := 46_340

/-- The dimension of the sparse upper-336 counterexample. -/
def counterexampleDimension : ℕ := counterexampleSide ^ 2

/-- The all-ones vector used by the sparse upper-336 counterexample. -/
@[nolint unusedArguments]
def sparseUpperCounterexampleVector : Fin counterexampleDimension → ℤ :=
  fun _ => 1

/-- Exact proposition asserted by the sparse upper-336 counterexample. -/
def SparseUpper336CounterexampleStatement : Prop :=
  let w := sparseUpperCounterexampleVector
  Odd counterexampleModulus ∧
    w ≠ 0 ∧
      eventProbability
          (sparseRademacherMatrix rowCount counterexampleDimension)
          (fun J =>
            modularProjectionSqNorm counterexampleModulus J w >
              336 * sqNorm w) >
        ((69 : ENNReal) / 50) * failureTarget securityBits

/-- Exact proposition showing that the upper endpoint `338` cannot provide a
uniform 130-bit failure bound. -/
def SparseUpper338Bits130CounterexampleStatement : Prop :=
  let w := sparseUpperCounterexampleVector
  Odd counterexampleModulus ∧
    w ≠ 0 ∧
      eventProbability
          (sparseRademacherMatrix rowCount counterexampleDimension)
          (fun J =>
            modularProjectionSqNorm counterexampleModulus J w >
              338 * sqNorm w) >
        ((3 : ENNReal) / 2) * failureTarget 130

/-! ## Maintained 192-row upper-frontier obstruction -/

/-- Square-root dimension of the explicit 192-row flat witness. -/
def rows192L2UpperCounterexampleSide : ℕ := 100_000_000

/-- Dimension `N²` of the explicit 192-row flat witness. -/
def rows192L2UpperCounterexampleDimension : ℕ :=
  rows192L2UpperCounterexampleSide ^ 2

/-- Odd modulus `2d+1`; every possible unreduced row sum is centered. -/
def rows192L2UpperCounterexampleModulus : ℕ :=
  2 * rows192L2UpperCounterexampleDimension + 1

/-- The all-ones vector in dimension `10¹⁶`. -/
@[nolint unusedArguments]
def rows192L2UpperCounterexampleVector :
    Fin rows192L2UpperCounterexampleDimension → ℤ :=
  fun _ => 1

/-- Exact finite obstruction to a 130-bit bound at the maintained 192-row
upper threshold.  The event is strict, exactly as in `L2UpperFailure`. -/
def Rows192L2Upper287Bits130CounterexampleStatement : Prop :=
  let w := rows192L2UpperCounterexampleVector
  Odd rows192L2UpperCounterexampleModulus ∧
    w ≠ 0 ∧
      eventProbability
          (sparseRademacherMatrix 192 rows192L2UpperCounterexampleDimension)
          (fun J =>
            modularProjectionSqNorm rows192L2UpperCounterexampleModulus J w >
              287 * sqNorm w) >
        failureTarget 130

/-! ## Higher-security flat upper-frontier obstructions -/

/-- Square-root dimension shared by the higher-security flat witnesses. -/
def highSecurityL2UpperCounterexampleSide : ℕ := 100_000_000

/-- Dimension `10^16` shared by the higher-security flat witnesses. -/
def highSecurityL2UpperCounterexampleDimension : ℕ :=
  highSecurityL2UpperCounterexampleSide ^ 2

/-- Odd modulus `2d+1`, which prevents wraparound for every row outcome. -/
def highSecurityL2UpperCounterexampleModulus : ℕ :=
  2 * highSecurityL2UpperCounterexampleDimension + 1

/-- The all-ones vector shared by the four higher-security obstructions. -/
@[nolint unusedArguments]
def highSecurityL2UpperCounterexampleVector :
    Fin highSecurityL2UpperCounterexampleDimension → ℤ :=
  fun _ => 1

/-- Exact finite obstruction at `(rows,bits,threshold) = (256,192,404)`. -/
def Rows256L2Upper404Bits192CounterexampleStatement : Prop :=
  let w := highSecurityL2UpperCounterexampleVector
  Odd highSecurityL2UpperCounterexampleModulus ∧
    w ≠ 0 ∧
      eventProbability
          (sparseRademacherMatrix 256 highSecurityL2UpperCounterexampleDimension)
          (fun J =>
            modularProjectionSqNorm highSecurityL2UpperCounterexampleModulus J w >
              404 * sqNorm w) >
        failureTarget 192

/-- Exact finite obstruction at `(rows,bits,threshold) = (384,192,507)`. -/
def Rows384L2Upper507Bits192CounterexampleStatement : Prop :=
  let w := highSecurityL2UpperCounterexampleVector
  Odd highSecurityL2UpperCounterexampleModulus ∧
    w ≠ 0 ∧
      eventProbability
          (sparseRademacherMatrix 384 highSecurityL2UpperCounterexampleDimension)
          (fun J =>
            modularProjectionSqNorm highSecurityL2UpperCounterexampleModulus J w >
              507 * sqNorm w) >
        failureTarget 192

/-- Exact finite obstruction at `(rows,bits,threshold) = (512,192,605)`. -/
def Rows512L2Upper605Bits192CounterexampleStatement : Prop :=
  let w := highSecurityL2UpperCounterexampleVector
  Odd highSecurityL2UpperCounterexampleModulus ∧
    w ≠ 0 ∧
      eventProbability
          (sparseRademacherMatrix 512 highSecurityL2UpperCounterexampleDimension)
          (fun J =>
            modularProjectionSqNorm highSecurityL2UpperCounterexampleModulus J w >
              605 * sqNorm w) >
        failureTarget 192

/-- Exact finite obstruction at `(rows,bits,threshold) = (512,256,678)`. -/
def Rows512L2Upper678Bits256CounterexampleStatement : Prop :=
  let w := highSecurityL2UpperCounterexampleVector
  Odd highSecurityL2UpperCounterexampleModulus ∧
    w ≠ 0 ∧
      eventProbability
          (sparseRademacherMatrix 512 highSecurityL2UpperCounterexampleDimension)
          (fun J =>
            modularProjectionSqNorm highSecurityL2UpperCounterexampleModulus J w >
              678 * sqNorm w) >
        failureTarget 256

end CertifiedJL
