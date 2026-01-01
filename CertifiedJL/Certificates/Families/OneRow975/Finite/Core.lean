/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Transcendental.Cosh
import CertifiedJL.Arithmetic.Interval.Reflection

/-!
# Sparse one-row scalar certificate evaluator

This is the proof-producing Lean counterpart of
`artifact/single-row/verify_single_row_975.py`.  It evaluates the monotone
cell envelope (O10) using outward-rounded dyadic intervals. The Python
artifact conservatively uses 512 fractional bits; Lean uses the smallest
audited precision that retains comfortable strict slack and keeps kernel
reduction practical. Analytic
soundness lemmas connecting the evaluator to the real scalar envelope live in
a separate module; the definitions here remain small and executable.
-/

namespace CertifiedJL
namespace SparseOneRowCertificate

/-- Audited fractional-bit precision of the Lean certificate. -/
def precision : ℕ := 256

/-- Fixed denominator of the original scalar mesh. -/
def gridDenominator : ℕ := 1200

/-- Number of retained cells, covering `[0,77/300]` and hence `[0,32/125]`. -/
def gridSize : ℕ := 308

/-- Largest profile value handled by the scalar Tyurin-envelope certificate. -/
def certifiedProfileUpper : ℚ := 32 / 125

/-- Number of repeated squarings in each exponential enclosure. -/
def squarings : ℕ := 28

/-- The certificate's signed-dyadic interval type. -/
abbrev DInterval := Interval precision

/-- Enclose one exact rational on the certificate grid. -/
def ratInterval (x : ℚ) : DInterval := Interval.ofRat precision x

/-- The artifact's rational upper bound on `39 * sqrt 2 / 4`. -/
def xUpper : ℚ := 13789 / 1000

/-- The rational upper bound on the Gaussian prefactor. -/
def gaussianCoefficientUpper : ℚ := 200 / 6903

/-- Twice the proved specialized Berry--Esseen constant `3/5`. -/
def berryEsseenFactor : ℚ := 6 / 5

/-- The exact negative-exponential rate `x²/2 = 1521/16`. -/
def exponentRate : ℚ := 1521 / 16

/-- The strict one-sided target `2⁻¹⁴²`. -/
def target : ℚ := 1 / 2 ^ 142

/-- Upper enclosure of `cosh x` for a nonnegative rational `x`. -/
def coshUpper (x : ℚ) : DInterval :=
  Cosh.upper precision x squarings

/-- Left endpoint of cell `index` on the exact rational grid. -/
def cellLeftRat (index : ℕ) : ℚ := index / gridDenominator

/-- Right endpoint of cell `index` on the exact rational grid. -/
def cellRightRat (index : ℕ) : ℚ := (index + 1) / gridDenominator

/-- Upper enclosure of the monotone scalar envelope on cell `index`. -/
def cellUpper (index : ℕ) : DInterval :=
  let left := cellLeftRat index
  let right := cellRightRat index
  let leftSquare := left * left
  let rightSquare := right * right
  let exponential :=
    Exp.negUpper precision (exponentRate * (1 + leftSquare)) squarings
  let coshLinear := coshUpper (xUpper * right)
  let coshQuadratic := coshUpper (xUpper * rightSquare)
  let bracket :=
    ratInterval gaussianCoefficientUpper * coshQuadratic +
      ratInterval berryEsseenFactor * ratInterval rightSquare *
        (coshQuadratic * coshQuadratic * coshQuadratic)
  exponential * coshLinear * bracket

/-- Executable strict check for one scalar cell. -/
def cellCheck (index : ℕ) : Bool :=
  Interval.upperLTCheck (cellUpper index) target

end SparseOneRowCertificate
end CertifiedJL
