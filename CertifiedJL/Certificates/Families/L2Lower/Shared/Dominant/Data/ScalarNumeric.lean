/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Transcendental.Exponential.DyadicExpData
import CertifiedJL.Arithmetic.Interval.ReflectionData
import CertifiedJL.Arithmetic.Transcendental.SquareRoot.SqrtData

/-!
# Shared executable arithmetic for dominant-coordinate certificates

This module contains only interval primitives and the residual-row correction
used by the public-threshold certificate families.
-/

namespace CertifiedJL
namespace DominantNumeric

/-- Fractional precision used by the dominant-cell replay. -/
def precision : ℕ := 160

/-- Repeated-squaring depth used by exponential enclosures. -/
def expSquarings : ℕ := 12

/-- Fixed decomposition keeping every positive growth input at most one. -/
def growthScale : ℕ := 64

abbrev DInterval := Interval precision

def rat (q : ℚ) : DInterval := Interval.ofRat precision q

def div (I J : DInterval) : DInterval := I * J.reciprocal

def minInterval (I J : DInterval) : DInterval :=
  ⟨min I.lo J.lo, min I.hi J.hi⟩

def maxInterval (I J : DInterval) : DInterval :=
  ⟨max I.lo J.lo, max I.hi J.hi⟩

instance instOneDInterval : One DInterval := ⟨rat 1⟩

/-- Binary exponentiation using the kernel-reducible standard recursion. -/
def powNat (I : DInterval) (n : ℕ) : DInterval :=
  npowBinRec n I

def expUpper (I : DInterval) : DInterval :=
  DyadicExp.ofIntervalUpper precision I expSquarings

def piInterval : DInterval :=
  Interval.enclose precision (3141592 / 1000000) (3141593 / 1000000)

/-- Exact rational form of the residual-cell maximum `H_I²(z)`. -/
def hSqRat (lower upper z : ℚ) : ℚ :=
  let endpointLower := z ^ 2 * lower / (1 + z * lower) ^ 2
  let endpointUpper := z ^ 2 * upper / (1 + z * upper) ^ 2
  let critical := if z * lower ≤ 1 ∧ 1 ≤ z * upper then z / 4 else 0
  max endpointLower (max endpointUpper critical)

/-- Exact rational form of the residual-row correction. -/
def rhoRat (lower upper z : ℚ) : ℚ :=
  let hsq := hSqRat lower upper z
  let sLower := z * lower
  let sUpper := z * upper
  min 1
    (1 - sLower / 2 * max 0 (1 - hsq) +
      3 * sUpper ^ 2 + 4 * sUpper ^ 2 * hsq ^ 2)

end DominantNumeric
end CertifiedJL
