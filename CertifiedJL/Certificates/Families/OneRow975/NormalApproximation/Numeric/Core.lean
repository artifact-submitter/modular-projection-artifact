/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Arithmetic.Transcendental.CubeRoot
import CertifiedJL.Arithmetic.Transcendental.Exponential.DyadicExp
import CertifiedJL.Arithmetic.Interval.Reflection

/-!
# Executable cells for the moderate-Lyapunov Prawitz certificate

This file contains only the small, executable interval language used by the
certificate.  Its analytic soundness is kept in `TyurinModerate.Soundness`.
The outer integral is parameterized by `x = 2 b u`, where `[a,b]` is the
current Lyapunov cell.  Consequently every outer mesh lives in the fixed
rational band ending at `157 / 25`, even when `a` is small.
-/

namespace CertifiedJL
namespace TyurinModerate

/-- Fractional precision of the moderate-Lyapunov certificate. -/
def precision : ℕ := 48

/-- Repeated squarings used by every exponential enclosure. -/
def squarings : ℕ := 8

/-- Number of trapezoids in the inner discrepancy envelopes. -/
def innerTrapezoids : ℕ := 8

/-- The rationalized cosine-loss constant. -/
def cosineLoss : ℚ := 49 / 50

/-- Six-decimal rational lower bound for `π`. -/
def piLower : ℚ := 3141592 / 1000000

/-- Six-decimal rational upper bound for `π`. -/
def piUpper : ℚ := 3141593 / 1000000

/-- Rational upper bound for `sqrt (2π)`. -/
def sqrtTwoPiUpper : ℚ := 250663 / 100000

/-- Certificate interval type. -/
abbrev DInterval := Interval precision

/-- Smallest dyadic enclosure of one rational. -/
def rat (q : ℚ) : DInterval := Interval.ofRat precision q

/-- Outward-rounded quotient.  Soundness requires a positive denominator. -/
def div (I J : DInterval) : DInterval := I * J.reciprocal

/-- Convex hull of two dyadic intervals. -/
def hull (I J : DInterval) : DInterval :=
  ⟨min I.lo J.lo, max I.hi J.hi⟩

/-- Pointwise minimum of two enclosed real quantities. -/
def minInterval (I J : DInterval) : DInterval :=
  ⟨min I.lo J.lo, min I.hi J.hi⟩

/-- Pointwise maximum of two enclosed real quantities. -/
def maxInterval (I J : DInterval) : DInterval :=
  ⟨max I.lo J.lo, max I.hi J.hi⟩

/-- A signed exponential enclosure evaluated at an interval upper endpoint. -/
def expUpper (I : DInterval) : DInterval :=
  DyadicExp.ofIntervalUpper precision I squarings

/--
Executable side condition for a signed exponential enclosure.

All certificate exponents lie below one.  Since both the dyadic scale and
the repeated-squaring scale are at least two, this single comparison implies
the former scaling and reciprocal-base checks.
-/
def expSafe (I : DInterval) : Bool :=
  decide (I.upperRat ≤ 1)

/-- Linear natural-number power, sufficient for exponents at most four. -/
def powNat (I : DInterval) : ℕ → DInterval
  | 0 => rat 1
  | n + 1 => powNat I n * I

/-- One closed rational Lyapunov cell and its fixed Prawitz parameters. -/
structure Cell where
  /-- Lower Lyapunov endpoint. -/
  lo : ℚ
  /-- Upper Lyapunov endpoint. -/
  hi : ℚ
  /-- Fixed core cutoff for this cell. -/
  cutoff : ℚ
  /-- Fixed Prawitz bandwidth for this cell. -/
  bandwidth : ℚ
  /-- Rational lower bracket for `L^(1/3)`. -/
  rootLo : ℚ
  /-- Rational upper bracket for `L^(1/3)`. -/
  rootHi : ℚ
  /-- Number of uniform core cells. -/
  coreCells : ℕ
  /-- Number of uniform scaled-outer cells. -/
  outerCells : ℕ
deriving DecidableEq, Repr

attribute [nolint unusedArguments] instReprCell

/--
Endpoint Lyapunov interval.  Analytic soundness first moves every
`L ∈ [lo,hi]` to `hi` by monotonicity; the numerical checker therefore does
not pay interval-dependency loss in `L`.
-/
def Cell.lyapunovInterval (C : Cell) : DInterval :=
  rat C.hi

/-- Cube-root interval recorded by a certificate cell. -/
def Cell.rootInterval (C : Cell) : DInterval :=
  Interval.enclose precision C.rootLo C.rootHi

/-- Fixed bandwidth interval. -/
def Cell.bandwidthInterval (C : Cell) : DInterval :=
  rat C.bandwidth

/-- Fixed core cutoff interval. -/
def Cell.cutoffInterval (C : Cell) : DInterval :=
  rat C.cutoff

/-- The `i`th uniform core interval. -/
def coreUInterval (C : Cell) (i : ℕ) : DInterval :=
  Interval.enclose precision
    (C.cutoff * i / C.coreCells)
    (C.cutoff * (i + 1) / C.coreCells)

/--
The `i`th outer interval in the scaled coordinate `x=2 b u`.
Its right endpoint is always `157/25`.
-/
def outerXInterval (C : Cell) (i : ℕ) : DInterval :=
  let left := 2 * C.hi * C.cutoff
  let right := 2 * C.hi * C.bandwidth
  Interval.enclose precision
    (left + (right - left) * i / C.outerCells)
    (left + (right - left) * (i + 1) / C.outerCells)

/-- Convert a scaled outer-coordinate interval to its `u=x/(2b)` interval. -/
def outerUInterval (C : Cell) (i : ℕ) : DInterval :=
  div (outerXInterval C i) (rat (2 * C.hi))

/-- Interval for the variance cap `L^(2/3)`. -/
def varianceCapInterval (C : Cell) : DInterval :=
  (C.rootInterval).square

/-- Interval for the switching point `A=5/(3L^(1/3))`. -/
def switchInterval (C : Cell) : DInterval :=
  div (rat 5) (rat 3 * C.rootInterval)

/-- The elementary quadratic-exponential integrand. -/
def sqExpSqTerm (c s : DInterval) : DInterval :=
  s.square * rat (1 / 2) *
    expUpper (c * s.square * rat (1 / 2))

/-- The elementary cubic-exponential integrand. -/
def sqExpCubeTerm (c s : DInterval) : DInterval :=
  s.square * rat (1 / 2) *
    expUpper (c * (powNat s 3) * rat (1 / 5))

/-- Eight-trapezoid enclosure on `[0,T]` for the quadratic exponential. -/
def sqExpSqTrap (c T : DInterval) : DInterval :=
  let n : ℚ := innerTrapezoids
  let h := div T (rat n)
  let endpoint := (sqExpSqTerm c (rat 0) + sqExpSqTerm c T) * rat (1 / 2)
  let interior := (List.range (innerTrapezoids - 1)).foldl
    (fun acc i => acc + sqExpSqTerm c (h * rat (i + 1))) (rat 0)
  h * (endpoint + interior)

/-- Eight-trapezoid enclosure on `[A,T]` for the cubic exponential. -/
def sqExpCubeTrap (c A T : DInterval) : DInterval :=
  let n : ℚ := innerTrapezoids
  let h := div (T - A) (rat n)
  let endpoint :=
    (sqExpCubeTerm c A + sqExpCubeTerm c T) * rat (1 / 2)
  let interior := (List.range (innerTrapezoids - 1)).foldl
    (fun acc i =>
      acc + sqExpCubeTerm c (A + h * rat (i + 1))) (rat 0)
  h * (endpoint + interior)

/--
Quadratic-exponential trapezoid over an explicit list of interior indices.
This compositional form lets the soundness proof remain independent of the
concrete eight-point certificate grid.
-/
def weightedSqExpSqTrapOn
    (indices : List ℕ) (n : ℚ) (c T : DInterval) : DInterval :=
  let h := div T (rat n)
  let term := fun s : DInterval =>
    s.square * rat (1 / 2) *
      expUpper ((c * s.square - T.square) * rat (1 / 2))
  let endpoint := (term (rat 0) + term T) * rat (1 / 2)
  let interior := indices.foldl
    (fun acc (i : ℕ) =>
      acc + term (h * rat (((i + 1 : ℕ) : ℚ)))) (rat 0)
  h * (endpoint + interior)

/--
Quadratic-exponential trapezoid after combining its outside Gaussian factor.
Keeping the exponent as `(c s²-T²)/2` avoids a major interval-dependency
loss at the endpoint `s=T`.
-/
def weightedSqExpSqTrap (c T : DInterval) : DInterval :=
  weightedSqExpSqTrapOn
    (List.range (innerTrapezoids - 1)) innerTrapezoids c T

/-- Cubic-exponential trapezoid over explicit interior indices. -/
def weightedSqExpCubeTrapOn
    (indices : List ℕ) (n : ℚ)
    (c A T : DInterval) : DInterval :=
  let h := div (T - A) (rat n)
  let term := fun s : DInterval =>
    s.square * rat (1 / 2) *
      expUpper
        (c * powNat s 3 * rat (1 / 5) -
          T.square * rat (1 / 2))
  let endpoint := (term A + term T) * rat (1 / 2)
  let interior := indices.foldl
    (fun acc (i : ℕ) =>
      acc + term (A + h * rat (((i + 1 : ℕ) : ℚ)))) (rat 0)
  h * (endpoint + interior)

/--
Cubic-exponential trapezoid after combining its outside Gaussian factor.
-/
def weightedSqExpCubeTrap
    (c A T : DInterval) : DInterval :=
  weightedSqExpCubeTrapOn
    (List.range (innerTrapezoids - 1)) innerTrapezoids c A T

/-- Exponential side conditions for an explicit quadratic trapezoid grid. -/
def weightedSqExpSqTrapSafeOn
    (indices : List ℕ) (n : ℚ) (c T : DInterval) : Bool :=
  let h := div T (rat n)
  let termSafe := fun s : DInterval =>
    expSafe ((c * s.square - T.square) * rat (1 / 2))
  termSafe (rat 0) && termSafe T &&
    indices.all (fun i =>
      termSafe (h * rat (((i + 1 : ℕ) : ℚ))))

/-- Exponential side conditions used by `weightedSqExpSqTrap`. -/
def weightedSqExpSqTrapSafe (c T : DInterval) : Bool :=
  weightedSqExpSqTrapSafeOn
    (List.range (innerTrapezoids - 1)) innerTrapezoids c T

/-- Exponential side conditions for an explicit cubic trapezoid grid. -/
def weightedSqExpCubeTrapSafeOn
    (indices : List ℕ) (n : ℚ)
    (c A T : DInterval) : Bool :=
  let h := div (T - A) (rat n)
  let termSafe := fun s : DInterval =>
    expSafe
      (c * powNat s 3 * rat (1 / 5) -
        T.square * rat (1 / 2))
  termSafe A && termSafe T &&
    indices.all (fun i =>
      termSafe (A + h * rat (((i + 1 : ℕ) : ℚ))))

/-- Exponential side conditions used by `weightedSqExpCubeTrap`. -/
def weightedSqExpCubeTrapSafe
    (c A T : DInterval) : Bool :=
  weightedSqExpCubeTrapSafeOn
    (List.range (innerTrapezoids - 1)) innerTrapezoids c A T

/-- Common `L exp(-u²/2)` front factor in both discrepancy envelopes. -/
def discrepancyFront (C : Cell) (T : DInterval) : DInterval :=
  C.lyapunovInterval *
    expUpper (-(T.square * rat (1 / 2)))

/-- Interval enclosure of the first trapezoidal discrepancy envelope. -/
def deltaOne (C : Cell) (T : DInterval) : DInterval :=
  C.lyapunovInterval * weightedSqExpSqTrap (rat 1) T

/-- Numerical safety check for the first trapezoidal discrepancy envelope. -/
def deltaOneSafe (_C : Cell) (T : DInterval) : Bool :=
  weightedSqExpSqTrapSafe (rat 1) T

attribute [nolint unusedArguments] deltaOneSafe

/-- First branch of the second trapezoidal discrepancy envelope. -/
def deltaTwoFirst (C : Cell) (T : DInterval) : DInterval :=
  C.lyapunovInterval *
    weightedSqExpSqTrap (varianceCapInterval C) T

/-- Numerical safety check for the first branch of the second discrepancy envelope. -/
def deltaTwoFirstSafe (C : Cell) (T : DInterval) : Bool :=
  weightedSqExpSqTrapSafe (varianceCapInterval C) T

/-- Second branch of the second trapezoidal discrepancy envelope. -/
def deltaTwoSecond (C : Cell) (T : DInterval) : DInterval :=
  let A := switchInterval C
  let invEll := expUpper (rat (25 / 54))
  C.lyapunovInterval *
    (weightedSqExpSqTrap (varianceCapInterval C) A *
        expUpper ((A.square - T.square) * rat (1 / 2)) +
      invEll *
        weightedSqExpCubeTrap C.lyapunovInterval A T)

/-- Numerical safety check for the second branch of the second discrepancy envelope. -/
def deltaTwoSecondSafe (C : Cell) (T : DInterval) : Bool :=
  let A := switchInterval C
  expSafe (rat (25 / 54)) &&
    weightedSqExpSqTrapSafe (varianceCapInterval C) A &&
    expSafe ((A.square - T.square) * rat (1 / 2)) &&
    weightedSqExpCubeTrapSafe C.lyapunovInterval A T

/--
Branch-independent enclosure of the second discrepancy envelope.  Taking a
hull is inexpensive and avoids embedding a fragile floating branch decision
in the certificate.
-/
def deltaTwo (C : Cell) (T : DInterval) : DInterval :=
  if T.upperRat * C.rootHi ≤ 5 / 3 then
    deltaTwoFirst C T
  else if 5 / 3 < T.lowerRat * C.rootLo then
    deltaTwoSecond C T
  else
    hull (deltaTwoFirst C T) (deltaTwoSecond C T)

/-- Branch-aware numerical safety check for the second discrepancy envelope. -/
def deltaTwoSafe (C : Cell) (T : DInterval) : Bool :=
  if T.upperRat * C.rootHi ≤ 5 / 3 then
    deltaTwoFirstSafe C T
  else if 5 / 3 < T.lowerRat * C.rootLo then
    deltaTwoSecondSafe C T
  else
    deltaTwoFirstSafe C T && deltaTwoSecondSafe C T

/-- Enclosure of the pointwise minimum of the two discrepancy envelopes. -/
def deltaMin (C : Cell) (T : DInterval) : DInterval :=
  minInterval (deltaOne C T) (deltaTwo C T)

/--
I.29 kernel envelope with `π` replaced by its proved lower bound `157/50`.
-/
def kernelI29 (T : DInterval) : DInterval :=
  div (rat (513 / 500))
    (rat (2 * piLower) * T)

/--
Endpoint-vanishing kernel envelope, with `π` replaced by `63/20`.
-/
def kernelEndpoint (C : Cell) (T : DInterval) : DInterval :=
  let U := C.bandwidthInterval
  let gap := rat 1 - div T U
  div (rat 1) U *
    (gap * rat (1 / 2) +
      rat piUpper * gap.square * rat (1 / 4))

/-- Kernel envelope used on one interval not containing zero. -/
def kernel (C : Cell) (T : DInterval) : DInterval :=
  if C.bandwidth / 2 ≤ T.lowerRat then
    minInterval (kernelI29 T) (kernelEndpoint C T)
  else
    kernelI29 T

/-- Positive denominator checks made by the kernel evaluator. -/
def kernelSafe (C : Cell) (T : DInterval) : Bool :=
  decide (0 < (rat (2 * piLower) * T).lo) &&
    decide (0 < C.bandwidthInterval.lo)

/-- Core certificate integrand on a nonzero uniform cell. -/
def coreIntegrand (C : Cell) (i : ℕ) : DInterval :=
  let T := coreUInterval C i
  kernel C T * deltaMin C T

/-- Numerical safety check for one nonzero core-certificate integrand. -/
def coreIntegrandSafe (C : Cell) (i : ℕ) : Bool :=
  let T := coreUInterval C i
  kernelSafe C T && deltaOneSafe C T && deltaTwoSafe C T

/-- Which discrepancy envelope a granular core certificate evaluates. -/
inductive DeltaChoice
  | one
  | two
  deriving DecidableEq, Repr

/-- Which analytic kernel envelope a granular core certificate evaluates. -/
inductive KernelChoice
  | i29
  | endpoint
  deriving DecidableEq, Repr

/-- Stored evaluator choices for one noninitial core rectangle. -/
structure CoreChoice where
  /-- Discrepancy envelope evaluated on this rectangle. -/
  delta : DeltaChoice
  /-- Analytic kernel envelope evaluated on this rectangle. -/
  kernel : KernelChoice
  deriving DecidableEq, Repr

/--
A compact per-cell choice plan.  The discrepancy choice is constant, while
the kernel may switch once at an inclusive node threshold.
-/
structure CoreChoicePlan where
  /-- Discrepancy envelope used throughout the cell. -/
  delta : DeltaChoice
  /-- Kernel envelope used before an optional switch. -/
  kernelInitial : KernelChoice
  /-- Optional inclusive node threshold and the kernel used from that node onward. -/
  kernelSwitch : Option (ℕ × KernelChoice) := none
  deriving DecidableEq, Repr

attribute [nolint unusedArguments] instReprCoreChoice instReprCoreChoicePlan

/-- Expand a compact per-cell plan at one core node. -/
def CoreChoicePlan.at
    (plan : CoreChoicePlan) (i : ℕ) : CoreChoice :=
  let kernel :=
    match plan.kernelSwitch with
    | none => plan.kernelInitial
    | some (switchAt, after) =>
        if switchAt ≤ i then after else plan.kernelInitial
  { delta := plan.delta, kernel }

/-- Evaluate only the selected discrepancy envelope. -/
def chosenDelta (C : Cell) (T : DInterval) : DeltaChoice → DInterval
  | .one => deltaOne C T
  | .two => deltaTwo C T

/-- Safety check for only the selected discrepancy envelope. -/
def chosenDeltaSafe (C : Cell) (T : DInterval) : DeltaChoice → Bool
  | .one => deltaOneSafe C T
  | .two => deltaTwoSafe C T

/-- Evaluate only the selected kernel envelope. -/
def chosenKernel (C : Cell) (T : DInterval) : KernelChoice → DInterval
  | .i29 => kernelI29 T
  | .endpoint => kernelEndpoint C T

/-- Safety and domain checks for only the selected kernel envelope. -/
def chosenKernelSafe
    (C : Cell) (T : DInterval) : KernelChoice → Bool
  | .i29 =>
      decide (0 < (rat (2 * piLower) * T).lo)
  | .endpoint =>
      decide (C.bandwidth / 2 ≤ T.lowerRat) &&
        decide (0 < C.bandwidthInterval.lo)

/-- Granular core integrand evaluating one stored pair of choices. -/
def chosenCoreIntegrand
    (C : Cell) (choice : CoreChoice) (i : ℕ) : DInterval :=
  let T := coreUInterval C i
  chosenKernel C T choice.kernel *
    chosenDelta C T choice.delta

/-- Local safety check for one granular core integrand. -/
def chosenCoreIntegrandSafe
    (C : Cell) (choice : CoreChoice) (i : ℕ) : Bool :=
  let T := coreUInterval C i
  chosenKernelSafe C T choice.kernel &&
    chosenDeltaSafe C T choice.delta

/--
Removable-singularity upper bound on the first core cell.  This is the
localized form of `tyurinCoreTrapezoidCertificateIntegrand_le`.
-/
def firstCoreUpper (C : Cell) : DInterval :=
  let T := rat (C.cutoff / C.coreCells)
  rat (513 / 500) * C.lyapunovInterval * T.square * rat (1 / 4)

/-- Upper endpoint used for one core quadrature cell. -/
def coreCellUpper (C : Cell) (i : ℕ) : ℚ :=
  if i = 0 then (firstCoreUpper C).upperRat
  else (coreIntegrand C i).upperRat

/-- Upper endpoint for a core rectangle using stored evaluator choices. -/
def chosenCoreCellUpper
    (C : Cell) (choice : CoreChoice) (i : ℕ) : ℚ :=
  if i = 0 then (firstCoreUpper C).upperRat
  else (chosenCoreIntegrand C choice i).upperRat

/-- The scaled product exponent in the cubic branch. -/
def cubicProductExponent (C : Cell) (X : DInterval) : DInterval :=
  let L := C.lyapunovInterval
  let b := rat C.hi
  let Ucoord := div X (rat 2 * b)
  (-(Ucoord.square) +
      rat (2 / 5) * L * powNat Ucoord 3) * rat (1 / 2)

/-- Rational lower envelope of `1-cos x` used by the executable checker. -/
def rationalCosineLower (X : DInterval) : DInterval :=
  let left := rat 2 - (X - rat (157 / 50)).square * rat (1 / 2)
  let middle := rat (2 / 5)
  let gap := rat (157 / 25) - X
  let right := gap.square * rat (1 / 2) -
    (powNat gap 4) * rat (1 / 24)
  if X.upperRat ≤ 471 / 100 then left
  else if 189 / 40 ≤ X.lowerRat then right
  else if X.upperRat ≤ 189 / 40 then middle
  else rat 0

/-- Product exponent in the rational cosine branch. -/
def cosineProductExponent (C : Cell) (X : DInterval) : DInterval :=
  let L := C.lyapunovInterval;
  let lower := rationalCosineLower (div (L * X) (rat C.hi));
  let inverseScale := div (rat 1) (rat 4 * L.square);
  -(rat cosineLoss * lower * inverseScale)

/--
Branch-independent product envelope on a scaled outer cell.  A hull handles
the possible cell crossing at argument four.
-/
def productEnvelope (C : Cell) (X : DInterval) : DInterval :=
  let actualX := div (C.lyapunovInterval * X) (rat C.hi)
  if actualX.upperRat < 4 then
    expUpper (cubicProductExponent C X)
  else if 4 ≤ actualX.lowerRat then
    expUpper (cosineProductExponent C X)
  else
    hull (expUpper (cubicProductExponent C X))
      (expUpper (cosineProductExponent C X))

/-- Numerical safety check for the branch-independent product envelope. -/
def productEnvelopeSafe (C : Cell) (X : DInterval) : Bool :=
  let actualX := div (C.lyapunovInterval * X) (rat C.hi)
  if actualX.upperRat < 4 then
    expSafe (cubicProductExponent C X)
  else if 4 ≤ actualX.lowerRat then
    expSafe (cosineProductExponent C X)
  else
    expSafe (cubicProductExponent C X) &&
      expSafe (cosineProductExponent C X)

/-- Outer certificate integrand in the scaled coordinate `x=2bu`. -/
def outerScaledIntegrand (C : Cell) (i : ℕ) : DInterval :=
  let X := outerXInterval C i
  let T := outerUInterval C i
  kernel C T * productEnvelope C X * div (rat 1) (rat (2 * C.hi))

/-- Numerical safety check for one scaled outer-certificate integrand. -/
def outerScaledIntegrandSafe (C : Cell) (i : ℕ) : Bool :=
  kernelSafe C (outerUInterval C i) &&
    productEnvelopeSafe C (outerXInterval C i)

/-- Upper endpoint used for one scaled-outer quadrature cell. -/
def outerCellUpper (C : Cell) (i : ℕ) : ℚ :=
  (outerScaledIntegrand C i).upperRat

/-- Uniform rectangle sum for the core integral. -/
def coreIntegralUpper (C : Cell) : ℚ :=
  (C.cutoff / C.coreCells) *
    (List.range C.coreCells).foldl
      (fun acc i => acc + coreCellUpper C i) 0

/-- Core rectangle sum using one stored evaluator choice per node. -/
def chosenCoreIntegralUpper
    (C : Cell) (choices : ℕ → CoreChoice) : ℚ :=
  (C.cutoff / C.coreCells) *
    (List.range C.coreCells).foldl
      (fun acc i =>
        acc + chosenCoreCellUpper C (choices i) i) 0

/-- Uniform rectangle sum for the scaled outer integral. -/
def outerIntegralUpper (C : Cell) : ℚ :=
  let left := 2 * C.hi * C.cutoff
  let right := 2 * C.hi * C.bandwidth
  ((right - left) / C.outerCells) *
    (List.range C.outerCells).foldl
      (fun acc i => acc + outerCellUpper C i) 0

/-- Certified upper endpoint for `exp(-U₀²/2)`. -/
def gaussianExpUpper (C : Cell) : ℚ :=
  (Exp.negUpper precision (C.cutoff ^ 2 / 2) squarings).upperRat

/-- Rationalized sharp Gaussian budget for one cell. -/
def gaussianBudgetUpper (C : Cell) : ℚ :=
  let U := C.bandwidth
  let e := gaussianExpUpper C
  sqrtTwoPiUpper / (2 * U) -
    (1 - e) / U ^ 2 +
    piUpper ^ 2 * sqrtTwoPiUpper / (36 * U ^ 3) +
    (1 / piLower) * e / C.cutoff ^ 2

/-- Complete numerator upper bound on one Lyapunov cell. -/
def numeratorUpper (C : Cell) : ℚ :=
  2 * coreIntegralUpper C +
    2 * outerIntegralUpper C +
      gaussianBudgetUpper C

/-- Strict numerical target for one Lyapunov cell. -/
def cellTarget (C : Cell) : ℚ := (3 / 5) * C.lo

/-- Every positive-exponential call made by one cell is numerically safe. -/
def numericSafeCheck (C : Cell) : Bool :=
  ((List.range C.coreCells).all fun i =>
      if i = 0 then true else coreIntegrandSafe C i) &&
    ((List.range C.outerCells).all fun i =>
      outerScaledIntegrandSafe C i)

/-- Basic rational geometry checks for a certificate cell. -/
def geometryCheck (C : Cell) : Bool :=
  decide
    (0 < C.lo ∧ C.lo ≤ C.hi ∧
      C.hi / C.lo ≤ 471 / 400 ∧
      0 < C.cutoff ∧ C.cutoff ≤ C.bandwidth ∧
      0 < C.bandwidthInterval.lo ∧
      0 < C.rootLo ∧ C.rootLo ^ 3 ≤ C.hi ∧
      0 ≤ C.rootHi ∧ C.hi ≤ C.rootHi ^ 3 ∧
      0 < (rat 3 * C.rootInterval).lo ∧
      0 < (rat C.hi).lo ∧
      0 < (rat 2 * rat C.hi).lo ∧
      0 < (rat (2 * C.hi)).lo ∧
      0 < (rat 4 * C.lyapunovInterval.square).lo ∧
      0 < C.coreCells ∧ 0 < C.outerCells ∧
      2 * C.hi * C.bandwidth ≤ 157 / 25)

/-- Final strict check for one fully evaluated Lyapunov cell. -/
def cellCheck (C : Cell) : Bool :=
  geometryCheck C && numericSafeCheck C &&
    decide (numeratorUpper C < cellTarget C)

end TyurinModerate
end CertifiedJL
