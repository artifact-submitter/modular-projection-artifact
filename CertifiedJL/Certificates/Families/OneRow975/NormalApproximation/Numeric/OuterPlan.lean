/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.OneRow975.NormalApproximation.Numeric.Core

/-!
# A switch-aligned scaled-coordinate Tyurin outer certificate

The original outer checker uses 500 uniform rectangles in `x = 2 b u`.
The useful mass is concentrated near the two endpoints, while a uniform cell
that crosses one of the rational cosine branches loses almost all damping.
This checker instead uses quadratic endpoint clustering and makes every
analytic branch boundary an explicit cell endpoint.
-/

namespace CertifiedJL
namespace TyurinModerate

/-- Number of quadratically clustered cells at each end of the outer band. -/
def moderateOuterPlanCells : ℕ := 25

/-- A point just below the strict cubic/cosine switch at four. -/
def outerPlanCubicEnd : ℚ := 3999 / 1000

/-- First branch endpoint of the rational cosine lower envelope. -/
def outerPlanCosineLeftEnd : ℚ := 471 / 100

/-- Second branch endpoint of the rational cosine lower envelope. -/
def outerPlanCosineRightStart : ℚ := 189 / 40

/-- The cubic endpoint exponent, factored in the scaled coordinate `x=2bu`. -/
def outerPlanCubicExponent (C : Cell) (X : DInterval) : DInterval :=
  X.square * (X - rat 5) *
    div (rat 1) (rat 40 * (rat C.hi).square)

/--
Branch-selected rational lower envelope of `1-cos x`.  Branching on the exact
rational cell endpoints, rather than rounded dyadic endpoints, permits cells
to meet at the non-dyadic analytic switches without a spurious zero hull.
-/
def outerPlanCosineLower (lo hi : ℚ) (X : DInterval) : DInterval :=
  let left := rat 2 - (X - rat (157 / 50)).square * rat (1 / 2)
  let middle := rat (2 / 5)
  let gap := rat (157 / 25) - X
  let right := gap.square * rat (1 / 2) -
    powNat gap 4 * rat (1 / 24)
  if hi ≤ outerPlanCosineLeftEnd then left
  else if outerPlanCosineRightStart ≤ lo then right
  else if hi ≤ outerPlanCosineRightStart then middle
  else rat 0

/-- Product exponent on a branch-selected cosine cell. -/
def outerPlanCosineExponent
    (C : Cell) (lo hi : ℚ) (X : DInterval) : DInterval :=
  -(rat cosineLoss * outerPlanCosineLower lo hi X *
    div (rat 1) (rat 4 * (rat C.hi).square))

/-- Product envelope on one exact scaled-coordinate cell. -/
def outerPlanProductEnvelope (C : Cell) (lo hi : ℚ) : DInterval :=
  let X := Interval.enclose precision lo hi
  if hi < 4 then
    expUpper (outerPlanCubicExponent C X)
  else if 4 ≤ lo then
    expUpper (outerPlanCosineExponent C lo hi X)
  else
    hull (expUpper (outerPlanCubicExponent C X))
      (expUpper (outerPlanCosineExponent C lo hi X))

/-- Exponential side conditions for one branch-selected product cell. -/
def outerPlanProductSafe (C : Cell) (lo hi : ℚ) : Bool :=
  let X := Interval.enclose precision lo hi
  if hi < 4 then
    decide (0 < (rat 40 * (rat C.hi).square).lo) &&
      expSafe (outerPlanCubicExponent C X)
  else if 4 ≤ lo then
    expSafe (outerPlanCosineExponent C lo hi X)
  else
    decide (0 < (rat 40 * (rat C.hi).square).lo) &&
      expSafe (outerPlanCubicExponent C X) &&
      expSafe (outerPlanCosineExponent C lo hi X)

/-- I.29 after absorbing the Jacobian `du=dx/(2b)`. -/
def outerPlanI29Scaled (X : DInterval) : DInterval :=
  div (rat (513 / 500)) (rat (2 * piLower) * X)

/-- Endpoint kernel after absorbing the Jacobian `du=dx/(2b)`. -/
def outerPlanEndpointScaled (C : Cell) (X : DInterval) : DInterval :=
  let scale := rat (C.hi * C.bandwidth)
  let gap := rat 1 - div X (rat 2 * scale)
  div (rat 1) (rat 2 * scale) *
    (gap * rat (1 / 2) +
      rat piUpper * gap.square * rat (1 / 4))

/-- Branch-independent Jacobian-scaled Prawitz kernel. -/
def outerPlanKernel (C : Cell) (X : DInterval) : DInterval :=
  if C.hi * C.bandwidth ≤ X.lowerRat then
    minInterval (outerPlanI29Scaled X)
      (outerPlanEndpointScaled C X)
  else
    outerPlanI29Scaled X

/-- Positive denominators used by the scaled kernel evaluator. -/
def outerPlanKernelSafe (C : Cell) (X : DInterval) : Bool :=
  decide (0 < (rat (2 * piLower) * X).lo) &&
    decide (0 < (rat 2 * rat (C.hi * C.bandwidth)).lo)

/-- Complete Jacobian-scaled integrand on one exact rational cell. -/
def outerPlanIntegrand (C : Cell) (lo hi : ℚ) : DInterval :=
  let X := Interval.enclose precision lo hi
  outerPlanKernel C X * outerPlanProductEnvelope C lo hi

/-- Local ordering and transcendental safety check for one plan cell. -/
def outerPlanCellSafe (C : Cell) (lo hi : ℚ) : Bool :=
  decide (2 * C.hi * C.cutoff ≤ lo ∧ lo ≤ hi ∧
      hi ≤ 2 * C.hi * C.bandwidth) &&
    outerPlanKernelSafe C (Interval.enclose precision lo hi) &&
    outerPlanProductSafe C lo hi

/-- Quadratic clustering toward the left endpoint. -/
def outerPlanSquareEndpoint
    (lo hi : ℚ) (cells i : ℕ) : ℚ :=
  let t : ℚ := i / cells
  lo + (hi - lo) * t ^ 2

/-- Quadratic clustering toward the right endpoint. -/
def outerPlanReverseSquareEndpoint
    (lo hi : ℚ) (cells i : ℕ) : ℚ :=
  let t : ℚ := i / cells
  lo + (hi - lo) * (2 * t - t ^ 2)

/-- Upper rectangle sum on a consecutive endpoint sequence. -/
def outerPlanSegmentUpper
    (C : Cell) (endpoint : ℕ → ℚ) (cells : ℕ) : ℚ :=
  (List.range cells).foldl (fun acc i =>
    let lo := endpoint i
    let hi := endpoint (i + 1)
    acc + (hi - lo) * (outerPlanIntegrand C lo hi).upperRat) 0

/-- Local checker on a consecutive endpoint sequence. -/
def outerPlanSegmentSafe
    (C : Cell) (endpoint : ℕ → ℚ) (cells : ℕ) : Bool :=
  (List.range cells).all fun i =>
    outerPlanCellSafe C (endpoint i) (endpoint (i + 1))

/-- The complete 53-cell reflected outer upper sum. -/
def outerPlanUpper (C : Cell) (cells : ℕ := moderateOuterPlanCells) : ℚ :=
  let left := 2 * C.hi * C.cutoff
  let right := 2 * C.hi * C.bandwidth
  outerPlanSegmentUpper C
      (outerPlanSquareEndpoint left outerPlanCubicEnd cells) cells +
    outerPlanSegmentUpper C
      (fun | 0 => outerPlanCubicEnd | _ => 4) 1 +
    outerPlanSegmentUpper C
      (fun | 0 => 4 | _ => outerPlanCosineLeftEnd) 1 +
    outerPlanSegmentUpper C
      (fun | 0 => outerPlanCosineLeftEnd
           | _ => outerPlanCosineRightStart) 1 +
    outerPlanSegmentUpper C
      (outerPlanReverseSquareEndpoint
        outerPlanCosineRightStart right cells) cells

/-- Complete local safety and coverage check for the switch-aligned plan. -/
def outerPlanCheck (C : Cell) (cells : ℕ := moderateOuterPlanCells) : Bool :=
  let left := 2 * C.hi * C.cutoff
  let right := 2 * C.hi * C.bandwidth
  decide (0 < cells) &&
    decide (left ≤ outerPlanCubicEnd) &&
    decide (outerPlanCosineRightStart ≤ right) &&
    outerPlanSegmentSafe C
      (outerPlanSquareEndpoint left outerPlanCubicEnd cells) cells &&
    outerPlanCellSafe C outerPlanCubicEnd 4 &&
    outerPlanCellSafe C 4 outerPlanCosineLeftEnd &&
    outerPlanCellSafe C outerPlanCosineLeftEnd
      outerPlanCosineRightStart &&
    outerPlanSegmentSafe C
      (outerPlanReverseSquareEndpoint
        outerPlanCosineRightStart right cells) cells

end TyurinModerate
end CertifiedJL
