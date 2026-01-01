/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Shared.UpperContourKernel

/-!
# Compact centered-hybrid arithmetic for the sparse upper tail

This experimental kernel combines the existing sparse fourth-order row
enclosure with a centered Gaussian of width `1/20` and a finite sum of
centered uniform variables.  The center is fixed at the strict threshold, so
the smoothing denominator is definitionally `1/2`; there is no displaced
configuration in this API.
-/

namespace CertifiedJL
namespace SparseUpperHybrid

open UpperContourKernel

/-- Fractional precision for the compact hybrid experiment. -/
def precision : ℕ := 320

def rows : ℕ := 256
def securityBits : ℕ := 128
def threshold : ℚ := 338
def gaussianSigma : ℚ := 1 / 20

/-- Sparse-specific coefficients in the normalized fourth-order row
majorant.  They live with the hybrid checker so its arithmetic core has no
dependency on the retired Gaussian-mesh certificate. -/
def rowCoefficients : UpperContourKernel.RowCoefficients where
  leading := 1 / 8
  error8 := 1 / 9216
  error6 := 11 / 5760

/-- The sparse fourth-order expression on one frequency cell. -/
def rowExpressionOnCell (profile frequencyLeft frequencyRight lam : ℚ) :
    DInterval precision :=
  UpperContourKernel.rowExpressionOnCell precision rowCoefficients
    profile frequencyLeft frequencyRight lam

/-- Outward upper enclosure of the decreasing real-axis row cap. -/
def realCapUpper (p : ℕ) (profileLeft lam : ℚ) : Interval p :=
  if profileLeft = 0 then Interval.mk 0 (Dyadic.scale p)
  else
    let squareRoot := (UpperContourKernel.frac p profileLeft).sqrt
    let squareRootLower := squareRoot.lowerRat
    let argument := squareRootLower * lam / (1 - lam)
    let exponent := argument / (1 + argument)
    let result := UpperContourKernel.divide
      (UpperContourKernel.one p + Exp.posUpper p exponent 30)
      (UpperContourKernel.frac p 2 *
        (UpperContourKernel.frac p (1 + argument)).sqrt)
    ⟨0, min (Dyadic.scale p : ℤ) result.hi⟩

/-- One profile box and its centered compact-smoothing parameters. -/
structure ProfileBox where
  profileLeft : ℚ
  profileRight : ℚ
  lam : ℚ
  uniformCount : ℕ
  uniformHalfWidth : ℚ
deriving DecidableEq, Inhabited

/-- A robust nontrivial box used for the first complete Lean replay. -/
def replayBox : ProfileBox :=
  ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩

/-- A uniform frequency segment represented without rational-to-natural
conversion inside the evaluator. -/
structure Segment where
  start : ℚ
  mesh : ℚ
  count : ℕ
deriving DecidableEq, Inhabited

/-- Build the four adjacent positive-length segments `[0,1]`, `[1,2]`,
`[2,4]`, and `[4,8]` from reciprocal integer meshes.  The final empty
segment keeps the generated five-segment replay schema stable while the
analytic compact-noise tail starts at `8`. -/
def mkSegments (d0 d1 d2 d3 d4 : ℕ) : List Segment :=
  [ ⟨0, 1 / d0, d0⟩,
    ⟨1, 1 / d1, d1⟩,
    ⟨2, 1 / d2, 2 * d2⟩,
    ⟨4, 1 / d3, 4 * d3⟩,
    ⟨8, 1 / d4, 0⟩ ]

/-- One profile box together with its independently optimized frequency
partition. -/
structure CertificateBox where
  box : ProfileBox
  segments : List Segment
deriving DecidableEq, Inhabited

/-- The complete exact low-profile manifest.  An earlier compact-noise tail
and coarser high-profile meshes reduce the replay to 5,049 cells while
preserving all strict endpoint budgets. -/
def certificateBoxes : List CertificateBox :=
  [ ⟨⟨0, 1 / 4096, 625 / 1000, 11, 3 / 10⟩, mkSegments 220 50 20 4 1⟩,
    ⟨⟨1 / 4096, 1 / 2048, 626 / 1000, 9, 4 / 10⟩, mkSegments 280 50 20 6 1⟩,
    ⟨⟨1 / 2048, 3 / 4096, 625 / 1000, 12, 4 / 10⟩, mkSegments 300 50 20 4 1⟩,
    ⟨⟨3 / 4096, 1 / 1024, 625 / 1000, 12, 4 / 10⟩, mkSegments 280 50 30 4 1⟩,
    ⟨⟨1 / 1024, 5 / 4096, 626 / 1000, 9, 5 / 10⟩, mkSegments 280 50 20 4 1⟩,
    ⟨⟨5 / 4096, 3 / 2048, 626 / 1000, 9, 5 / 10⟩, mkSegments 260 50 25 4 1⟩,
    ⟨⟨3 / 2048, 7 / 4096, 626 / 1000, 10, 5 / 10⟩, mkSegments 220 50 40 6 1⟩,
    ⟨⟨7 / 4096, 1 / 512, 626 / 1000, 10, 5 / 10⟩, mkSegments 220 50 25 4 1⟩,
    ⟨⟨1 / 512, 5 / 2048, 625 / 1000, 9, 6 / 10⟩, mkSegments 280 50 30 4 1⟩,
    ⟨⟨5 / 2048, 3 / 1024, 625 / 1000, 9, 6 / 10⟩, mkSegments 200 50 35 4 1⟩,
    ⟨⟨3 / 1024, 1 / 256, 627 / 1000, 10, 6 / 10⟩, mkSegments 240 50 40 4 1⟩,
    ⟨⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩, mkSegments 280 50 30 4 1⟩,
    ⟨⟨3 / 512, 1 / 128, 627 / 1000, 8, 8 / 10⟩, mkSegments 125 13 9 1 1⟩,
    ⟨⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩, mkSegments 126 21 5 1 1⟩,
    ⟨replayBox, mkSegments 48 11 2 1 1⟩,
    ⟨⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩, mkSegments 40 13 2 1 1⟩,
    ⟨⟨3 / 128, 1 / 32, 631 / 1000, 7, 11 / 10⟩, mkSegments 16 11 1 1 1⟩,
    ⟨⟨1 / 32, 1 / 20, 631 / 1000, 6, 12 / 10⟩, mkSegments 19 4 1 1 1⟩ ]

def cutoff : ℚ := 8

/-- Rational Taylor upper bound for `sinh x` on the parameter range used by
the checker.  Soundness is proved separately from this evaluator. -/
def sinhUpper (x : ℚ) (terms : ℕ := 7) : ℚ :=
  let sumTerms := (List.range terms).foldl
    (fun result index => result + x ^ (2 * index + 1) /
      (Nat.factorial (2 * index + 1) : ℚ)) 0
  let nextTerm := x ^ (2 * terms + 1) /
    (Nat.factorial (2 * terms + 1) : ℚ)
  let ratio := x * x /
    (((2 * terms + 2) * (2 * terms + 3) : ℕ) : ℚ)
  sumTerms + nextTerm / (1 - ratio)

/-- Rational Taylor upper bound for `cosh x` on the parameter range used by
the checker. -/
def coshUpper (x : ℚ) (terms : ℕ := 7) : ℚ :=
  let sumTerms := (List.range terms).foldl
    (fun result index => result + x ^ (2 * index) /
      (Nat.factorial (2 * index) : ℚ)) 0
  let nextTerm := x ^ (2 * terms) /
    (Nat.factorial (2 * terms) : ℚ)
  let ratio := x * x /
    (((2 * terms + 1) * (2 * terms + 2) : ℕ) : ℚ)
  sumTerms + nextTerm / (1 - ratio)

/-- No-trigonometry enclosure of one centered-uniform transform factor,
raised to the number of uniforms in the box. -/
def compactNoiseUpper (box : ProfileBox) (frequencyLeft : ℚ) :
    DInterval precision :=
  let h := box.uniformHalfWidth
  let sinhBound := frac precision (sinhUpper (h * box.lam))
  let sineSquareUpper := min 1 ((h * frequencyLeft) ^ 2)
  let numerator := (sinhBound.square + frac precision sineSquareUpper).sqrt
  let denominator := frac precision h *
    (frac precision (box.lam ^ 2 + frequencyLeft ^ 2)).sqrt
  powNat (divide numerator denominator) box.uniformCount

/-- One outward-rounded hybrid frequency cell. -/
def hybridCell (box : ProfileBox) (segment : Segment) (index : ℕ) :
    DInterval precision :=
  let frequencyLeft := segment.start + index * segment.mesh
  let frequencyRight := frequencyLeft + segment.mesh
  let expressionLeft := rowExpressionOnCell
    box.profileLeft frequencyLeft frequencyRight box.lam
  let expressionRight := rowExpressionOnCell
    box.profileRight frequencyLeft frequencyRight box.lam
  let cap := realCapUpper precision box.profileLeft box.lam
  let rowUpper := min cap.hi (max expressionLeft.hi expressionRight.hi)
  let gaussianWeight := Exp.negUpper precision
    (gaussianSigma ^ 2 * frequencyLeft ^ 2 / 2) 24
  frac precision segment.mesh *
    (Interval.mk 0 rowUpper).squareN 8 *
    compactNoiseUpper box frequencyLeft * gaussianWeight *
    inverseSqrtAtLeft precision frequencyLeft box.lam

/-- Primitive sign conditions needed by the semantic consumer for one
hybrid cell.  Keeping them executable lets the generated replay discharge
exactly the interval preconditions it uses, without adding any analytic
assumption to the trust boundary. -/
def hybridCellSideCheck (box : ProfileBox) (segment : Segment) (index : ℕ) : Bool :=
  let frequencyLeft := segment.start + index * segment.mesh
  let sinhBound := frac precision
    (sinhUpper (box.uniformHalfWidth * box.lam))
  let sineSquareUpper := min 1 ((box.uniformHalfWidth * frequencyLeft) ^ 2)
  let compactNumerator := sinhBound.square + frac precision sineSquareUpper
  let compactBase := frac precision (box.lam ^ 2 + frequencyLeft ^ 2)
  let compactDenominator := frac precision box.uniformHalfWidth * compactBase.sqrt
  decide (0 ≤ compactNumerator.lo) &&
    decide (0 ≤ compactBase.lo) &&
    decide (0 < compactDenominator.lo) &&
    decide (0 < compactBase.sqrt.lo)

/-- Catalog-facing name for the exact cell-side checker. -/
def hybridCertificateCellCheck := hybridCellSideCheck

/-- A bounded subcomputation inside one segment. -/
def segmentChunk (box : ProfileBox) (segment : Segment)
    (start count : ℕ) : DInterval precision :=
  (List.range count).foldl
    (fun result offset => result + hybridCell box segment (start + offset))
    (zero precision)

/-- Reference a bounded chunk by segment index and local cell range. -/
structure Chunk where
  segmentIndex : ℕ
  start : ℕ
  count : ℕ
deriving DecidableEq, Inhabited

/-- Split one segment into chunks of at most ten cells.  Keeping this bound
small makes each kernel replay predictable while the generated manifest
contains thousands of cells. -/
def chunksForSegment (segmentIndex count : ℕ) : List Chunk :=
  (List.range ((count + 9) / 10)).map fun chunkIndex =>
    let start := 10 * chunkIndex
    ⟨segmentIndex, start, min 10 (count - start)⟩

/-- Reflection plan for one optimized certificate box. -/
def certificateChunkPlan (certificate : CertificateBox) : List Chunk :=
  (certificate.segments.zipIdx.flatMap fun pair =>
    chunksForSegment pair.2 pair.1.count)

/-- Evaluate one optimized certificate chunk. -/
def certificateChunkValue (certificate : CertificateBox) (chunk : Chunk) :
    DInterval precision :=
  segmentChunk certificate.box
    (certificate.segments.getD chunk.segmentIndex default)
    chunk.start chunk.count

/-- Reassemble the finite integral from already reflected chunks. -/
def finiteIntegralFrom (chunks : List (DInterval precision)) :
    DInterval precision :=
  chunks.foldl (· + ·) (zero precision)

/-- Polynomial compact-noise tail after discarding only the Gaussian decay. -/
def tail (box : ProfileBox) : DInterval precision :=
  let cap := realCapUpper precision box.profileLeft box.lam
  let compactConstant :=
    (coshUpper (box.uniformHalfWidth * box.lam) /
      box.uniformHalfWidth) ^ box.uniformCount
  cap.squareN 8 * frac precision
    (compactConstant / (box.uniformCount * cutoff ^ box.uniformCount))

/-- Exact centered-hybrid prefactor.  The final factor `2` is the reciprocal
of the exact centered denominator `1/2`. -/
def prefactor (box : ProfileBox) : DInterval precision :=
  let exponent := threshold * box.lam -
    gaussianSigma ^ 2 * box.lam ^ 2 / 2
  frac precision (2 ^ securityBits) *
    frac precision (1 / (314159 / 100000)) *
    Exp.negUpper precision exponent 32 *
    frac precision (1 / (1 - box.lam) ^ (rows / 2)) *
    frac precision 2

/-- Complete bound assembled from supplied reflected chunks. -/
def boxBoundFrom (box : ProfileBox) (chunks : List (DInterval precision)) :
    DInterval precision :=
  prefactor box * (finiteIntegralFrom chunks + tail box)

/-- Complete optimized bound evaluated directly from its reflected chunks. -/
def certificateBound (certificate : CertificateBox) : DInterval precision :=
  boxBoundFrom certificate.box
    (certificateChunkPlan certificate |>.map
      (certificateChunkValue certificate))

/-- Total number of finite frequency cells in the optimized manifest. -/
def certificateCellCount : ℕ :=
  (certificateBoxes.flatMap fun certificate =>
    certificate.segments.map Segment.count).sum

theorem certificateCellCount_eq : certificateCellCount = 5049 := by
  decide +kernel

end SparseUpperHybrid
end CertifiedJL
