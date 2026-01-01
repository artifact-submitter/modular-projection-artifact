/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Shared.UpperContourKernel

/-!
# Parameterized balanced-ternary upper-contour arithmetic

This is the reusable executable layer for the high-security upper-tail
family.  Row counts are represented as `oddPart * 2^squareCount`, which
covers 256, 384, and 512 while retaining logarithmic tensor powering.
Security scaling is factored the same way so that 256-bit endpoints do not
underflow on the 512-bit dyadic grid.
-/

namespace CertifiedJL.SparseUpperContourFamily

/-- Global arithmetic parameters shared by every profile box in one result. -/
structure Parameters where
  precision : ℕ
  rowOddPart : ℕ
  rowSquareCount : ℕ
  securityBlockBits : ℕ
  securityScaleSquarings : ℕ
  threshold : ℚ
deriving DecidableEq, Inhabited

namespace Parameters

/-- Number of independent rows. -/
def rows (parameters : Parameters) : ℕ :=
  parameters.rowOddPart * 2 ^ parameters.rowSquareCount

/-- Failure-probability exponent. -/
def securityBits (parameters : Parameters) : ℕ :=
  parameters.securityBlockBits * 2 ^ parameters.securityScaleSquarings

end Parameters

/-- A uniform frequency segment. -/
structure Segment where
  start : ℚ
  mesh : ℚ
  count : ℕ
deriving DecidableEq, Inhabited

namespace Segment

/-- Right endpoint of a uniform frequency segment. -/
def rightEndpoint (segment : Segment) : ℚ :=
  segment.start + segment.count * segment.mesh

/-- Left endpoint of one cell inside a segment. -/
def cellLeft (segment : Segment) (index : ℕ) : ℚ :=
  segment.start + index * segment.mesh

/-- Right endpoint of one cell inside a segment. -/
def cellRight (segment : Segment) (index : ℕ) : ℚ :=
  segment.cellLeft index + segment.mesh

end Segment

/-- Consecutive segments meet at exact rational endpoints. -/
def SegmentsAdjacent : List Segment → Prop
  | [] | [_] => True
  | left :: right :: rest =>
      left.rightEndpoint = right.start ∧
        SegmentsAdjacent (right :: rest)

/-- Executable adjacency check for a segment list. -/
def segmentsAdjacentCheck : List Segment → Bool
  | [] | [_] => true
  | left :: right :: rest =>
      decide (left.rightEndpoint = right.start) &&
        segmentsAdjacentCheck (right :: rest)

theorem segmentsAdjacentCheck_eq_true_iff (segments : List Segment) :
    segmentsAdjacentCheck segments = true ↔ SegmentsAdjacent segments := by
  induction segments with
  | nil => simp [segmentsAdjacentCheck, SegmentsAdjacent]
  | cons left rest ih =>
      cases rest with
      | nil => simp [segmentsAdjacentCheck, SegmentsAdjacent]
      | cons right tail =>
          simp only [segmentsAdjacentCheck, SegmentsAdjacent, Bool.and_eq_true,
            decide_eq_true_eq]
          constructor
          · rintro ⟨hleft, htail⟩
            exact ⟨hleft, ih.mp htail⟩
          · rintro ⟨hleft, htail⟩
            exact ⟨hleft, ih.mpr htail⟩

/-- Every segment has a positive mesh and at least one cell. -/
def SegmentsPositive : List Segment → Prop
  | [] => True
  | segment :: rest =>
      0 < segment.mesh ∧ 0 < segment.count ∧ SegmentsPositive rest

/-- Executable positivity check for every segment. -/
def segmentsPositiveCheck : List Segment → Bool
  | [] => true
  | segment :: rest =>
      decide (0 < segment.mesh) && decide (0 < segment.count) &&
        segmentsPositiveCheck rest

theorem segmentsPositiveCheck_eq_true_iff (segments : List Segment) :
    segmentsPositiveCheck segments = true ↔ SegmentsPositive segments := by
  induction segments with
  | nil => simp [segmentsPositiveCheck, SegmentsPositive]
  | cons segment rest ih =>
      simp only [segmentsPositiveCheck, SegmentsPositive, Bool.and_eq_true,
        decide_eq_true_eq, ih]
      tauto

/-- A rational profile interval and its shifted-Gaussian contour parameters. -/
structure ProfileBox where
  profileLeft : ℚ
  profileRight : ℚ
  lam : ℚ
  sigma : ℚ
  theta : ℚ
  target : ℚ
  cutoff : ℚ
  segments : List Segment
  chunkSize : ℕ
deriving DecidableEq, Inhabited

/-- Exact geometry required by the segmented quadrature soundness theorem. -/
def SegmentGeometry (box : ProfileBox) : Prop :=
  0 < box.chunkSize ∧
  box.segments ≠ [] ∧
  box.segments.head!.start = 0 ∧
  SegmentsPositive box.segments ∧
  SegmentsAdjacent box.segments ∧
  box.segments.getLast!.rightEndpoint = box.cutoff ∧
  0 < box.cutoff

/-- Small kernel-replayed checker for segment positivity, adjacency, and exact
coverage of `[0, cutoff]`.  It is independent of the expensive cell replay. -/
def segmentGeometryCheck (box : ProfileBox) : Bool :=
  decide (0 < box.chunkSize) &&
  decide (box.segments ≠ []) &&
  decide (box.segments.head!.start = 0) &&
  segmentsPositiveCheck box.segments &&
  segmentsAdjacentCheck box.segments &&
  decide (box.segments.getLast!.rightEndpoint = box.cutoff) &&
  decide (0 < box.cutoff)

/-- Soundness of the exact segment-geometry checker. -/
theorem segmentGeometryCheck_sound {box : ProfileBox}
    (hcheck : segmentGeometryCheck box = true) : SegmentGeometry box := by
  simp only [segmentGeometryCheck, Bool.and_eq_true,
    decide_eq_true_eq, segmentsPositiveCheck_eq_true_iff,
    segmentsAdjacentCheck_eq_true_iff] at hcheck
  rcases hcheck with
    ⟨⟨⟨⟨⟨⟨hchunk, hnonempty⟩, hfirst⟩, hpositive⟩, hadjacent⟩,
      hlast⟩, hcutoff⟩
  exact ⟨hchunk, hnonempty, hfirst, hpositive, hadjacent, hlast, hcutoff⟩

/-- Reference a bounded subcomputation inside one frequency segment. -/
structure Chunk where
  segmentIndex : ℕ
  start : ℕ
  count : ℕ
deriving DecidableEq, Inhabited

/-- Parameters for the independent high-profile real-axis endpoint. -/
structure HighProfileBox where
  profileMinimum : ℚ
  lam : ℚ
  target : ℚ
deriving DecidableEq, Inhabited

/-- Balanced-ternary fourth-order coefficients. -/
def rowCoefficients : UpperContourKernel.RowCoefficients where
  leading := 1 / 8
  error8 := 1 / 9216
  error6 := 11 / 5760

/-- The balanced-ternary fourth-order row expression on one frequency cell. -/
def rowExpressionOnCell (parameters : Parameters)
    (profile frequencyLeft frequencyRight lam : ℚ) :
    UpperContourKernel.DInterval parameters.precision :=
  UpperContourKernel.rowExpressionOnCell parameters.precision rowCoefficients
    profile frequencyLeft frequencyRight lam

/-- Outward upper enclosure of the decreasing real-axis deficit cap. -/
def realCapUpper (precision : ℕ) (profileLeft lam : ℚ) : Interval precision :=
  if profileLeft = 0 then Interval.mk 0 (Dyadic.scale precision)
  else
    let squareRoot := (UpperContourKernel.frac precision profileLeft).sqrt
    let squareRootLower := squareRoot.lowerRat
    let argument := squareRootLower * lam / (1 - lam)
    let exponent := argument / (1 + argument)
    let result := UpperContourKernel.divide
      (UpperContourKernel.one precision + Exp.posUpper precision exponent 30)
      (UpperContourKernel.frac precision 2 *
        (UpperContourKernel.frac precision (1 + argument)).sqrt)
    ⟨0, min (Dyadic.scale precision : ℤ) result.hi⟩

/-- One Gaussian-weighted quadrature cell for a profile box. -/
def gaussianCell (parameters : Parameters) (box : ProfileBox)
    (segment : Segment) (index : ℕ) :
    UpperContourKernel.DInterval parameters.precision :=
  let frequencyLeft := segment.start + index * segment.mesh
  let frequencyRight := frequencyLeft + segment.mesh
  let expressionLeft := rowExpressionOnCell parameters box.profileLeft
    frequencyLeft frequencyRight box.lam
  let expressionRight := rowExpressionOnCell parameters box.profileRight
    frequencyLeft frequencyRight box.lam
  let cap := realCapUpper parameters.precision box.profileLeft box.lam
  let rowUpper := min cap.hi (max expressionLeft.hi expressionRight.hi)
  let alpha := box.sigma * box.sigma / 2
  let gaussianWeight := Exp.negUpper parameters.precision
    (alpha * frequencyLeft * frequencyLeft) 24
  UpperContourKernel.frac parameters.precision segment.mesh * gaussianWeight *
    UpperContourKernel.tensorPower (Interval.mk 0 rowUpper)
      parameters.rowOddPart parameters.rowSquareCount *
    UpperContourKernel.inverseSqrtAtLeft parameters.precision
      frequencyLeft box.lam

/-- Evaluate consecutive quadrature cells. -/
def segmentChunk (parameters : Parameters) (box : ProfileBox)
    (segment : Segment)
    (start count : ℕ) : UpperContourKernel.DInterval parameters.precision :=
  (List.range count).foldl
    (fun result offset =>
      result + gaussianCell parameters box segment (start + offset))
    (UpperContourKernel.zero parameters.precision)

/-- Split one segment into bounded replay chunks. -/
def chunksForSegment (chunkSize segmentIndex count : ℕ) : List Chunk :=
  (List.range ((count + chunkSize - 1) / chunkSize)).map fun chunkIndex =>
    let start := chunkSize * chunkIndex
    ⟨segmentIndex, start, min chunkSize (count - start)⟩

/-- Consecutive chunk plan for all segments in one profile box. -/
def boxChunkPlan (box : ProfileBox) : List Chunk :=
  box.segments.zipIdx.flatMap fun pair =>
    chunksForSegment box.chunkSize pair.2 pair.1.count

/-- The one box-level strict dyadic condition needed by every row-expression
cell: the rounded enclosure of `(1-lam)^2` stays positive. -/
def rowExpressionBaseCheck (parameters : Parameters) (box : ProfileBox) : Bool :=
  decide (0 < (UpperContourKernel.frac parameters.precision
    ((1 - box.lam) * (1 - box.lam))).lo)

/-- Soundness of the box-level row-expression base check. -/
theorem rowExpressionBaseCheck_sound
    {parameters : Parameters} {box : ProfileBox}
    (hcheck : rowExpressionBaseCheck parameters box = true) :
    0 < (UpperContourKernel.frac parameters.precision
      ((1 - box.lam) * (1 - box.lam))).lo := by
  simpa [rowExpressionBaseCheck] using hcheck

/-- The one box-level strict dyadic condition needed by every Gaussian
normalization cell: the rounded enclosure of `lam^2` stays positive. -/
def lambdaSquareBaseCheck (parameters : Parameters) (box : ProfileBox) : Bool :=
  decide (0 < (UpperContourKernel.frac parameters.precision
    (box.lam * box.lam)).lo)

/-- Soundness of the box-level Gaussian-normalization base check. -/
theorem lambdaSquareBaseCheck_sound
    {parameters : Parameters} {box : ProfileBox}
    (hcheck : lambdaSquareBaseCheck parameters box = true) :
    0 < (UpperContourKernel.frac parameters.precision
      (box.lam * box.lam)).lo := by
  simpa [lambdaSquareBaseCheck] using hcheck

/-- Concrete segment/cell references enumerated by one replay chunk. -/
def chunkCells (box : ProfileBox) (chunk : Chunk) : List (Segment × ℕ) :=
  (List.range chunk.count).map fun offset =>
    (box.segments.getD chunk.segmentIndex default, chunk.start + offset)

/-- Segment/cell references enumerated by the complete replay plan. -/
def boxChunkCells (box : ProfileBox) : List (Segment × ℕ) :=
  (boxChunkPlan box).flatMap (chunkCells box)

/-- The semantic segment/cell order prescribed directly by the segment list. -/
def boxSegmentCells (box : ProfileBox) : List (Segment × ℕ) :=
  box.segments.flatMap fun segment =>
    (List.range segment.count).map fun index => (segment, index)

/-- Executable check that chunking neither drops, duplicates, nor reorders a
semantic segment cell.  This check contains no interval arithmetic. -/
def boxChunkCoverageCheck (box : ProfileBox) : Bool :=
  decide (boxChunkCells box = boxSegmentCells box)

/-- Soundness of the exact chunk-coverage checker. -/
theorem boxChunkCoverageCheck_sound {box : ProfileBox}
    (hcheck : boxChunkCoverageCheck box = true) :
    boxChunkCells box = boxSegmentCells box := by
  simpa [boxChunkCoverageCheck] using hcheck

/-- Evaluate one referenced replay chunk. -/
def boxChunkValue (parameters : Parameters) (box : ProfileBox) (chunk : Chunk) :
    UpperContourKernel.DInterval parameters.precision :=
  segmentChunk parameters box
    (box.segments.getD chunk.segmentIndex default) chunk.start chunk.count

/-- Recomputed chunks for one box. -/
def boxComputedChunks (parameters : Parameters) (box : ProfileBox) :
    List (UpperContourKernel.DInterval parameters.precision) :=
  (boxChunkPlan box).map (boxChunkValue parameters box)

/-- Assemble one quadrature integral from supplied raw chunk endpoints. -/
def boxIntegralFrom (parameters : Parameters) (box : ProfileBox)
    (chunks : List (UpperContourKernel.DInterval parameters.precision)) :
    UpperContourKernel.DInterval parameters.precision :=
  let alpha := box.sigma * box.sigma / 2
  let cap := realCapUpper parameters.precision box.profileLeft box.lam
  let cells := chunks.foldl (· + ·)
    (UpperContourKernel.zero parameters.precision)
  let tail := UpperContourKernel.tensorPower cap parameters.rowOddPart
      parameters.rowSquareCount *
    Exp.negUpper parameters.precision
      (alpha * box.cutoff * box.cutoff) 28 *
    UpperContourKernel.frac parameters.precision
      (1 / (2 * (alpha * box.cutoff * box.cutoff)))
  cells + tail

/-- Complete integral from recomputed cells. -/
def boxIntegral (parameters : Parameters) (box : ProfileBox) :
    UpperContourKernel.DInterval parameters.precision :=
  boxIntegralFrom parameters box (boxComputedChunks parameters box)

/-- Security-scaled shifted-Gaussian prefactor. -/
def boxPrefactor (parameters : Parameters) (box : ProfileBox) :
    UpperContourKernel.DInterval parameters.precision :=
  let exponent := box.lam *
      (parameters.threshold - box.theta * box.sigma) -
    box.sigma * box.sigma * box.lam * box.lam / 2
  UpperContourKernel.scaledNegExpUpper parameters.precision
      parameters.securityBlockBits exponent 32
      parameters.securityScaleSquarings *
    UpperContourKernel.frac parameters.precision (1 / (314159 / 100000)) *
    UpperContourKernel.frac parameters.precision
      (1 / UpperContourKernel.phiLower box.theta) *
    UpperContourKernel.frac parameters.precision
      (1 / (1 - box.lam) ^ (Parameters.rows parameters / 2))

/-- Complete numeric endpoint for one profile box. -/
def boxBound (parameters : Parameters) (box : ProfileBox) :
    UpperContourKernel.DInterval parameters.precision :=
  boxPrefactor parameters box * boxIntegral parameters box

/-- Strict endpoint checker for one low-profile box. -/
def boxCheck (parameters : Parameters) (box : ProfileBox) : Bool :=
  Interval.upperLTCheck (boxBound parameters box) box.target

/-- Aggregate strict endpoint checker for a profile partition. -/
def allBoxesCheck (parameters : Parameters) (boxes : List ProfileBox) : Bool :=
  (boxes.map (boxCheck parameters)).all id

/-- Independent high-profile real-axis endpoint. -/
def highProfileBound (parameters : Parameters) (box : HighProfileBox) :
    UpperContourKernel.DInterval parameters.precision :=
  let cap := realCapUpper parameters.precision box.profileMinimum box.lam
  UpperContourKernel.scaledNegExpUpper parameters.precision
      parameters.securityBlockBits (box.lam * parameters.threshold) 34
      parameters.securityScaleSquarings *
    UpperContourKernel.frac parameters.precision
      (1 / (1 - box.lam) ^ (Parameters.rows parameters / 2)) *
    UpperContourKernel.tensorPower cap parameters.rowOddPart
      parameters.rowSquareCount

/-- Strict high-profile endpoint checker. -/
def highProfileCheck (parameters : Parameters) (box : HighProfileBox) : Bool :=
  Interval.upperLTCheck (highProfileBound parameters box) box.target

end CertifiedJL.SparseUpperContourFamily
