/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Shared.UpperContourKernel

/-!
# Sparse 512-row, 192-bit, threshold-607 contour arithmetic

This module instantiates the shared interval kernel with exactly the sparse
U12 coefficients.  It fixes 512 rows, 192 security bits, and the strict
threshold `X > 607`, but it does not claim the analytic U10/U4 reduction.
-/

namespace CertifiedJL
namespace SparseUpperContour

/-- Fractional precision for the ten low-profile contour boxes. -/
def contourPrecision : ℕ := 512

/-- Fractional precision for the high-profile real-axis bound.  At 384 bits,
the negative-exponential enclosure underflows to one dyadic unit before the
remaining factors are multiplied; 512 bits preserves the strict endpoint. -/
def highProfilePrecision : ℕ := 512

/-- Number of independent rows in U10/U12. -/
def rows : ℕ := 512

/-- Security exponent in the scaled certificate endpoint. -/
def securityBits : ℕ := 192

/-- Strict upper-tail threshold from U11. -/
def threshold : ℚ := 607

/-- Sparse-specific coefficients from U12. -/
def rowCoefficients : UpperContourKernel.RowCoefficients where
  leading := 1 / 8
  error8 := 1 / 9216
  error6 := 11 / 5760

/-- A rational profile box and its U10 contour parameters. -/
structure ProfileBox where
  profileLeft : ℚ
  profileRight : ℚ
  lam : ℚ
  sigma : ℚ
  theta : ℚ
  target : ℚ
deriving DecidableEq, Inhabited

/-- The ten exact U14 boxes in profile order. -/
def profileBoxes : List ProfileBox :=
  [ ⟨0, 1 / 1024, 579 / 1000, 743 / 1000, 59 / 100, 97 / 100⟩,
    ⟨1 / 1024, 1 / 512, 579 / 1000, 891 / 1000, 41 / 100, 99 / 100⟩,
    ⟨1 / 512, 3 / 1024, 579 / 1000, 993 / 1000, 29 / 100, 99 / 100⟩,
    ⟨3 / 1024, 1 / 256, 579 / 1000, 1073 / 1000, 21 / 100, 49 / 50⟩,
    ⟨1 / 256, 3 / 512, 579 / 1000, 1201 / 1000, 7 / 100, 99 / 100⟩,
    ⟨3 / 512, 1 / 128, 579 / 1000, 1294 / 1000, 0, 19 / 20⟩,
    ⟨1 / 128, 1 / 64, 579 / 1000, 1511 / 1000, 0, 99 / 100⟩,
    ⟨1 / 64, 3 / 128, 579 / 1000, 1617 / 1000, 0, 3 / 4⟩,
    ⟨3 / 128, 1 / 32, 579 / 1000, 1659 / 1000, 0, 3 / 5⟩,
    ⟨1 / 32, 1 / 20, 579 / 1000, 1692 / 1000, 0, 3 / 5⟩ ]

/-- The U14 profile endpoints are adjacent and cover `[0,1/20]`. -/
theorem profileBoxes_cover :
    profileBoxes.map (fun box => (box.profileLeft, box.profileRight)) =
      [ (0, 1 / 1024), (1 / 1024, 1 / 512),
        (1 / 512, 3 / 1024), (3 / 1024, 1 / 256),
        (1 / 256, 3 / 512), (3 / 512, 1 / 128),
        (1 / 128, 1 / 64), (1 / 64, 3 / 128),
        (3 / 128, 1 / 32), (1 / 32, 1 / 20) ] := by
  norm_num [profileBoxes]

/-- First U14 box, used for the complete 800-cell replay. -/
def firstBox : ProfileBox := profileBoxes.head!

/-- Profile box at an explicit certificate index, defaulting to the first box. -/
def profileBox (index : ℕ) : ProfileBox := profileBoxes.getD index firstBox

/-- Pairwise endpoint adjacency for a list of profile boxes. -/
def ProfileBoxesAdjacent : List ProfileBox → Prop
  | [] | [_] => True
  | left :: right :: rest =>
      left.profileRight = right.profileLeft ∧
        ProfileBoxesAdjacent (right :: rest)

/-- All ten U14 boxes meet exactly at their rational endpoints. -/
theorem profileBoxes_adjacent : ProfileBoxesAdjacent profileBoxes := by
  norm_num [ProfileBoxesAdjacent, profileBoxes]

/-- The sparse certificate contains exactly ten low-profile boxes. -/
theorem profileBoxes_length : profileBoxes.length = 10 := by
  norm_num [profileBoxes]

/-- The sparse U12 expression on one frequency cell. -/
def rowExpressionOnCell (profile frequencyLeft frequencyRight lam : ℚ) :
    UpperContourKernel.DInterval contourPrecision :=
  UpperContourKernel.rowExpressionOnCell contourPrecision rowCoefficients
    profile frequencyLeft frequencyRight lam

/-- Outward upper enclosure of the decreasing U8 real-axis cap. -/
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

/-- One Gaussian-weighted sparse quadrature cell, capped by U8. -/
def gaussianCell
    (profileLeft profileRight lam sigma mesh : ℚ) (index : ℕ) :
    UpperContourKernel.DInterval contourPrecision :=
  let frequencyLeft := index * mesh
  let frequencyRight := (index + 1) * mesh
  let expressionLeft :=
    rowExpressionOnCell profileLeft frequencyLeft frequencyRight lam
  let expressionRight :=
    rowExpressionOnCell profileRight frequencyLeft frequencyRight lam
  let cap := realCapUpper contourPrecision profileLeft lam
  let rowUpper := min cap.hi (max expressionLeft.hi expressionRight.hi)
  let alpha := sigma * sigma / 2
  let gaussianWeight :=
    Exp.negUpper contourPrecision (alpha * frequencyLeft * frequencyLeft) 24
  UpperContourKernel.frac contourPrecision mesh * gaussianWeight *
    (Interval.mk 0 rowUpper).squareN 9 *
    UpperContourKernel.inverseSqrtAtLeft contourPrecision frequencyLeft lam

/-- Evaluate `count` cells of a sparse U14 box, beginning at `start`. -/
def boxCellChunk (box : ProfileBox) (start count : ℕ) :
    UpperContourKernel.DInterval contourPrecision :=
  let mesh : ℚ := 1 / 100
  (List.range count).foldl
    (fun result offset =>
      result + gaussianCell box.profileLeft box.profileRight
        box.lam box.sigma mesh (start + offset))
    (UpperContourKernel.zero contourPrecision)

/-- Evaluate a chunk of the first box. Kept for source compatibility. -/
def firstBoxCellChunk (start count : ℕ) :
    UpperContourKernel.DInterval contourPrecision :=
  boxCellChunk firstBox start count

/-- Default replay chunk size selected by the bounded benchmark. -/
def boxChunkSize : ℕ := 25

/-- First-box spelling retained for source compatibility. -/
def firstBoxChunkSize : ℕ := boxChunkSize

/-- Number of chunks covering all 800 frequency cells. -/
def boxChunkCount : ℕ := 32

/-- First-box spelling retained for source compatibility. -/
def firstBoxChunkCount : ℕ := boxChunkCount

/-- Consecutive chunk plan shared by every sparse profile box. -/
def boxChunkPlan : List (ℕ × ℕ) :=
  (List.range boxChunkCount).map fun index =>
    (boxChunkSize * index, boxChunkSize)

/-- First-box spelling retained for source compatibility. -/
def firstBoxChunkPlan : List (ℕ × ℕ) := boxChunkPlan

/-- The shared sparse plan covers exactly the mesh cells `0, ..., 799`. -/
theorem boxChunkPlan_covers :
    UpperContourKernel.coveredCellsFor boxChunkPlan = List.range 800 := by
  decide +kernel

/-- First-box coverage theorem retained for source compatibility. -/
theorem firstBoxChunkPlan_covers :
    UpperContourKernel.coveredCellsFor firstBoxChunkPlan = List.range 800 :=
  boxChunkPlan_covers

/-- Recomputed chunks for all 800 cells of one sparse U14 box. -/
def boxComputedChunks (box : ProfileBox) :
    List (UpperContourKernel.DInterval contourPrecision) :=
  boxChunkPlan.map fun chunk => boxCellChunk box chunk.1 chunk.2

/-- Recomputed first-box chunks retained for source compatibility. -/
def firstBoxComputedChunks :
    List (UpperContourKernel.DInterval contourPrecision) :=
  boxComputedChunks firstBox

/-- Assemble one box integral from supplied raw chunk endpoints. -/
def boxIntegralFrom (box : ProfileBox)
    (chunks : List (UpperContourKernel.DInterval contourPrecision)) :
    UpperContourKernel.DInterval contourPrecision :=
  let cutoff : ℚ := 8
  let alpha := box.sigma * box.sigma / 2
  let cap := realCapUpper contourPrecision box.profileLeft box.lam
  let cells := chunks.foldl (· + ·) (UpperContourKernel.zero contourPrecision)
  let tail := cap.squareN 9 *
    Exp.negUpper contourPrecision (alpha * cutoff * cutoff) 28 *
    UpperContourKernel.frac contourPrecision
      (1 / (2 * (alpha * cutoff * cutoff)))
  cells + tail

/-- First-box assembly retained for source compatibility. -/
def firstBoxIntegralFrom
    (chunks : List (UpperContourKernel.DInterval contourPrecision)) :
    UpperContourKernel.DInterval contourPrecision :=
  boxIntegralFrom firstBox chunks

/-- Complete integral from recomputed cells for one box. -/
def boxIntegral (box : ProfileBox) :
    UpperContourKernel.DInterval contourPrecision :=
  boxIntegralFrom box (boxComputedChunks box)

/-- Complete first-box integral retained for source compatibility. -/
def firstBoxIntegral : UpperContourKernel.DInterval contourPrecision :=
  boxIntegral firstBox

/-- Exact U10 prefactor for one sparse U14 box. -/
def boxPrefactor (box : ProfileBox) :
    UpperContourKernel.DInterval contourPrecision :=
  let exponent := box.lam *
      (threshold - box.theta * box.sigma) -
    box.sigma * box.sigma * box.lam * box.lam / 2
  UpperContourKernel.scaledNegExpUpper contourPrecision 12 exponent 32 4 *
    UpperContourKernel.frac contourPrecision (1 / (314159 / 100000)) *
    UpperContourKernel.frac contourPrecision
      (1 / UpperContourKernel.phiLower box.theta) *
    UpperContourKernel.frac contourPrecision
      (1 / (1 - box.lam) ^ (rows / 2))

/-- First-box prefactor retained for source compatibility. -/
def firstBoxPrefactor : UpperContourKernel.DInterval contourPrecision :=
  boxPrefactor firstBox

/-- Complete numeric endpoint for one sparse U14 profile box. -/
def boxBound (box : ProfileBox) :
    UpperContourKernel.DInterval contourPrecision :=
  boxPrefactor box * boxIntegral box

/-- First-box bound retained for source compatibility. -/
def firstBoxBound : UpperContourKernel.DInterval contourPrecision :=
  boxBound firstBox

/-- Strict U14 endpoint check for one sparse box. -/
def boxCheck (box : ProfileBox) : Bool :=
  Interval.upperLTCheck (boxBound box) box.target

/-- First-box check retained for source compatibility. -/
def firstBoxCheck : Bool := boxCheck firstBox

/-- Strict endpoint checks for all ten low-profile boxes. -/
def allBoxChecks : List Bool := profileBoxes.map boxCheck

/-- Aggregate strict endpoint checker for all ten low-profile boxes. -/
def allBoxesCheck : Bool := allBoxChecks.all id

/-- Separate high-profile U8/Chernoff endpoint at 384 bits. -/
def highProfileBound : UpperContourKernel.DInterval highProfilePrecision :=
  let lam : ℚ := 583 / 1000
  let cap := realCapUpper highProfilePrecision (1 / 20) lam
  UpperContourKernel.scaledNegExpUpper highProfilePrecision 12
      (lam * threshold) 34 4 *
    UpperContourKernel.frac highProfilePrecision (1 / (1 - lam) ^ (rows / 2)) *
    cap.squareN 9

/-- Strict endpoint check for the independent high-profile range. -/
def highProfileCheck : Bool :=
  Interval.upperLTCheck highProfileBound (1 / 2)

end SparseUpperContour
end CertifiedJL
