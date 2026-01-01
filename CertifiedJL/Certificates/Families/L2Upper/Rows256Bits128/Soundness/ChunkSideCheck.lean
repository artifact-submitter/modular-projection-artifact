/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.Core

/-!
# Compact side-condition checks for hybrid certificate chunks

The generated replay proves one Boolean side-condition check per ten-cell
chunk.  This module supplies the kernel theorem extracting any individual
cell check from that compact Boolean fact.
-/

namespace CertifiedJL
namespace SparseUpperHybrid

/-- All semantic interval side conditions in one bounded segment chunk. -/
def segmentChunkSideCheck (box : ProfileBox) (segment : Segment)
    (start count : ℕ) : Bool :=
  (List.range count).all fun offset =>
    hybridCellSideCheck box segment (start + offset)

/-- Extract one cell's side-condition check from the chunk Boolean. -/
theorem segmentChunkSideCheck_cell
    (box : ProfileBox) (segment : Segment) (start count : ℕ)
    (hcheck : segmentChunkSideCheck box segment start count = true)
    (offset : ℕ) (hoffset : offset < count) :
    hybridCellSideCheck box segment (start + offset) = true := by
  exact (List.all_eq_true.mp hcheck) offset (List.mem_range.mpr hoffset)

/-- Check that a finite list of `(start, count)` chunk ranges covers every
cell index below `cellCount`.  This is cheap structural arithmetic; the
expensive cell conditions remain in the independently replayed chunk facts. -/
def chunkRangesCover (cellCount : ℕ) (chunks : List (ℕ × ℕ)) : Bool :=
  (List.range cellCount).all fun i =>
    chunks.any fun chunk => decide (chunk.1 ≤ i ∧ i < chunk.1 + chunk.2)

/-- Covered chunk checks supply every individual cell check. -/
theorem segmentSideChecks_of_chunkRanges
    (box : ProfileBox) (segment : Segment) (chunks : List (ℕ × ℕ))
    (hcover : chunkRangesCover segment.count chunks = true)
    (hchecks : chunks.all fun chunk =>
      segmentChunkSideCheck box segment chunk.1 chunk.2)
    (i : ℕ) (hi : i < segment.count) :
    hybridCellSideCheck box segment i = true := by
  have hiMem : i ∈ List.range segment.count := List.mem_range.mpr hi
  have hcovered := (List.all_eq_true.mp hcover) i hiMem
  rcases List.any_eq_true.mp hcovered with ⟨chunk, hchunkMem, hbounds⟩
  have hbounds' : chunk.1 ≤ i ∧ i < chunk.1 + chunk.2 :=
    of_decide_eq_true hbounds
  have hchunk := (List.all_eq_true.mp hchecks) chunk hchunkMem
  have hoffset : i - chunk.1 < chunk.2 := by omega
  have hcell := segmentChunkSideCheck_cell box segment chunk.1 chunk.2
    hchunk (i - chunk.1) hoffset
  rwa [Nat.add_sub_of_le hbounds'.1] at hcell

end SparseUpperHybrid
end CertifiedJL
