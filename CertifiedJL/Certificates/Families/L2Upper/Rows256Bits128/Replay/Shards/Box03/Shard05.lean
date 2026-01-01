import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box03
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box03

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_025 :
    segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 250 10 =
      SparseUpperHybridGenerated.Box03.chunk 25 := by
  change segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 250 10 =
    ⟨0, 487456811241520732700762760650089238242666⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_025_sideCheck :
    segmentChunkSideCheck ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 250 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_026 :
    segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 260 10 =
      SparseUpperHybridGenerated.Box03.chunk 26 := by
  change segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 260 10 =
    ⟨0, 6897015555134740236706386385537483123492⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_026_sideCheck :
    segmentChunkSideCheck ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 260 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_027 :
    segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 270 10 =
      SparseUpperHybridGenerated.Box03.chunk 27 := by
  change segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 270 10 =
    ⟨0, 110542823086503650253584526690885212652⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_027_sideCheck :
    segmentChunkSideCheck ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 270 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_028 :
    segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨1, 1 / 50, 50⟩ 0 10 =
      SparseUpperHybridGenerated.Box03.chunk 28 := by
  change segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨1, 1 / 50, 50⟩ 0 10 =
    ⟨0, 4309587010062557828674743656949137602⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_028_sideCheck :
    segmentChunkSideCheck ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨1, 1 / 50, 50⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_029 :
    segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨1, 1 / 50, 50⟩ 10 10 =
      SparseUpperHybridGenerated.Box03.chunk 29 := by
  change segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨1, 1 / 50, 50⟩ 10 10 =
    ⟨0, 5799560456104094645912786925⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_029_sideCheck :
    segmentChunkSideCheck ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨1, 1 / 50, 50⟩ 10 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box03
