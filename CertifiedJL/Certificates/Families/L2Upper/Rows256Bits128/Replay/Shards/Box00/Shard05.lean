import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box00
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box00

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_025 :
    segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨1, 1 / 50, 50⟩ 30 10 =
      SparseUpperHybridGenerated.Box00.chunk 25 := by
  change segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨1, 1 / 50, 50⟩ 30 10 =
    ⟨0, 3839708640187⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_025_sideCheck :
    segmentChunkSideCheck ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨1, 1 / 50, 50⟩ 30 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_026 :
    segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨1, 1 / 50, 50⟩ 40 10 =
      SparseUpperHybridGenerated.Box00.chunk 26 := by
  change segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨1, 1 / 50, 50⟩ 40 10 =
    ⟨0, 3259809⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_026_sideCheck :
    segmentChunkSideCheck ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨1, 1 / 50, 50⟩ 40 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_027 :
    segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨2, 1 / 20, 40⟩ 0 10 =
      SparseUpperHybridGenerated.Box00.chunk 27 := by
  change segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨2, 1 / 20, 40⟩ 0 10 =
    ⟨0, 43⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_027_sideCheck :
    segmentChunkSideCheck ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨2, 1 / 20, 40⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_028 :
    segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨2, 1 / 20, 40⟩ 10 10 =
      SparseUpperHybridGenerated.Box00.chunk 28 := by
  change segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨2, 1 / 20, 40⟩ 10 10 =
    ⟨0, 10⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_028_sideCheck :
    segmentChunkSideCheck ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨2, 1 / 20, 40⟩ 10 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_029 :
    segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨2, 1 / 20, 40⟩ 20 10 =
      SparseUpperHybridGenerated.Box00.chunk 29 := by
  change segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨2, 1 / 20, 40⟩ 20 10 =
    ⟨0, 10⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_029_sideCheck :
    segmentChunkSideCheck ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨2, 1 / 20, 40⟩ 20 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box00
