import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box01
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box01

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_030 :
    segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨1, 1 / 50, 50⟩ 20 10 =
      SparseUpperHybridGenerated.Box01.chunk 30 := by
  change segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨1, 1 / 50, 50⟩ 20 10 =
    ⟨0, 36635670742076617120⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_030_sideCheck :
    segmentChunkSideCheck ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨1, 1 / 50, 50⟩ 20 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_031 :
    segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨1, 1 / 50, 50⟩ 30 10 =
      SparseUpperHybridGenerated.Box01.chunk 31 := by
  change segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨1, 1 / 50, 50⟩ 30 10 =
    ⟨0, 7490935660509⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_031_sideCheck :
    segmentChunkSideCheck ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨1, 1 / 50, 50⟩ 30 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_032 :
    segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨1, 1 / 50, 50⟩ 40 10 =
      SparseUpperHybridGenerated.Box01.chunk 32 := by
  change segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨1, 1 / 50, 50⟩ 40 10 =
    ⟨0, 15847617⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_032_sideCheck :
    segmentChunkSideCheck ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨1, 1 / 50, 50⟩ 40 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_033 :
    segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨2, 1 / 20, 40⟩ 0 10 =
      SparseUpperHybridGenerated.Box01.chunk 33 := by
  change segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨2, 1 / 20, 40⟩ 0 10 =
    ⟨0, 974⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_033_sideCheck :
    segmentChunkSideCheck ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨2, 1 / 20, 40⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_034 :
    segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨2, 1 / 20, 40⟩ 10 10 =
      SparseUpperHybridGenerated.Box01.chunk 34 := by
  change segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨2, 1 / 20, 40⟩ 10 10 =
    ⟨0, 112⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_034_sideCheck :
    segmentChunkSideCheck ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨2, 1 / 20, 40⟩ 10 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box01
