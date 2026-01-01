import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box00
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box00

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_020 :
    segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 200 10 =
      SparseUpperHybridGenerated.Box00.chunk 20 := by
  change segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 200 10 =
    ⟨0, 56134789831268021692671329718128426353030⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_020_sideCheck :
    segmentChunkSideCheck ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 200 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_021 :
    segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 210 10 =
      SparseUpperHybridGenerated.Box00.chunk 21 := by
  change segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 210 10 =
    ⟨0, 259458212846568348702664016197977742838⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_021_sideCheck :
    segmentChunkSideCheck ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 210 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_022 :
    segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨1, 1 / 50, 50⟩ 0 10 =
      SparseUpperHybridGenerated.Box00.chunk 22 := by
  change segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨1, 1 / 50, 50⟩ 0 10 =
    ⟨0, 2868392038239096035023125623984395929⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_022_sideCheck :
    segmentChunkSideCheck ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨1, 1 / 50, 50⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_023 :
    segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨1, 1 / 50, 50⟩ 10 10 =
      SparseUpperHybridGenerated.Box00.chunk 23 := by
  change segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨1, 1 / 50, 50⟩ 10 10 =
    ⟨0, 2364153806470124214626407756⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_023_sideCheck :
    segmentChunkSideCheck ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨1, 1 / 50, 50⟩ 10 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_024 :
    segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨1, 1 / 50, 50⟩ 20 10 =
      SparseUpperHybridGenerated.Box00.chunk 24 := by
  change segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨1, 1 / 50, 50⟩ 20 10 =
    ⟨0, 30839628663901370422⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_024_sideCheck :
    segmentChunkSideCheck ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨1, 1 / 50, 50⟩ 20 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box00
