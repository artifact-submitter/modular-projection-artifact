import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box06
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box06

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_020 :
    segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 200 10 =
      SparseUpperHybridGenerated.Box06.chunk 20 := by
  change segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 200 10 =
    ⟨0, 83477355595036682954541684858865877803946⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_020_sideCheck :
    segmentChunkSideCheck ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 200 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_021 :
    segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 210 10 =
      SparseUpperHybridGenerated.Box06.chunk 21 := by
  change segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 210 10 =
    ⟨0, 441207810799861895236249311321117024250⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_021_sideCheck :
    segmentChunkSideCheck ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 210 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_022 :
    segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨1, 1 / 50, 50⟩ 0 10 =
      SparseUpperHybridGenerated.Box06.chunk 22 := by
  change segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨1, 1 / 50, 50⟩ 0 10 =
    ⟨0, 6014211235541224296998521929116854631⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_022_sideCheck :
    segmentChunkSideCheck ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨1, 1 / 50, 50⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_023 :
    segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨1, 1 / 50, 50⟩ 10 10 =
      SparseUpperHybridGenerated.Box06.chunk 23 := by
  change segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨1, 1 / 50, 50⟩ 10 10 =
    ⟨0, 18038874960739234262034165843⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_023_sideCheck :
    segmentChunkSideCheck ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨1, 1 / 50, 50⟩ 10 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_024 :
    segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨1, 1 / 50, 50⟩ 20 10 =
      SparseUpperHybridGenerated.Box06.chunk 24 := by
  change segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨1, 1 / 50, 50⟩ 20 10 =
    ⟨0, 3617365880819062771714⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_024_sideCheck :
    segmentChunkSideCheck ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨1, 1 / 50, 50⟩ 20 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box06
