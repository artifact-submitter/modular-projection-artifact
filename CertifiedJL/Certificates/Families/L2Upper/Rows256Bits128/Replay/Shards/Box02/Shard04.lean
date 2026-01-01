import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box02
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box02

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_020 :
    segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 200 10 =
      SparseUpperHybridGenerated.Box02.chunk 20 := by
  change segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 200 10 =
    ⟨0, 5482739798098123492681990853126584967662047593000230974⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_020_sideCheck :
    segmentChunkSideCheck ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 200 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_021 :
    segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 210 10 =
      SparseUpperHybridGenerated.Box02.chunk 21 := by
  change segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 210 10 =
    ⟨0, 45049242113922333044939314780724253355777453827197091⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_021_sideCheck :
    segmentChunkSideCheck ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 210 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_022 :
    segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 220 10 =
      SparseUpperHybridGenerated.Box02.chunk 22 := by
  change segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 220 10 =
    ⟨0, 420321949421588127810708092271562422609356745865961⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_022_sideCheck :
    segmentChunkSideCheck ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 220 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_023 :
    segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 230 10 =
      SparseUpperHybridGenerated.Box02.chunk 23 := by
  change segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 230 10 =
    ⟨0, 4444300179712534967461947712985102910824241909868⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_023_sideCheck :
    segmentChunkSideCheck ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 230 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_024 :
    segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 240 10 =
      SparseUpperHybridGenerated.Box02.chunk 24 := by
  change segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 240 10 =
    ⟨0, 53113325092856070837107651333829810050027994208⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_024_sideCheck :
    segmentChunkSideCheck ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 240 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box02
