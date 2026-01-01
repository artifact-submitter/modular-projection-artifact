import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box01
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box01

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_020 :
    segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 200 10 =
      SparseUpperHybridGenerated.Box01.chunk 20 := by
  change segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 200 10 =
    ⟨0, 4408671226650349426775602472142632858420679143481690⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_020_sideCheck :
    segmentChunkSideCheck ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 200 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_021 :
    segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 210 10 =
      SparseUpperHybridGenerated.Box01.chunk 21 := by
  change segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 210 10 =
    ⟨0, 31047395069314102113391891103529831283508822367868⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_021_sideCheck :
    segmentChunkSideCheck ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 210 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_022 :
    segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 220 10 =
      SparseUpperHybridGenerated.Box01.chunk 22 := by
  change segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 220 10 =
    ⟨0, 251901276278070294030049991275345127788393508445⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_022_sideCheck :
    segmentChunkSideCheck ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 220 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_023 :
    segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 230 10 =
      SparseUpperHybridGenerated.Box01.chunk 23 := by
  change segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 230 10 =
    ⟨0, 2345768614517257308824556533312437554708562877⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_023_sideCheck :
    segmentChunkSideCheck ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 230 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_024 :
    segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 240 10 =
      SparseUpperHybridGenerated.Box01.chunk 24 := by
  change segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 240 10 =
    ⟨0, 24967054328196455841640637142334046453188226⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_024_sideCheck :
    segmentChunkSideCheck ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 240 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box01
