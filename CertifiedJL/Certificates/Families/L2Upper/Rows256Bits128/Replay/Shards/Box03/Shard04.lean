import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box03
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box03

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_020 :
    segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 200 10 =
      SparseUpperHybridGenerated.Box03.chunk 20 := by
  change segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 200 10 =
    ⟨0, 6391521231516874756938929354801680753153941170869623⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_020_sideCheck :
    segmentChunkSideCheck ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 200 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_021 :
    segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 210 10 =
      SparseUpperHybridGenerated.Box03.chunk 21 := by
  change segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 210 10 =
    ⟨0, 45757579554340995939247392225170194058055397787275⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_021_sideCheck :
    segmentChunkSideCheck ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 210 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_022 :
    segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 220 10 =
      SparseUpperHybridGenerated.Box03.chunk 22 := by
  change segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 220 10 =
    ⟨0, 378138942238590811318823217383799729818646458234⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_022_sideCheck :
    segmentChunkSideCheck ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 220 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_023 :
    segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 230 10 =
      SparseUpperHybridGenerated.Box03.chunk 23 := by
  change segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 230 10 =
    ⟨0, 3595170280177244162617493397722713341982185948⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_023_sideCheck :
    segmentChunkSideCheck ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 230 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_024 :
    segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 240 10 =
      SparseUpperHybridGenerated.Box03.chunk 24 := by
  change segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 240 10 =
    ⟨0, 39178555301096348175958984479300075287878189⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_024_sideCheck :
    segmentChunkSideCheck ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 240 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box03
