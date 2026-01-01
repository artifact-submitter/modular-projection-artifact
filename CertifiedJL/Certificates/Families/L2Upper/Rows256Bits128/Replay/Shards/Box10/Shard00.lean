import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box10
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box10

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_000 :
    segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 0 10 =
      SparseUpperHybridGenerated.Box10.chunk 0 := by
  change segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 0 10 =
    ⟨0, 117448736905963824067294291648900062111143308229608598411500486198205237245719722758864566482031⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_000_sideCheck :
    segmentChunkSideCheck ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_001 :
    segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 10 10 =
      SparseUpperHybridGenerated.Box10.chunk 1 := by
  change segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 10 10 =
    ⟨0, 32452087469169659391959776324828234411181955901299753500965024073935225613223595075663670876047⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_001_sideCheck :
    segmentChunkSideCheck ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 10 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_002 :
    segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 20 10 =
      SparseUpperHybridGenerated.Box10.chunk 2 := by
  change segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 20 10 =
    ⟨0, 2350000424022725872391979668842712165458556380032647459133420000909104603605944342895617375288⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_002_sideCheck :
    segmentChunkSideCheck ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 20 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_003 :
    segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 30 10 =
      SparseUpperHybridGenerated.Box10.chunk 3 := by
  change segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 30 10 =
    ⟨0, 49609974105034754546945823705171266311024860961831576599059298493005284692587425332046792820⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_003_sideCheck :
    segmentChunkSideCheck ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 30 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_004 :
    segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 40 10 =
      SparseUpperHybridGenerated.Box10.chunk 4 := by
  change segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 40 10 =
    ⟨0, 369911882002694602441721972350226780812305651074699256139825458917815606693686189422265706⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_004_sideCheck :
    segmentChunkSideCheck ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 40 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box10
