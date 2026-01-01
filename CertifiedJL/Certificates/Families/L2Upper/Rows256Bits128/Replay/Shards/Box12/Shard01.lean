import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box12
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box12

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_005 :
    segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 50 10 =
      SparseUpperHybridGenerated.Box12.chunk 5 := by
  change segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 50 10 =
    ⟨0, 62389661254302895463839477764698994732246541196549147401440138286876932226⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_005_sideCheck :
    segmentChunkSideCheck ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 50 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_006 :
    segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 60 10 =
      SparseUpperHybridGenerated.Box12.chunk 6 := by
  change segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 60 10 =
    ⟨0, 101968640772866838105946313084347549210664707164272407946705211711636⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_006_sideCheck :
    segmentChunkSideCheck ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 60 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_007 :
    segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 70 10 =
      SparseUpperHybridGenerated.Box12.chunk 7 := by
  change segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 70 10 =
    ⟨0, 322479936158880700157919696490353732868875722063685295579738816⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_007_sideCheck :
    segmentChunkSideCheck ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 70 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_008 :
    segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 80 10 =
      SparseUpperHybridGenerated.Box12.chunk 8 := by
  change segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 80 10 =
    ⟨0, 2526365149001851277834309603185903202513497355101309871815⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_008_sideCheck :
    segmentChunkSideCheck ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 80 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_009 :
    segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 90 10 =
      SparseUpperHybridGenerated.Box12.chunk 9 := by
  change segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 90 10 =
    ⟨0, 57091931687684120321507092916066306475409118049922950⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_009_sideCheck :
    segmentChunkSideCheck ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 90 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box12
