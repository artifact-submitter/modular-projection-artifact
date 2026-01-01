import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box03
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box03

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_015 :
    segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 150 10 =
      SparseUpperHybridGenerated.Box03.chunk 15 := by
  change segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 150 10 =
    ⟨0, 3070275557422067591443013939723346325770906710383356470477240956⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_015_sideCheck :
    segmentChunkSideCheck ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 150 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_016 :
    segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 160 10 =
      SparseUpperHybridGenerated.Box03.chunk 16 := by
  change segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 160 10 =
    ⟨0, 10592607038919058294180032400665384925586470946624761044887848⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_016_sideCheck :
    segmentChunkSideCheck ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 160 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_017 :
    segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 170 10 =
      SparseUpperHybridGenerated.Box03.chunk 17 := by
  change segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 170 10 =
    ⟨0, 42101310602954213168375800943357452092851328382326160124774⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_017_sideCheck :
    segmentChunkSideCheck ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 170 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_018 :
    segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 180 10 =
      SparseUpperHybridGenerated.Box03.chunk 18 := by
  change segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 180 10 =
    ⟨0, 193689867050483329119453700159903667164644378390416533279⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_018_sideCheck :
    segmentChunkSideCheck ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 180 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_019 :
    segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 190 10 =
      SparseUpperHybridGenerated.Box03.chunk 19 := by
  change segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 190 10 =
    ⟨0, 1033336207417232880361793318149737348378960300856069996⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_019_sideCheck :
    segmentChunkSideCheck ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 190 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box03
