import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box04
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box04

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_015 :
    segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 150 10 =
      SparseUpperHybridGenerated.Box04.chunk 15 := by
  change segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 150 10 =
    ⟨0, 2548185156768187988787082538591762794566544244993975774653290104⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_015_sideCheck :
    segmentChunkSideCheck ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 150 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_016 :
    segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 160 10 =
      SparseUpperHybridGenerated.Box04.chunk 16 := by
  change segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 160 10 =
    ⟨0, 8729045369575879136677811106968958216356382304812552350441660⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_016_sideCheck :
    segmentChunkSideCheck ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 160 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_017 :
    segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 170 10 =
      SparseUpperHybridGenerated.Box04.chunk 17 := by
  change segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 170 10 =
    ⟨0, 34506950508732955010063154857077626853592782200156218443738⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_017_sideCheck :
    segmentChunkSideCheck ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 170 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_018 :
    segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 180 10 =
      SparseUpperHybridGenerated.Box04.chunk 18 := by
  change segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 180 10 =
    ⟨0, 158169468609414936595231474289652398050917793003894439809⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_018_sideCheck :
    segmentChunkSideCheck ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 180 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_019 :
    segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 190 10 =
      SparseUpperHybridGenerated.Box04.chunk 19 := by
  change segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 190 10 =
    ⟨0, 842264204987988869955240163557180589475543903416560063⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_019_sideCheck :
    segmentChunkSideCheck ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 190 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box04
