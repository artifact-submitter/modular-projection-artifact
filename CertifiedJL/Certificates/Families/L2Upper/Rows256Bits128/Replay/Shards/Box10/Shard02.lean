import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box10
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box10

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_010 :
    segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 100 10 =
      SparseUpperHybridGenerated.Box10.chunk 10 := by
  change segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 100 10 =
    ⟨0, 1324726168281914741939637381543799452190466669549164093034487318876011773⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_010_sideCheck :
    segmentChunkSideCheck ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 100 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_011 :
    segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 110 10 =
      SparseUpperHybridGenerated.Box10.chunk 11 := by
  change segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 110 10 =
    ⟨0, 1158665581390053470727632280897648617406891466237237574305450942661038⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_011_sideCheck :
    segmentChunkSideCheck ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 110 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_012 :
    segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 120 10 =
      SparseUpperHybridGenerated.Box10.chunk 12 := by
  change segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 120 10 =
    ⟨0, 1163481658852622767090751821738739849994886063544884756917711448453⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_012_sideCheck :
    segmentChunkSideCheck ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 120 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_013 :
    segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 130 10 =
      SparseUpperHybridGenerated.Box10.chunk 13 := by
  change segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 130 10 =
    ⟨0, 1392948587510373869012262528686678967437757919102001912163528992⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_013_sideCheck :
    segmentChunkSideCheck ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 130 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_014 :
    segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 140 10 =
      SparseUpperHybridGenerated.Box10.chunk 14 := by
  change segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 140 10 =
    ⟨0, 2038441503260865107153737108708167255095242847484643941787856⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_014_sideCheck :
    segmentChunkSideCheck ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 140 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box10
