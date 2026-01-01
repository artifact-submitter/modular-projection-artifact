import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box14
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box14

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_005 :
    segmentChunk ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨1, 1 / 11, 11⟩ 0 10 =
      SparseUpperHybridGenerated.Box14.chunk 5 := by
  change segmentChunk ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨1, 1 / 11, 11⟩ 0 10 =
    ⟨0, 18359069577324988817907655244405098981314824190769674852200623063855064530679765717601660078167⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_005_sideCheck :
    segmentChunkSideCheck ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨1, 1 / 11, 11⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_006 :
    segmentChunk ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨1, 1 / 11, 11⟩ 10 1 =
      SparseUpperHybridGenerated.Box14.chunk 6 := by
  change segmentChunk ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨1, 1 / 11, 11⟩ 10 1 =
    ⟨0, 712769498163195644895428641994147869746497300841435598638331406269795926351610524719215529962⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_006_sideCheck :
    segmentChunkSideCheck ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨1, 1 / 11, 11⟩ 10 1 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_007 :
    segmentChunk ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨2, 1 / 2, 4⟩ 0 4 =
      SparseUpperHybridGenerated.Box14.chunk 7 := by
  change segmentChunk ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨2, 1 / 2, 4⟩ 0 4 =
    ⟨0, 2964281346936559704274795105129925205551834262777339450331248246088076969691092004721983606171⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_007_sideCheck :
    segmentChunkSideCheck ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨2, 1 / 2, 4⟩ 0 4 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_008 :
    segmentChunk ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨4, 1, 4⟩ 0 4 =
      SparseUpperHybridGenerated.Box14.chunk 8 := by
  change segmentChunk ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨4, 1, 4⟩ 0 4 =
    ⟨0, 7928482689284960750128093872000373052827518538805484483698271382779063970617785537984634740⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_008_sideCheck :
    segmentChunkSideCheck ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨4, 1, 4⟩ 0 4 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box14
