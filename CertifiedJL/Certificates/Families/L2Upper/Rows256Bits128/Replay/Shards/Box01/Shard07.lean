import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box01
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box01

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_035 :
    segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨2, 1 / 20, 40⟩ 20 10 =
      SparseUpperHybridGenerated.Box01.chunk 35 := by
  change segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨2, 1 / 20, 40⟩ 20 10 =
    ⟨0, 13981432440257727158684302⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_035_sideCheck :
    segmentChunkSideCheck ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨2, 1 / 20, 40⟩ 20 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_036 :
    segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨2, 1 / 20, 40⟩ 30 10 =
      SparseUpperHybridGenerated.Box01.chunk 36 := by
  change segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨2, 1 / 20, 40⟩ 30 10 =
    ⟨0, 668059287185554652340105348884082187621824945055220664532333358339988⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_036_sideCheck :
    segmentChunkSideCheck ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨2, 1 / 20, 40⟩ 30 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_037 :
    segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨4, 1 / 6, 24⟩ 0 10 =
      SparseUpperHybridGenerated.Box01.chunk 37 := by
  change segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨4, 1 / 6, 24⟩ 0 10 =
    ⟨0, 3066116397473922936401215607613816836232274231736573875373608222709454360747704097935318640855⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_037_sideCheck :
    segmentChunkSideCheck ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨4, 1 / 6, 24⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_038 :
    segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨4, 1 / 6, 24⟩ 10 10 =
      SparseUpperHybridGenerated.Box01.chunk 38 := by
  change segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨4, 1 / 6, 24⟩ 10 10 =
    ⟨0, 181289922464104196893516310022859890309293393085699500862697235744251335532683133380726173301⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_038_sideCheck :
    segmentChunkSideCheck ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨4, 1 / 6, 24⟩ 10 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_039 :
    segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨4, 1 / 6, 24⟩ 20 4 =
      SparseUpperHybridGenerated.Box01.chunk 39 := by
  change segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨4, 1 / 6, 24⟩ 20 4 =
    ⟨0, 10395783245976602521210688105461586875166725289004169238017756662640709803693400396283515499⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_039_sideCheck :
    segmentChunkSideCheck ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨4, 1 / 6, 24⟩ 20 4 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box01
