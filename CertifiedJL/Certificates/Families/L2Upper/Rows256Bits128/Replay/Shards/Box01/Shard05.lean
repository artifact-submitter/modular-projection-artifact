import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box01
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box01

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_025 :
    segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 250 10 =
      SparseUpperHybridGenerated.Box01.chunk 25 := by
  change segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 250 10 =
    ⟨0, 302379913328588827612732911193513573386616⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_025_sideCheck :
    segmentChunkSideCheck ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 250 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_026 :
    segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 260 10 =
      SparseUpperHybridGenerated.Box01.chunk 26 := by
  change segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 260 10 =
    ⟨0, 4148371291316730935226024649763488501015⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_026_sideCheck :
    segmentChunkSideCheck ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 260 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_027 :
    segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 270 10 =
      SparseUpperHybridGenerated.Box01.chunk 27 := by
  change segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 270 10 =
    ⟨0, 64177225277541172579810363269058701851⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_027_sideCheck :
    segmentChunkSideCheck ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 270 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_028 :
    segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨1, 1 / 50, 50⟩ 0 10 =
      SparseUpperHybridGenerated.Box01.chunk 28 := by
  change segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨1, 1 / 50, 50⟩ 0 10 =
    ⟨0, 2370414868984465278717443606633869075⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_028_sideCheck :
    segmentChunkSideCheck ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨1, 1 / 50, 50⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_029 :
    segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨1, 1 / 50, 50⟩ 10 10 =
      SparseUpperHybridGenerated.Box01.chunk 29 := by
  change segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨1, 1 / 50, 50⟩ 10 10 =
    ⟨0, 2184778280546323299766724442⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_029_sideCheck :
    segmentChunkSideCheck ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨1, 1 / 50, 50⟩ 10 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box01
