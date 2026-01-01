import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box09
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box09

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_005 :
    segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 50 10 =
      SparseUpperHybridGenerated.Box09.chunk 5 := by
  change segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 50 10 =
    ⟨0, 2449540632255379658357263043212485706956654351362558533470029645819459811023948891332⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_005_sideCheck :
    segmentChunkSideCheck ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 50 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_006 :
    segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 60 10 =
      SparseUpperHybridGenerated.Box09.chunk 6 := by
  change segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 60 10 =
    ⟨0, 714640490025632613264045203933817548556446271834252167617934024942496057627573009⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_006_sideCheck :
    segmentChunkSideCheck ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 60 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_007 :
    segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 70 10 =
      SparseUpperHybridGenerated.Box09.chunk 7 := by
  change segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 70 10 =
    ⟨0, 153043953957732981150741397762866809518911321931309916748004115790059179164283⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_007_sideCheck :
    segmentChunkSideCheck ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 70 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_008 :
    segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 80 10 =
      SparseUpperHybridGenerated.Box09.chunk 8 := by
  change segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 80 10 =
    ⟨0, 30029238719872535684023762552942289409735406370633145568715105632751335213⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_008_sideCheck :
    segmentChunkSideCheck ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 80 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_009 :
    segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 90 10 =
      SparseUpperHybridGenerated.Box09.chunk 9 := by
  change segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 90 10 =
    ⟨0, 6313954064854399157080364486340315088540450283050870179466635492476284⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_009_sideCheck :
    segmentChunkSideCheck ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 90 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box09
