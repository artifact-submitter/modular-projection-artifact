import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box10
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box10

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_005 :
    segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 50 10 =
      SparseUpperHybridGenerated.Box10.chunk 5 := by
  change segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 50 10 =
    ⟨0, 1187868740868193993582561546005063832084932277260124805283179238041773325126328424135178⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_005_sideCheck :
    segmentChunkSideCheck ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 50 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_006 :
    segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 60 10 =
      SparseUpperHybridGenerated.Box10.chunk 6 := by
  change segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 60 10 =
    ⟨0, 2042324522034861026686769983349308180026249553094406678246013599696851280471135226732⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_006_sideCheck :
    segmentChunkSideCheck ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 60 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_007 :
    segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 70 10 =
      SparseUpperHybridGenerated.Box10.chunk 7 := by
  change segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 70 10 =
    ⟨0, 2311271967662220640529758986287251914404878233497951018370446767856154660848977959⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_007_sideCheck :
    segmentChunkSideCheck ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 70 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_008 :
    segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 80 10 =
      SparseUpperHybridGenerated.Box10.chunk 8 := by
  change segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 80 10 =
    ⟨0, 2052251935567763777952552912305066715241882318954681790776359686676785464284030⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_008_sideCheck :
    segmentChunkSideCheck ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 80 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_009 :
    segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 90 10 =
      SparseUpperHybridGenerated.Box10.chunk 9 := by
  change segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 90 10 =
    ⟨0, 1645117423716257722206380201473866023176997114168783092847148909534296714097⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_009_sideCheck :
    segmentChunkSideCheck ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨0, 1 / 240, 240⟩ 90 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box10
