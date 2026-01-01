import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box03
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box03

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_005 :
    segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 50 10 =
      SparseUpperHybridGenerated.Box03.chunk 5 := by
  change segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 50 10 =
    ⟨0, 71396395113923546181591583557966438497053845603734337017932980083113179492591793030896737⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_005_sideCheck :
    segmentChunkSideCheck ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 50 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_006 :
    segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 60 10 =
      SparseUpperHybridGenerated.Box03.chunk 6 := by
  change segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 60 10 =
    ⟨0, 445982695635205683177632083979601075003081205324998234548916067572512902764618560368889⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_006_sideCheck :
    segmentChunkSideCheck ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 60 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_007 :
    segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 70 10 =
      SparseUpperHybridGenerated.Box03.chunk 7 := by
  change segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 70 10 =
    ⟨0, 1817339474288230078429687582983359193557598607619395517646689555202439068369488856198⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_007_sideCheck :
    segmentChunkSideCheck ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 70 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_008 :
    segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 80 10 =
      SparseUpperHybridGenerated.Box03.chunk 8 := by
  change segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 80 10 =
    ⟨0, 5492066643230980948997855564874176662657754082949023987921855419541627136389980132⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_008_sideCheck :
    segmentChunkSideCheck ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 80 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_009 :
    segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 90 10 =
      SparseUpperHybridGenerated.Box03.chunk 9 := by
  change segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 90 10 =
    ⟨0, 13740849536660829467917325122424466872562073511400805218159752380490481476691702⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_009_sideCheck :
    segmentChunkSideCheck ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 90 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box03
