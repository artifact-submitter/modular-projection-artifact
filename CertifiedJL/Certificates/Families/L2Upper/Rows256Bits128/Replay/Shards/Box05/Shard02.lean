import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box05
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box05

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_010 :
    segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 100 10 =
      SparseUpperHybridGenerated.Box05.chunk 10 := by
  change segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 100 10 =
    ⟨0, 257041721690426762380814197630817424035325668133194311012744937404571868870⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_010_sideCheck :
    segmentChunkSideCheck ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 100 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_011 :
    segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 110 10 =
      SparseUpperHybridGenerated.Box05.chunk 11 := by
  change segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 110 10 =
    ⟨0, 357150036029561644597858273501777967178171382915271866857156522619573069⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_011_sideCheck :
    segmentChunkSideCheck ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 110 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_012 :
    segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 120 10 =
      SparseUpperHybridGenerated.Box05.chunk 12 := by
  change segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 120 10 =
    ⟨0, 534791607882134569445780124139969195187503187185938679774944421864583⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_012_sideCheck :
    segmentChunkSideCheck ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 120 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_013 :
    segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 130 10 =
      SparseUpperHybridGenerated.Box05.chunk 13 := by
  change segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 130 10 =
    ⟨0, 897263135212934943497306000790567843702883162200449253860879718208⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_013_sideCheck :
    segmentChunkSideCheck ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 130 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_014 :
    segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 140 10 =
      SparseUpperHybridGenerated.Box05.chunk 14 := by
  change segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 140 10 =
    ⟨0, 1732225114798371199641622388562116865327160981081586375902488470⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_014_sideCheck :
    segmentChunkSideCheck ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 140 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box05
