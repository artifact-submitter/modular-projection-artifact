import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box13
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box13

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_010 :
    segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 100 10 =
      SparseUpperHybridGenerated.Box13.chunk 10 := by
  change segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 100 10 =
    ⟨0, 544286122326894368674393842369833315281985179551731⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_010_sideCheck :
    segmentChunkSideCheck ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 100 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_011 :
    segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 110 10 =
      SparseUpperHybridGenerated.Box13.chunk 11 := by
  change segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 110 10 =
    ⟨0, 932493899283812842965738078328401810016335954702⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_011_sideCheck :
    segmentChunkSideCheck ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 110 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_012 :
    segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 120 6 =
      SparseUpperHybridGenerated.Box13.chunk 12 := by
  change segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 120 6 =
    ⟨0, 14282491202138261325307039186674529716342897547⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_012_sideCheck :
    segmentChunkSideCheck ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 120 6 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_013 :
    segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨1, 1 / 21, 21⟩ 0 10 =
      SparseUpperHybridGenerated.Box13.chunk 13 := by
  change segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨1, 1 / 21, 21⟩ 0 10 =
    ⟨0, 77224246785302838675863200378699088169462716426459992311569915098219049⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_013_sideCheck :
    segmentChunkSideCheck ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨1, 1 / 21, 21⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_014 :
    segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨1, 1 / 21, 21⟩ 10 10 =
      SparseUpperHybridGenerated.Box13.chunk 14 := by
  change segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨1, 1 / 21, 21⟩ 10 10 =
    ⟨0, 8418760216918016671631246366858013014101829905029610240187597643756996332900214289477425396365⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_014_sideCheck :
    segmentChunkSideCheck ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨1, 1 / 21, 21⟩ 10 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box13
