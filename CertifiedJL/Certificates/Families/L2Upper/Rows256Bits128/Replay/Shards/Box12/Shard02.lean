import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box12
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box12

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_010 :
    segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 100 10 =
      SparseUpperHybridGenerated.Box12.chunk 10 := by
  change segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 100 10 =
    ⟨0, 4218370285479910250901668112813999096490603213379⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_010_sideCheck :
    segmentChunkSideCheck ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 100 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_011 :
    segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 110 10 =
      SparseUpperHybridGenerated.Box12.chunk 11 := by
  change segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 110 10 =
    ⟨0, 1177041402791566780533973015979636025533378317⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_011_sideCheck :
    segmentChunkSideCheck ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 110 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_012 :
    segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 120 5 =
      SparseUpperHybridGenerated.Box12.chunk 12 := by
  change segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 120 5 =
    ⟨0, 1417808133122291257483672414624607222839567⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_012_sideCheck :
    segmentChunkSideCheck ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 120 5 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_013 :
    segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨1, 1 / 13, 13⟩ 0 10 =
      SparseUpperHybridGenerated.Box12.chunk 13 := by
  change segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨1, 1 / 13, 13⟩ 0 10 =
    ⟨0, 27273649846956713465850637988371061334635221956107536890770964745595447264393674⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_013_sideCheck :
    segmentChunkSideCheck ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨1, 1 / 13, 13⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_014 :
    segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨1, 1 / 13, 13⟩ 10 3 =
      SparseUpperHybridGenerated.Box12.chunk 14 := by
  change segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨1, 1 / 13, 13⟩ 10 3 =
    ⟨0, 6699636545081239697546962615748780171700630051459392460742606608678832063094906027748069143503⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_014_sideCheck :
    segmentChunkSideCheck ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨1, 1 / 13, 13⟩ 10 3 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box12
