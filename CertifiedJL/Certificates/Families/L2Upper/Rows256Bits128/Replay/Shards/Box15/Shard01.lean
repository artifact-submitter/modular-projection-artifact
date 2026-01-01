import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box15
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box15

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_005 :
    segmentChunk ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨1, 1 / 13, 13⟩ 10 3 =
      SparseUpperHybridGenerated.Box15.chunk 5 := by
  change segmentChunk ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨1, 1 / 13, 13⟩ 10 3 =
    ⟨0, 1679295129882177921551434693924646475787755112876492544767779396468681966915580596133851532869⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_005_sideCheck :
    segmentChunkSideCheck ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨1, 1 / 13, 13⟩ 10 3 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_006 :
    segmentChunk ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨2, 1 / 2, 4⟩ 0 4 =
      SparseUpperHybridGenerated.Box15.chunk 6 := by
  change segmentChunk ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨2, 1 / 2, 4⟩ 0 4 =
    ⟨0, 2473490886491178564200040501947811780075238883207288712524383262558090102321427567691881370517⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_006_sideCheck :
    segmentChunkSideCheck ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨2, 1 / 2, 4⟩ 0 4 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_007 :
    segmentChunk ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨4, 1, 4⟩ 0 4 =
      SparseUpperHybridGenerated.Box15.chunk 7 := by
  change segmentChunk ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨4, 1, 4⟩ 0 4 =
    ⟨0, 24625651982265520267795078857292268564591490004052627989287912696092891942160556247006512883⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_007_sideCheck :
    segmentChunkSideCheck ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨4, 1, 4⟩ 0 4 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box15
