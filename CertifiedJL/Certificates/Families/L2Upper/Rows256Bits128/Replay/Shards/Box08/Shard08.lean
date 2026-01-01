import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box08
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box08

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_040 :
    segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨4, 1 / 4, 16⟩ 10 6 =
      SparseUpperHybridGenerated.Box08.chunk 40 := by
  change segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨4, 1 / 4, 16⟩ 10 6 =
    ⟨0, 1628921230696531120813775942015763964453574905574063847603335316839544839082901028858920692⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_040_sideCheck :
    segmentChunkSideCheck ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨4, 1 / 4, 16⟩ 10 6 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box08
