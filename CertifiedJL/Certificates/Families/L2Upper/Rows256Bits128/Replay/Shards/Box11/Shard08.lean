import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box11
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box11

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_040 :
    segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨4, 1 / 4, 16⟩ 10 6 =
      SparseUpperHybridGenerated.Box11.chunk 40 := by
  change segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨4, 1 / 4, 16⟩ 10 6 =
    ⟨0, 431052335022044596133384022077820265385648709565912164705137504614464249711056437562167982⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_040_sideCheck :
    segmentChunkSideCheck ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨4, 1 / 4, 16⟩ 10 6 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box11
