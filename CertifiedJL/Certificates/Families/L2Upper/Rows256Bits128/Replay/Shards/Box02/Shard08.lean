import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box02
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box02

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_040 :
    segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨4, 1 / 4, 16⟩ 10 6 =
      SparseUpperHybridGenerated.Box02.chunk 40 := by
  change segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨4, 1 / 4, 16⟩ 10 6 =
    ⟨0, 2662788902309880565439079723749236281916194027488263547894639027288993853745949707109839884⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_040_sideCheck :
    segmentChunkSideCheck ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨4, 1 / 4, 16⟩ 10 6 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box02
