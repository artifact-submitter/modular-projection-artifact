import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box03
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box03

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_040 :
    segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨4, 1 / 4, 16⟩ 10 6 =
      SparseUpperHybridGenerated.Box03.chunk 40 := by
  change segmentChunk ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨4, 1 / 4, 16⟩ 10 6 =
    ⟨0, 2607936914126489066499999155571950239092054695556890736583856063680527045460203314780938320⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_040_sideCheck :
    segmentChunkSideCheck ⟨3 / 4096, 1 / 1024, 5 / 8, 12, 2 / 5⟩ ⟨4, 1 / 4, 16⟩ 10 6 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box03
