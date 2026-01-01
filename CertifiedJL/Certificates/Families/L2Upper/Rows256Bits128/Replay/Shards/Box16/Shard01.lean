import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box16
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box16

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_005 :
    segmentChunk ⟨3 / 128, 1 / 32, 631 / 1000, 7, 11 / 10⟩ ⟨4, 1, 4⟩ 0 4 =
      SparseUpperHybridGenerated.Box16.chunk 5 := by
  change segmentChunk ⟨3 / 128, 1 / 32, 631 / 1000, 7, 11 / 10⟩ ⟨4, 1, 4⟩ 0 4 =
    ⟨0, 13932252612317660701013962828612129723681727757605472163085818718978094332985172948444037018⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_005_sideCheck :
    segmentChunkSideCheck ⟨3 / 128, 1 / 32, 631 / 1000, 7, 11 / 10⟩ ⟨4, 1, 4⟩ 0 4 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box16
