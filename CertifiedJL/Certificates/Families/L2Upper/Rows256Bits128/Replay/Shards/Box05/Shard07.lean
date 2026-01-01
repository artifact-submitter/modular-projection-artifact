import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box05
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box05

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_035 :
    segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨2, 1 / 25, 50⟩ 40 10 =
      SparseUpperHybridGenerated.Box05.chunk 35 := by
  change segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨2, 1 / 25, 50⟩ 40 10 =
    ⟨0, 918605647092907957317975411580501799637786199389983299671423243889914810504525453874507380374⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_035_sideCheck :
    segmentChunkSideCheck ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨2, 1 / 25, 50⟩ 40 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_036 :
    segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨4, 1 / 4, 16⟩ 0 10 =
      SparseUpperHybridGenerated.Box05.chunk 36 := by
  change segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨4, 1 / 4, 16⟩ 0 10 =
    ⟨0, 732857936675447622654125258002191230472431302074301420423395446338955975066175067779306159339⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_036_sideCheck :
    segmentChunkSideCheck ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨4, 1 / 4, 16⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_037 :
    segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨4, 1 / 4, 16⟩ 10 6 =
      SparseUpperHybridGenerated.Box05.chunk 37 := by
  change segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨4, 1 / 4, 16⟩ 10 6 =
    ⟨0, 7418484728005555529086407418795870169395720270885760224332150901119807899025645535125929732⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_037_sideCheck :
    segmentChunkSideCheck ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨4, 1 / 4, 16⟩ 10 6 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box05
