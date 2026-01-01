import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box13
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box13

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_000 :
    segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 0 10 =
      SparseUpperHybridGenerated.Box13.chunk 0 := by
  change segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 0 10 =
    ⟨0, 146638447265369011408965630571306162832899789046085518486218581583373948659397823191949264675626⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_000_sideCheck :
    segmentChunkSideCheck ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_001 :
    segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 10 10 =
      SparseUpperHybridGenerated.Box13.chunk 1 := by
  change segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 10 10 =
    ⟨0, 4266851821790412178352829121776836437697447762055170292592372479598132069931097039488255372777⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_001_sideCheck :
    segmentChunkSideCheck ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 10 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_002 :
    segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 20 10 =
      SparseUpperHybridGenerated.Box13.chunk 2 := by
  change segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 20 10 =
    ⟨0, 2161179785974019951319162201454056808476797045383411360657789443637333047671423871738099302⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_002_sideCheck :
    segmentChunkSideCheck ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 20 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_003 :
    segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 30 10 =
      SparseUpperHybridGenerated.Box13.chunk 3 := by
  change segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 30 10 =
    ⟨0, 44555492031702910767105406734596736556427781614631199194954941067474175015523603665356⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_003_sideCheck :
    segmentChunkSideCheck ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 30 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_004 :
    segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 40 10 =
      SparseUpperHybridGenerated.Box13.chunk 4 := by
  change segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 40 10 =
    ⟨0, 146194310165284247932770313225644840567994899439051705014720563764401634437564403⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_004_sideCheck :
    segmentChunkSideCheck ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 40 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box13
