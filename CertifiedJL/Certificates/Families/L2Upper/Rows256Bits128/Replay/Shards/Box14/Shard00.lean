import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box14
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box14

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_000 :
    segmentChunk ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 48, 48⟩ 0 10 =
      SparseUpperHybridGenerated.Box14.chunk 0 := by
  change segmentChunk ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 48, 48⟩ 0 10 =
    ⟨0, 139958085263226447261467594100363173699335826523679200514946902958536098213524849753750933863858⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_000_sideCheck :
    segmentChunkSideCheck ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 48, 48⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_001 :
    segmentChunk ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 48, 48⟩ 10 10 =
      SparseUpperHybridGenerated.Box14.chunk 1 := by
  change segmentChunk ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 48, 48⟩ 10 10 =
    ⟨0, 11133814011724141513187677340709990590849747790639561403456934802765516056537312211690135⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_001_sideCheck :
    segmentChunkSideCheck ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 48, 48⟩ 10 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_002 :
    segmentChunk ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 48, 48⟩ 20 10 =
      SparseUpperHybridGenerated.Box14.chunk 2 := by
  change segmentChunk ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 48, 48⟩ 20 10 =
    ⟨0, 60696353228970370554119903469380795138362289296113813121496764232084558450⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_002_sideCheck :
    segmentChunkSideCheck ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 48, 48⟩ 20 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_003 :
    segmentChunk ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 48, 48⟩ 30 10 =
      SparseUpperHybridGenerated.Box14.chunk 3 := by
  change segmentChunk ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 48, 48⟩ 30 10 =
    ⟨0, 3804692701380181955099324366174162867784262210773654169165626⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_003_sideCheck :
    segmentChunkSideCheck ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 48, 48⟩ 30 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_004 :
    segmentChunk ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 48, 48⟩ 40 8 =
      SparseUpperHybridGenerated.Box14.chunk 4 := by
  change segmentChunk ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 48, 48⟩ 40 8 =
    ⟨0, 32338333849616807484183430641676618466920558015422425⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_004_sideCheck :
    segmentChunkSideCheck ⟨3 / 256, 1 / 64, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 48, 48⟩ 40 8 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box14
