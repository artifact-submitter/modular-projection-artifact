import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box15
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box15

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_000 :
    segmentChunk ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨0, 1 / 40, 40⟩ 0 10 =
      SparseUpperHybridGenerated.Box15.chunk 0 := by
  change segmentChunk ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨0, 1 / 40, 40⟩ 0 10 =
    ⟨0, 128187762816295796299894325733236852973507242413405885677719962152915346523562185437410312025805⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_000_sideCheck :
    segmentChunkSideCheck ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨0, 1 / 40, 40⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_001 :
    segmentChunk ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨0, 1 / 40, 40⟩ 10 10 =
      SparseUpperHybridGenerated.Box15.chunk 1 := by
  change segmentChunk ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨0, 1 / 40, 40⟩ 10 10 =
    ⟨0, 102548551884724070282451587274224419009418490131012091342897318457140368440946856877450⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_001_sideCheck :
    segmentChunkSideCheck ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨0, 1 / 40, 40⟩ 10 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_002 :
    segmentChunk ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨0, 1 / 40, 40⟩ 20 10 =
      SparseUpperHybridGenerated.Box15.chunk 2 := by
  change segmentChunk ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨0, 1 / 40, 40⟩ 20 10 =
    ⟨0, 2962878689853474634834734423938266608567930390527208046219454419776533⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_002_sideCheck :
    segmentChunkSideCheck ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨0, 1 / 40, 40⟩ 20 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_003 :
    segmentChunk ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨0, 1 / 40, 40⟩ 30 10 =
      SparseUpperHybridGenerated.Box15.chunk 3 := by
  change segmentChunk ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨0, 1 / 40, 40⟩ 30 10 =
    ⟨0, 6375680208014718408767375489460637821117524304076015539814742253⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_003_sideCheck :
    segmentChunkSideCheck ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨0, 1 / 40, 40⟩ 30 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_004 :
    segmentChunk ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨1, 1 / 13, 13⟩ 0 10 =
      SparseUpperHybridGenerated.Box15.chunk 4 := by
  change segmentChunk ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨1, 1 / 13, 13⟩ 0 10 =
    ⟨0, 25376792445032347120498825823336153047612647491195360001172642311971105231909292692702632285863⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_004_sideCheck :
    segmentChunkSideCheck ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨1, 1 / 13, 13⟩ 0 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box15
