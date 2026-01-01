import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box00
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box00

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_015 :
    segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 150 10 =
      SparseUpperHybridGenerated.Box00.chunk 15 := by
  change segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 150 10 =
    ⟨0, 603303494660728388907025139879955755460732999625199849⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_015_sideCheck :
    segmentChunkSideCheck ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 150 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_016 :
    segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 160 10 =
      SparseUpperHybridGenerated.Box00.chunk 16 := by
  change segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 160 10 =
    ⟨0, 956930008932730837797487146290144735202657483488370⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_016_sideCheck :
    segmentChunkSideCheck ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 160 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_017 :
    segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 170 10 =
      SparseUpperHybridGenerated.Box00.chunk 17 := by
  change segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 170 10 =
    ⟨0, 1911282274872821541907316784292552228494459054066⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_017_sideCheck :
    segmentChunkSideCheck ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 170 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_018 :
    segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 180 10 =
      SparseUpperHybridGenerated.Box00.chunk 18 := by
  change segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 180 10 =
    ⟨0, 4772487139448261694379000891519862715544586367⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_018_sideCheck :
    segmentChunkSideCheck ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 180 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_019 :
    segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 190 10 =
      SparseUpperHybridGenerated.Box00.chunk 19 := by
  change segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 190 10 =
    ⟨0, 14770658270802309099032072315141097594970005⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_019_sideCheck :
    segmentChunkSideCheck ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 190 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box00
