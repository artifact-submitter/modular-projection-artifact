import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box11
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box11

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_025 :
    segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨0, 1 / 280, 280⟩ 250 10 =
      SparseUpperHybridGenerated.Box11.chunk 25 := by
  change segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨0, 1 / 280, 280⟩ 250 10 =
    ⟨0, 18860363386284738880757314750094024108527925⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_025_sideCheck :
    segmentChunkSideCheck ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨0, 1 / 280, 280⟩ 250 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_026 :
    segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨0, 1 / 280, 280⟩ 260 10 =
      SparseUpperHybridGenerated.Box11.chunk 26 := by
  change segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨0, 1 / 280, 280⟩ 260 10 =
    ⟨0, 546626323391804869076755148527838915235733⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_026_sideCheck :
    segmentChunkSideCheck ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨0, 1 / 280, 280⟩ 260 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_027 :
    segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨0, 1 / 280, 280⟩ 270 10 =
      SparseUpperHybridGenerated.Box11.chunk 27 := by
  change segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨0, 1 / 280, 280⟩ 270 10 =
    ⟨0, 20298924659021072705182165929936833186101⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_027_sideCheck :
    segmentChunkSideCheck ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨0, 1 / 280, 280⟩ 270 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_028 :
    segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨1, 1 / 50, 50⟩ 0 10 =
      SparseUpperHybridGenerated.Box11.chunk 28 := by
  change segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨1, 1 / 50, 50⟩ 0 10 =
    ⟨0, 2985941186100369488648108267028432248197⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_028_sideCheck :
    segmentChunkSideCheck ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨1, 1 / 50, 50⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_029 :
    segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨1, 1 / 50, 50⟩ 10 10 =
      SparseUpperHybridGenerated.Box11.chunk 29 := by
  change segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨1, 1 / 50, 50⟩ 10 10 =
    ⟨0, 179117719162725941005143167760454876⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_029_sideCheck :
    segmentChunkSideCheck ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨1, 1 / 50, 50⟩ 10 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box11
