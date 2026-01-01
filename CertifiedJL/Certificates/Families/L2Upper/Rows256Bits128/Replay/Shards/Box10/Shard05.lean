import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box10
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box10

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_025 :
    segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨1, 1 / 50, 50⟩ 10 10 =
      SparseUpperHybridGenerated.Box10.chunk 25 := by
  change segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨1, 1 / 50, 50⟩ 10 10 =
    ⟨0, 11939795085994057684217015435589⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_025_sideCheck :
    segmentChunkSideCheck ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨1, 1 / 50, 50⟩ 10 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_026 :
    segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨1, 1 / 50, 50⟩ 20 10 =
      SparseUpperHybridGenerated.Box10.chunk 26 := by
  change segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨1, 1 / 50, 50⟩ 20 10 =
    ⟨0, 89002752502954310589216647144⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_026_sideCheck :
    segmentChunkSideCheck ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨1, 1 / 50, 50⟩ 20 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_027 :
    segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨1, 1 / 50, 50⟩ 30 10 =
      SparseUpperHybridGenerated.Box10.chunk 27 := by
  change segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨1, 1 / 50, 50⟩ 30 10 =
    ⟨0, 852498411642611451015618614831666629⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_027_sideCheck :
    segmentChunkSideCheck ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨1, 1 / 50, 50⟩ 30 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_028 :
    segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨1, 1 / 50, 50⟩ 40 10 =
      SparseUpperHybridGenerated.Box10.chunk 28 := by
  change segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨1, 1 / 50, 50⟩ 40 10 =
    ⟨0, 1620529187170082084845949719519967913362614786387619⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_028_sideCheck :
    segmentChunkSideCheck ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨1, 1 / 50, 50⟩ 40 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_029 :
    segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨2, 1 / 40, 80⟩ 0 10 =
      SparseUpperHybridGenerated.Box10.chunk 29 := by
  change segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨2, 1 / 40, 80⟩ 0 10 =
    ⟨0, 53512952981537246075796800136861713134724408570014749081498934759523703160099483410⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_029_sideCheck :
    segmentChunkSideCheck ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨2, 1 / 40, 80⟩ 0 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box10
