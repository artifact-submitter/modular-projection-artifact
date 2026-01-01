import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box04
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box04

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_025 :
    segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 250 10 =
      SparseUpperHybridGenerated.Box04.chunk 25 := by
  change segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 250 10 =
    ⟨0, 411023120130698527349190390675419241941994⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_025_sideCheck :
    segmentChunkSideCheck ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 250 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_026 :
    segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 260 10 =
      SparseUpperHybridGenerated.Box04.chunk 26 := by
  change segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 260 10 =
    ⟨0, 5903789902617967737048394666040181769727⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_026_sideCheck :
    segmentChunkSideCheck ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 260 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_027 :
    segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 270 10 =
      SparseUpperHybridGenerated.Box04.chunk 27 := by
  change segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 270 10 =
    ⟨0, 96393519141313639658238195512847974970⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_027_sideCheck :
    segmentChunkSideCheck ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 270 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_028 :
    segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨1, 1 / 50, 50⟩ 0 10 =
      SparseUpperHybridGenerated.Box04.chunk 28 := by
  change segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨1, 1 / 50, 50⟩ 0 10 =
    ⟨0, 3878745101808406393880534883030425978⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_028_sideCheck :
    segmentChunkSideCheck ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨1, 1 / 50, 50⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_029 :
    segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨1, 1 / 50, 50⟩ 10 10 =
      SparseUpperHybridGenerated.Box04.chunk 29 := by
  change segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨1, 1 / 50, 50⟩ 10 10 =
    ⟨0, 6581713543342834818854707462⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_029_sideCheck :
    segmentChunkSideCheck ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨1, 1 / 50, 50⟩ 10 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box04
