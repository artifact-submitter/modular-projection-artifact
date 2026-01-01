import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box02
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box02

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_035 :
    segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨2, 1 / 20, 40⟩ 0 10 =
      SparseUpperHybridGenerated.Box02.chunk 35 := by
  change segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨2, 1 / 20, 40⟩ 0 10 =
    ⟨0, 231461⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_035_sideCheck :
    segmentChunkSideCheck ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨2, 1 / 20, 40⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_036 :
    segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨2, 1 / 20, 40⟩ 10 10 =
      SparseUpperHybridGenerated.Box02.chunk 36 := by
  change segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨2, 1 / 20, 40⟩ 10 10 =
    ⟨0, 237322727220805606822⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_036_sideCheck :
    segmentChunkSideCheck ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨2, 1 / 20, 40⟩ 10 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_037 :
    segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨2, 1 / 20, 40⟩ 20 10 =
      SparseUpperHybridGenerated.Box02.chunk 37 := by
  change segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨2, 1 / 20, 40⟩ 20 10 =
    ⟨0, 17041938315642487760379655224603127792653092769381230384347286⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_037_sideCheck :
    segmentChunkSideCheck ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨2, 1 / 20, 40⟩ 20 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_038 :
    segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨2, 1 / 20, 40⟩ 30 10 =
      SparseUpperHybridGenerated.Box02.chunk 38 := by
  change segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨2, 1 / 20, 40⟩ 30 10 =
    ⟨0, 925036326174891953814162510061301261164172917535351862989185857359267679961525240852944709903⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_038_sideCheck :
    segmentChunkSideCheck ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨2, 1 / 20, 40⟩ 30 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_039 :
    segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨4, 1 / 4, 16⟩ 0 10 =
      SparseUpperHybridGenerated.Box02.chunk 39 := by
  change segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨4, 1 / 4, 16⟩ 0 10 =
    ⟨0, 1059149955886108188885279431544444727282849022160489558693787760167933809921924902424160291025⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_039_sideCheck :
    segmentChunkSideCheck ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨4, 1 / 4, 16⟩ 0 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box02
