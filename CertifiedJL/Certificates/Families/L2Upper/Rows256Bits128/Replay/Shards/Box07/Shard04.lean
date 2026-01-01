import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box07
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box07

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_020 :
    segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 200 10 =
      SparseUpperHybridGenerated.Box07.chunk 20 := by
  change segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 200 10 =
    ⟨0, 97853974018564337155419848362386272485105⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_020_sideCheck :
    segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 200 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_021 :
    segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 210 10 =
      SparseUpperHybridGenerated.Box07.chunk 21 := by
  change segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 210 10 =
    ⟨0, 535592785671885134836422964122710883302⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_021_sideCheck :
    segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 210 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_022 :
    segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨1, 1 / 50, 50⟩ 0 10 =
      SparseUpperHybridGenerated.Box07.chunk 22 := by
  change segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨1, 1 / 50, 50⟩ 0 10 =
    ⟨0, 7699596280968875247571968002287536929⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_022_sideCheck :
    segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨1, 1 / 50, 50⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_023 :
    segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨1, 1 / 50, 50⟩ 10 10 =
      SparseUpperHybridGenerated.Box07.chunk 23 := by
  change segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨1, 1 / 50, 50⟩ 10 10 =
    ⟨0, 32053829917603360505057866840⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_023_sideCheck :
    segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨1, 1 / 50, 50⟩ 10 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_024 :
    segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨1, 1 / 50, 50⟩ 20 10 =
      SparseUpperHybridGenerated.Box07.chunk 24 := by
  change segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨1, 1 / 50, 50⟩ 20 10 =
    ⟨0, 12876973000379314966279⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_024_sideCheck :
    segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨1, 1 / 50, 50⟩ 20 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box07
