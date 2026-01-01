import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box17
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box17

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_000 :
    segmentChunk ⟨1 / 32, 1 / 20, 631 / 1000, 6, 6 / 5⟩ ⟨0, 1 / 19, 19⟩ 0 10 =
      SparseUpperHybridGenerated.Box17.chunk 0 := by
  change segmentChunk ⟨1 / 32, 1 / 20, 631 / 1000, 6, 6 / 5⟩ ⟨0, 1 / 19, 19⟩ 0 10 =
    ⟨0, 92152940959556261616667587457532019200322049824270589298771050639356544953474872258490093052836⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_000_sideCheck :
    segmentChunkSideCheck ⟨1 / 32, 1 / 20, 631 / 1000, 6, 6 / 5⟩ ⟨0, 1 / 19, 19⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_001 :
    segmentChunk ⟨1 / 32, 1 / 20, 631 / 1000, 6, 6 / 5⟩ ⟨0, 1 / 19, 19⟩ 10 9 =
      SparseUpperHybridGenerated.Box17.chunk 1 := by
  change segmentChunk ⟨1 / 32, 1 / 20, 631 / 1000, 6, 6 / 5⟩ ⟨0, 1 / 19, 19⟩ 10 9 =
    ⟨0, 27647807549967317843585664788483412484562932335564707963163548671915165664248997425388813977774⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_001_sideCheck :
    segmentChunkSideCheck ⟨1 / 32, 1 / 20, 631 / 1000, 6, 6 / 5⟩ ⟨0, 1 / 19, 19⟩ 10 9 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_002 :
    segmentChunk ⟨1 / 32, 1 / 20, 631 / 1000, 6, 6 / 5⟩ ⟨1, 1 / 4, 4⟩ 0 4 =
      SparseUpperHybridGenerated.Box17.chunk 2 := by
  change segmentChunk ⟨1 / 32, 1 / 20, 631 / 1000, 6, 6 / 5⟩ ⟨1, 1 / 4, 4⟩ 0 4 =
    ⟨0, 36161245265919245325339472007511711482213503939555032498838426052035882813363233989898833857566⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_002_sideCheck :
    segmentChunkSideCheck ⟨1 / 32, 1 / 20, 631 / 1000, 6, 6 / 5⟩ ⟨1, 1 / 4, 4⟩ 0 4 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_003 :
    segmentChunk ⟨1 / 32, 1 / 20, 631 / 1000, 6, 6 / 5⟩ ⟨2, 1, 2⟩ 0 2 =
      SparseUpperHybridGenerated.Box17.chunk 3 := by
  change segmentChunk ⟨1 / 32, 1 / 20, 631 / 1000, 6, 6 / 5⟩ ⟨2, 1, 2⟩ 0 2 =
    ⟨0, 1919493187605024121675665123111569145918561238429906315563108028918845363810850137621328898700⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_003_sideCheck :
    segmentChunkSideCheck ⟨1 / 32, 1 / 20, 631 / 1000, 6, 6 / 5⟩ ⟨2, 1, 2⟩ 0 2 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_004 :
    segmentChunk ⟨1 / 32, 1 / 20, 631 / 1000, 6, 6 / 5⟩ ⟨4, 1, 4⟩ 0 4 =
      SparseUpperHybridGenerated.Box17.chunk 4 := by
  change segmentChunk ⟨1 / 32, 1 / 20, 631 / 1000, 6, 6 / 5⟩ ⟨4, 1, 4⟩ 0 4 =
    ⟨0, 22855739397485188540893420819614601670968736936707193533181739419558725283671811757487047616⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_004_sideCheck :
    segmentChunkSideCheck ⟨1 / 32, 1 / 20, 631 / 1000, 6, 6 / 5⟩ ⟨4, 1, 4⟩ 0 4 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box17
