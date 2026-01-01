import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box08
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box08

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_035 :
    segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 30, 60⟩ 20 10 =
      SparseUpperHybridGenerated.Box08.chunk 35 := by
  change segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 30, 60⟩ 20 10 =
    ⟨0, 2916731446685820506751833835963171868691062853160664780984563386316974731218348565093309673480⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_035_sideCheck :
    segmentChunkSideCheck ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 30, 60⟩ 20 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_036 :
    segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 30, 60⟩ 30 10 =
      SparseUpperHybridGenerated.Box08.chunk 36 := by
  change segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 30, 60⟩ 30 10 =
    ⟨0, 986342651647644237831814473636314877074729982410116506548193567727337435283694127134948336511⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_036_sideCheck :
    segmentChunkSideCheck ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 30, 60⟩ 30 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_037 :
    segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 30, 60⟩ 40 10 =
      SparseUpperHybridGenerated.Box08.chunk 37 := by
  change segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 30, 60⟩ 40 10 =
    ⟨0, 369473788089725022880664054849828412051915853352031544645118213834828622976033046651723424410⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_037_sideCheck :
    segmentChunkSideCheck ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 30, 60⟩ 40 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_038 :
    segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 30, 60⟩ 50 10 =
      SparseUpperHybridGenerated.Box08.chunk 38 := by
  change segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 30, 60⟩ 50 10 =
    ⟨0, 150683099910650139927461635528989461706822733620493933880031035531665326303564459473239632272⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_038_sideCheck :
    segmentChunkSideCheck ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 30, 60⟩ 50 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_039 :
    segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨4, 1 / 4, 16⟩ 0 10 =
      SparseUpperHybridGenerated.Box08.chunk 39 := by
  change segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨4, 1 / 4, 16⟩ 0 10 =
    ⟨0, 160950324312815630294618548250349192247976640821854754361058327341498662817521936229629442142⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_039_sideCheck :
    segmentChunkSideCheck ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨4, 1 / 4, 16⟩ 0 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box08
