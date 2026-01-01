import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box05
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box05

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_005 :
    segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 50 10 =
      SparseUpperHybridGenerated.Box05.chunk 5 := by
  change segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 50 10 =
    ⟨0, 10500186523480748999453228202929768149474065219540610892410323831394974979205657926436600⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_005_sideCheck :
    segmentChunkSideCheck ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 50 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_006 :
    segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 60 10 =
      SparseUpperHybridGenerated.Box05.chunk 6 := by
  change segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 60 10 =
    ⟨0, 35506233397667596336929726594663291375385746638926486705919511398615196599626617029880⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_006_sideCheck :
    segmentChunkSideCheck ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 60 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_007 :
    segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 70 10 =
      SparseUpperHybridGenerated.Box05.chunk 7 := by
  change segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 70 10 =
    ⟨0, 78384757861263749917002797056509269585951213120373804254304751353954002403223597963⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_007_sideCheck :
    segmentChunkSideCheck ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 70 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_008 :
    segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 80 10 =
      SparseUpperHybridGenerated.Box05.chunk 8 := by
  change segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 80 10 =
    ⟨0, 131259585335703291438451819447478358001648345133403785639522537931472324512497870⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_008_sideCheck :
    segmentChunkSideCheck ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 80 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_009 :
    segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 90 10 =
      SparseUpperHybridGenerated.Box05.chunk 9 := by
  change segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 90 10 =
    ⟨0, 188745252418883527103850912877423874994973972811699560045960757116770346458092⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_009_sideCheck :
    segmentChunkSideCheck ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 90 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box05
