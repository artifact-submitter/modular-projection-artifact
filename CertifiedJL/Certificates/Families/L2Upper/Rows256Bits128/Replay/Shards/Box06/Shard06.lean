import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box06
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box06

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_030 :
    segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨2, 1 / 40, 80⟩ 30 10 =
      SparseUpperHybridGenerated.Box06.chunk 30 := by
  change segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨2, 1 / 40, 80⟩ 30 10 =
    ⟨0, 796134349379425178220784861747697488338845630011255276636621566834601333924167285959307203626⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_030_sideCheck :
    segmentChunkSideCheck ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨2, 1 / 40, 80⟩ 30 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_031 :
    segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨2, 1 / 40, 80⟩ 40 10 =
      SparseUpperHybridGenerated.Box06.chunk 31 := by
  change segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨2, 1 / 40, 80⟩ 40 10 =
    ⟨0, 2412405100704710998491251508491543705427085987853018535395124116528300470514470997787243640471⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_031_sideCheck :
    segmentChunkSideCheck ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨2, 1 / 40, 80⟩ 40 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_032 :
    segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨2, 1 / 40, 80⟩ 50 10 =
      SparseUpperHybridGenerated.Box06.chunk 32 := by
  change segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨2, 1 / 40, 80⟩ 50 10 =
    ⟨0, 1056729126395026179528591774953215725046750719139507370694402070007390090794111433437872233993⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_032_sideCheck :
    segmentChunkSideCheck ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨2, 1 / 40, 80⟩ 50 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_033 :
    segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨2, 1 / 40, 80⟩ 60 10 =
      SparseUpperHybridGenerated.Box06.chunk 33 := by
  change segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨2, 1 / 40, 80⟩ 60 10 =
    ⟨0, 489341376711990636647027052222520328013791267535738324313498688274045916420550015732070542108⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_033_sideCheck :
    segmentChunkSideCheck ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨2, 1 / 40, 80⟩ 60 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_034 :
    segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨2, 1 / 40, 80⟩ 70 10 =
      SparseUpperHybridGenerated.Box06.chunk 34 := by
  change segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨2, 1 / 40, 80⟩ 70 10 =
    ⟨0, 237909903892414952001040881968355948533495172856899523826079213520443994754195358927566567939⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_034_sideCheck :
    segmentChunkSideCheck ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨2, 1 / 40, 80⟩ 70 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box06
