import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box05
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box05

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_020 :
    segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 200 10 =
      SparseUpperHybridGenerated.Box05.chunk 20 := by
  change segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 200 10 =
    ⟨0, 3055193340371580837147662368316351677944392618929⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_020_sideCheck :
    segmentChunkSideCheck ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 200 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_021 :
    segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 210 10 =
      SparseUpperHybridGenerated.Box05.chunk 21 := by
  change segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 210 10 =
    ⟨0, 19411302251437887215604017048601452946486854647⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_021_sideCheck :
    segmentChunkSideCheck ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 210 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_022 :
    segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 220 10 =
      SparseUpperHybridGenerated.Box05.chunk 22 := by
  change segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 220 10 =
    ⟨0, 145517426369700503096756724033083255536432061⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_022_sideCheck :
    segmentChunkSideCheck ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 220 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_023 :
    segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 230 10 =
      SparseUpperHybridGenerated.Box05.chunk 23 := by
  change segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 230 10 =
    ⟨0, 1281840474557972682755893805230087031879697⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_023_sideCheck :
    segmentChunkSideCheck ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 230 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_024 :
    segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 240 10 =
      SparseUpperHybridGenerated.Box05.chunk 24 := by
  change segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 240 10 =
    ⟨0, 13213685538475416549287341066051024433507⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_024_sideCheck :
    segmentChunkSideCheck ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 240 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box05
