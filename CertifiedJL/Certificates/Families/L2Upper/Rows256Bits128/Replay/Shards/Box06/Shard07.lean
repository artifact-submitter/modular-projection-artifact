import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box06
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box06

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_035 :
    segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨4, 1 / 6, 24⟩ 0 10 =
      SparseUpperHybridGenerated.Box06.chunk 35 := by
  change segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨4, 1 / 6, 24⟩ 0 10 =
    ⟨0, 307708415995766677969738890214906930213928500015548402807580826958164476875815512510052372441⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_035_sideCheck :
    segmentChunkSideCheck ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨4, 1 / 6, 24⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_036 :
    segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨4, 1 / 6, 24⟩ 10 10 =
      SparseUpperHybridGenerated.Box06.chunk 36 := by
  change segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨4, 1 / 6, 24⟩ 10 10 =
    ⟨0, 8812469536691102426249586326810946210928921958138061976325148814621342198813119087673349408⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_036_sideCheck :
    segmentChunkSideCheck ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨4, 1 / 6, 24⟩ 10 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_037 :
    segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨4, 1 / 6, 24⟩ 20 4 =
      SparseUpperHybridGenerated.Box06.chunk 37 := by
  change segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨4, 1 / 6, 24⟩ 20 4 =
    ⟨0, 407391191709447980974203156571959782975691938025606696870441782209865288732224299756209884⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_037_sideCheck :
    segmentChunkSideCheck ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨4, 1 / 6, 24⟩ 20 4 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box06
