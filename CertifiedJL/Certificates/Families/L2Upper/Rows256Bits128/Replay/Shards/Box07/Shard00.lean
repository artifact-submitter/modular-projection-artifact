import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box07
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box07

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_000 :
    segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 0 10 =
      SparseUpperHybridGenerated.Box07.chunk 0 := by
  change segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 0 10 =
    ⟨0, 126050717597001681986608543068313710864645116382943699771003534149543870340494092375522476068596⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_000_sideCheck :
    segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_001 :
    segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 10 10 =
      SparseUpperHybridGenerated.Box07.chunk 1 := by
  change segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 10 10 =
    ⟨0, 27869808535455479785826106014424868546759727790864909672194411271906943698714694748814757649781⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_001_sideCheck :
    segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 10 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_002 :
    segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 20 10 =
      SparseUpperHybridGenerated.Box07.chunk 2 := by
  change segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 20 10 =
    ⟨0, 1290200951303298615825240631873759659431543356468116502524562767345101710000366878146771646065⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_002_sideCheck :
    segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 20 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_003 :
    segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 30 10 =
      SparseUpperHybridGenerated.Box07.chunk 3 := by
  change segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 30 10 =
    ⟨0, 14304509164881668493338944140105291250180560984049621781040542866276777178055358040523771672⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_003_sideCheck :
    segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 30 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_004 :
    segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 40 10 =
      SparseUpperHybridGenerated.Box07.chunk 4 := by
  change segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 40 10 =
    ⟨0, 48401779431249551637585001978641957104444740305315530291514353546985614958778604847491916⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_004_sideCheck :
    segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 40 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box07
