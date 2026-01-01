import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box06
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box06

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_000 :
    segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 0 10 =
      SparseUpperHybridGenerated.Box06.chunk 0 := by
  change segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 0 10 =
    ⟨0, 128305724151945535477334205482924456036856336615999431389125287815887129482012341935161175698650⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_000_sideCheck :
    segmentChunkSideCheck ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_001 :
    segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 10 10 =
      SparseUpperHybridGenerated.Box06.chunk 1 := by
  change segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 10 10 =
    ⟨0, 28265243789756100626196547649261418261058082988064526580324284453189958153227204454411234637895⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_001_sideCheck :
    segmentChunkSideCheck ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 10 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_002 :
    segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 20 10 =
      SparseUpperHybridGenerated.Box06.chunk 2 := by
  change segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 20 10 =
    ⟨0, 1301487241689684703912216883730015315873026283328234252586617556574150614825915050931107467336⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_002_sideCheck :
    segmentChunkSideCheck ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 20 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_003 :
    segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 30 10 =
      SparseUpperHybridGenerated.Box06.chunk 3 := by
  change segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 30 10 =
    ⟨0, 14330045272314278428986398643343448005329817349014041244737086682429685602460797180201859885⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_003_sideCheck :
    segmentChunkSideCheck ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 30 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_004 :
    segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 40 10 =
      SparseUpperHybridGenerated.Box06.chunk 4 := by
  change segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 40 10 =
    ⟨0, 48125230288323161725198314013459992085405366390149651397711345929504332345325897097919014⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_004_sideCheck :
    segmentChunkSideCheck ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 40 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box06
