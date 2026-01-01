import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box05
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box05

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_000 :
    segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 0 10 =
      SparseUpperHybridGenerated.Box05.chunk 0 := by
  change segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 0 10 =
    ⟨0, 115598660865791997568377312145426401234524927244818378219863528869797265826910223027213945638148⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_000_sideCheck :
    segmentChunkSideCheck ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_001 :
    segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 10 10 =
      SparseUpperHybridGenerated.Box05.chunk 1 := by
  change segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 10 10 =
    ⟨0, 37274518633326171068360652990767299811443254565095271791311264357195737897444987406369631913469⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_001_sideCheck :
    segmentChunkSideCheck ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 10 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_002 :
    segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 20 10 =
      SparseUpperHybridGenerated.Box05.chunk 2 := by
  change segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 20 10 =
    ⟨0, 3756862778222369085469320577330122921889968764768820915775020699588562522849496739104460859528⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_002_sideCheck :
    segmentChunkSideCheck ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 20 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_003 :
    segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 30 10 =
      SparseUpperHybridGenerated.Box05.chunk 3 := by
  change segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 30 10 =
    ⟨0, 128563839268666756207621647431189807063530484510837754391900428438282293887846368449562517517⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_003_sideCheck :
    segmentChunkSideCheck ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 30 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_004 :
    segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 40 10 =
      SparseUpperHybridGenerated.Box05.chunk 4 := by
  change segmentChunk ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 40 10 =
    ⟨0, 1709080805025858696954974308758911688070626132060039349859315042961665148669464073479543470⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_004_sideCheck :
    segmentChunkSideCheck ⟨5 / 4096, 3 / 2048, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 260, 260⟩ 40 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box05
