import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box09
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box09

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_000 :
    segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 0 10 =
      SparseUpperHybridGenerated.Box09.chunk 0 := by
  change segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 0 10 =
    ⟨0, 132929214379777803592253095332902567015168713295998217534307755320663598020115307107314670136045⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_000_sideCheck :
    segmentChunkSideCheck ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_001 :
    segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 10 10 =
      SparseUpperHybridGenerated.Box09.chunk 1 := by
  change segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 10 10 =
    ⟨0, 22986582369179193004634408438207800941569420143876639902530681722017442729270670394831404456392⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_001_sideCheck :
    segmentChunkSideCheck ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 10 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_002 :
    segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 20 10 =
      SparseUpperHybridGenerated.Box09.chunk 2 := by
  change segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 20 10 =
    ⟨0, 631193766923168063390524959877955979780780307243845100773506744309317352791849785204096370625⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_002_sideCheck :
    segmentChunkSideCheck ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 20 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_003 :
    segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 30 10 =
      SparseUpperHybridGenerated.Box09.chunk 3 := by
  change segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 30 10 =
    ⟨0, 3303865892072921165240100115306356048084893240383190319845275280895707803743245206511202113⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_003_sideCheck :
    segmentChunkSideCheck ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 30 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_004 :
    segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 40 10 =
      SparseUpperHybridGenerated.Box09.chunk 4 := by
  change segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 40 10 =
    ⟨0, 4594726262636290976057415408314492570297742846194315096513632902515715290287280545083317⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_004_sideCheck :
    segmentChunkSideCheck ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 40 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box09
