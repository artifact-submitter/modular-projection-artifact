import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box08
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box08

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_000 :
    segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 0 10 =
      SparseUpperHybridGenerated.Box08.chunk 0 := by
  change segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 0 10 =
    ⟨0, 111229448853638283616469668614999037082535278866524042004089442334676870702357687339185486957485⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_000_sideCheck :
    segmentChunkSideCheck ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_001 :
    segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 10 10 =
      SparseUpperHybridGenerated.Box08.chunk 1 := by
  change segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 10 10 =
    ⟨0, 41805459185502390693377726695172889442505112837972831082768947503502730857660347714119350235306⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_001_sideCheck :
    segmentChunkSideCheck ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 10 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_002 :
    segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 20 10 =
      SparseUpperHybridGenerated.Box08.chunk 2 := by
  change segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 20 10 =
    ⟨0, 5718792964030034692313381740349092168083708540382416737772864762821310481522130986786692002444⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_002_sideCheck :
    segmentChunkSideCheck ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 20 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_003 :
    segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 30 10 =
      SparseUpperHybridGenerated.Box08.chunk 3 := by
  change segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 30 10 =
    ⟨0, 304493929436135956351088261779933702491337059363382665756046392695168956815550950203407062249⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_003_sideCheck :
    segmentChunkSideCheck ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 30 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_004 :
    segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 40 10 =
      SparseUpperHybridGenerated.Box08.chunk 4 := by
  change segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 40 10 =
    ⟨0, 6991114525131587296564649167246420220238540968741684242722523428257087055366460926256156052⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_004_sideCheck :
    segmentChunkSideCheck ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 40 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box08
