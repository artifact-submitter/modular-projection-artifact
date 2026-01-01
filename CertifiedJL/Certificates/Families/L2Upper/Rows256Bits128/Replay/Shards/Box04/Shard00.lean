import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box04
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box04

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_000 :
    segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 0 10 =
      SparseUpperHybridGenerated.Box04.chunk 0 := by
  change segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 0 10 =
    ⟨0, 111804077368915555005260188194876157623183192380072815047547259814923626199984375587611079844713⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_000_sideCheck :
    segmentChunkSideCheck ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_001 :
    segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 10 10 =
      SparseUpperHybridGenerated.Box04.chunk 1 := by
  change segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 10 10 =
    ⟨0, 41403076927291837837617179980248953322069645298784779212881754449135720119500556473587668789922⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_001_sideCheck :
    segmentChunkSideCheck ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 10 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_002 :
    segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 20 10 =
      SparseUpperHybridGenerated.Box04.chunk 2 := by
  change segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 20 10 =
    ⟨0, 5532228400381881971679400288446002314026211913868389057755376859938099926968314579530740327177⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_002_sideCheck :
    segmentChunkSideCheck ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 20 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_003 :
    segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 30 10 =
      SparseUpperHybridGenerated.Box04.chunk 3 := by
  change segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 30 10 =
    ⟨0, 285176071258035715905219041680381029063566962350031971154237928699428804795780834003152746116⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_003_sideCheck :
    segmentChunkSideCheck ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 30 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_004 :
    segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 40 10 =
      SparseUpperHybridGenerated.Box04.chunk 4 := by
  change segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 40 10 =
    ⟨0, 6298689976474842101625607272498574065161936224403847312816340685899150851837035304054383531⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_004_sideCheck :
    segmentChunkSideCheck ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 40 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box04
