import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box16
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box16

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_000 :
    segmentChunk ⟨3 / 128, 1 / 32, 631 / 1000, 7, 11 / 10⟩ ⟨0, 1 / 16, 16⟩ 0 10 =
      SparseUpperHybridGenerated.Box16.chunk 0 := by
  change segmentChunk ⟨3 / 128, 1 / 32, 631 / 1000, 7, 11 / 10⟩ ⟨0, 1 / 16, 16⟩ 0 10 =
    ⟨0, 122671210363422780942370053959253885440126858697092601521970291864581197813246641497857521924696⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_000_sideCheck :
    segmentChunkSideCheck ⟨3 / 128, 1 / 32, 631 / 1000, 7, 11 / 10⟩ ⟨0, 1 / 16, 16⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_001 :
    segmentChunk ⟨3 / 128, 1 / 32, 631 / 1000, 7, 11 / 10⟩ ⟨0, 1 / 16, 16⟩ 10 6 =
      SparseUpperHybridGenerated.Box16.chunk 1 := by
  change segmentChunk ⟨3 / 128, 1 / 32, 631 / 1000, 7, 11 / 10⟩ ⟨0, 1 / 16, 16⟩ 10 6 =
    ⟨0, 54813825384074615160793555277582916126098005053665630608132101919622682138507627⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_001_sideCheck :
    segmentChunkSideCheck ⟨3 / 128, 1 / 32, 631 / 1000, 7, 11 / 10⟩ ⟨0, 1 / 16, 16⟩ 10 6 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_002 :
    segmentChunk ⟨3 / 128, 1 / 32, 631 / 1000, 7, 11 / 10⟩ ⟨1, 1 / 11, 11⟩ 0 10 =
      SparseUpperHybridGenerated.Box16.chunk 2 := by
  change segmentChunk ⟨3 / 128, 1 / 32, 631 / 1000, 7, 11 / 10⟩ ⟨1, 1 / 11, 11⟩ 0 10 =
    ⟨0, 32339150974209454225663480505694864525752846606876240532147534230358816960688566370156420220245⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_002_sideCheck :
    segmentChunkSideCheck ⟨3 / 128, 1 / 32, 631 / 1000, 7, 11 / 10⟩ ⟨1, 1 / 11, 11⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_003 :
    segmentChunk ⟨3 / 128, 1 / 32, 631 / 1000, 7, 11 / 10⟩ ⟨1, 1 / 11, 11⟩ 10 1 =
      SparseUpperHybridGenerated.Box16.chunk 3 := by
  change segmentChunk ⟨3 / 128, 1 / 32, 631 / 1000, 7, 11 / 10⟩ ⟨1, 1 / 11, 11⟩ 10 1 =
    ⟨0, 284532946915612633254571438738326157623780490377082680730078960655219101825391477870143024297⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_003_sideCheck :
    segmentChunkSideCheck ⟨3 / 128, 1 / 32, 631 / 1000, 7, 11 / 10⟩ ⟨1, 1 / 11, 11⟩ 10 1 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_004 :
    segmentChunk ⟨3 / 128, 1 / 32, 631 / 1000, 7, 11 / 10⟩ ⟨2, 1, 2⟩ 0 2 =
      SparseUpperHybridGenerated.Box16.chunk 4 := by
  change segmentChunk ⟨3 / 128, 1 / 32, 631 / 1000, 7, 11 / 10⟩ ⟨2, 1, 2⟩ 0 2 =
    ⟨0, 2339885303348934383078740602584125096911476890123224012558042737964926200194981504670577462072⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_004_sideCheck :
    segmentChunkSideCheck ⟨3 / 128, 1 / 32, 631 / 1000, 7, 11 / 10⟩ ⟨2, 1, 2⟩ 0 2 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box16
