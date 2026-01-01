import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box04
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box04

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_020 :
    segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 200 10 =
      SparseUpperHybridGenerated.Box04.chunk 20 := by
  change segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 200 10 =
    ⟨0, 5209864705091949797679998719182275226308034840528149⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_020_sideCheck :
    segmentChunkSideCheck ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 200 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_021 :
    segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 210 10 =
      SparseUpperHybridGenerated.Box04.chunk 21 := by
  change segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 210 10 =
    ⟨0, 37374521455823433218686340077570197115171953316513⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_021_sideCheck :
    segmentChunkSideCheck ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 210 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_022 :
    segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 220 10 =
      SparseUpperHybridGenerated.Box04.chunk 22 := by
  change segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 220 10 =
    ⟨0, 310165188851917527163231336523518522939624003505⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_022_sideCheck :
    segmentChunkSideCheck ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 220 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_023 :
    segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 230 10 =
      SparseUpperHybridGenerated.Box04.chunk 23 := by
  change segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 230 10 =
    ⟨0, 2968298077649435120811637866352243617372085502⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_023_sideCheck :
    segmentChunkSideCheck ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 230 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_024 :
    segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 240 10 =
      SparseUpperHybridGenerated.Box04.chunk 24 := by
  change segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 240 10 =
    ⟨0, 32643380124447741544890312964888427063886885⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_024_sideCheck :
    segmentChunkSideCheck ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 240 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box04
