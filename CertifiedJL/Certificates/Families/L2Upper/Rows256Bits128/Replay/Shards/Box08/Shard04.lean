import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box08
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box08

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_020 :
    segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 200 10 =
      SparseUpperHybridGenerated.Box08.chunk 20 := by
  change segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 200 10 =
    ⟨0, 9866652591810348084039564949387446858260517367885967⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_020_sideCheck :
    segmentChunkSideCheck ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 200 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_021 :
    segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 210 10 =
      SparseUpperHybridGenerated.Box08.chunk 21 := by
  change segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 210 10 =
    ⟨0, 74882365559455333836615844284994861123765863710202⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_021_sideCheck :
    segmentChunkSideCheck ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 210 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_022 :
    segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 220 10 =
      SparseUpperHybridGenerated.Box08.chunk 22 := by
  change segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 220 10 =
    ⟨0, 663944307289852867159236126311117796494247881966⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_022_sideCheck :
    segmentChunkSideCheck ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 220 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_023 :
    segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 230 10 =
      SparseUpperHybridGenerated.Box08.chunk 23 := by
  change segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 230 10 =
    ⟨0, 6867244207159697517016427547984961092503939691⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_023_sideCheck :
    segmentChunkSideCheck ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 230 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_024 :
    segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 240 10 =
      SparseUpperHybridGenerated.Box08.chunk 24 := by
  change segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 240 10 =
    ⟨0, 82721758171964249533914230154270304855741719⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_024_sideCheck :
    segmentChunkSideCheck ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 240 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box08
