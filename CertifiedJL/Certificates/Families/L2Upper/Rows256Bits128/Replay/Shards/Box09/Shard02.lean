import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box09
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box09

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_010 :
    segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 100 10 =
      SparseUpperHybridGenerated.Box09.chunk 10 := by
  change segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 100 10 =
    ⟨0, 1580028469815112530980623939021052977506225058621304163159071781460⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_010_sideCheck :
    segmentChunkSideCheck ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 100 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_011 :
    segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 110 10 =
      SparseUpperHybridGenerated.Box09.chunk 11 := by
  change segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 110 10 =
    ⟨0, 502959420650379104054979225170532439214884577997990195171729428⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_011_sideCheck :
    segmentChunkSideCheck ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 110 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_012 :
    segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 120 10 =
      SparseUpperHybridGenerated.Box09.chunk 12 := by
  change segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 120 10 =
    ⟨0, 211883674940270661633027402589536714740692434585282235141107⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_012_sideCheck :
    segmentChunkSideCheck ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 120 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_013 :
    segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 130 10 =
      SparseUpperHybridGenerated.Box09.chunk 13 := by
  change segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 130 10 =
    ⟨0, 120734909646239900586427880697943350650475874353451434871⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_013_sideCheck :
    segmentChunkSideCheck ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 130 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_014 :
    segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 140 10 =
      SparseUpperHybridGenerated.Box09.chunk 14 := by
  change segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 140 10 =
    ⟨0, 94020391622434769096251603228469398222152104621106386⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_014_sideCheck :
    segmentChunkSideCheck ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 200, 200⟩ 140 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box09
