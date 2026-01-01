import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box02
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box02

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_010 :
    segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 100 10 =
      SparseUpperHybridGenerated.Box02.chunk 10 := by
  change segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 100 10 =
    ⟨0, 1748886343879311774589343141704019794082840087889704948090941605729278914762759⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_010_sideCheck :
    segmentChunkSideCheck ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 100 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_011 :
    segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 110 10 =
      SparseUpperHybridGenerated.Box02.chunk 11 := by
  change segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 110 10 =
    ⟨0, 5855062604169402295895889413891825190102015757710047065273783354686956639518⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_011_sideCheck :
    segmentChunkSideCheck ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 110 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_012 :
    segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 120 10 =
      SparseUpperHybridGenerated.Box02.chunk 12 := by
  change segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 120 10 =
    ⟨0, 19427239537595516056240971672781369926886149997674139142499506208062643405⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_012_sideCheck :
    segmentChunkSideCheck ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 120 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_013 :
    segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 130 10 =
      SparseUpperHybridGenerated.Box02.chunk 13 := by
  change segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 130 10 =
    ⟨0, 66596049106771205084997519972227891861385852989742160141154241464081236⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_013_sideCheck :
    segmentChunkSideCheck ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 130 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_014 :
    segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 140 10 =
      SparseUpperHybridGenerated.Box02.chunk 14 := by
  change segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 140 10 =
    ⟨0, 243376496862470532448239669979811354323290187824954422188614823157566⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_014_sideCheck :
    segmentChunkSideCheck ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 140 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box02
