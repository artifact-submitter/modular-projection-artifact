import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box07
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box07

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_005 :
    segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 50 10 =
      SparseUpperHybridGenerated.Box07.chunk 5 := by
  change segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 50 10 =
    ⟨0, 66377598579001976272130310821411288510384647142533863927170947640484432879222052017498⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_005_sideCheck :
    segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 50 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_006 :
    segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 60 10 =
      SparseUpperHybridGenerated.Box07.chunk 6 := by
  change segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 60 10 =
    ⟨0, 48935930316513438324938715404732521014463603782323628827575706982374001895404494041⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_006_sideCheck :
    segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 60 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_007 :
    segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 70 10 =
      SparseUpperHybridGenerated.Box07.chunk 7 := by
  change segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 70 10 =
    ⟨0, 24837813954259473158353193642789957867556925826105534085353137446232278503092717⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_007_sideCheck :
    segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 70 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_008 :
    segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 80 10 =
      SparseUpperHybridGenerated.Box07.chunk 8 := by
  change segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 80 10 =
    ⟨0, 10576088753613337776417475744325111567362429581869504406261966537486433230641⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_008_sideCheck :
    segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 80 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_009 :
    segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 90 10 =
      SparseUpperHybridGenerated.Box07.chunk 9 := by
  change segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 90 10 =
    ⟨0, 4381819256720624208935110425816588341387513007805458547782545195870409959⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_009_sideCheck :
    segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 90 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box07
