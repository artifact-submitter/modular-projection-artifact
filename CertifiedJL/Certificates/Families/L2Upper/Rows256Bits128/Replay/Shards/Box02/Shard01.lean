import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box02
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box02

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_005 :
    segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 50 10 =
      SparseUpperHybridGenerated.Box02.chunk 5 := by
  change segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 50 10 =
    ⟨0, 337799882560447982834838702732756105372913232967465765487398913963675483978416999299048581⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_005_sideCheck :
    segmentChunkSideCheck ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 50 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_006 :
    segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 60 10 =
      SparseUpperHybridGenerated.Box02.chunk 6 := by
  change segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 60 10 =
    ⟨0, 3517537059876294550031493976002223649354840935411774871796280412791461920417293693170873⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_006_sideCheck :
    segmentChunkSideCheck ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 60 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_007 :
    segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 70 10 =
      SparseUpperHybridGenerated.Box02.chunk 7 := by
  change segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 70 10 =
    ⟨0, 24075053223719854832294546264603287682515121299249755892660136496714323296219708174671⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_007_sideCheck :
    segmentChunkSideCheck ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 70 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_008 :
    segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 80 10 =
      SparseUpperHybridGenerated.Box02.chunk 8 := by
  change segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 80 10 =
    ⟨0, 120875490148794200299673381436074148198161037832529479612860202313158131899418880503⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_008_sideCheck :
    segmentChunkSideCheck ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 80 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_009 :
    segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 90 10 =
      SparseUpperHybridGenerated.Box02.chunk 9 := by
  change segmentChunk ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 90 10 =
    ⟨0, 490682448283514157060678596214587858415718909102876643400343690130316303061269637⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_009_sideCheck :
    segmentChunkSideCheck ⟨1 / 2048, 3 / 4096, 5 / 8, 12, 2 / 5⟩ ⟨0, 1 / 300, 300⟩ 90 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box02
