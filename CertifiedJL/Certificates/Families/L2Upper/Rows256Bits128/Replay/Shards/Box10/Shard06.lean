import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box10
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box10

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_030 :
    segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨2, 1 / 40, 80⟩ 10 10 =
      SparseUpperHybridGenerated.Box10.chunk 30 := by
  change segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨2, 1 / 40, 80⟩ 10 10 =
    ⟨0, 5446268641203349358285748367383014720768551687501092146467527930456625451103772588948041823993⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_030_sideCheck :
    segmentChunkSideCheck ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨2, 1 / 40, 80⟩ 10 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_031 :
    segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨2, 1 / 40, 80⟩ 20 10 =
      SparseUpperHybridGenerated.Box10.chunk 31 := by
  change segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨2, 1 / 40, 80⟩ 20 10 =
    ⟨0, 2706147610860276047313371455435545685916668898060919922378951010931674026242661906671283189250⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_031_sideCheck :
    segmentChunkSideCheck ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨2, 1 / 40, 80⟩ 20 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_032 :
    segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨2, 1 / 40, 80⟩ 30 10 =
      SparseUpperHybridGenerated.Box10.chunk 32 := by
  change segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨2, 1 / 40, 80⟩ 30 10 =
    ⟨0, 1032698171585974667348832720086643651744061665535203245724148189416974573277593852076970364232⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_032_sideCheck :
    segmentChunkSideCheck ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨2, 1 / 40, 80⟩ 30 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_033 :
    segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨2, 1 / 40, 80⟩ 40 10 =
      SparseUpperHybridGenerated.Box10.chunk 33 := by
  change segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨2, 1 / 40, 80⟩ 40 10 =
    ⟨0, 424406405685188477581201415500565109826337606615851994894829424950604077622592428976983214503⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_033_sideCheck :
    segmentChunkSideCheck ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨2, 1 / 40, 80⟩ 40 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_034 :
    segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨2, 1 / 40, 80⟩ 50 10 =
      SparseUpperHybridGenerated.Box10.chunk 34 := by
  change segmentChunk ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨2, 1 / 40, 80⟩ 50 10 =
    ⟨0, 185924820878364230671021353265594497292645926837091575178332241534293269977112255039094744394⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_034_sideCheck :
    segmentChunkSideCheck ⟨3 / 1024, 1 / 256, 627 / 1000, 10, 3 / 5⟩ ⟨2, 1 / 40, 80⟩ 50 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box10
