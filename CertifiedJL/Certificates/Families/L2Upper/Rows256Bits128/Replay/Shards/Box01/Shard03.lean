import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box01
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box01

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_015 :
    segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 150 10 =
      SparseUpperHybridGenerated.Box01.chunk 15 := by
  change segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 150 10 =
    ⟨0, 2264062504401877232976468872390495606527978798842885070636027187⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_015_sideCheck :
    segmentChunkSideCheck ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 150 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_016 :
    segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 160 10 =
      SparseUpperHybridGenerated.Box01.chunk 16 := by
  change segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 160 10 =
    ⟨0, 7713747130091118166460965293089456917722756612673390374330183⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_016_sideCheck :
    segmentChunkSideCheck ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 160 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_017 :
    segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 170 10 =
      SparseUpperHybridGenerated.Box01.chunk 17 := by
  change segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 170 10 =
    ⟨0, 30275662697706677182916426339360684490338333158378508040086⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_017_sideCheck :
    segmentChunkSideCheck ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 170 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_018 :
    segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 180 10 =
      SparseUpperHybridGenerated.Box01.chunk 18 := by
  change segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 180 10 =
    ⟨0, 137487662559703627531690336506122144646247249696982517247⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_018_sideCheck :
    segmentChunkSideCheck ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 180 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_019 :
    segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 190 10 =
      SparseUpperHybridGenerated.Box01.chunk 19 := by
  change segmentChunk ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 190 10 =
    ⟨0, 723470616941492986385590583831164613686583922182810059⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_019_sideCheck :
    segmentChunkSideCheck ⟨1 / 4096, 1 / 2048, 313 / 500, 9, 2 / 5⟩ ⟨0, 1 / 280, 280⟩ 190 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box01
