import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box11
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box11

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_000 :
    segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨0, 1 / 280, 280⟩ 0 10 =
      SparseUpperHybridGenerated.Box11.chunk 0 := by
  change segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨0, 1 / 280, 280⟩ 0 10 =
    ⟨0, 104159890144703823246038499431502460172984852580059342313618630537973842677222865826939000085392⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_000_sideCheck :
    segmentChunkSideCheck ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨0, 1 / 280, 280⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_001 :
    segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨0, 1 / 280, 280⟩ 10 10 =
      SparseUpperHybridGenerated.Box11.chunk 1 := by
  change segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨0, 1 / 280, 280⟩ 10 10 =
    ⟨0, 39841450246550392733061721492643040665327327453891222980504573157838609846450390464958607950880⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_001_sideCheck :
    segmentChunkSideCheck ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨0, 1 / 280, 280⟩ 10 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_002 :
    segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨0, 1 / 280, 280⟩ 20 10 =
      SparseUpperHybridGenerated.Box11.chunk 2 := by
  change segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨0, 1 / 280, 280⟩ 20 10 =
    ⟨0, 5510187197904942145874658467023967702442332040805535002332612729633192589995007316867130345434⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_002_sideCheck :
    segmentChunkSideCheck ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨0, 1 / 280, 280⟩ 20 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_003 :
    segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨0, 1 / 280, 280⟩ 30 10 =
      SparseUpperHybridGenerated.Box11.chunk 3 := by
  change segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨0, 1 / 280, 280⟩ 30 10 =
    ⟨0, 297154419556004545938229518750117061600783330309846136615669494396223799399561510458638341863⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_003_sideCheck :
    segmentChunkSideCheck ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨0, 1 / 280, 280⟩ 30 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_004 :
    segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨0, 1 / 280, 280⟩ 40 10 =
      SparseUpperHybridGenerated.Box11.chunk 4 := by
  change segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨0, 1 / 280, 280⟩ 40 10 =
    ⟨0, 7081895739013127654862934165210211109037217911135677247939544593206181245813686280303613147⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_004_sideCheck :
    segmentChunkSideCheck ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨0, 1 / 280, 280⟩ 40 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box11
