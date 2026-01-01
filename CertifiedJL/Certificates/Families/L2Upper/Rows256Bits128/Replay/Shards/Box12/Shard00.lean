import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box12
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box12

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_000 :
    segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 0 10 =
      SparseUpperHybridGenerated.Box12.chunk 0 := by
  change segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 0 10 =
    ⟨0, 143155389094221668254433207668542468433804553947273000735011071215105223051504767941756583914044⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_000_sideCheck :
    segmentChunkSideCheck ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_001 :
    segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 10 10 =
      SparseUpperHybridGenerated.Box12.chunk 1 := by
  change segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 10 10 =
    ⟨0, 3660940458159450886435485747361968336070344128680996188902638921683842816453836697831910911035⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_001_sideCheck :
    segmentChunkSideCheck ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 10 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_002 :
    segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 20 10 =
      SparseUpperHybridGenerated.Box12.chunk 2 := by
  change segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 20 10 =
    ⟨0, 1349631440029330794047628545372007256460498765355505703922346506913311322899002890116821773⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_002_sideCheck :
    segmentChunkSideCheck ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 20 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_003 :
    segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 30 10 =
      SparseUpperHybridGenerated.Box12.chunk 3 := by
  change segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 30 10 =
    ⟨0, 19608145125466598072483305803202451245960799193300230285163255030987358664289594242024⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_003_sideCheck :
    segmentChunkSideCheck ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 30 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_004 :
    segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 40 10 =
      SparseUpperHybridGenerated.Box12.chunk 4 := by
  change segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 40 10 =
    ⟨0, 46896285446982237801642590021006374547008486583872582845653723596540297168950567⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_004_sideCheck :
    segmentChunkSideCheck ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨0, 1 / 125, 125⟩ 40 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box12
