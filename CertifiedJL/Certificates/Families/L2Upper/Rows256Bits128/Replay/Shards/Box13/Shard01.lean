import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box13
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box13

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_005 :
    segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 50 10 =
      SparseUpperHybridGenerated.Box13.chunk 5 := by
  change segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 50 10 =
    ⟨0, 261215091014199042142200709416568073432659565248495422610489945893932732084⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_005_sideCheck :
    segmentChunkSideCheck ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 50 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_006 :
    segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 60 10 =
      SparseUpperHybridGenerated.Box13.chunk 6 := by
  change segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 60 10 =
    ⟨0, 590229327980649146776781923064692353271001680163947982946441542645963⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_006_sideCheck :
    segmentChunkSideCheck ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 60 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_007 :
    segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 70 10 =
      SparseUpperHybridGenerated.Box13.chunk 7 := by
  change segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 70 10 =
    ⟨0, 2836050449650102046561720348683682383402466927571597280481477786⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_007_sideCheck :
    segmentChunkSideCheck ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 70 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_008 :
    segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 80 10 =
      SparseUpperHybridGenerated.Box13.chunk 8 := by
  change segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 80 10 =
    ⟨0, 40006229501468042012726028486420338435176518672504909871452⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_008_sideCheck :
    segmentChunkSideCheck ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 80 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_009 :
    segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 90 10 =
      SparseUpperHybridGenerated.Box13.chunk 9 := by
  change segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 90 10 =
    ⟨0, 2122183123144826536054230766228451701326109363853766507⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_009_sideCheck :
    segmentChunkSideCheck ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨0, 1 / 126, 126⟩ 90 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box13
