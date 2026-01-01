import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box04
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box04

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_005 :
    segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 50 10 =
      SparseUpperHybridGenerated.Box04.chunk 5 := by
  change segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 50 10 =
    ⟨0, 68325771653133012571495721152534249003554266371357948827365045629454143923072239207061327⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_005_sideCheck :
    segmentChunkSideCheck ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 50 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_006 :
    segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 60 10 =
      SparseUpperHybridGenerated.Box04.chunk 6 := by
  change segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 60 10 =
    ⟨0, 419986762840044019759861124044578872202125332024888969303222504024567409686672494629462⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_006_sideCheck :
    segmentChunkSideCheck ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 60 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_007 :
    segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 70 10 =
      SparseUpperHybridGenerated.Box04.chunk 7 := by
  change segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 70 10 =
    ⟨0, 1682599935039901908562400509155463502525130447858213308799126684535391790131252515058⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_007_sideCheck :
    segmentChunkSideCheck ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 70 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_008 :
    segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 80 10 =
      SparseUpperHybridGenerated.Box04.chunk 8 := by
  change segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 80 10 =
    ⟨0, 4998321391878217245165056060081585892725121252425624598284182871082691350511500194⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_008_sideCheck :
    segmentChunkSideCheck ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 80 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_009 :
    segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 90 10 =
      SparseUpperHybridGenerated.Box04.chunk 9 := by
  change segmentChunk ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 90 10 =
    ⟨0, 12297349716774144741943535392262084756292638929120857773865572711695102504722815⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_009_sideCheck :
    segmentChunkSideCheck ⟨1 / 1024, 5 / 4096, 313 / 500, 9, 1 / 2⟩ ⟨0, 1 / 280, 280⟩ 90 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box04
