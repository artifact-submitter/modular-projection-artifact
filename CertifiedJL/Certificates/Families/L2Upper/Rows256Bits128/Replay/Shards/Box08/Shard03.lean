import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box08
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box08

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_015 :
    segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 150 10 =
      SparseUpperHybridGenerated.Box08.chunk 15 := by
  change segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 150 10 =
    ⟨0, 4021431992687626171484441294947056244034280170763120889128417220⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_015_sideCheck :
    segmentChunkSideCheck ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 150 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_016 :
    segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 160 10 =
      SparseUpperHybridGenerated.Box08.chunk 16 := by
  change segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 160 10 =
    ⟨0, 14156911198186560753207167491740432615618324013568708458117020⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_016_sideCheck :
    segmentChunkSideCheck ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 160 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_017 :
    segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 170 10 =
      SparseUpperHybridGenerated.Box08.chunk 17 := by
  change segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 170 10 =
    ⟨0, 57711416796532196619823950257475979808957350946333821264564⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_017_sideCheck :
    segmentChunkSideCheck ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 170 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_018 :
    segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 180 10 =
      SparseUpperHybridGenerated.Box08.chunk 18 := by
  change segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 180 10 =
    ⟨0, 274037406476094563047396286947259400550570726986795301226⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_018_sideCheck :
    segmentChunkSideCheck ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 180 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_019 :
    segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 190 10 =
      SparseUpperHybridGenerated.Box08.chunk 19 := by
  change segmentChunk ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 190 10 =
    ⟨0, 1520374535265410984444449075857947583295962471559901078⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_019_sideCheck :
    segmentChunkSideCheck ⟨1 / 512, 5 / 2048, 5 / 8, 9, 3 / 5⟩ ⟨0, 1 / 280, 280⟩ 190 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box08
