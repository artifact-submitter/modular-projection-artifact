import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box07
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box07

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_015 :
    segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 150 10 =
      SparseUpperHybridGenerated.Box07.chunk 15 := by
  change segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 150 10 =
    ⟨0, 675845394806213418526877628716559432175821387134491320⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_015_sideCheck :
    segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 150 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_016 :
    segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 160 10 =
      SparseUpperHybridGenerated.Box07.chunk 16 := by
  change segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 160 10 =
    ⟨0, 1124501769363206641822918045672828228032639936941161⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_016_sideCheck :
    segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 160 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_017 :
    segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 170 10 =
      SparseUpperHybridGenerated.Box07.chunk 17 := by
  change segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 170 10 =
    ⟨0, 2396276128753975018498690406588311988432226694397⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_017_sideCheck :
    segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 170 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_018 :
    segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 180 10 =
      SparseUpperHybridGenerated.Box07.chunk 18 := by
  change segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 180 10 =
    ⟨0, 6513159823251264067542492374704749340319319747⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_018_sideCheck :
    segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 180 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_019 :
    segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 190 10 =
      SparseUpperHybridGenerated.Box07.chunk 19 := by
  change segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 190 10 =
    ⟨0, 22467207990777460179031108259251016772425188⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_019_sideCheck :
    segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 190 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box07
