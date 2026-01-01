import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box07
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box07

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_030 :
    segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨2, 1 / 25, 50⟩ 30 10 =
      SparseUpperHybridGenerated.Box07.chunk 30 := by
  change segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨2, 1 / 25, 50⟩ 30 10 =
    ⟨0, 1635962490051942109521860443083755681545444464915474285809175036927825981162525236712753148346⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_030_sideCheck :
    segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨2, 1 / 25, 50⟩ 30 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_031 :
    segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨2, 1 / 25, 50⟩ 40 10 =
      SparseUpperHybridGenerated.Box07.chunk 31 := by
  change segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨2, 1 / 25, 50⟩ 40 10 =
    ⟨0, 487590979451877799246279268130364287116048066037437489759017090060496033867991103477582058502⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_031_sideCheck :
    segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨2, 1 / 25, 50⟩ 40 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_032 :
    segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨4, 1 / 4, 16⟩ 0 10 =
      SparseUpperHybridGenerated.Box07.chunk 32 := by
  change segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨4, 1 / 4, 16⟩ 0 10 =
    ⟨0, 339230529369785598470323033824749655813254694635727648769750964413063718951509507404824988305⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_032_sideCheck :
    segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨4, 1 / 4, 16⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_033 :
    segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨4, 1 / 4, 16⟩ 10 6 =
      SparseUpperHybridGenerated.Box07.chunk 33 := by
  change segmentChunk ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨4, 1 / 4, 16⟩ 10 6 =
    ⟨0, 2168747604766689054548031284344810162059030750239481646575836643055844078590080121105183656⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_033_sideCheck :
    segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨4, 1 / 4, 16⟩ 10 6 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box07
