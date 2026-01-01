import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box12
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box12

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_015 :
    segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨2, 1 / 9, 18⟩ 0 10 =
      SparseUpperHybridGenerated.Box12.chunk 15 := by
  change segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨2, 1 / 9, 18⟩ 0 10 =
    ⟨0, 8412047071186346246623153954935775204021966260663227271059657202807416244918170187205981372060⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_015_sideCheck :
    segmentChunkSideCheck ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨2, 1 / 9, 18⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_016 :
    segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨2, 1 / 9, 18⟩ 10 8 =
      SparseUpperHybridGenerated.Box12.chunk 16 := by
  change segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨2, 1 / 9, 18⟩ 10 8 =
    ⟨0, 247544676209398678450421729010318929121060907002093573876416471628254181012772157220054917975⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_016_sideCheck :
    segmentChunkSideCheck ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨2, 1 / 9, 18⟩ 10 8 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_017 :
    segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨4, 1, 4⟩ 0 4 =
      SparseUpperHybridGenerated.Box12.chunk 17 := by
  change segmentChunk ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨4, 1, 4⟩ 0 4 =
    ⟨0, 80937319514862329730162384280403967811709710792770292955736403253634324088023064747235922488⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_017_sideCheck :
    segmentChunkSideCheck ⟨3 / 512, 1 / 128, 627 / 1000, 8, 4 / 5⟩ ⟨4, 1, 4⟩ 0 4 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box12
