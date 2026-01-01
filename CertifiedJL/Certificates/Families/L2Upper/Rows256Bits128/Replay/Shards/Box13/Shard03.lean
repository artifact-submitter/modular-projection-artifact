import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box13
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box13

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_015 :
    segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨1, 1 / 21, 21⟩ 20 1 =
      SparseUpperHybridGenerated.Box13.chunk 15 := by
  change segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨1, 1 / 21, 21⟩ 20 1 =
    ⟨0, 410228827491209829205146464383592495317338402923710097625809647997594422920576714145527981814⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_015_sideCheck :
    segmentChunkSideCheck ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨1, 1 / 21, 21⟩ 20 1 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_016 :
    segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨2, 1 / 5, 10⟩ 0 10 =
      SparseUpperHybridGenerated.Box13.chunk 16 := by
  change segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨2, 1 / 5, 10⟩ 0 10 =
    ⟨0, 2461353906124008010016579340696586620774364328816230470115467906733377285745878156409334611490⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_016_sideCheck :
    segmentChunkSideCheck ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨2, 1 / 5, 10⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_017 :
    segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨4, 1, 4⟩ 0 4 =
      SparseUpperHybridGenerated.Box13.chunk 17 := by
  change segmentChunk ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨4, 1, 4⟩ 0 4 =
    ⟨0, 10672654434573212879498470981733724777911774494006565005524224543374890813482577779395270485⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_017_sideCheck :
    segmentChunkSideCheck ⟨1 / 128, 3 / 256, 627 / 1000, 9, 9 / 10⟩ ⟨4, 1, 4⟩ 0 4 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box13
