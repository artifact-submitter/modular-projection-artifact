import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box11
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box11

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_030 :
    segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨1, 1 / 50, 50⟩ 20 10 =
      SparseUpperHybridGenerated.Box11.chunk 30 := by
  change segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨1, 1 / 50, 50⟩ 20 10 =
    ⟨0, 770319997859325234323918139498342590289364⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_030_sideCheck :
    segmentChunkSideCheck ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨1, 1 / 50, 50⟩ 20 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_031 :
    segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨1, 1 / 50, 50⟩ 30 10 =
      SparseUpperHybridGenerated.Box11.chunk 31 := by
  change segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨1, 1 / 50, 50⟩ 30 10 =
    ⟨0, 47745079618698644812721002772138726819137807505494753356703⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_031_sideCheck :
    segmentChunkSideCheck ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨1, 1 / 50, 50⟩ 30 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_032 :
    segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨1, 1 / 50, 50⟩ 40 10 =
      SparseUpperHybridGenerated.Box11.chunk 32 := by
  change segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨1, 1 / 50, 50⟩ 40 10 =
    ⟨0, 81941970870423478147269770837357193170421981189500096034402107049212779232218607408570⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_032_sideCheck :
    segmentChunkSideCheck ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨1, 1 / 50, 50⟩ 40 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_033 :
    segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨2, 1 / 30, 60⟩ 0 10 =
      SparseUpperHybridGenerated.Box11.chunk 33 := by
  change segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨2, 1 / 30, 60⟩ 0 10 =
    ⟨0, 8371584972641344584638379967076666131716942652953531283527685175393152064049924426939040691887⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_033_sideCheck :
    segmentChunkSideCheck ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨2, 1 / 30, 60⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_034 :
    segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨2, 1 / 30, 60⟩ 10 10 =
      SparseUpperHybridGenerated.Box11.chunk 34 := by
  change segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨2, 1 / 30, 60⟩ 10 10 =
    ⟨0, 2581911370101520714207884147508276790993013660818715843715466132965678508583437147757935877427⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_034_sideCheck :
    segmentChunkSideCheck ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨2, 1 / 30, 60⟩ 10 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box11
