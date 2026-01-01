import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box06
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box06

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_005 :
    segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 50 10 =
      SparseUpperHybridGenerated.Box06.chunk 5 := by
  change segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 50 10 =
    ⟨0, 65574532974320617108038055821852032546055728860666565020480576493437231459953588075313⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_005_sideCheck :
    segmentChunkSideCheck ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 50 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_006 :
    segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 60 10 =
      SparseUpperHybridGenerated.Box06.chunk 6 := by
  change segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 60 10 =
    ⟨0, 48087444873835038365010079055428393943236863386246002000281683188064693065162927642⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_006_sideCheck :
    segmentChunkSideCheck ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 60 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_007 :
    segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 70 10 =
      SparseUpperHybridGenerated.Box06.chunk 7 := by
  change segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 70 10 =
    ⟨0, 24304071095261077139531870137811882847914318438804717425165944739647524905796528⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_007_sideCheck :
    segmentChunkSideCheck ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 70 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_008 :
    segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 80 10 =
      SparseUpperHybridGenerated.Box06.chunk 8 := by
  change segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 80 10 =
    ⟨0, 10313219149413966815733806382754225546779122651170293890331078927442265662862⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_008_sideCheck :
    segmentChunkSideCheck ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 80 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_009 :
    segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 90 10 =
      SparseUpperHybridGenerated.Box06.chunk 9 := by
  change segmentChunk ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 90 10 =
    ⟨0, 4259834882258032873449585257426367315750970039503097014397197155181741047⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_009_sideCheck :
    segmentChunkSideCheck ⟨3 / 2048, 7 / 4096, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩ 90 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box06
