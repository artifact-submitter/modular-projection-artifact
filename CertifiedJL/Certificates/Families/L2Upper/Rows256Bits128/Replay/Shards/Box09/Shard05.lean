import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box09
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box09

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_025 :
    segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 35, 70⟩ 0 10 =
      SparseUpperHybridGenerated.Box09.chunk 25 := by
  change segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 35, 70⟩ 0 10 =
    ⟨0, 179421396314673027554767422298713618817328085226777876552251⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_025_sideCheck :
    segmentChunkSideCheck ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 35, 70⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_026 :
    segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 35, 70⟩ 10 10 =
      SparseUpperHybridGenerated.Box09.chunk 26 := by
  change segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 35, 70⟩ 10 10 =
    ⟨0, 1267048314776961209948141969560539385635005455766378582726607637784892052745232773782663900535⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_026_sideCheck :
    segmentChunkSideCheck ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 35, 70⟩ 10 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_027 :
    segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 35, 70⟩ 20 10 =
      SparseUpperHybridGenerated.Box09.chunk 27 := by
  change segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 35, 70⟩ 20 10 =
    ⟨0, 3552107446722380024472718573330599067955803925056934210593418641176256776198068132744762148353⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_027_sideCheck :
    segmentChunkSideCheck ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 35, 70⟩ 20 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_028 :
    segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 35, 70⟩ 30 10 =
      SparseUpperHybridGenerated.Box09.chunk 28 := by
  change segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 35, 70⟩ 30 10 =
    ⟨0, 1348086615467264452691762546572740559410758309031820706776989896034115372724232761519042746624⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_028_sideCheck :
    segmentChunkSideCheck ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 35, 70⟩ 30 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_029 :
    segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 35, 70⟩ 40 10 =
      SparseUpperHybridGenerated.Box09.chunk 29 := by
  change segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 35, 70⟩ 40 10 =
    ⟨0, 555394124692473714094637809363902023703014731520186496315858576089969378959317681287548081692⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_029_sideCheck :
    segmentChunkSideCheck ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 35, 70⟩ 40 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box09
