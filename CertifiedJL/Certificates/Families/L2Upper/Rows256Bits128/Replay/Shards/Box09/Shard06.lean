import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box09
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box09

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_030 :
    segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 35, 70⟩ 50 10 =
      SparseUpperHybridGenerated.Box09.chunk 30 := by
  change segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 35, 70⟩ 50 10 =
    ⟨0, 245313874105005939619742366619188336621966885162622007737657301910318593368067984285265838485⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_030_sideCheck :
    segmentChunkSideCheck ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 35, 70⟩ 50 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_031 :
    segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 35, 70⟩ 60 10 =
      SparseUpperHybridGenerated.Box09.chunk 31 := by
  change segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 35, 70⟩ 60 10 =
    ⟨0, 115018366421151319187131967417434571545567823661173802387758895919806448437037110320522409026⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_031_sideCheck :
    segmentChunkSideCheck ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨2, 1 / 35, 70⟩ 60 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_032 :
    segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨4, 1 / 4, 16⟩ 0 10 =
      SparseUpperHybridGenerated.Box09.chunk 32 := by
  change segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨4, 1 / 4, 16⟩ 0 10 =
    ⟨0, 154629601616339949839667188396687393854943605721872830531025919696551864653833232264667301441⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_032_sideCheck :
    segmentChunkSideCheck ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨4, 1 / 4, 16⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_033 :
    segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨4, 1 / 4, 16⟩ 10 6 =
      SparseUpperHybridGenerated.Box09.chunk 33 := by
  change segmentChunk ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨4, 1 / 4, 16⟩ 10 6 =
    ⟨0, 1564951434813275178335171152025349626784491519530240591729977617103013705719316970986422951⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_033_sideCheck :
    segmentChunkSideCheck ⟨5 / 2048, 3 / 1024, 5 / 8, 9, 3 / 5⟩ ⟨4, 1 / 4, 16⟩ 10 6 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box09
