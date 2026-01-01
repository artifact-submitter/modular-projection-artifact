import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box00
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box00

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_000 :
    segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 0 10 =
      SparseUpperHybridGenerated.Box00.chunk 0 := by
  change segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 0 10 =
    ⟨0, 130590869295079592634842044964217836502082852048154146925889643325014373147852999124558806382816⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_000_sideCheck :
    segmentChunkSideCheck ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_001 :
    segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 10 10 =
      SparseUpperHybridGenerated.Box00.chunk 1 := by
  change segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 10 10 =
    ⟨0, 28451079449409053842613864220438331923507594378116576312129431229949580356144760178594311403356⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_001_sideCheck :
    segmentChunkSideCheck ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 10 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_002 :
    segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 20 10 =
      SparseUpperHybridGenerated.Box00.chunk 2 := by
  change segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 20 10 =
    ⟨0, 1289605351192352861490298635413954296038512202840779955059972097280968376980958707745221975394⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_002_sideCheck :
    segmentChunkSideCheck ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 20 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_003 :
    segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 30 10 =
      SparseUpperHybridGenerated.Box00.chunk 3 := by
  change segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 30 10 =
    ⟨0, 13955317321386864119409883743219877567640197506211235827620717587240902790853287492022697555⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_003_sideCheck :
    segmentChunkSideCheck ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 30 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_004 :
    segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 40 10 =
      SparseUpperHybridGenerated.Box00.chunk 4 := by
  change segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 40 10 =
    ⟨0, 46048289697623538626315668181366137822391790240939149727696835071311407757624877117200181⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_004_sideCheck :
    segmentChunkSideCheck ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 40 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box00
