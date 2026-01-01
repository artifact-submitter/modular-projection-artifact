import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box00
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box00

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_010 :
    segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 100 10 =
      SparseUpperHybridGenerated.Box00.chunk 10 := by
  change segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 100 10 =
    ⟨0, 1876027872954409575484095834802124351254336342082179739998106140469057⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_010_sideCheck :
    segmentChunkSideCheck ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 100 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_011 :
    segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 110 10 =
      SparseUpperHybridGenerated.Box00.chunk 11 := by
  change segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 110 10 =
    ⟨0, 979373633367536648982170095625807509887661196158612922659364392982⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_011_sideCheck :
    segmentChunkSideCheck ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 110 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_012 :
    segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 120 10 =
      SparseUpperHybridGenerated.Box00.chunk 12 := by
  change segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 120 10 =
    ⟨0, 618918125906705248785489475428728665506635615911528114513357307⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_012_sideCheck :
    segmentChunkSideCheck ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 120 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_013 :
    segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 130 10 =
      SparseUpperHybridGenerated.Box00.chunk 13 := by
  change segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 130 10 =
    ⟨0, 486167594388217672032002472653157927251681211303320234590086⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_013_sideCheck :
    segmentChunkSideCheck ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 130 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_014 :
    segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 140 10 =
      SparseUpperHybridGenerated.Box00.chunk 14 := by
  change segmentChunk ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 140 10 =
    ⟨0, 481248167340308384039539405328214093736748194320119245613⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_014_sideCheck :
    segmentChunkSideCheck ⟨0, 1 / 4096, 5 / 8, 11, 3 / 10⟩ ⟨0, 1 / 220, 220⟩ 140 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box00
