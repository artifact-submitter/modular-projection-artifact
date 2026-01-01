import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Data.Box11
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Soundness.ChunkSideCheck

namespace CertifiedJL.SparseUpperHybrid.Internal.Box11

set_option linter.style.longLine false

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_035 :
    segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨2, 1 / 30, 60⟩ 20 10 =
      SparseUpperHybridGenerated.Box11.chunk 35 := by
  change segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨2, 1 / 30, 60⟩ 20 10 =
    ⟨0, 770854542456911145885008672044595768283871619520287216400925599113046232082794718519356274008⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_035_sideCheck :
    segmentChunkSideCheck ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨2, 1 / 30, 60⟩ 20 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_036 :
    segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨2, 1 / 30, 60⟩ 30 10 =
      SparseUpperHybridGenerated.Box11.chunk 36 := by
  change segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨2, 1 / 30, 60⟩ 30 10 =
    ⟨0, 260756463948287024556780215462549416393276556451813295593153570599020234633853599407381300944⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_036_sideCheck :
    segmentChunkSideCheck ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨2, 1 / 30, 60⟩ 30 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_037 :
    segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨2, 1 / 30, 60⟩ 40 10 =
      SparseUpperHybridGenerated.Box11.chunk 37 := by
  change segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨2, 1 / 30, 60⟩ 40 10 =
    ⟨0, 97698349395270782920320248778200718101523744962590841036779467074838477432780555485585733340⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_037_sideCheck :
    segmentChunkSideCheck ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨2, 1 / 30, 60⟩ 40 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_038 :
    segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨2, 1 / 30, 60⟩ 50 10 =
      SparseUpperHybridGenerated.Box11.chunk 38 := by
  change segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨2, 1 / 30, 60⟩ 50 10 =
    ⟨0, 39851147591808545051207442548403134144511881669272732237731544320951206773984107643704341910⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_038_sideCheck :
    segmentChunkSideCheck ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨2, 1 / 30, 60⟩ 50 10 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Direct ten-cell interval replay needs a larger budget than ordinary proofs.
theorem chunk_039 :
    segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨4, 1 / 4, 16⟩ 0 10 =
      SparseUpperHybridGenerated.Box11.chunk 39 := by
  change segmentChunk ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨4, 1 / 4, 16⟩ 0 10 =
    ⟨0, 42574276561331508175099328270888956157325944156704851179760480204730377095609331456243500102⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The compact ten-cell side-condition replay uses the same bounded budget.
theorem chunk_039_sideCheck :
    segmentChunkSideCheck ⟨1 / 256, 3 / 512, 627 / 1000, 9, 7 / 10⟩ ⟨4, 1 / 4, 16⟩ 0 10 = true := by
  decide +kernel

end CertifiedJL.SparseUpperHybrid.Internal.Box11
