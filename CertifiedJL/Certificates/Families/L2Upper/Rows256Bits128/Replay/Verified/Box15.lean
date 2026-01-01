import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Shards.Box15.Shard00
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Shards.Box15.Shard01

namespace CertifiedJL.SparseUpperHybrid

open UpperContourKernel

private def certificate : CertificateBox := certificateBoxes.getD 15 default

private def generatedCertificate : CertificateBox :=
  ⟨⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩,
    [ ⟨0, 1 / 40, 40⟩,
      ⟨1, 1 / 13, 13⟩,
      ⟨2, 1 / 2, 4⟩,
      ⟨4, 1, 4⟩,
      ⟨8, 1, 0⟩ ]⟩

private theorem certificate_eq_generated :
    certificate = generatedCertificate := by
  decide +kernel

private def generatedPlan : List Chunk :=
  [ ⟨0, 0, 10⟩,
    ⟨0, 10, 10⟩,
    ⟨0, 20, 10⟩,
    ⟨0, 30, 10⟩,
    ⟨1, 0, 10⟩,
    ⟨1, 10, 3⟩,
    ⟨2, 0, 4⟩,
    ⟨3, 0, 4⟩ ]

private theorem chunkPlan_eq_generated :
    certificateChunkPlan certificate = generatedPlan := by
  decide +kernel

private theorem computedChunks_eq_generated :
    (certificateChunkPlan certificate).map (certificateChunkValue certificate) =
      SparseUpperHybridGenerated.Box15.chunks := by
  rw [chunkPlan_eq_generated, certificate_eq_generated]
  simp only [generatedPlan, generatedCertificate, certificateChunkValue,
    List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
  rw [Internal.Box15.chunk_000,
    Internal.Box15.chunk_001,
    Internal.Box15.chunk_002,
    Internal.Box15.chunk_003,
    Internal.Box15.chunk_004,
    Internal.Box15.chunk_005,
    Internal.Box15.chunk_006,
    Internal.Box15.chunk_007]
  norm_num [SparseUpperHybridGenerated.Box15.chunk,
    SparseUpperHybridGenerated.Box15.chunks]
  rfl

private def segment0_chunkRanges : List (ℕ × ℕ) :=
  [ (0, 10), (10, 10), (20, 10), (30, 10) ]

private theorem segment0_chunkRanges_cover :
    chunkRangesCover 40 segment0_chunkRanges = true := by
  decide +kernel

private theorem segment0_chunkRanges_sideChecks :
    segment0_chunkRanges.all (fun chunk =>
      segmentChunkSideCheck ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨0, 1 / 40, 40⟩
        chunk.1 chunk.2) = true := by
  simp only [segment0_chunkRanges, List.all_cons, List.all_nil, Bool.and_eq_true]
  exact ⟨Internal.Box15.chunk_000_sideCheck,
    Internal.Box15.chunk_001_sideCheck,
    Internal.Box15.chunk_002_sideCheck,
    Internal.Box15.chunk_003_sideCheck,
    True.intro⟩

private def segment1_chunkRanges : List (ℕ × ℕ) :=
  [ (0, 10), (10, 3) ]

private theorem segment1_chunkRanges_cover :
    chunkRangesCover 13 segment1_chunkRanges = true := by
  decide +kernel

private theorem segment1_chunkRanges_sideChecks :
    segment1_chunkRanges.all (fun chunk =>
      segmentChunkSideCheck ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨1, 1 / 13, 13⟩
        chunk.1 chunk.2) = true := by
  simp only [segment1_chunkRanges, List.all_cons, List.all_nil, Bool.and_eq_true]
  exact ⟨Internal.Box15.chunk_004_sideCheck,
    Internal.Box15.chunk_005_sideCheck,
    True.intro⟩

private def segment2_chunkRanges : List (ℕ × ℕ) :=
  [ (0, 4) ]

private theorem segment2_chunkRanges_cover :
    chunkRangesCover 4 segment2_chunkRanges = true := by
  decide +kernel

private theorem segment2_chunkRanges_sideChecks :
    segment2_chunkRanges.all (fun chunk =>
      segmentChunkSideCheck ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨2, 1 / 2, 4⟩
        chunk.1 chunk.2) = true := by
  simp only [segment2_chunkRanges, List.all_cons, List.all_nil, Bool.and_eq_true]
  exact ⟨Internal.Box15.chunk_006_sideCheck,
    True.intro⟩

private def segment3_chunkRanges : List (ℕ × ℕ) :=
  [ (0, 4) ]

private theorem segment3_chunkRanges_cover :
    chunkRangesCover 4 segment3_chunkRanges = true := by
  decide +kernel

private theorem segment3_chunkRanges_sideChecks :
    segment3_chunkRanges.all (fun chunk =>
      segmentChunkSideCheck ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨4, 1, 4⟩
        chunk.1 chunk.2) = true := by
  simp only [segment3_chunkRanges, List.all_cons, List.all_nil, Bool.and_eq_true]
  exact ⟨Internal.Box15.chunk_007_sideCheck,
    True.intro⟩

private def segment4_chunkRanges : List (ℕ × ℕ) :=
  [  ]

private theorem segment4_chunkRanges_cover :
    chunkRangesCover 0 segment4_chunkRanges = true := by
  decide +kernel

private theorem segment4_chunkRanges_sideChecks :
    segment4_chunkRanges.all (fun chunk =>
      segmentChunkSideCheck ⟨1 / 64, 3 / 128, 631 / 1000, 7, 11 / 10⟩ ⟨8, 1, 0⟩
        chunk.1 chunk.2) = true := by rfl


theorem certificate_15_finiteTail_lo_eq_zero :
    (finiteIntegralFrom
      ((certificateChunkPlan (certificateBoxes.getD 15 default)).map
        (certificateChunkValue (certificateBoxes.getD 15 default))) +
      tail (certificateBoxes.getD 15 default).box).lo = 0 := by
  change (finiteIntegralFrom
    ((certificateChunkPlan certificate).map (certificateChunkValue certificate)) +
      tail certificate.box).lo = 0
  rw [computedChunks_eq_generated, certificate_eq_generated]
  decide +kernel

theorem certificate_15_finiteTail_nonneg :
    0 ≤ (finiteIntegralFrom
      ((certificateChunkPlan (certificateBoxes.getD 15 default)).map
        (certificateChunkValue (certificateBoxes.getD 15 default))) +
      tail (certificateBoxes.getD 15 default).box).lo := by
  rw [certificate_15_finiteTail_lo_eq_zero]

theorem certificate_15_finiteTail_valid :
    (finiteIntegralFrom
      ((certificateChunkPlan (certificateBoxes.getD 15 default)).map
        (certificateChunkValue (certificateBoxes.getD 15 default))) +
      tail (certificateBoxes.getD 15 default).box).Valid := by
  change (finiteIntegralFrom
    ((certificateChunkPlan certificate).map (certificateChunkValue certificate)) +
      tail certificate.box).Valid
  rw [computedChunks_eq_generated, certificate_eq_generated]
  change (finiteIntegralFrom SparseUpperHybridGenerated.Box15.chunks +
      tail generatedCertificate.box).lo ≤
    (finiteIntegralFrom SparseUpperHybridGenerated.Box15.chunks +
      tail generatedCertificate.box).hi
  decide +kernel

set_option maxRecDepth 10000 in
theorem certificate_15_sideChecks :
    ∀ segment ∈ (certificateBoxes.getD 15 default).segments,
      ∀ i < segment.count,
        hybridCellSideCheck (certificateBoxes.getD 15 default).box
          segment i = true := by
  change ∀ segment ∈ certificate.segments, ∀ i < segment.count,
    hybridCellSideCheck certificate.box segment i = true
  rw [certificate_eq_generated]
  intro segment hsegment i hi
  norm_num [generatedCertificate] at hsegment
  rcases hsegment with rfl | rfl | rfl | rfl | rfl
  · exact segmentSideChecks_of_chunkRanges _ _ segment0_chunkRanges
      segment0_chunkRanges_cover segment0_chunkRanges_sideChecks i hi
  · exact segmentSideChecks_of_chunkRanges _ _ segment1_chunkRanges
      segment1_chunkRanges_cover segment1_chunkRanges_sideChecks i hi
  · exact segmentSideChecks_of_chunkRanges _ _ segment2_chunkRanges
      segment2_chunkRanges_cover segment2_chunkRanges_sideChecks i hi
  · exact segmentSideChecks_of_chunkRanges _ _ segment3_chunkRanges
      segment3_chunkRanges_cover segment3_chunkRanges_sideChecks i hi
  · exact segmentSideChecks_of_chunkRanges _ _ segment4_chunkRanges
      segment4_chunkRanges_cover segment4_chunkRanges_sideChecks i hi

private def generatedBound : DInterval precision :=
  boxBoundFrom certificate.box SparseUpperHybridGenerated.Box15.chunks

private theorem generatedCheck :
    Interval.upperLTCheck generatedBound 1 = true := by
  decide +kernel

theorem certificate_15_upperRat_lt :
    (certificateBound (certificateBoxes.getD 15 default)).upperRat < 1 := by
  have hbound : certificateBound certificate = generatedBound := by
    simp only [certificateBound, generatedBound,
      computedChunks_eq_generated]
  have hcheck := generatedCheck
  rw [← hbound] at hcheck
  exact Interval.upperLTCheck_sound hcheck

end CertifiedJL.SparseUpperHybrid
