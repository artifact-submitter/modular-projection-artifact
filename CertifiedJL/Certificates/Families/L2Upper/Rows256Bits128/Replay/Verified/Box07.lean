import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Shards.Box07.Shard00
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Shards.Box07.Shard01
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Shards.Box07.Shard02
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Shards.Box07.Shard03
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Shards.Box07.Shard04
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Shards.Box07.Shard05
import CertifiedJL.Certificates.Families.L2Upper.Rows256Bits128.Replay.Shards.Box07.Shard06

namespace CertifiedJL.SparseUpperHybrid

open UpperContourKernel

private def certificate : CertificateBox := certificateBoxes.getD 7 default

private def generatedCertificate : CertificateBox :=
  ⟨⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩,
    [ ⟨0, 1 / 220, 220⟩,
      ⟨1, 1 / 50, 50⟩,
      ⟨2, 1 / 25, 50⟩,
      ⟨4, 1 / 4, 16⟩,
      ⟨8, 1, 0⟩ ]⟩

private theorem certificate_eq_generated :
    certificate = generatedCertificate := by
  decide +kernel

private def generatedPlan : List Chunk :=
  [ ⟨0, 0, 10⟩,
    ⟨0, 10, 10⟩,
    ⟨0, 20, 10⟩,
    ⟨0, 30, 10⟩,
    ⟨0, 40, 10⟩,
    ⟨0, 50, 10⟩,
    ⟨0, 60, 10⟩,
    ⟨0, 70, 10⟩,
    ⟨0, 80, 10⟩,
    ⟨0, 90, 10⟩,
    ⟨0, 100, 10⟩,
    ⟨0, 110, 10⟩,
    ⟨0, 120, 10⟩,
    ⟨0, 130, 10⟩,
    ⟨0, 140, 10⟩,
    ⟨0, 150, 10⟩,
    ⟨0, 160, 10⟩,
    ⟨0, 170, 10⟩,
    ⟨0, 180, 10⟩,
    ⟨0, 190, 10⟩,
    ⟨0, 200, 10⟩,
    ⟨0, 210, 10⟩,
    ⟨1, 0, 10⟩,
    ⟨1, 10, 10⟩,
    ⟨1, 20, 10⟩,
    ⟨1, 30, 10⟩,
    ⟨1, 40, 10⟩,
    ⟨2, 0, 10⟩,
    ⟨2, 10, 10⟩,
    ⟨2, 20, 10⟩,
    ⟨2, 30, 10⟩,
    ⟨2, 40, 10⟩,
    ⟨3, 0, 10⟩,
    ⟨3, 10, 6⟩ ]

private theorem chunkPlan_eq_generated :
    certificateChunkPlan certificate = generatedPlan := by
  decide +kernel

private theorem computedChunks_eq_generated :
    (certificateChunkPlan certificate).map (certificateChunkValue certificate) =
      SparseUpperHybridGenerated.Box07.chunks := by
  rw [chunkPlan_eq_generated, certificate_eq_generated]
  simp only [generatedPlan, generatedCertificate, certificateChunkValue,
    List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
  rw [Internal.Box07.chunk_000,
    Internal.Box07.chunk_001,
    Internal.Box07.chunk_002,
    Internal.Box07.chunk_003,
    Internal.Box07.chunk_004,
    Internal.Box07.chunk_005,
    Internal.Box07.chunk_006,
    Internal.Box07.chunk_007,
    Internal.Box07.chunk_008,
    Internal.Box07.chunk_009,
    Internal.Box07.chunk_010,
    Internal.Box07.chunk_011,
    Internal.Box07.chunk_012,
    Internal.Box07.chunk_013,
    Internal.Box07.chunk_014,
    Internal.Box07.chunk_015,
    Internal.Box07.chunk_016,
    Internal.Box07.chunk_017,
    Internal.Box07.chunk_018,
    Internal.Box07.chunk_019,
    Internal.Box07.chunk_020,
    Internal.Box07.chunk_021,
    Internal.Box07.chunk_022,
    Internal.Box07.chunk_023,
    Internal.Box07.chunk_024,
    Internal.Box07.chunk_025,
    Internal.Box07.chunk_026,
    Internal.Box07.chunk_027,
    Internal.Box07.chunk_028,
    Internal.Box07.chunk_029,
    Internal.Box07.chunk_030,
    Internal.Box07.chunk_031,
    Internal.Box07.chunk_032,
    Internal.Box07.chunk_033]
  norm_num [SparseUpperHybridGenerated.Box07.chunk,
    SparseUpperHybridGenerated.Box07.chunks]
  rfl

private def segment0_chunkRanges : List (ℕ × ℕ) :=
  [ (0, 10), (10, 10), (20, 10), (30, 10), (40, 10), (50, 10), (60, 10), (70, 10), (80, 10), (90, 10), (100, 10), (110, 10), (120, 10), (130, 10), (140, 10), (150, 10), (160, 10), (170, 10), (180, 10), (190, 10), (200, 10), (210, 10) ]

private theorem segment0_chunkRanges_cover :
    chunkRangesCover 220 segment0_chunkRanges = true := by
  decide +kernel

private theorem segment0_chunkRanges_sideChecks :
    segment0_chunkRanges.all (fun chunk =>
      segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨0, 1 / 220, 220⟩
        chunk.1 chunk.2) = true := by
  simp only [segment0_chunkRanges, List.all_cons, List.all_nil, Bool.and_eq_true]
  exact ⟨Internal.Box07.chunk_000_sideCheck,
    Internal.Box07.chunk_001_sideCheck,
    Internal.Box07.chunk_002_sideCheck,
    Internal.Box07.chunk_003_sideCheck,
    Internal.Box07.chunk_004_sideCheck,
    Internal.Box07.chunk_005_sideCheck,
    Internal.Box07.chunk_006_sideCheck,
    Internal.Box07.chunk_007_sideCheck,
    Internal.Box07.chunk_008_sideCheck,
    Internal.Box07.chunk_009_sideCheck,
    Internal.Box07.chunk_010_sideCheck,
    Internal.Box07.chunk_011_sideCheck,
    Internal.Box07.chunk_012_sideCheck,
    Internal.Box07.chunk_013_sideCheck,
    Internal.Box07.chunk_014_sideCheck,
    Internal.Box07.chunk_015_sideCheck,
    Internal.Box07.chunk_016_sideCheck,
    Internal.Box07.chunk_017_sideCheck,
    Internal.Box07.chunk_018_sideCheck,
    Internal.Box07.chunk_019_sideCheck,
    Internal.Box07.chunk_020_sideCheck,
    Internal.Box07.chunk_021_sideCheck,
    True.intro⟩

private def segment1_chunkRanges : List (ℕ × ℕ) :=
  [ (0, 10), (10, 10), (20, 10), (30, 10), (40, 10) ]

private theorem segment1_chunkRanges_cover :
    chunkRangesCover 50 segment1_chunkRanges = true := by
  decide +kernel

private theorem segment1_chunkRanges_sideChecks :
    segment1_chunkRanges.all (fun chunk =>
      segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨1, 1 / 50, 50⟩
        chunk.1 chunk.2) = true := by
  simp only [segment1_chunkRanges, List.all_cons, List.all_nil, Bool.and_eq_true]
  exact ⟨Internal.Box07.chunk_022_sideCheck,
    Internal.Box07.chunk_023_sideCheck,
    Internal.Box07.chunk_024_sideCheck,
    Internal.Box07.chunk_025_sideCheck,
    Internal.Box07.chunk_026_sideCheck,
    True.intro⟩

private def segment2_chunkRanges : List (ℕ × ℕ) :=
  [ (0, 10), (10, 10), (20, 10), (30, 10), (40, 10) ]

private theorem segment2_chunkRanges_cover :
    chunkRangesCover 50 segment2_chunkRanges = true := by
  decide +kernel

private theorem segment2_chunkRanges_sideChecks :
    segment2_chunkRanges.all (fun chunk =>
      segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨2, 1 / 25, 50⟩
        chunk.1 chunk.2) = true := by
  simp only [segment2_chunkRanges, List.all_cons, List.all_nil, Bool.and_eq_true]
  exact ⟨Internal.Box07.chunk_027_sideCheck,
    Internal.Box07.chunk_028_sideCheck,
    Internal.Box07.chunk_029_sideCheck,
    Internal.Box07.chunk_030_sideCheck,
    Internal.Box07.chunk_031_sideCheck,
    True.intro⟩

private def segment3_chunkRanges : List (ℕ × ℕ) :=
  [ (0, 10), (10, 6) ]

private theorem segment3_chunkRanges_cover :
    chunkRangesCover 16 segment3_chunkRanges = true := by
  decide +kernel

private theorem segment3_chunkRanges_sideChecks :
    segment3_chunkRanges.all (fun chunk =>
      segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨4, 1 / 4, 16⟩
        chunk.1 chunk.2) = true := by
  simp only [segment3_chunkRanges, List.all_cons, List.all_nil, Bool.and_eq_true]
  exact ⟨Internal.Box07.chunk_032_sideCheck,
    Internal.Box07.chunk_033_sideCheck,
    True.intro⟩

private def segment4_chunkRanges : List (ℕ × ℕ) :=
  [  ]

private theorem segment4_chunkRanges_cover :
    chunkRangesCover 0 segment4_chunkRanges = true := by
  decide +kernel

private theorem segment4_chunkRanges_sideChecks :
    segment4_chunkRanges.all (fun chunk =>
      segmentChunkSideCheck ⟨7 / 4096, 1 / 512, 313 / 500, 10, 1 / 2⟩ ⟨8, 1, 0⟩
        chunk.1 chunk.2) = true := by rfl


theorem certificate_07_finiteTail_lo_eq_zero :
    (finiteIntegralFrom
      ((certificateChunkPlan (certificateBoxes.getD 7 default)).map
        (certificateChunkValue (certificateBoxes.getD 7 default))) +
      tail (certificateBoxes.getD 7 default).box).lo = 0 := by
  change (finiteIntegralFrom
    ((certificateChunkPlan certificate).map (certificateChunkValue certificate)) +
      tail certificate.box).lo = 0
  rw [computedChunks_eq_generated, certificate_eq_generated]
  decide +kernel

theorem certificate_07_finiteTail_nonneg :
    0 ≤ (finiteIntegralFrom
      ((certificateChunkPlan (certificateBoxes.getD 7 default)).map
        (certificateChunkValue (certificateBoxes.getD 7 default))) +
      tail (certificateBoxes.getD 7 default).box).lo := by
  rw [certificate_07_finiteTail_lo_eq_zero]

theorem certificate_07_finiteTail_valid :
    (finiteIntegralFrom
      ((certificateChunkPlan (certificateBoxes.getD 7 default)).map
        (certificateChunkValue (certificateBoxes.getD 7 default))) +
      tail (certificateBoxes.getD 7 default).box).Valid := by
  change (finiteIntegralFrom
    ((certificateChunkPlan certificate).map (certificateChunkValue certificate)) +
      tail certificate.box).Valid
  rw [computedChunks_eq_generated, certificate_eq_generated]
  change (finiteIntegralFrom SparseUpperHybridGenerated.Box07.chunks +
      tail generatedCertificate.box).lo ≤
    (finiteIntegralFrom SparseUpperHybridGenerated.Box07.chunks +
      tail generatedCertificate.box).hi
  decide +kernel

set_option maxRecDepth 10000 in
theorem certificate_07_sideChecks :
    ∀ segment ∈ (certificateBoxes.getD 7 default).segments,
      ∀ i < segment.count,
        hybridCellSideCheck (certificateBoxes.getD 7 default).box
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
  boxBoundFrom certificate.box SparseUpperHybridGenerated.Box07.chunks

private theorem generatedCheck :
    Interval.upperLTCheck generatedBound 1 = true := by
  decide +kernel

theorem certificate_07_upperRat_lt :
    (certificateBound (certificateBoxes.getD 7 default)).upperRat < 1 := by
  have hbound : certificateBound certificate = generatedBound := by
    simp only [certificateBound, generatedBound,
      computedChunks_eq_generated]
  have hcheck := generatedCheck
  rw [← hbound] at hcheck
  exact Interval.upperLTCheck_sound hcheck

end CertifiedJL.SparseUpperHybrid
