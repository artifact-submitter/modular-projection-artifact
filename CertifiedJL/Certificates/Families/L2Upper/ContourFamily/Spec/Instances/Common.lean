/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Numeric.Core

/-!
# Shared data for the high-security sparse upper-contour instances

These meshes are a direct transcription of
`paper/artifact/upper-gap/verify_high_security_upper_contour_configs.py`.
The common box constructor fixes the certificate target, frequency cutoff,
and kernel chunk size shared by all four configurations.
-/

namespace CertifiedJL.SparseUpperContourFamily.Instances

def mesh180 : List Segment :=
  [ ⟨0, 1 / 200, 100⟩,
    ⟨1 / 2, 1 / 100, 50⟩,
    ⟨1, 1 / 10, 10⟩,
    ⟨2, 1 / 5, 10⟩,
    ⟨4, 2 / 5, 10⟩ ]

/-- Compact five-segment mesh for the 512-row threshold-681 instance. -/
def mesh46 : List Segment :=
  [ ⟨0, 1 / 50, 25⟩,
    ⟨1 / 2, 1 / 20, 10⟩,
    ⟨1, 1 / 5, 5⟩,
    ⟨2, 2 / 3, 3⟩,
    ⟨4, 4 / 3, 3⟩ ]

/-- Slightly finer tail mesh for the two difficult threshold-681 boxes. -/
def mesh48 : List Segment :=
  [ ⟨0, 1 / 50, 25⟩,
    ⟨1 / 2, 1 / 20, 10⟩,
    ⟨1, 1 / 5, 5⟩,
    ⟨2, 1 / 2, 4⟩,
    ⟨4, 1, 4⟩ ]

def mesh285 : List Segment :=
  [ ⟨0, 1 / 300, 150⟩,
    ⟨1 / 2, 1 / 150, 75⟩,
    ⟨1, 1 / 20, 20⟩,
    ⟨2, 1 / 10, 20⟩,
    ⟨4, 1 / 5, 20⟩ ]

/-- A high-security profile box with the shared target, cutoff, and kernel
chunk size used by the exact Python configurations. -/
def profileBox (profileLeft profileRight lam sigma theta : ℚ)
    (segments : List Segment) : ProfileBox where
  profileLeft := profileLeft
  profileRight := profileRight
  lam := lam
  sigma := sigma
  theta := theta
  target := 1
  cutoff := 8
  segments := segments
  chunkSize := 25

def segmentCellCount (segments : List Segment) : ℕ :=
  (segments.map Segment.count).sum

def familyCellCount (boxes : List ProfileBox) : ℕ :=
  (boxes.map fun box ↦ segmentCellCount box.segments).sum

def profileChunkCount (box : ProfileBox) : ℕ :=
  (box.segments.map fun segment ↦
    (segment.count + box.chunkSize - 1) / box.chunkSize).sum

def familyChunkCount (boxes : List ProfileBox) : ℕ :=
  (boxes.map profileChunkCount).sum

/-- Number of replay modules when consecutive chunks are grouped without
crossing a profile-box boundary.  A shard may cross a frequency-segment
boundary; theorem names retain their segment-local identities. -/
def familyReplayShardCount (chunksPerShard : ℕ)
    (boxes : List ProfileBox) : ℕ :=
  (boxes.map fun box ↦
    let chunks := profileChunkCount box
    (chunks + chunksPerShard - 1) / chunksPerShard).sum

end CertifiedJL.SparseUpperContourFamily.Instances
