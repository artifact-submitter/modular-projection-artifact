/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Common

/-!
# The 256-row, 152-bit, threshold-365 upper-contour instance

This instance retunes the exact 128-bit threshold-338 contour profile to the
152-bit target. It uses the compact segmented mesh from the high-security
contour family.
-/

namespace CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365

open CertifiedJL.SparseUpperContourFamily.Instances

def parameters : Parameters where
  precision := 512
  rowOddPart := 1
  rowSquareCount := 8
  securityBlockBits := 19
  securityScaleSquarings := 3
  threshold := 365

def profileBoxes : List ProfileBox :=
  [ profileBox 0 (1 / 1024) (6241 / 10000) (743 / 1000) (59 / 100) mesh180,
    profileBox (1 / 1024) (1 / 512) (6245 / 10000) (891 / 1000) (41 / 100) mesh180,
    profileBox (1 / 512) (3 / 1024) (6252 / 10000) (993 / 1000) (29 / 100) mesh180,
    profileBox (3 / 1024) (1 / 256) (6257 / 10000) (1073 / 1000) (21 / 100) mesh180,
    profileBox (1 / 256) (3 / 512) (6260 / 10000) (1201 / 1000) (7 / 100) mesh180,
    profileBox (3 / 512) (1 / 128) (6268 / 10000) (1294 / 1000) 0 mesh180,
    profileBox (1 / 128) (1 / 64) (6265 / 10000) (1511 / 1000) 0 mesh180,
    profileBox (1 / 64) (3 / 128) (6291 / 10000) (1617 / 1000) 0 mesh180,
    profileBox (3 / 128) (1 / 32) (6315 / 10000) (1659 / 1000) 0 mesh180,
    profileBox (1 / 32) (1 / 20) (6331 / 10000) (1692 / 1000) 0 mesh180 ]

def highProfile : HighProfileBox where
  profileMinimum := 1 / 20
  lam := 131 / 200
  target := 1

theorem rows_eq : parameters.rows = 256 := by decide
theorem securityBits_eq : parameters.securityBits = 152 := by decide
theorem profileBoxCount_eq : profileBoxes.length = 10 := by decide
theorem cellCount_eq : familyCellCount profileBoxes = 1800 := by decide
theorem chunkCount_eq : familyChunkCount profileBoxes = 90 := by decide
theorem replayShardCount_eq : familyReplayShardCount 4 profileBoxes = 30 := by decide

end CertifiedJL.SparseUpperContourFamily.Instances.Rows256Bits152Threshold365
