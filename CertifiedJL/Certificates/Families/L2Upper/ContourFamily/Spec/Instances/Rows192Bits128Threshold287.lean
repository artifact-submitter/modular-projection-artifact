/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Common

/-!
# The 192-row, 128-bit, threshold-287 upper-contour instance

This source instance transcribes the exact positive configuration in
`verify_upper_frontier_sparse_contours.py`. It contains data only; the
analytic soundness module supplies the semantic contour proofs separately.
-/

namespace CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287

open CertifiedJL.SparseUpperContourFamily.Instances

def parameters : Parameters where
  precision := 512
  rowOddPart := 3
  rowSquareCount := 6
  securityBlockBits := 8
  securityScaleSquarings := 4
  threshold := 287

def profileBoxes : List ProfileBox :=
  [ profileBox 0 (1 / 1024) (67 / 100) (743 / 1000) (59 / 100) mesh285,
    profileBox (1 / 1024) (1 / 512) (67 / 100) (891 / 1000) (41 / 100) mesh285,
    profileBox (1 / 512) (3 / 1024) (67 / 100) (993 / 1000) (29 / 100) mesh285,
    profileBox (3 / 1024) (1 / 256) (67 / 100) (1073 / 1000) (21 / 100) mesh285,
    profileBox (1 / 256) (3 / 512) (67 / 100) (1201 / 1000) (7 / 100) mesh285,
    profileBox (3 / 512) (1 / 128) (67 / 100) (1294 / 1000) 0 mesh285,
    profileBox (1 / 128) (1 / 64) (67 / 100) (1511 / 1000) 0 mesh285,
    profileBox (1 / 64) (3 / 128) (67 / 100) (1617 / 1000) 0 mesh285,
    profileBox (3 / 128) (1 / 32) (67 / 100) (1659 / 1000) 0 mesh285,
    profileBox (1 / 32) (1 / 20) (67 / 100) (1692 / 1000) 0 mesh285 ]

def highProfile : HighProfileBox where
  profileMinimum := 1 / 20
  lam := 69 / 100
  target := 1

theorem rows_eq : parameters.rows = 192 := by decide
theorem securityBits_eq : parameters.securityBits = 128 := by decide
theorem profileBoxCount_eq : profileBoxes.length = 10 := by decide
theorem cellCount_eq : familyCellCount profileBoxes = 2850 := by decide
theorem chunkCount_eq : familyChunkCount profileBoxes = 120 := by decide
theorem replayShardCount_eq : familyReplayShardCount 4 profileBoxes = 30 := by decide

end CertifiedJL.SparseUpperContourFamily.Instances.Rows192Bits128Threshold287
