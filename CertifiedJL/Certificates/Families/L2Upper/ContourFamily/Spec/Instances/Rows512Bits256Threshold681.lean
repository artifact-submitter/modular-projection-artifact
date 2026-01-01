/-
Copyright (c) 2026 Anonymous Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous Author
-/

import CertifiedJL.Certificates.Families.L2Upper.ContourFamily.Spec.Instances.Common

/-!
# The 512-row, 256-bit, threshold-681 upper-contour instance

This source instance transcribes the corresponding positive configuration in
`verify_high_security_upper_contour_configs.py`. Two difficult boxes use the
48-cell override mesh; the remaining thirty-three use the 46-cell mesh. It
contains data only, with semantic contour proofs supplied separately.
-/

namespace CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681

open CertifiedJL.SparseUpperContourFamily.Instances

def parameters : Parameters where
  precision := 512
  rowOddPart := 1
  rowSquareCount := 9
  securityBlockBits := 16
  securityScaleSquarings := 4
  threshold := 681

def profileBoxes : List ProfileBox :=
  [ profileBox 0 (1 / 8192) (5 / 8) (1 / 2) (9 / 10) mesh46,
    profileBox (1 / 8192) (1 / 4096) (5 / 8) (3 / 5) (4 / 5) mesh46,
    profileBox (1 / 4096) (3 / 8192) (5 / 8) (3 / 5) (4 / 5) mesh46,
    profileBox (3 / 8192) (7 / 16384) (5 / 8) (3 / 5) (4 / 5) mesh46,
    profileBox (7 / 16384) (1 / 2048) (5 / 8) (7 / 10) (3 / 5) mesh46,
    profileBox (1 / 2048) (9 / 16384) (5 / 8) (7 / 10) (3 / 5) mesh46,
    profileBox (9 / 16384) (5 / 8192) (5 / 8) (7 / 10) (3 / 5) mesh46,
    profileBox (5 / 8192) (11 / 16384) (5 / 8) (7 / 10) (3 / 5) mesh46,
    profileBox (11 / 16384) (3 / 4096) (5 / 8) (7 / 10) (3 / 5) mesh46,
    profileBox (3 / 4096) (25 / 32768) (5 / 8) (7 / 10) (3 / 5) mesh46,
    profileBox (25 / 32768) (13 / 16384) (313 / 500) (39 / 50)
      (11 / 20) mesh46,
    profileBox (13 / 16384) (27 / 32768) (313 / 500) (39 / 50)
      (11 / 20) mesh46,
    profileBox (27 / 32768) (7 / 8192) (313 / 500) (39 / 50)
      (11 / 20) mesh46,
    profileBox (7 / 8192) (15 / 16384) (313 / 500) (39 / 50)
      (11 / 20) mesh46,
    profileBox (15 / 16384) (1 / 1024) (313 / 500) (39 / 50)
      (11 / 20) mesh46,
    profileBox (1 / 1024) (17 / 16384) (5 / 8) (4 / 5) (1 / 2) mesh46,
    profileBox (17 / 16384) (9 / 8192) (5 / 8) (4 / 5) (1 / 2) mesh46,
    profileBox (9 / 8192) (19 / 16384) (5 / 8) (4 / 5) (1 / 2) mesh46,
    profileBox (19 / 16384) (5 / 4096) (5 / 8) (4 / 5) (1 / 2) mesh46,
    profileBox (5 / 4096) (21 / 16384) (5 / 8) (4 / 5) (1 / 2) mesh46,
    profileBox (21 / 16384) (11 / 8192) (5 / 8) (4 / 5) (1 / 2) mesh46,
    profileBox (11 / 8192) (23 / 16384) (623 / 1000) (891 / 1000)
      (41 / 100) mesh46,
    profileBox (23 / 16384) (3 / 2048) (623 / 1000) (891 / 1000)
      (41 / 100) mesh46,
    profileBox (3 / 2048) (13 / 8192) (623 / 1000) (891 / 1000)
      (41 / 100) mesh46,
    profileBox (13 / 8192) (7 / 4096) (623 / 1000) (891 / 1000)
      (41 / 100) mesh46,
    profileBox (7 / 4096) (1 / 512) (5 / 8) 1 (3 / 10) mesh46,
    profileBox (1 / 512) (5 / 2048) (5 / 8) 1 (3 / 10) mesh48,
    profileBox (5 / 2048) (3 / 1024) (5 / 8) 1 (3 / 10) mesh48,
    profileBox (3 / 1024) (1 / 256) (5 / 8) (6 / 5) (1 / 10) mesh46,
    profileBox (1 / 256) (3 / 512) (5 / 8) (6 / 5) (1 / 10) mesh46,
    profileBox (3 / 512) (1 / 128) (623 / 1000) (647 / 500) 0 mesh46,
    profileBox (1 / 128) (1 / 64) (623 / 1000) (1511 / 1000) 0 mesh46,
    profileBox (1 / 64) (3 / 128) (623 / 1000) (1617 / 1000) 0 mesh46,
    profileBox (3 / 128) (1 / 32) (623 / 1000) (1659 / 1000) 0 mesh46,
    profileBox (1 / 32) (1 / 20) (623 / 1000) (423 / 250) 0 mesh46 ]

def highProfile : HighProfileBox where
  profileMinimum := 1 / 20
  lam := 82 / 125
  target := 1

theorem rows_eq : parameters.rows = 512 := by decide
theorem securityBits_eq : parameters.securityBits = 256 := by decide
theorem profileBoxCount_eq : profileBoxes.length = 35 := by decide
theorem cellCount_eq : familyCellCount profileBoxes = 1614 := by decide
theorem chunkCount_eq : familyChunkCount profileBoxes = 175 := by decide
theorem replayShardCount_eq : familyReplayShardCount 4 profileBoxes = 70 := by decide

end CertifiedJL.SparseUpperContourFamily.Instances.Rows512Bits256Threshold681
